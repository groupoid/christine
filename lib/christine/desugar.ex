defmodule Christine.Desugar do
  alias Christine.AST

  def desugar(%AST.Module{declarations: decls} = m, env \\ %Christine.Typechecker.Env{}) do
    desugared_decls =
      Enum.map(decls, fn decl ->
        case decl do
          %AST.DeclData{} -> desugar_decl(decl, env)
          _ -> decl
        end
      end)

    ind_map =
      Enum.reduce(desugared_decls, %{}, fn decl, acc ->
        case decl do
          %AST.Inductive{name: n} = ind -> Map.put(acc, n, ind)
          _ -> acc
        end
      end)

    env_with_types = %{env | env: Map.merge(env.env, ind_map)}

    %AST.Module{
      m
      | declarations:
          Enum.map(desugared_decls, fn
            %AST.Inductive{} = d -> d
            d -> desugar_decl(d, env_with_types)
          end)
    }
  end

  def desugar_decl(decl, env \\ %Christine.Typechecker.Env{})

  def desugar_decl({:command, k, expr}, env) do
    {:command, k, desugar_expression(expr, env)}
  end

  def desugar_decl({:module_start, name}, _env), do: {:module_start, name}
  def desugar_decl({:section_start, name}, _env), do: {:section_start, name}
  def desugar_decl({:proof, tacs}, _env), do: {:proof, tacs}
  def desugar_decl({:proof_skipped} = d, _env), do: d
  def desugar_decl({:tactic_skipped, _} = d, _env), do: d

  def desugar_decl(
        %AST.DeclValue{
          name: name,
          binders: binders,
          expr: expr,
          type: type,
          where_decls: where_decls
        },
        env
      ) do
    desugared_where = Enum.map(where_decls || [], &desugar_decl(&1, env))

    if expr do
      expr_with_where =
        if desugared_where == [] do
          expr
        else
          decls_list = Enum.map(desugared_where, fn d -> {d.name, d.expr} end)
          %AST.Let{decls: decls_list, body: expr}
        end

      body =
        Enum.reduce(
          Enum.reverse(binders),
          desugar_expression(expr_with_where, env, name),
          fn
            {vn, vt}, acc ->
              %AST.Lam{name: vn, domain: desugar_expression(vt, env), body: acc}

            %AST.Var{name: vn}, acc ->
              %AST.Lam{name: vn, domain: %AST.Var{name: "Any"}, body: acc}
          end
        )

      desugared_type = if type, do: desugar_expression(type, env), else: nil

      %AST.DeclValue{name: name, binders: [], expr: body, type: desugared_type}
    else
      # Axiom case: expr is nil. We should fold binders into the type (Pi types).
      final_type =
        Enum.reduce(Enum.reverse(binders), desugar_expression(type, env), fn
          {vn, vt}, acc ->
            %AST.Pi{name: vn, domain: desugar_expression(vt, env), codomain: acc}

          %AST.Var{name: vn}, acc ->
            %AST.Pi{name: vn, domain: %AST.Var{name: "Any"}, codomain: acc}
        end)

      %AST.DeclValue{name: name, binders: [], expr: nil, type: final_type}
    end
  end

  def desugar_decl(%AST.DeclData{name: name, params: params, constructors: constructors}, env) do
    # params is list of {name, type}
    ind_params = Enum.map(params, fn {n, ty} -> {n, ty} end)

    # default result type should be (name param1 param2 ...)
    default_res_type =
      Enum.reduce(params, %AST.Var{name: name}, fn {pname, _pty}, acc ->
        %AST.App{func: acc, arg: %AST.Var{name: pname}}
      end)

    constrs =
      Enum.with_index(constructors, 1)
      |> Enum.map(fn {{cname, cparams, ctype}, idx} ->
        # Use explicit ctype if available, else default_res_type
        # When desugaring ctype, we need the inductive name in scope
        # and its parameters (but Pi takes care of that later)
        res_type = if ctype, do: desugar_expression(ctype, env), else: default_res_type

        # Type includes cparams then inductive params
        # In CIC, it's usually (params) -> (cparams) -> (res_type)
        inner_ty =
          Enum.reduce(Enum.reverse(cparams), res_type, fn {_pname, pty}, acc ->
            %AST.Pi{name: "_", domain: desugar_expression(pty, env), codomain: acc}
          end)

        full_ty =
          Enum.reduce(Enum.reverse(params), inner_ty, fn {pname, pty}, acc ->
            %AST.Pi{name: pname, domain: desugar_expression(pty, env), codomain: acc}
          end)

        {idx, cname, full_ty}
      end)

    %AST.Inductive{name: name, params: ind_params, level: 0, constrs: constrs}
  end

  def desugar_decl(decl, _env), do: decl

  def desugar_expression(expr, env \\ %{}, func_name \\ nil) do
    case expr do
      %AST.Lambda{binders: binders, body: body} ->
        Enum.reduce(Enum.reverse(binders), desugar_expression(body, env, func_name), fn
          {vn, vt}, acc ->
            %AST.Lam{name: vn, domain: desugar_expression(vt, env), body: acc}

          %AST.Var{name: vn}, acc ->
            %AST.Lam{name: vn, domain: %AST.Universe{level: 0}, body: acc}
        end)

      %AST.Case{expr: e, branches: branches} ->
        ind =
          if branches == [] do
            %AST.Inductive{name: "Empty", params: [], level: 0, constrs: []}
          else
            {first_pat, _} = hd(branches)

            case first_pat do
              %AST.BinderConstructor{name: cname} ->
                Enum.find_value(Map.values(env.env), fn
                  %AST.Inductive{} = ind ->
                    if Enum.any?(ind.constrs, fn {_, name, _} ->
                         name == cname or (cname == "::" and name == "cons")
                       end),
                       do: ind
                  _ -> nil
                end)

              _ ->
                nil
            end
          end

        ind =
          ind ||
            %AST.Inductive{
              name: "Unknown",
              params: [],
              level: 0,
              constrs: []
            }

        desugared_target = desugar_expression(e, env, func_name)

        cases =
          Enum.map(ind.constrs, fn {_idx, cname, _cty} ->
            branch =
              Enum.find(branches, fn {pat, _} ->
                case pat do
                  %AST.BinderConstructor{name: ^cname} -> true
                  # Alias :: to cons for list patterns
                  %AST.BinderConstructor{name: "::"} when cname == "cons" -> true
                  # Alias Nil to nil (Prelude uses Nil, Coq uses nil)
                  %AST.BinderConstructor{name: "Nil"} when cname == "nil" -> true
                  %AST.BinderConstructor{name: "nil"} when cname == "Nil" -> true
                  %AST.BinderConstructor{name: "Cons"} when cname == "cons" -> true
                  _ -> false
                end
              end)

            case branch do
              {pat, body} ->
                # If constructor has args, wrap in lambdas
                case pat do
                  %AST.BinderConstructor{args: args} when args != [] ->
                    Enum.reduce(Enum.reverse(args), desugar_expression(body, env, func_name), fn
                      {k, _}, acc ->
                        ih_name = "ih_#{k}"
                        acc_with_ih = replace_recursion(acc, func_name, k, ih_name)

                        %AST.Lam{
                          name: k,
                          domain: %AST.Var{name: "Any"},
                          body: %AST.Lam{
                            name: ih_name,
                            domain: %AST.Var{name: "Any"},
                            body: acc_with_ih
                          }
                        }

                      %AST.Var{name: k}, acc ->
                        ih_name = "ih_#{k}"
                        acc_with_ih = replace_recursion(acc, func_name, k, ih_name)

                        %AST.Lam{
                          name: k,
                          domain: %AST.Var{name: "Any"},
                          body: %AST.Lam{
                            name: ih_name,
                            domain: %AST.Var{name: "Any"},
                            body: acc_with_ih
                          }
                        }

                      # BinderConstructor as arg (e.g. `tl` in `a::tl` pattern)
                      %AST.BinderConstructor{name: k}, acc ->
                        ih_name = "ih_#{k}"
                        acc_with_ih = replace_recursion(acc, func_name, k, ih_name)

                        %AST.Lam{
                          name: k,
                          domain: %AST.Var{name: "Any"},
                          body: %AST.Lam{
                            name: ih_name,
                            domain: %AST.Var{name: "Any"},
                            body: acc_with_ih
                          }
                        }
                    end)

                  _ ->
                    desugar_expression(body, env, func_name)
                end

              _ ->
                # Missing branch?
                %AST.Var{name: "missing_branch_#{cname}"}
            end
          end)

        %AST.Ind{
          inductive: ind,
          motive: %AST.Lam{name: "_", domain: ind, body: %AST.Var{name: "Any"}},
          cases: cases,
          term: desugared_target
        }

      %AST.Number{value: n} ->
        nat_to_succ(n)

      %AST.App{func: %AST.App{func: %AST.Var{name: op}, arg: l}, arg: r}
      when op in ["::", "+", "-", "*", "/", "<=", "<", ">=", ">", "=", "/\\", "\\/", "<->", ":"] ->
        mapped_name =
          case op do
            "::" -> "cons"
            "+" -> "plus"
            "-" -> "minus"
            "*" -> "mult"
            "/" -> "div"
            "<=" -> "le"
            "<" -> "lt"
            ">=" -> "ge"
            ">" -> "gt"
            "=" -> "eq"
            "/\\" -> "and"
            "\\/" -> "or"
            "<->" -> "iff"
            _ -> op
          end

        # For polymorphic propositions, insert implicit type arg `Any`
        mapped_expr =
          case op do
            "::" ->
              # cons _ left right
              %AST.App{
                func: %AST.App{
                  func: %AST.App{func: %AST.Var{name: "cons"}, arg: %AST.Var{name: "Any"}},
                  arg: desugar_expression(l, env, func_name)
                },
                arg: desugar_expression(r, env, func_name)
              }

            "=" ->
              # eq Any left right
              %AST.App{
                func: %AST.App{
                  func: %AST.App{func: %AST.Var{name: "eq"}, arg: %AST.Var{name: "Any"}},
                  arg: desugar_expression(l, env, func_name)
                },
                arg: desugar_expression(r, env, func_name)
              }

            _ ->
              # Standard binary function application
              %AST.App{
                func: %AST.App{
                  func: %AST.Var{name: mapped_name},
                  arg: desugar_expression(l, env, func_name)
                },
                arg: desugar_expression(r, env, func_name)
              }
          end

        mapped_expr

      %AST.Pi{name: name, domain: d, codomain: c} ->
        %AST.Pi{
          name: name,
          domain: desugar_expression(d, env, func_name),
          codomain: desugar_expression(c, env, func_name)
        }

      %AST.App{func: f, arg: arg} ->
        %AST.App{
          func: desugar_expression(f, env, func_name),
          arg: desugar_expression(arg, env, func_name)
        }

      %AST.Let{decls: decls, body: let_body} ->
        decls_desugared =
          Enum.map(decls, fn {n, e} ->
            {n, desugar_expression(e, env, n)}
          end)

        %AST.Let{
          decls: decls_desugared,
          body: desugar_expression(let_body, env, func_name)
        }

      _ ->
        expr
    end
  end

  defp replace_recursion(expr, func_name, k, ih_name) do
    # Flatten application tree: (((f arg1) arg2) arg3) -> {f, [arg1, arg2, arg3]}
    {f_node, args} = flatten_app(expr, [])

    case f_node do
      %AST.Var{name: ^func_name} ->
        # Search for induction var `k` in args, or `k arg` (subtree recursion)
        case find_recursion_arg(args, k) do
          {:val, before_args, after_args} ->
            # Case: (func_name ...before... k) ...after...
            # Replace with (ih_name ...before...) ...after...
            ih_app = build_app(%AST.Var{name: ih_name}, before_args)
            replaced_after = Enum.map(after_args, &replace_recursion(&1, func_name, k, ih_name))
            build_app(ih_app, replaced_after)

          {:subtree, subtree_arg, before_args, after_args} ->
            # Case: (func_name ...before... (k subtree_arg)) ...after...
            # Replace with (ih_name ...before... subtree_arg) ...after...
            # Note: in W-types, (f tt) is the subtree.
            # Usually ih_f is mapped to \before... -> \subtree -> ...
            ih_with_before = build_app(%AST.Var{name: ih_name}, before_args)
            ih_app = %AST.App{func: ih_with_before, arg: subtree_arg}
            replaced_after = Enum.map(after_args, &replace_recursion(&1, func_name, k, ih_name))
            build_app(ih_app, replaced_after)

          :not_found ->
            # Recursive call not found in this App, recurse on arguments
            replaced_args = Enum.map(args, &replace_recursion(&1, func_name, k, ih_name))
            build_app(f_node, replaced_args)
        end

      _ ->
        case expr do
          %AST.App{func: func, arg: arg} ->
            %AST.App{
              func: replace_recursion(func, func_name, k, ih_name),
              arg: replace_recursion(arg, func_name, k, ih_name)
            }

          %AST.Lam{name: name, domain: domain, body: body} ->
            %AST.Lam{
              name: name,
              domain: replace_recursion(domain, func_name, k, ih_name),
              body: replace_recursion(body, func_name, k, ih_name)
            }

          %AST.Case{expr: e, branches: branches} ->
            %AST.Case{
              expr: replace_recursion(e, func_name, k, ih_name),
              branches:
                Enum.map(branches, fn {p, b} ->
                  {p, replace_recursion(b, func_name, k, ih_name)}
                end)
            }

          _ ->
            expr
        end
    end
  end

  defp flatten_app(%AST.App{func: f, arg: arg}, acc) do
    flatten_app(f, [arg | acc])
  end

  defp flatten_app(other, acc) do
    {other, acc}
  end

  defp build_app(f, []), do: f

  defp build_app(f, [arg | rest]) do
    build_app(%AST.App{func: f, arg: arg}, rest)
  end

  defp nat_to_succ(0), do: %AST.Var{name: "Zero"}
  defp nat_to_succ(n), do: %AST.App{func: %AST.Var{name: "Succ"}, arg: nat_to_succ(n - 1)}

  defp find_recursion_arg(args, k) do
    Enum.with_index(args)
    |> Enum.find_value(:not_found, fn {arg, i} ->
      case arg do
        %AST.Var{name: ^k} ->
          {before_args, [_k_var | after_args]} = Enum.split(args, i)
          {:val, before_args, after_args}

        %AST.App{func: %AST.Var{name: ^k}, arg: subtree} ->
          {before_args, [_subtree_app | after_args]} = Enum.split(args, i)
          {:subtree, subtree, before_args, after_args}

        _ ->
          nil
      end
    end)
  end
end
