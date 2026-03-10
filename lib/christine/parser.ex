defmodule Christine.Parser do
  alias Christine.AST

  def parse(tokens) do
    parse_module(tokens)
  end

  def parse_expression(tokens) do
    parse_expr(tokens)
  end

  def parse_declaration(tokens) do
    parse_decl(tokens)
  end

  defp parse_module(tokens) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:module, _, _} | rest] ->
        case parse_module_name(rest) do
          {:ok, name, rest2} ->
            case skip_virtual(rest2) do
              [{:dot, _, _} | rest3] ->
                case parse_decls(rest3, []) do
                  {:ok, decls, rest4} ->
                    {:ok, %AST.Module{name: name, declarations: decls}, rest4}

                  err ->
                    err
                end

              _ ->
                {:error, :expected_dot_after_module_name}
            end

          err ->
            err
        end

      _ ->
        case parse_decls(tokens, []) do
          {:ok, decls, remaining} ->
            {:ok, %AST.Module{name: "Main", declarations: decls}, remaining}

          err ->
            err
        end
    end
  end

  defp parse_module_name(tokens) do
    case skip_virtual(tokens) do
      [{:ident, _, _, name} | rest] ->
        parse_module_name_tail(rest, name)

      _ ->
        {:error, :invalid_module_name}
    end
  end

  defp parse_module_name_tail([{:dot, _, _}, {:ident, _, _, next} | rest], acc) do
    parse_module_name_tail(rest, acc <> "." <> next)
  end

  defp parse_module_name_tail(rest, acc), do: {:ok, acc, rest}

  defp skip_virtual(tokens) do
    Enum.drop_while(tokens, fn t ->
      elem(t, 0) in [:v_left_brace, :v_semicolon, :v_right_brace, :semicolon]
    end)
  end

  defp parse_decls(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [] ->
        {:ok, Enum.reverse(acc), []}

      _ ->
        case parse_decl(tokens) do
          {:ok, decl, rest} -> parse_decls(rest, [decl | acc])
          err when elem(err, 0) == :error -> err
        end
    end
  end

  defp parse_decl(tokens) do
    case skip_virtual(tokens) do
      [{:inductive_kw, _, _} | rest] ->
        case skip_virtual(rest) do
          [{:ident, _, _, name} | rest1] ->
            case parse_decl_params(rest1, []) do
              {:ok, params, rest2} ->
                case skip_virtual(rest2) do
                  [{:assign, _, _} | rest3] ->
                    case parse_constructors(rest3, []) do
                      {:ok, constructors, rest4} ->
                        case skip_virtual(rest4) do
                          [{:dot, _, _} | rest5] ->
                            {:ok,
                             %AST.DeclData{
                               name: name,
                               params: params,
                               constructors: constructors
                             }, rest5}

                          _ ->
                            {:error, :expected_dot_after_inductive}
                        end

                      err ->
                        err
                    end

                  _ ->
                    {:error, :expected_assign_after_inductive}
                end

              err ->
                err
            end

          _ ->
            {:error, :expected_name_after_inductive}
        end

      [{:definition, _, _} | rest] ->
        parse_def_theorem(rest)

      [{:theorem, _, _} | rest] ->
        parse_def_theorem(rest)

      [{:import, _, _} | rest] ->
        case parse_module_name(rest) do
          {:ok, name, rest2} ->
            case skip_virtual(rest2) do
              [{:dot, _, _} | rest3] -> {:ok, {:import, name}, rest3}
              _ -> {:ok, {:import, name}, rest2}
            end

          _ ->
            {:error, :invalid_import}
        end

      [{:ident, _, _, name} | rest] ->
        # Try as type signature
        tokens2 = skip_virtual(rest)

        case tokens2 do
          [{:colon, _, _} | rest2] ->
            case parse_type(rest2) do
              {:ok, ty, rest3} ->
                case skip_virtual(rest3) do
                  [{:dot, _, _} | rest4] ->
                    {:ok, %AST.DeclTypeSignature{name: name, type: ty}, rest4}

                  _ ->
                    {:ok, %AST.DeclTypeSignature{name: name, type: ty}, rest3}
                end

              _ ->
                {:error, :invalid_type_sig}
            end

          _ ->
            # Try as definition (ident binders := expr)
            case parse_binders(rest, []) do
              {:ok, binders, rest2} ->
                case skip_virtual(rest2) do
                  [{:assign, _, _} | rest3] ->
                    case parse_expr(rest3) do
                      {:ok, expr, rest4} ->
                        case skip_virtual(rest4) do
                          [{:dot, _, _} | rest5] ->
                            {:ok, %AST.DeclValue{name: name, binders: binders, expr: expr}, rest5}

                          _ ->
                            {:ok, %AST.DeclValue{name: name, binders: binders, expr: expr}, rest4}
                        end

                      err ->
                        err
                    end

                  _ ->
                    {:error, :unrecognized_decl}
                end

              _ ->
                {:error, :unrecognized_decl}
            end
        end

      [] ->
        {:error, :empty_tokens}

      _ ->
        case tokens do
          [] -> :ok
          _ -> IO.inspect(Enum.take(tokens, 5), label: "UNRECOGNIZED DECL")
        end

        {:error, :unrecognized_decl, Enum.take(tokens, 5)}
    end
  end

  defp parse_def_theorem(tokens) do
    case skip_virtual(tokens) do
      [{:ident, _, _, name} | rest] ->
        case parse_decl_params(rest, []) do
          {:ok, params, rest2} ->
            case skip_virtual(rest2) do
              [{:colon, _, _} | rest3] ->
                case parse_type(rest3) do
                  {:ok, ty, rest4} ->
                    case skip_virtual(rest4) do
                      [{:assign, _, _} | rest5] ->
                        case parse_expr(rest5) do
                          {:ok, expr, rest6} ->
                            case skip_virtual(rest6) do
                              [{:dot, _, _} | rest7] ->
                                {:ok, %AST.DeclValue{name: name, binders: params, expr: expr},
                                 rest7}

                              _ ->
                                {:ok, %AST.DeclValue{name: name, binders: params, expr: expr},
                                 rest6}
                            end

                          err ->
                            err
                        end

                      [{:dot, _, _} | rest5] ->
                        {:ok, %AST.DeclValue{name: name, binders: params, expr: ty}, rest5}

                      _ ->
                        {:error, :expected_assign_after_type}
                    end

                  err ->
                    err
                end

              [{:assign, _, _} | rest3] ->
                case parse_expr(rest3) do
                  {:ok, expr, rest4} ->
                    case skip_virtual(rest4) do
                      [{:dot, _, _} | rest5] ->
                        {:ok, %AST.DeclValue{name: name, binders: params, expr: expr}, rest5}

                      _ ->
                        {:ok, %AST.DeclValue{name: name, binders: params, expr: expr}, rest4}
                    end

                  err ->
                    err
                end

              _ ->
                {:error, :expected_colon_or_assign_in_definition}
            end

          err ->
            err
        end

      _ ->
        {:error, :invalid_definition_name}
    end
  end

  defp parse_decl_params(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:left_paren, _, _}, {:ident, _, _, name}, {:colon, _, _} | rest] ->
        case parse_type(rest) do
          {:ok, ty, [{:right_paren, _, _} | rest2]} ->
            parse_decl_params(rest2, [{name, ty} | acc])

          _ ->
            {:error, :invalid_param_type}
        end

      _ ->
        {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_constructors(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:pipe, _, _} | _] ->
        case parse_constructor(tokens) do
          {:ok, constr, rest} -> parse_constructors(rest, [constr | acc])
          err -> err
        end

      [{:dot, _, _} | _] ->
        {:ok, Enum.reverse(acc), tokens}

      _ ->
        # Try a single constructor without pipe (e.g. Unit := tt.)
        case parse_constructor_no_pipe(tokens) do
          {:ok, constr, rest} -> {:ok, Enum.reverse([constr | acc]), rest}
          _ -> {:ok, Enum.reverse(acc), tokens}
        end
    end
  end

  defp parse_constructor_no_pipe(tokens) do
    case tokens do
      [{:ident, _, _, name} | rest] ->
        case parse_decl_params(rest, []) do
          {:ok, params, rest2} ->
            case skip_virtual(rest2) do
              [{:colon, _, _} | rest3] ->
                case parse_type(rest3) do
                  {:ok, ty, rest4} -> {:ok, {name, params, ty}, rest4}
                  err -> err
                end

              _ ->
                {:ok, {name, params, nil}, rest2}
            end

          err ->
            err
        end

      _ ->
        {:error, :expected_constructor_name}
    end
  end

  defp parse_constructor([{:pipe, _, _} | rest]) do
    case skip_virtual(rest) do
      [{:ident, _, _, name} | rest2] ->
        case parse_decl_params(rest2, []) do
          {:ok, params, rest3} ->
            case skip_virtual(rest3) do
              [{:colon, _, _} | rest4] ->
                case parse_type(rest4) do
                  {:ok, ty, rest5} -> {:ok, {name, params, ty}, rest5}
                  err -> err
                end

              _ ->
                {:ok, {name, params, nil}, rest3}
            end

          err ->
            err
        end

      _ ->
        {:error, :expected_constructor_name}
    end
  end

  defp parse_constructor(tokens), do: {:error, :no_constructor, Enum.take(tokens, 5)}

  defp parse_type(tokens) do
    case skip_virtual(tokens) do
      [{:forall, _, _} | rest] ->
        case parse_forall_binders(rest, []) do
          {:ok, binders, [{:comma, _, _} | rest2]} ->
            case parse_type(rest2) do
              {:ok, body, rest3} ->
                final =
                  Enum.reduce(Enum.reverse(binders), body, fn {n, d}, acc ->
                    %AST.Pi{name: n, domain: d, codomain: acc}
                  end)

                {:ok, final, rest3}

              err ->
                err
            end

          _ ->
            {:error, :expected_comma_in_forall}
        end

      _ ->
        case parse_type_app(tokens) do
          {:ok, t, [{:arrow, _, _} | rest]} ->
            case parse_type(rest) do
              {:ok, body, rest2} ->
                {:ok, %AST.Pi{name: "_", domain: t, codomain: body}, rest2}

              err ->
                err
            end

          res ->
            res
        end
    end
  end

  defp parse_forall_binders(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:left_paren, _, _}, {:ident, _, _, name}, {:colon, _, _} | rest] ->
        case parse_type(rest) do
          {:ok, ty, [{:right_paren, _, _} | rest2]} ->
            parse_forall_binders(rest2, [{name, ty} | acc])

          _ ->
            {:error, :invalid_forall_param}
        end

      [{:ident, _, _, name} | rest] ->
        # Simple identifier in forall: forall x, T is PI x: Any -> T
        # But in Coq subset we usually use (x: A)
        parse_forall_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])

      _ ->
        {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_type_app(tokens) do
    case parse_type_atom(tokens) do
      {:ok, t, rest} -> parse_type_args(rest, t)
      err -> err
    end
  end

  defp parse_type_args(tokens, acc) do
    case parse_type_atom(tokens) do
      {:ok, t, rest} -> parse_type_args(rest, %AST.App{func: acc, arg: t})
      _ -> {:ok, acc, tokens}
    end
  end

  defp parse_type_atom(tokens) do
    case skip_virtual(tokens) do
      [{:ident, _, _, name} | rest] ->
        {:ok, %AST.Var{name: name}, rest}

      [{:type_kw, _, _} | rest] ->
        {:ok, %AST.Universe{level: 0}, rest}

      [{:prop_kw, _, _} | rest] ->
        {:ok, %AST.Universe{level: -1}, rest}

      [{:left_paren, _, _} | rest] ->
        case parse_type(rest) do
          {:ok, t, [{:right_paren, _, _} | rest2]} -> {:ok, t, rest2}
          _ -> {:error, :expected_right_paren}
        end

      _ ->
        {:error, :not_a_type_atom}
    end
  end

  defp parse_expr(tokens) do
    case skip_virtual(tokens) do
      [{:fun_kw, _, _} | rest] ->
        case parse_binders(rest, []) do
          {:ok, binders, [{arrow_type, _, _} | rest2]} when arrow_type in [:arrow, :fat_arrow] ->
            case parse_expr(rest2) do
              {:ok, body, rest3} ->
                {:ok, %AST.Lambda{binders: binders, body: body}, rest3}

              err ->
                err
            end

          _ ->
            {:error, :expected_arrow_in_lambda}
        end

      [{:match_kw, _, _} | rest] ->
        case parse_expr(rest) do
          {:ok, e, [{:with_kw, _, _} | rest2]} ->
            case parse_branches(rest2, []) do
              {:ok, branches, [{:end_kw, _, _} | rest3]} ->
                {:ok, %AST.Case{expr: e, branches: branches}, rest3}

              err ->
                err
            end

          err ->
            err
        end

      _ ->
        parse_expr_app(tokens)
    end
  end

  defp parse_expr_app(tokens) do
    case parse_expr_atom(tokens) do
      {:ok, e, rest} -> parse_expr_args(rest, e)
      err -> err
    end
  end

  defp parse_expr_args(tokens, acc) do
    case parse_expr_atom(tokens) do
      {:ok, e, rest} -> parse_expr_args(rest, %AST.App{func: acc, arg: e})
      _ -> {:ok, acc, tokens}
    end
  end

  defp parse_expr_atom(tokens) do
    case skip_virtual(tokens) do
      [{:ident, _, _, name} | rest] ->
        {:ok, %AST.Var{name: name}, rest}

      [{:number, _, _, n} | rest] ->
        {:ok, %AST.Number{value: n}, rest}

      [{:string, _, _, s} | rest] ->
        {:ok, %AST.String{value: s}, rest}

      [{:left_paren, _, _} | rest] ->
        case parse_expr(rest) do
          {:ok, e, [{:right_paren, _, _} | rest2]} -> {:ok, e, rest2}
          _ -> {:error, :expected_right_paren_expr}
        end

      _ ->
        {:error, :not_an_expr_atom}
    end
  end

  defp parse_binders(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:ident, _, _, name} | rest] ->
        parse_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])

      [{:left_paren, _, _}, {:ident, _, _, name}, {:colon, _, _} | rest] ->
        case parse_type(rest) do
          {:ok, ty, [{:right_paren, _, _} | rest2]} ->
            parse_binders(rest2, [{name, ty} | acc])

          _ ->
            {:error, :invalid_binder}
        end

      _ ->
        {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_branches(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:pipe, _, _} | rest] ->
        case parse_branch(rest) do
          {:ok, branch, rest2} -> parse_branches(rest2, [branch | acc])
          err -> err
        end

      _ ->
        {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_branch(tokens) do
    case skip_virtual(tokens) do
      [{:ident, _, _, cname} | rest] ->
        case parse_binders(rest, []) do
          {:ok, args, [{:fat_arrow, _, _} | rest2]} ->
            case parse_expr(rest2) do
              {:ok, body, rest3} ->
                {:ok, {%AST.BinderConstructor{name: cname, args: args}, body}, rest3}

              err ->
                err
            end

          _ ->
            {:error, :expected_arrow_in_branch}
        end

      _ ->
        {:error, :invalid_branch}
    end
  end
end
