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
    tokens2 = skip_virtual(tokens)

    case tokens2 do
      [] ->
        {:ok, Enum.reverse(acc), tokens2}

      _ ->
        case parse_decl(tokens2) do
          {:ok, decl, rest} when is_list(decl) -> parse_decls(rest, Enum.reverse(decl) ++ acc)
          {:ok, decl, rest} -> parse_decls(rest, [decl | acc])
          {:error, reason, rest} -> {:error, reason, rest}
          {:error, reason} -> {:error, reason, tokens2}
        end
    end
  end

  defp parse_decl(tokens) do
    case skip_virtual(tokens) do
      [{:qed, _, _} | rest] ->
        case skip_virtual(rest) do
          [{:dot, _, _} | rest2] -> {:ok, {:tactic_skipped, "Qed"}, rest2}
          _ -> {:ok, {:tactic_skipped, "Qed"}, rest}
        end

      [{:proof_kw, _, _} | rest] ->
        {tactic_tokens, rest_after_qed} = Enum.split_while(rest, fn
          {:qed, _, _} -> false
          _ -> true
        end)

        tactics = tactic_tokens
          |> Enum.reject(fn t -> elem(t, 0) in [:left_brace, :right_brace] end)
          |> Enum.chunk_by(fn t -> elem(t, 0) == :dot end)
          |> Enum.reject(fn chunk -> match?([{:dot, _, _} | _], chunk) end)
          |> Enum.map(&tokens_to_string/1)
          |> Enum.reject(&(&1 == ""))

        case skip_virtual(rest_after_qed) do
           [{:qed, _, _}, {:dot, _, _} | rest3] -> {:ok, {:proof, tactics}, rest3}
           [{:qed, _, _} | rest3] -> {:ok, {:proof, tactics}, rest3}
           _ -> {:ok, {:proof, tactics}, rest_after_qed}
        end

      [{:ident, _, _, name}, {:dot, _, _} | rest]
      when name in ["Intros", "Intros.", "Rewrite", "reflexivity", "Split", "Left", "Right", "Apply", "Assumption",
                    "tauto", "Goal", "Auto", "Trivial", "Eauto", "Exact", "Cut", "Generalize", "Elim", "Case",
                    "Induction", "Recursive", "Abort", "intros", "rewrite", "split", "left", "right", "apply",
                    "assumption", "exact", "elim", "case", "induction", "destruct"] ->
        {:ok, {:tactic_skipped, name}, rest}

      [{:ident, _, _, name} | rest]
      when name in ["intros", "rewrite", "split", "left", "right", "apply", "assumption", "exact", "elim", "case", "induction", "destruct"] ->
        # Tactic without dot? Usually ends in dot.
        rest2 = Enum.drop_while(rest, fn t -> elem(t, 0) != :dot end)
        case rest2 do
          [{:dot, _, _} | rest3] -> {:ok, {:tactic_skipped, name}, rest3}
          _ -> {:ok, {:tactic_skipped, name}, rest2}
        end
      [{:inductive_kw, _, _} | rest] ->
        case skip_virtual(rest) do
          [{:ident, _, _, name} | rest1] ->
            case parse_decl_params(rest1, []) do
              {:ok, params, rest2} ->
                # Skip optional `: <kind>` annotation (Coq 6.3 style: Inductive le (n:nat) : nat -> Prop :=)
                rest2 =
                  case skip_virtual(rest2) do
                    [{:colon, _, _} | rest_after_colon] ->
                      # Skip the kind expression up to :=
                      kind_tokens = Enum.take_while(rest_after_colon, fn t -> elem(t, 0) != :assign end)
                      Enum.drop(rest_after_colon, length(kind_tokens))
                    _ ->
                      rest2
                  end

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
                            {:error, {:expected_dot_after_inductive, name}}
                        end

                      err ->
                        err
                    end

                  _ ->
                    {:error, {:expected_assign_after_inductive, name}}
                end

              err ->
                err
            end

          _ ->
            {:error, :expected_name_after_inductive}
        end

      [{kw, _, _} | rest]
      when kw in [:definition, :theorem, :lemma, :fact, :remark, :fixpoint, :hypothesis, :variable] ->
        parse_def_theorem(rest)

      [{:ident, _, _, name} | rest] when name in ["Variables", "End"] ->
        # Skip until dot
        rest2 = Enum.drop_while(rest, fn t -> elem(t, 0) != :dot end)

        case rest2 do
          [{:dot, _, _} | rest3] -> {:ok, {:command_skipped, name}, rest3}
          _ -> {:ok, {:command_skipped, name}, rest2}
        end

      [{:section, _, _} | rest] ->
        # Just skip section and name until dot
        rest2 = Enum.drop_while(rest, fn t -> elem(t, 0) != :dot end)
        case rest2 do
          [{:dot, _, _} | rest3] -> {:ok, {:section_skipped}, rest3}
          _ -> {:ok, {:section_skipped}, rest2}
        end

      [{:module, _, _} | rest] ->
        # Skip until dot
        rest2 = Enum.drop_while(rest, fn t -> elem(t, 0) != :dot end)
        case rest2 do
          [{:dot, _, _} | rest3] -> {:ok, {:module_skipped}, rest3}
          _ -> {:ok, {:module_skipped}, rest2}
        end

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

      [{:import_kw, _, _} | rest] ->
        # "Import" vs "import" -> Treat same
        case parse_module_name(rest) do
          {:ok, name, rest2} ->
            case skip_virtual(rest2) do
              [{:dot, _, _} | rest3] -> {:ok, {:import, name}, rest3}
              _ -> {:ok, {:import, name}, rest2}
            end

          _ ->
            {:error, :invalid_import}
        end

      [{:require, _, _} | rest] ->
        # Require [Import] Name.
        rest =
          case skip_virtual(rest) do
            [{:import_kw, _, _} | r] -> r
            r -> r
          end

        case parse_module_name(rest) do
          {:ok, name, rest2} ->
            case skip_virtual(rest2) do
              [{:dot, _, _} | rest3] -> {:ok, {:import, name}, rest3}
              _ -> {:ok, {:import, name}, rest2}
            end

          _ ->
            {:error, :invalid_require}
        end

      [{:notation, _, _} | rest] ->
        # Notation "sum" := (plus).
        case skip_virtual(rest) do
          [{:string, _, _, _} | rest2] ->
            case skip_virtual(rest2) do
              [{:assign, _, _} | rest3] ->
                # Skip until dot
                rest4 = Enum.drop_while(rest3, fn t -> elem(t, 0) != :dot end)

                case rest4 do
                  [{:dot, _, _} | rest5] -> {:ok, {:notation_skipped}, rest5}
                  _ -> {:ok, {:notation_skipped}, rest4}
                end

              _ ->
                {:error, :invalid_notation}
            end

          _ ->
            {:error, :invalid_notation}
        end

      [{k, _, _} | rest] when k in [:check_kw, :eval_kw, :search_kw, :print_kw] ->
        # Check expr. Eval compute in expr.
        rest =
          if k == :eval_kw do
            # skip "compute in" if present
            case skip_virtual(rest) do
              [{:ident, _, _, "compute"}, {:in, _, _} | r] -> r
              [{:ident, _, _, "compute"} | r] -> r
              r -> r
            end
          else
            rest
          end

        case parse_expr(rest) do
          {:ok, e, rest2} ->
            case skip_virtual(rest2) do
              [{:dot, _, _} | rest3] -> {:ok, {:command, k, e}, rest3}
              _ -> {:ok, {:command, k, e}, rest2}
            end

          err ->
            err
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
        {:error, :unrecognized_decl, Enum.take(tokens, 5)}
    end
  end

  defp parse_def_theorem(tokens) do
    # Strategy:
    # 1. Take the FIRST identifier as the function/lemma name.
    # 2. Parse zero or more bare identifiers as untyped binders (for Coq 6.3: `f x y :=`).
    # 3. Parse zero or more typed params in parens (for Coq 8.x: `f (x:nat) :=`).
    # 4. If a colon follows, parse the return type.
    # 5. If := follows, parse the body.
    # 6. Multiple names (Hypothesis H1 H2 : T) = fallback handled via parse_binder_names.
    case skip_virtual(tokens) do
      [{:ident, _, _, func_name} | rest1] ->
        # Parse bare ident binders (e.g. `l`, `n`, `t`) until we hit ( or : or :=
        {bare_binders, rest_after_bare} = parse_bare_binders(rest1, [])

        # Parse typed params in parens
        case parse_decl_params(rest_after_bare, []) do
          {:ok, typed_params, rest2} ->
            all_binders = bare_binders ++ typed_params

            case skip_virtual(rest2) do
              [{:colon, _, _} | rest3] ->
                case parse_expr(rest3, 200) do
                  {:ok, ty, rest4} ->
                    case skip_virtual(rest4) do
                      [{:assign, _, _} | rest5] ->
                        case parse_expr(rest5) do
                          {:ok, expr, rest6} ->
                            case skip_virtual(rest6) do
                              [{:dot, _, _} | rest7] ->
                                {:ok, [%AST.DeclValue{name: func_name, binders: all_binders, expr: expr, type: ty}], rest7}
                              _ ->
                                {:ok, [%AST.DeclValue{name: func_name, binders: all_binders, expr: expr, type: ty}], rest6}
                            end
                          err -> err
                        end

                      [{:dot, _, _} | rest5] ->
                        {:ok, [%AST.DeclValue{name: func_name, binders: all_binders, expr: nil, type: ty}], rest5}

                      _ ->
                        {:ok, [%AST.DeclValue{name: func_name, binders: all_binders, expr: nil, type: ty}], rest4}
                    end

                  err -> err
                end

              [{:assign, _, _} | rest3] ->
                case parse_expr(rest3) do
                  {:ok, expr, rest4} ->
                    case skip_virtual(rest4) do
                      [{:dot, _, _} | rest5] ->
                        {:ok, [%AST.DeclValue{name: func_name, binders: all_binders, expr: expr}], rest5}
                      _ ->
                        {:ok, [%AST.DeclValue{name: func_name, binders: all_binders, expr: expr}], rest4}
                    end
                  err -> err
                end

              [{:dot, _, _} | rest3] ->
                {:ok, [%AST.DeclValue{name: func_name, binders: all_binders, expr: nil}], rest3}

              _ ->
                # Check if this is a multi-name hypothesis: H1 H2 ... : T.
                # We already consumed func_name; check if bare_binders look like names followed by colon
                # Fall back: skip to dot
                rest = Enum.drop_while(tokens, fn t -> elem(t, 0) != :dot end)
                case rest do
                  [{:dot, _, _} | rest2] -> {:ok, {:unknown_skipped}, rest2}
                  _ -> {:ok, {:unknown_skipped}, rest}
                end
            end

          err -> err
        end

      _ ->
        # Skip until dot as fallback unknown
        rest = Enum.drop_while(tokens, fn t -> elem(t, 0) != :dot end)
        case rest do
          [{:dot, _, _} | rest2] -> {:ok, {:unknown_skipped}, rest2}
          _ -> {:ok, {:unknown_skipped}, rest}
        end
    end
  end

  # Parse bare (untyped) identifier binders until we see ( or : or := or . or virtual token that isn't an ident
  defp parse_bare_binders(tokens, acc) do
    case skip_virtual(tokens) do
      [{:ident, _, _, name} | rest] when name not in ["in", "with", "end", "then", "else"] ->
        # peek: if the next non-virtual token after name is also an ident, colon, assign, etc.
        # Only consume if it looks like a positional parameter (not a keyword expression)
        case skip_virtual(rest) do
          [{:ident, _, _, _} | _] ->
            # next token is also an ident - this is a bare binder
            parse_bare_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])
          [{:colon, _, _} | _] ->
            # Colon follows - stop, name was consumed as func_name before us
            {Enum.reverse(acc), tokens}
          [{:assign, _, _} | _] ->
            # := follows - current bare idents are all binders
            parse_bare_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])
          [{:dot, _, _} | _] ->
            # Dot follows - current name might be the last binder-less signature
            {Enum.reverse(acc), tokens}
          [{:left_paren, _, _} | _] ->
            # Typed param follows after this bare binder
            parse_bare_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])
          _ ->
            {Enum.reverse(acc), tokens}
        end

      _ ->
        {Enum.reverse(acc), tokens}
    end
  end


  defp parse_decl_params(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:left_paren, _, _} | rest] ->
        case parse_binder_names(rest, []) do
          {:ok, names, [{:colon, _, _} | rest2]} ->
            case parse_type(rest2) do
              {:ok, ty, [{:right_paren, _, _} | rest3]} ->
                new_params = Enum.map(names, fn n -> {n, ty} end)
                parse_decl_params(rest3, Enum.reverse(new_params) ++ acc)

              _ ->
                {:error, :invalid_param_type}
            end

          _ ->
            {:error, :invalid_binder}
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

  defp parse_type(tokens), do: parse_expr(tokens)

  defp parse_forall_binders(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:left_paren, _, _} | rest] ->
        case parse_binder_names(rest, []) do
          {:ok, names, rest2} ->
            case skip_virtual(rest2) do
              [{:colon, _, _} | rest3] ->
                case parse_type(rest3) do
                  {:ok, ty, rest4} ->
                    case skip_virtual(rest4) do
                      [{:right_paren, _, _} | rest5] ->
                        new_acc = Enum.reduce(names, acc, fn n, a -> [{n, ty} | a] end)
                        parse_forall_binders(rest5, new_acc)
                      _ -> {:ok, Enum.reverse(acc), tokens}
                    end
                  _ -> {:ok, Enum.reverse(acc), tokens}
                end
              _ -> {:ok, Enum.reverse(acc), tokens}
            end
          _ -> {:ok, Enum.reverse(acc), tokens}
        end

      [{:ident, _, _, name} | rest] ->
        case skip_virtual(rest) do
          [{:colon, _, _} | rest2] ->
            case parse_type(rest2) do
              {:ok, ty, rest3} ->
                parse_forall_binders(rest3, [{name, ty} | acc])

              _ ->
                parse_forall_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])
            end

          _ ->
            parse_forall_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])
        end

      _ ->
        {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_expr(tokens, prec \\ 120) do
    case parse_prefix(tokens, prec) do
      {:ok, left, rest} -> parse_infix_climber(rest, left, prec)
      err -> err
    end
  end

  defp parse_prefix(tokens, _prec) do
    case skip_virtual(tokens) do
      [{:fun_kw, _, _} | rest] ->
        case parse_binders(rest, []) do
          {:ok, binders, [{arrow_type, _, _} | rest2]} when arrow_type in [:arrow, :fat_arrow] ->
            case parse_expr(rest2, get_precedence("fun")) do
              {:ok, body, rest3} ->
                {:ok, %AST.Lambda{binders: binders, body: body}, rest3}

              err ->
                err
            end

          _ ->
            {:error, :expected_arrow_in_lambda}
        end

      [{:forall, _, _} | rest] ->
        case parse_forall_binders(rest, []) do
          {:ok, binders, rest_f} ->
            case skip_virtual(rest_f) do
              [{:comma, _, _} | rest2] ->
                case parse_expr(rest2, get_precedence("forall")) do
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

          err ->
            err
        end

      [{:exists, _, _} | rest] ->
        case parse_forall_binders(rest, []) do
          {:ok, binders, rest_e} ->
            case skip_virtual(rest_e) do
              [{:comma, _, _} | rest2] ->
                case parse_expr(rest2, get_precedence("exists")) do
                  {:ok, body, rest3} ->
                    final =
                      Enum.reduce(Enum.reverse(binders), body, fn {n, d}, acc ->
                        %AST.App{
                          func: %AST.App{func: %AST.Var{name: "Exists"}, arg: d},
                          arg: %AST.Lambda{binders: [{n, d}], body: acc}
                        }
                      end)

                    {:ok, final, rest3}

                  err ->
                    err
                end

              _ ->
                {:error, :expected_comma_in_exists}
            end

          err ->
            err
        end

      [{:operator, _, _, "~"} | rest] ->
        case parse_expr(rest, 90) do
          {:ok, e, rest2} -> {:ok, %AST.App{func: %AST.Var{name: "not"}, arg: e}, rest2}
          err -> err
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

      [{:if_kw, _, _} | rest] ->
        case parse_expr(rest) do
          {:ok, cond_e, [{:then_kw, _, _} | rest2]} ->
            case parse_expr(rest2) do
              {:ok, then_e, [{:else_kw, _, _} | rest3]} ->
                case parse_expr(rest3) do
                  {:ok, else_e, rest4} ->
                    {:ok,
                     %AST.Case{
                       expr: cond_e,
                       branches: [
                         {%AST.BinderConstructor{name: "true", args: []}, then_e},
                         {%AST.BinderConstructor{name: "false", args: []}, else_e}
                       ]
                     }, rest4}

                  err ->
                    err
                end

              err ->
                err
            end

          err ->
            err
        end

      [{:let, _, _} | rest] ->
        case parse_binder_names(rest, []) do
          {:ok, [name], rest2} ->
            case skip_virtual(rest2) do
              [{:assign, _, _} | rest3] ->
                case parse_expr(rest3) do
                  {:ok, e1, rest4} ->
                    case skip_virtual(rest4) do
                      [{:in, _, _} | rest5] ->
                        case parse_expr(rest5) do
                          {:ok, e2, rest6} ->
                            {:ok, %AST.Let{decls: [{name, e1}], body: e2}, rest6}

                          err ->
                            err
                        end

                      _ ->
                        {:error, :expected_in_after_let}
                    end

                  err ->
                    err
                end

              _ ->
                {:error, :expected_assign_in_let}
            end

          _ ->
            {:error, :expected_name_in_let}
        end

      _ ->
        parse_expr_app(tokens)
    end
  end

  defp parse_infix_climber(tokens, left, prec) do
    case skip_virtual(tokens) do
      [tok | rest] ->
        op_info =
          case tok do
            {:operator, _, _, op_val} -> {op_val, rest}
            {:cons, _, _} -> {"::", rest}
            {:and_kw, _, _} -> {"/\\", rest}
            {:or_kw, _, _} -> {"\\/", rest}
            {:iff, _, _} -> {"<->", rest}
            {:arrow, _, _} -> {"->", rest}
            {:colon, _, _} -> {":", rest}
            _ -> nil
          end

        case op_info do
          {op_val, rest_after_op} ->
            op_prec = get_precedence(op_val)

            if op_prec <= prec do
              next_prec = if right_associative?(op_val), do: op_prec, else: op_prec - 1

              case parse_expr(rest_after_op, next_prec) do
                {:ok, right, rest2} ->
                  node =
                    case op_val do
                      "->" -> %AST.Pi{name: "_", domain: left, codomain: right}
                      ":" -> %AST.App{func: %AST.Var{name: "cast"}, arg: %AST.App{func: left, arg: right}}
                      _ -> %AST.App{func: %AST.App{func: %AST.Var{name: op_val}, arg: left}, arg: right}
                    end

                  parse_infix_climber(rest2, node, prec)

                err ->
                  err
              end
            else
              {:ok, left, tokens}
            end

          nil ->
            {:ok, left, tokens}
        end

      _ ->
        {:ok, left, tokens}
    end
  end

  defp get_precedence(op) do
    case op do
      "match" -> 200
      "forall" -> 200
      "fun" -> 200
      "exists" -> 200
      ":" -> 100
      "->" -> 99
      "<->" -> 90
      "\\/" -> 85
      "/\\" -> 80
      op when op in ["=", "<>", "<=", ">=", "<", ">"] -> 70
      "::" -> 60
      op when op in ["+", "-"] -> 50
      op when op in ["*", "/"] -> 40
      ".." -> 30
      _ -> 110
    end
  end

  defp right_associative?(op) do
    op in ["->", "<->", "\\/", "/\\", "::"]
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
    # IO.inspect({:parse_expr_atom, List.first(tokens)}, label: "ATOM")
    case skip_virtual(tokens) do
      [{:ident, _, _, name} | rest] ->
        {:ok, %AST.Var{name: name}, rest}

      [{:type_kw, _, _} | rest] ->
        {:ok, %AST.Universe{level: 0}, rest}

      [{:prop_kw, _, _} | rest] ->
        {:ok, %AST.Universe{level: -1}, rest}

      [{:number, _, _, n} | rest] ->
        {:ok, %AST.Number{value: n}, rest}

      [{:string, _, _, s} | rest] ->
        {:ok, %AST.String{value: s}, rest}

      [{:left_paren, _, _} | rest] ->
        case parse_expr(rest) do
          {:ok, e, [{:comma, _, _} | rest2]} ->
            parse_tuple([e], rest2)

          {:ok, e, [{:right_paren, _, _} | rest2]} ->
            {:ok, e, rest2}

          _ ->
            {:error, :expected_right_paren_expr}
        end

      _ ->
        {:error, :not_an_expr_atom}
    end
  end

  defp parse_tuple(acc, tokens) do
    case parse_expr(tokens) do
      {:ok, e, [{:comma, _, _} | rest]} ->
        parse_tuple(acc ++ [e], rest)

      {:ok, e, [{:right_paren, _, _} | rest]} ->
        # Convert list of exprs to nested pairs
        tuple =
          Enum.reduce(Enum.reverse(acc ++ [e]), nil, fn
            x, nil -> x
            x, acc_expr -> %AST.App{func: %AST.App{func: %AST.Var{name: "pair"}, arg: x}, arg: acc_expr}
          end)

        {:ok, tuple, rest}

      _ ->
        {:error, :expected_right_paren_in_tuple}
    end
  end

  defp parse_binders(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:ident, _, _, name} | rest] ->
        case skip_virtual(rest) do
          [{:colon, _, _} | rest2] ->
            case parse_type(rest2) do
              {:ok, ty, rest3} ->
                parse_binders(rest3, [{name, ty} | acc])

              _ ->
                parse_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])
            end

          _ ->
            parse_binders(rest, [{name, %AST.Var{name: "Any"}} | acc])
        end

      [{:left_paren, _, _} | rest] ->
        case parse_binder_names(rest, []) do
          {:ok, names, [{:colon, _, _} | rest2]} ->
            case parse_type(rest2) do
              {:ok, ty, [{:right_paren, _, _} | rest3]} ->
                new_binders = Enum.map(names, fn n -> {n, ty} end)
                parse_binders(rest3, Enum.reverse(new_binders) ++ acc)

              _ ->
                {:error, :invalid_binder_type}
            end

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
    case parse_pattern(tokens) do
      {:ok, pat, [{:fat_arrow, _, _} | rest]} ->
        case parse_expr(rest) do
          {:ok, body, rest2} ->
            {:ok, {pat, body}, rest2}

          err ->
            err
        end

      _ ->
        {:error, :expected_arrow_in_branch}
    end
  end

  defp parse_binder_names(tokens, acc) do
    tokens = skip_virtual(tokens)

    case tokens do
      [{:ident, _, _, name} | rest] ->
        parse_binder_names(rest, acc ++ [name])

      _ ->
        {:ok, acc, tokens}
    end
  end

  defp parse_pattern(tokens) do
    case skip_virtual(tokens) do
      [{:number, _, _, n} | rest] ->
        {:ok, %AST.Number{value: n}, rest}

      [{:string, _, _, s} | rest] ->
        {:ok, %AST.String{value: s}, rest}

      [{:ident, _, _, cname} | rest] ->
        case parse_pattern_args(rest, []) do
          {:ok, args, rest2} ->
            # Check for cons pattern: h :: tl
            case skip_virtual(rest2) do
              [{:cons, _, _} | rest3] ->
                case parse_pattern(rest3) do
                  {:ok, right_pat, rest4} ->
                    {:ok,
                     %AST.BinderConstructor{
                       name: "::",
                       args: [
                         %AST.BinderConstructor{name: cname, args: args},
                         right_pat
                       ]
                     }, rest4}

                  err ->
                    err
                end

              _ ->
                {:ok, %AST.BinderConstructor{name: cname, args: args}, rest2}
            end

          err ->
            err
        end

      [{:left_paren, _, _} | rest] ->
        case parse_pattern(rest) do
          {:ok, pat, [{:right_paren, _, _} | rest2]} -> {:ok, pat, rest2}
          _ -> {:error, :expected_right_paren_pattern}
        end

      _ ->
        {:error, :invalid_pattern}
    end
  end

  defp parse_pattern_args(tokens, acc) do
    case skip_virtual(tokens) do
      [{:ident, _, _, name} | rest] ->
        parse_pattern_args(rest, acc ++ [%AST.Var{name: name}])

      [{:left_paren, _, _} | _] = tokens ->
        case parse_pattern(tokens) do
          {:ok, pat, rest} -> parse_pattern_args(rest, acc ++ [pat])
          err -> err
        end

      _ ->
        {:ok, acc, tokens}
    end
  end

  defp tokens_to_string(tokens) do
    tokens
    |> Enum.map(fn t ->
      case t do
        {:ident, _, _, val} -> val
        {:number, _, _, val} -> to_string(val)
        {:operator, _, _, val} -> val
        {:string, _, _, val} -> "\"#{val}\""
        {type, _, _, val} when is_atom(type) -> to_string(val)
        {type, _, _} ->
          case type do
            :dot -> "."
            :colon -> ":"
            :assign -> ":="
            :fat_arrow -> "=>"
            :arrow -> "->"
            :back_arrow -> "<-"
            :iff -> "<->"
            :cons -> "::"
            :left_paren -> "("
            :right_paren -> ")"
            :left_bracket -> "["
            :right_bracket -> "]"
            :left_brace -> "{"
            :right_brace -> "}"
            :comma -> ","
            :pipe -> "|"
            :plus -> "+"
            :minus -> "-"
            :star -> "*"
            :slash -> "/"
            :equal -> "="
            :tilde -> "~"
            :and_kw -> "/\\"
            :or_kw -> "\\/"
            :not_equal -> "<>"
            :semicolon -> ";"
            :forall -> "forall"
            :exists -> "exists"
            :fun_kw -> "fun"
            :match_kw -> "match"
            :with_kw -> "with"
            :end_kw -> "end"
            :if_kw -> "if"
            :then_kw -> "then"
            :else_kw -> "else"
            :prop_kw -> "Prop"
            :type_kw -> "Type"
            _ -> ""
          end
        _ -> ""
      end
    end)
    |> Enum.join(" ")
    |> String.trim()
  end
end
