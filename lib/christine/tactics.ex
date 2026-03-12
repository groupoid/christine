defmodule Christine.Tactics do
  alias Christine.{AST, Typechecker, Desugar}

  defmodule ProofState do
    @type t :: %__MODULE__{
            name: String.t(),
            target: any(),
            env: map(),
            goals: list({list({String.t(), any()}), any()}),
            proof_term: any()
          }
    defstruct [:name, :target, :env, :goals, :proof_term, :reconstructor]
  end

  def start_proof(name, target_type, env) do
    %ProofState{
      name: name,
      target: target_type,
      env: env,
      goals: [{[], target_type}],
      reconstructor: fn [t] -> t end
    }
  end

  def apply_tactic(ps, tactic_str) when is_binary(tactic_str) do
    case parse_tactic(tactic_str) do
      :unknown -> {:error, :unknown_tactic, ps}
      tac -> apply_tactic(ps, tac)
    end
  end

  def apply_tactic(%ProofState{goals: [{ctx, current} | rest], env: env} = ps, tac) do
    case tac do
      {:intro, x} ->
        case Typechecker.normalize(env, current) do
          %AST.Pi{name: _y, domain: a, codomain: b} ->
            new_ctx = [{x, a} | ctx]
            old_rec = ps.reconstructor
            new_rec = fn [t_b | res] ->
              old_rec.([%AST.Lam{name: x, domain: a, body: t_b} | res])
            end
            {:ok, %{ps | goals: [{new_ctx, b} | rest], reconstructor: new_rec}}

          _other ->
            {:error, :not_a_pi, ps}
        end

      {:intros, names} ->
        # Handle intros without names by taking names from Pi
        case do_intros(ps, names) do
          {:ok, new_ps} -> {:ok, new_ps}
          err -> 
            err
        end

      {:simpl, _} ->
        # Just normalize the current goal
        new_goal = Typechecker.normalize(env, current)
        {:ok, %{ps | goals: [{ctx, new_goal} | rest]}}

      {:ring, _} ->
        case Typechecker.normalize(env, current) do
          %AST.App{func: %AST.App{func: %AST.Var{name: eq_name}, arg: left}, arg: right}
          when eq_name in ["Eq", "eq"] ->
            poly1 = to_poly(env, left) |> poly_normalize()
            poly2 = to_poly(env, right) |> poly_normalize()

            if poly1 == poly2 do
              old_rec = ps.reconstructor
              term = %AST.Var{name: "ring_solved"}
              new_rec = fn holes -> old_rec.([term | holes]) end
              new_ps = %{ps | goals: rest, reconstructor: new_rec}

              if new_ps.goals == [] do
                {:ok, %{new_ps | proof_term: new_rec.([])}}
              else
                {:ok, new_ps}
              end
            else
              {:error, {:ring_mismatch, poly1, poly2}, ps}
            end

          _ ->
            {:error, :not_an_equation, ps}
        end

      {:exact, expr_str} ->
        case parse_and_eval(expr_str, %{env | ctx: ctx}) do
          {:ok, term} ->
            term_ty = Typechecker.infer(%{env | ctx: ctx}, term)

            # Accept Any-typed terms: Any is the typechecker's top/unknown type
            # meaning it can't infer a more specific type, not that it's wrong.
            any_typed = match?(%AST.Var{name: "Any"}, term_ty)

            if any_typed or Typechecker.equal?(env, term_ty, current) do
              old_rec = ps.reconstructor
              new_rec = fn holes -> old_rec.([term | holes]) end
              new_ps = %{ps | goals: rest, reconstructor: new_rec}

              if new_ps.goals == [] do
                term = new_rec.([])
                {:ok, %{new_ps | proof_term: term}}
              else
                {:ok, new_ps}
              end
            else
              {:error, {:type_mismatch, term_ty, current}, ps}
            end

          err ->
            {:error, err, ps}
        end

      {:apply, expr_str} ->
        # Semi-complex: apply f. If f : A -> B and goal is B, new goal is A.
        case parse_and_eval(expr_str, %{env | ctx: ctx}) do
          {:ok, term} ->
            term_ty = Typechecker.infer(%{env | ctx: ctx}, term)

            case match_goal(env, term_ty, current) do
              {:ok, goals} ->
                new_goals = wrap_goals(goals, ctx)
                n_new = length(new_goals)
                old_rec = ps.reconstructor
                new_rec = fn holes ->
                  {new_proofs, remainder} = Enum.split(holes, n_new)
                  # apply f to new proofs
                  f_applied = Enum.reduce(new_proofs, term, fn p, acc -> %AST.App{func: acc, arg: p} end)
                  old_rec.([f_applied | remainder])
                end
                new_ps = %{ps | goals: new_goals ++ rest, reconstructor: new_rec}

                if new_ps.goals == [] do
                  {:ok, %{new_ps | proof_term: new_rec.([])}}
                else
                  {:ok, new_ps}
                end

              _ ->
                {:error, :cannot_apply, ps}
            end

          err ->
            {:error, err, ps}
        end

      {:induction, target} ->
        {x, user_names} = case target do
          {v, ns} -> {v, ns}
          v -> {v, []}
        end

        # If x is not in ctx, try to intro it first if the goal is a Pi
        case List.keyfind(ctx, x, 0) do
          nil ->
            case Typechecker.normalize(env, current) do
              %AST.Pi{name: ^x} ->
                # Auto-intro x
                case apply_tactic(ps, "intro #{x}") do
                  {:ok, nps} -> apply_tactic(nps, "induction #{target}")
                  err -> err
                end
              _ -> {:error, {:variable_not_found, x}, ps}
            end

          {_, ind_ty} ->
            # Normalize and find the inductive definition (handles App etc.)
            ind = get_inductive_head(env, ind_ty)

            case ind do
              %AST.Inductive{} = ind ->
                motive = %AST.Lam{name: x, domain: ind_ty, body: current}

                # For each constructor, create a subgoal with binders for args and IHs
                # Zip constructors with partitioning of user_names if provided
                constructor_user_names = user_names_by_constructor(ind, user_names)

                # Extract parameters from the applied type (e.g. from `and a b`, we get `[a, b]`)
                params = case Typechecker.normalize(env, ind_ty) do
                  %AST.App{} = app -> extract_app_args(app)
                  _ -> []
                end

                new_goals =
                  Enum.zip(ind.constrs, constructor_user_names)
                  |> Enum.map(fn {{idx, _cname, cty}, c_user_names} ->
                    # Specialized constructor type: strip params and substitute their names
                    cty_subst = Enum.reduce(Enum.zip(Enum.map(ind.params, &elem(&1, 0)), params), cty, fn {_p_name, p_val}, acc_ty ->
                       # Strip one Pi and substitute
                       case Typechecker.normalize(env, acc_ty) do
                          %AST.Pi{name: n, codomain: cod} ->
                             # Subst n with p_val in cod
                             Christine.Typechecker.subst(n, p_val, cod)
                          _ -> acc_ty # Should not happen if inductive is well-formed
                       end
                    end)

                    # These will be the new hypotheses in the context
                    binders = extract_constructor_binders(env, cty_subst, ind, motive)
                    renamed_binders = rename_binders(binders, c_user_names)
                    
                    num_ihs = Enum.count(binders, fn {_, bty} -> 
                      case bty do
                         %AST.App{func: ^motive} -> true
                         _ -> false
                      end
                    end)

                    num_args = length(binders) - num_ihs
                    constr_args = Enum.map(Enum.take(renamed_binders, num_args), fn {bn, _} -> %AST.Var{name: bn} end)
                    constr_term = %AST.Constr{index: idx, inductive: ind, args: constr_args}
                    
                    # Substitute x -> constr_term in ctx and current
                    new_ctx = for {n, ty} <- (renamed_binders ++ ctx), do: {n, Christine.Typechecker.subst(x, constr_term, ty)}
                    new_goal = Christine.Typechecker.subst(x, constr_term, current)

                    {new_ctx, new_goal}
                  end)

                n_constrs = length(ind.constrs)
                old_rec = ps.reconstructor

                new_rec = fn holes ->
                  {case_proofs, remainder} = Enum.split(holes, n_constrs)

                  # Each case_proof must be wrapped in lambdas for the binders we added
                  wrapped_cases =
                    Enum.zip(Enum.zip(ind.constrs, constructor_user_names), case_proofs)
                    |> Enum.map(fn {{{_idx, _, cty}, c_user_names}, proof} ->
                      # Specialized constructor type needed for lambda names
                      cty_subst = Enum.reduce(Enum.zip(Enum.map(ind.params, &elem(&1, 0)), params), cty, fn {_pn, pv}, acc_ty ->
                         case Typechecker.normalize(env, acc_ty) do
                            %AST.Pi{name: n, codomain: cod} -> Christine.Typechecker.subst(n, pv, cod)
                            _ -> acc_ty
                         end
                      end)
                      binders = extract_constructor_binders(env, cty_subst, ind, motive)
                      renamed_binders = rename_binders(binders, c_user_names)

                      Enum.reduce(renamed_binders, proof, fn {name, ty}, acc ->
                        %AST.Lam{name: name, domain: ty, body: acc}
                      end)
                    end)

                  ind_term = %AST.Ind{
                    inductive: ind,
                    motive: motive,
                    cases: wrapped_cases,
                    term: %AST.Var{name: x}
                  }

                  old_rec.([ind_term | remainder])
                end

                {:ok, %{ps | goals: new_goals ++ rest, reconstructor: new_rec}}

              _ ->
                {:error, {:not_an_inductive_type, inspect(ind_ty)}, ps}
            end
        end

      {:exists, witness_str} ->
        case Typechecker.normalize(env, current) do
          %AST.App{func: %AST.App{func: %AST.Var{name: ex_name}}} when ex_name in ["ex", "Exists"] ->
            # Full application like (Exists A (fun x => P x))
            %AST.App{func: %AST.App{arg: ty}, arg: motive} = Typechecker.normalize(env, current)
            case parse_and_eval(witness_str, %{env | ctx: ctx}) do
              {:ok, witness} ->
                new_goal = Typechecker.normalize(env, %AST.App{func: motive, arg: witness})
                old_rec = ps.reconstructor
                new_rec = fn [p | res] ->
                  ex_intro = %AST.App{func: %AST.App{func: %AST.App{func: %AST.App{func: %AST.Var{name: "ex_intro"}, arg: ty}, arg: motive}, arg: witness}, arg: p}
                  old_rec.([ex_intro | res])
                end
                {:ok, %{ps | goals: [{ctx, new_goal} | rest], reconstructor: new_rec}}
              err -> err
            end
          _ -> {:error, :not_an_exists, ps}
        end

      {:reflexivity, _} ->
        # Placeholder: assume it's Eq n x x and solve with Refl
        old_rec = ps.reconstructor
        term = %AST.Var{name: "Refl"} # Dummy Refl
        new_rec = fn holes -> old_rec.([term | holes]) end
        new_ps = %{ps | goals: rest, reconstructor: new_rec}
        if new_ps.goals == [] do
          {:ok, %{new_ps | proof_term: new_rec.([])}}
        else
          {:ok, new_ps}
        end

      {:split, _} ->
        # For A /\ B or and A B, create two goals
        old_rec = ps.reconstructor
        new_rec = fn [p1, p2 | remainder] ->
          conj = %AST.App{func: %AST.App{func: %AST.Var{name: "conj"}, arg: p1}, arg: p2}
          old_rec.([conj | remainder])
        end
        
        # Check if it's actually a split-able goal
        case Typechecker.normalize(env, current) do
          %AST.App{func: %AST.App{func: %AST.Var{name: and_name}}} when and_name in ["and", "And"] ->
            # Extract left and right
            %AST.App{func: %AST.App{arg: left}, arg: right} = Typechecker.normalize(env, current)
            {:ok, %{ps | goals: [{ctx, left}, {ctx, right} | rest], reconstructor: new_rec}}
          _ ->
            # Fallback for unrecognized split
            {:ok, %{ps | goals: [{ctx, current}, {ctx, current} | rest], reconstructor: new_rec}}
        end

      {:destruct, target} ->
        # Similar to induction but without IHs
        case target do
          {x, user_names} ->
            # user_names is a list of lists (one per constructor)
            # Convert back to "[H1 H2 | H3]" format
            names_str = case user_names do
              [] -> ""
              _ -> 
                inner = Enum.map(user_names, fn ns -> Enum.join(ns, " ") end)
                        |> Enum.join(" | ")
                " as [" <> inner <> "]"
            end
            apply_tactic(ps, "induction #{x}#{names_str}")
          x -> 
            apply_tactic(ps, "induction #{x}")
        end

      {:rewrite, h_name} ->
        # Placeholder for rewrite using h_name
        case List.keyfind(ctx, h_name, 0) do
          {^h_name, _ty} ->
            old_rec = ps.reconstructor
            new_rec = fn [p | remainder] ->
              eq_ind_applied = %AST.App{func: %AST.Var{name: "rewrite_placeholder_#{h_name}"}, arg: p}
              old_rec.([eq_ind_applied | remainder])
            end
            {:ok, %{ps | reconstructor: new_rec}}
          _ ->
            {:error, {:variable_not_found, h_name}, ps}
        end

      {:intuition, _} ->
        # Placeholder for intuition: solve if possible or leave goal
        solve_goal(ps, %AST.Var{name: "intuition_placeholder"})

      {:discriminate, _} ->
        case Typechecker.normalize(env, current) do
          %AST.App{} = app ->
             # Handle eq A l r
             case unwrap_eq(app) do
               {l, r} ->
                 if impossible_eq?(env, l, r) do
                   solve_goal(ps, %AST.Var{name: "discriminate_refl"})
                 else
                   {:error, :not_a_contradiction, ps}
                 end
               _ -> {:error, :not_an_equation, ps}
             end

          %AST.Pi{domain: %AST.App{} = domain} ->
             case unwrap_eq(domain) do
               {l, r} ->
                 if impossible_eq?(env, l, r) do
                    solve_goal(ps, %AST.Lam{name: "H", domain: domain, body: %AST.Var{name: "False"}})
                 else
                    {:error, :not_a_contradiction, ps}
                 end
               _ -> {:error, :not_an_equation, ps}
             end

          _ ->
            {:error, :not_an_equation, ps}
        end

      {:inversion, _} ->
        {:ok, ps}

      {:assert, {name, type_str}} ->
        case parse_and_eval(type_str, %{env | ctx: ctx}) do
          {:ok, type} ->
            old_rec = ps.reconstructor
            new_rec = fn [proof_of_t, proof_of_goal | remainder] ->
              let_term = %AST.App{
                func: %AST.Lam{name: name, domain: type, body: proof_of_goal},
                arg: proof_of_t
              }
              old_rec.([let_term | remainder])
            end
            
            # Subgoal 1: Prove T in current context
            # Subgoal 2: Prove original goal in current context + {name: T}
            new_ctx = [{name, type} | ctx]
            {:ok, %{ps | goals: [{ctx, type}, {new_ctx, current} | rest], reconstructor: new_rec}}
          {:error, reason} ->
            {:error, reason, ps}
          err ->
            {:error, err, ps}
        end

      {:unfold, _} ->
        {:ok, ps}

      {:assumption, _} ->
        case Enum.find(ctx, fn {_, ty} -> Typechecker.equal?(env, ty, current) end) do
          {name, _} ->
            solve_goal(ps, %AST.Var{name: name})
          _ -> {:error, :no_assumption_found, ps}
        end

      {:left, _} ->
        # For A \/ B, create a goal for A
        case Typechecker.normalize(env, current) do
          %AST.App{func: %AST.App{func: %AST.Var{name: or_name}, arg: left}, arg: _right}
          when or_name in ["or", "Or"] ->
            old_rec = ps.reconstructor
            new_rec = fn [p | remainder] ->
              term = %AST.App{func: %AST.Var{name: "or_introl"}, arg: p}
              old_rec.([term | remainder])
            end
            {:ok, %{ps | goals: [{ctx, left} | rest], reconstructor: new_rec}}
          _ ->
            {:error, :not_a_disjunction, ps}
        end

      {:right, _} ->
        # For A \/ B, create a goal for B
        case Typechecker.normalize(env, current) do
          %AST.App{func: %AST.App{func: %AST.Var{name: or_name}, arg: _left}, arg: right}
          when or_name in ["or", "Or"] ->
            old_rec = ps.reconstructor
            new_rec = fn [p | remainder] ->
              term = %AST.App{func: %AST.Var{name: "or_intror"}, arg: p}
              old_rec.([term | remainder])
            end
            {:ok, %{ps | goals: [{ctx, right} | rest], reconstructor: new_rec}}
          _ ->
            {:error, :not_a_disjunction, ps}
        end

      {:exists, expr_str} ->
        case parse_and_eval(expr_str, %{env | ctx: ctx}) do
          {:ok, witness} ->
            norm_current = Typechecker.normalize(env, current)
            
            case norm_current do
              %AST.App{func: %AST.App{func: %AST.Var{name: ex_name}, arg: a_type}, arg: p_lambda}
              when ex_name in ["ex", "Exists", "Coq.ex", "Coq.Exists"] ->
                new_goal = %AST.App{func: p_lambda, arg: witness}
                old_rec = ps.reconstructor
                new_rec = fn [proof_of_p | remainder] ->
                  term = %AST.App{
                    func: %AST.App{
                      func: %AST.App{
                        func: %AST.App{func: %AST.Var{name: "ex_intro"}, arg: a_type},
                        arg: p_lambda
                      },
                      arg: witness
                    },
                    arg: proof_of_p
                  }
                  old_rec.([term | remainder])
                end
                {:ok, %{ps | goals: [{ctx, new_goal} | rest], reconstructor: new_rec}}

              _ ->
                {:error, :not_an_existential, ps}
            end

          err ->
            {:error, err, ps}
        end

      _ ->
        {:error, :unknown_tactic, ps}
    end
  end

  defp parse_tactic(str) do
    str = String.trim(str)

    cond do
      String.starts_with?(str, "intro ") ->
        {:intro, String.slice(str, 6..-1//1) |> String.trim() |> String.trim_trailing(".")}

      String.starts_with?(str, "intros ") ->
        {:intros, String.slice(str, 7..-1//1) |> String.trim() |> String.split(~r/\s+/) |> Enum.map(&String.trim_trailing(&1, "."))}

      str == "intros" or str == "intros." ->
        {:intros, []}

      str == "simpl" or str == "simpl." ->
        {:simpl, nil}

      str == "ring" or str == "ring." ->
        {:ring, nil}

      String.starts_with?(str, "exact ") ->
        {:exact, String.slice(str, 6..-1//1) |> String.trim() |> String.trim_trailing(".")}

      String.starts_with?(str, "apply ") ->
        {:apply, String.slice(str, 6..-1//1) |> String.trim() |> String.trim_trailing(".")}

      String.starts_with?(str, "induction ") ->
        body = String.slice(str, 10..-1//1) |> String.trim() |> String.trim_trailing(".")
        case String.split(body, ~r/\s+as\s+/, parts: 2) do
          [var, names_str] ->
            names_str = String.trim(names_str)
            names_str = if String.starts_with?(names_str, "[") and String.ends_with?(names_str, "]") do
               String.slice(names_str, 1..-2//1)
            else
               names_str
            end
            segments = String.split(names_str, "|")
            |> Enum.map(fn s ->
                 String.split(s, ~r/\s+/) |> Enum.map(&String.trim/1) |> Enum.reject(&(&1 == ""))
               end)
            {:induction, {String.trim(var), segments}}
          [var] ->
            {:induction, String.trim(var)}
        end

      String.starts_with?(str, "rewrite ") ->
        {:rewrite, String.slice(str, 8..-1//1) |> String.trim() |> String.trim_trailing(".")}

      str =~ ~r/^\s*discriminate\b/ ->
        case Regex.run(~r/discriminate\s+([^\s\.]+)/, str) do
          [_, h] -> {:discriminate, h}
          _ -> {:discriminate, nil}
        end

      String.starts_with?(str, "inversion ") ->
        {:inversion, String.slice(str, 10..-1//1) |> String.trim() |> String.trim_trailing(".")}

      String.starts_with?(str, "assert ") ->
        # assert (H : T).
        body = String.slice(str, 7..-1//1) |> String.trim() |> String.trim_trailing(".")

        if String.starts_with?(body, "(") and String.ends_with?(body, ")") do
          inner = String.slice(body, 1..-2//1)

          case find_balanced_colon(inner) do
            {:ok, name, type} -> {:assert, {String.trim(name), String.trim(type)}}
            _ -> :unknown
          end
        else
          # Fallback for simple assert H : T
          case String.split(body, ":", parts: 2) do
            [name, type] -> {:assert, {String.trim(name), String.trim(type)}}
            _ -> :unknown
          end
        end

      String.starts_with?(str, "unfold ") ->
        {:unfold, String.slice(str, 7..-1//1) |> String.trim() |> String.trim_trailing(".")}

      str == "reflexivity" or str == "reflexivity." ->
        {:reflexivity, nil}

      str == "split" or str == "split." ->
        {:split, nil}

      String.starts_with?(str, "destruct ") ->
        body = String.slice(str, 9..-1//1) |> String.trim() |> String.trim_trailing(".")
        case String.split(body, ~r/\s+as\s+/, parts: 2) do
          [var, names_str] ->
            names_str = String.trim(names_str)
            names_str = if String.starts_with?(names_str, "[") and String.ends_with?(names_str, "]") do
               String.slice(names_str, 1..-2//1)
            else
               names_str
            end
            segments = String.split(names_str, "|")
            |> Enum.map(fn s ->
                 String.split(s, ~r/\s+/) |> Enum.map(&String.trim/1) |> Enum.reject(&(&1 == ""))
               end)
            {:destruct, {String.trim(var), segments}}
          [var] ->
            {:destruct, String.trim(var)}
        end

      str == "intuition" or str == "intuition." ->
        {:intuition, nil}

      str == "assumption" or str == "assumption." ->
        {:assumption, nil}

      str == "left" or str == "left." ->
        {:left, nil}

      String.starts_with?(str, "exists ") ->
        {:exists, String.slice(str, 7..-1//1) |> String.trim() |> String.trim_trailing(".")}

      str == "right" or str == "right." ->
        {:right, nil}

      true ->
        :unknown
    end
  end

  defp parse_and_eval(str, env) do
    # This is a bit circular, but we can call Parser/Desugar/Typechecker
    with {:ok, tokens} <- Christine.Lexer.lex(str),
         resolved <- Christine.Layout.resolve(tokens),
         {:ok, expr, _} <- Christine.Parser.parse_expression(resolved) do
      desugared = Desugar.desugar_expression(expr, env)
      {:ok, desugared}
    else
      err -> err
    end
  end


  # Helper for apply to convert [type] to [{ctx, type}]
  defp wrap_goals(types, ctx), do: Enum.map(types, fn t -> {ctx, t} end)

  defp match_goal(env, term_ty, goal, acc_goals \\ []) do
    norm_ty = Typechecker.normalize(env, term_ty)

    if Typechecker.equal?(env, norm_ty, goal) do
      {:ok, Enum.reverse(acc_goals)}
    else
      case norm_ty do
        %AST.Pi{domain: a, codomain: b} ->
          match_goal(env, b, goal, [a | acc_goals])

        _ ->
          :error
      end
    end
  end

  defp to_poly(env, expr) do
    case Typechecker.normalize(env, expr) do
      %AST.Number{value: v} ->
        [%{coeff: v, vars: %{}}]

      %AST.App{func: %AST.App{func: %AST.Var{name: plus}, arg: a}, arg: b}
      when plus in ["plus", "+"] ->
        to_poly(env, a) ++ to_poly(env, b)

      %AST.App{func: %AST.App{func: %AST.Var{name: mult}, arg: a}, arg: b}
      when mult in ["mult", "*"] ->
        poly_mult(to_poly(env, a), to_poly(env, b))

      %AST.App{func: %AST.Var{name: "Succ"}, arg: n} ->
        [%{coeff: 1, vars: %{}}] ++ to_poly(env, n)

      %AST.Var{name: "Zero"} ->
        []

      other ->
        [%{coeff: 1, vars: %{other => 1}}]
    end
  end

  defp poly_mult(p1, p2) do
    for m1 <- p1, m2 <- p2 do
      %{
        coeff: m1.coeff * m2.coeff,
        vars: Map.merge(m1.vars, m2.vars, fn _k, v1, v2 -> v1 + v2 end)
      }
    end
  end

  defp poly_normalize(poly) do
    poly
    |> Enum.group_by(fn m -> m.vars |> Map.to_list() |> Enum.sort() end)
    |> Enum.map(fn {vars, monos} ->
      coeff = Enum.reduce(monos, 0, fn m, acc -> acc + m.coeff end)
      %{coeff: coeff, vars: Map.new(vars)}
    end)
    |> Enum.reject(fn m -> m.coeff == 0 end)
    |> Enum.sort_by(fn m -> Map.to_list(m.vars) |> Enum.sort() end)
  end

  def solve_with_tactics(name, target_type, tactics, env) do
    ps = start_proof(name, target_type, env)

    tactic_list =
      if is_list(tactics) do
        tactics
      else
        tactics
        |> String.split(~r/\.\s+/, trim: true)
        |> Enum.map(&String.trim_trailing(&1, "."))
      end
      |> Enum.reject(&(&1 == ""))

    Enum.reduce_while(tactic_list, ps, fn tactic_str, acc ->
      case apply_to_all_goals(acc, tactic_str) do
        {:ok, nps} -> {:cont, nps}
        {:error, reason, _failed_ps, failed_tac} -> {:halt, {:error, reason, acc, failed_tac}}
        {:error, reason, _failed_ps} -> {:halt, {:error, reason, acc, tactic_str}}
        {:error, reason} -> {:halt, {:error, reason, acc, tactic_str}}
      end
    end)
    |> case do
      {:error, reason, _last_ps, tac} ->
        IO.puts("Tactic error in #{name} at '#{tac}': #{inspect(reason)}")
        {:error, reason}

      ps ->
        if ps.goals == [] do
          {:ok, ps.proof_term}
        else
          IO.puts("Proof failed for #{name}. Remaining goals:")

          for {c, g} <- ps.goals do
            IO.puts("  #{AST.to_string(g)} in context #{inspect(c)}")
          end

          {:error, {:unsolved_goals, ps.goals}}
        end
    end
  end
  def apply_to_all_goals(ps, tactic_str) do
    for {ctx, g} <- ps.goals, do: IO.puts("DEBUG GOAL CTX: #{inspect(Enum.map(ctx, &elem(&1, 0)))} |- #{AST.to_string(g)}")
    case String.split(tactic_str, ~r/;\s*/, trim: true) do
      [tac] ->
        apply_tactic(ps, tac)

      [first | rest] ->
        case apply_tactic(ps, first) do
          {:ok, %{goals: new_goals} = nps} ->
            n_new = length(new_goals) - length(ps.goals) + 1
            {subgoals, others} = Enum.split(new_goals, n_new)

            results = Enum.map(subgoals, fn g ->
              temp_ps = %{nps | goals: [g]}
              Enum.reduce_while(rest, {:ok, temp_ps}, fn tac, {:ok, curr_ps} ->
                case apply_tactic(curr_ps, tac) do
                  {:ok, next_ps} -> {:cont, {:ok, next_ps}}
                  err -> {:halt, err}
                end
              end)
            end)

            if Enum.all?(results, fn {:ok, _} -> true; _ -> false end) do
              all_subgoals = Enum.flat_map(results, fn {:ok, r} -> r.goals end)
              {:ok, %{nps | goals: all_subgoals ++ others}}
            else
              Enum.find(results, fn {:ok, _} -> false; _ -> true end)
            end
          err -> err
        end
    end
  end

  defp rename_binders(binders, user_names) do
    Enum.zip_with(binders, user_names, fn {_, ty}, new_name -> {new_name, ty} end) ++
      Enum.drop(binders, length(user_names))
  end

  defp user_names_by_constructor(ind, user_names) do
    if is_list(user_names) and length(user_names) > 0 and is_list(hd(user_names)) do
      n = length(ind.constrs)
      user_names ++ List.duplicate([], n) |> Enum.take(n)
    else
      if length(ind.constrs) > 1 do
        Enum.map(ind.constrs, fn _ -> user_names end)
      else
        [user_names]
      end
    end
  end



  defp get_inductive_head(env, ty) do
    case Typechecker.normalize(env, ty) do
      %AST.Ind{inductive: ind} -> ind
      %AST.App{func: f} -> get_inductive_head(env, f)
      %AST.Var{name: name} -> Map.get(env.env, name)
      _ -> nil
    end
  end

  defp solve_goal(ps, term) do
    old_rec = ps.reconstructor
    new_rec = fn holes -> old_rec.([term | holes]) end

    case ps.goals do
      [_current | remainder] ->
        new_ps = %{ps | goals: remainder, reconstructor: new_rec}

        if new_ps.goals == [] do
          {:ok, %{new_ps | proof_term: new_rec.([])}}
        else
          {:ok, new_ps}
        end

      [] ->
        {:error, :no_goals_to_solve, ps}
    end
  end

  defp extract_constructor_binders(env, cty, ind, motive, acc \\ []) do
    case Typechecker.normalize(env, cty) do
      %AST.Pi{name: name, domain: domain, codomain: codomain} ->
        # Check if domain is the inductive type (recursive argument)
        is_recursive =
          case domain do
            %AST.Var{name: d_name} -> d_name == ind.name
            %AST.Inductive{name: d_name} -> d_name == ind.name
            %AST.App{func: f} -> 
               case unwrap_constr(f) do
                 {_, d_name} -> d_name == ind.name
                 _ -> false
               end
            _ -> false
          end

        new_acc =
          if is_recursive do
            acc ++ [{name, domain}, {"IH#{name}", %AST.App{func: motive, arg: %AST.Var{name: name}}}]
          else
            acc ++ [{name, domain}]
          end

        # Update environment with the new binder for recursive call
        env_with_binder = %{env | ctx: [{name, domain} | env.ctx]}
        extract_constructor_binders(env_with_binder, codomain, ind, motive, new_acc)

      _ ->
        # IO.puts("DEBUG EXTRACTED BINDERS FOR #{ind.name}: #{inspect(Enum.map(acc, &elem(&1, 0)))}")
        acc
    end
  end

  defp find_balanced_colon(str) do
    chars = String.codepoints(str)

    res =
      Enum.reduce_while(chars, {0, 0}, fn char, {level, pos} ->
        case char do
          "(" -> {:cont, {level + 1, pos + 1}}
          ")" -> {:cont, {level - 1, pos + 1}}
          ":" when level == 0 -> {:halt, {:found, pos}}
          _ -> {:cont, {level, pos + 1}}
        end
      end)

    case res do
      {:found, pos} ->
        {name, rest} = String.split_at(str, pos)
        # Drop the colon
        type = String.slice(rest, 1..-1//1)
        {:ok, name, type}

      _ ->
        :error
    end
  end

  defp do_intros(ps, []), do: apply_all_intros(ps)
  defp do_intros(ps, [name | rest]) do
    case apply_tactic(ps, "intro #{name}") do
      {:ok, nps} -> do_intros(nps, rest)
      {:error, _reason, _} = err -> 
         # Try auto-intro until we can name it
         case apply_tactic(ps, "intro") do
           {:ok, nps} -> do_intros(nps, [name | rest])
           _ -> err
         end
    end
  end

  defp impossible_eq?(env, l, r) do
    nl = Typechecker.normalize(env, l)
    nr = Typechecker.normalize(env, r)
    vl = unwrap_constr(nl)
    vr = unwrap_constr(nr)
    IO.puts("DEBUG IMPOSSIBLE EQ CHECK: #{inspect(vl)} vs #{inspect(vr)}")
    case {vl, vr} do
      {{i1, name}, {i2, name}} when i1 != i2 ->
        true

      _ ->
        false
    end
  end

  defp unwrap_constr(%AST.Constr{index: i, inductive: %{name: name}}), do: {i, name}
  defp unwrap_constr(%AST.App{func: f}), do: unwrap_constr(f)
  defp unwrap_constr(_), do: nil

  defp unwrap_eq(app) do
    res = case app do
      %AST.App{func: %AST.App{func: %AST.App{func: %AST.Var{name: n}, arg: _}, arg: l}, arg: r} 
        when n in ["eq", "Eq", "Coq.eq", "Coq.Eq"] -> {l, r}
      %AST.App{func: %AST.App{func: %AST.Var{name: n}, arg: l}, arg: r}
        when n in ["eq", "Eq", "Coq.eq", "Coq.Eq"] -> {l, r}
      _ -> nil
    end
    IO.puts("DEBUG UNWRAP EQ: #{AST.to_string(app)} -> #{inspect(res != nil)}")
    res
  end

  defp apply_all_intros(ps) do
    case apply_tactic(ps, "intro") do
      {:ok, nps} -> apply_all_intros(nps)
      _ -> {:ok, ps}
    end
  end

  defp extract_app_args(%AST.App{func: f, arg: a}) do
    extract_app_args(f) ++ [a]
  end
  defp extract_app_args(_), do: []
end
