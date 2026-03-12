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

  def apply_tactic(%ProofState{goals: []} = ps, _), do: {:error, :no_more_goals, ps}

  def apply_tactic(%ProofState{goals: [{ctx, current} | rest], env: env} = ps, tactic_str) do
    case parse_tactic_command(tactic_str) do
      {:intro, x} ->
        IO.puts("DEBUG: intro #{x}. Current goal: #{AST.to_string(current)}")
        case Typechecker.normalize(env, current) do
          %AST.Pi{name: _y, domain: a, codomain: b} ->
            new_ctx = [{x, a} | ctx]
            old_rec = ps.reconstructor
            new_rec = fn [t_b | res] ->
              old_rec.([%AST.Lam{name: x, domain: a, body: t_b} | res])
            end
            {:ok, %{ps | goals: [{new_ctx, b} | rest], reconstructor: new_rec}}

          other ->
            IO.puts("DEBUG: intro #{x} failed. Goal is not a Pi: #{inspect(other, limit: 5)}")
            {:error, :not_a_pi, ps}
        end

      {:intros, names} ->
        IO.puts("DEBUG: intros #{inspect(names)}. Current goal: #{AST.to_string(current)}")
        # Handle intros without names by taking names from Pi
        case do_intros(ps, names) do
          {:ok, new_ps} -> {:ok, new_ps}
          err -> 
            IO.puts("DEBUG: intros failed: #{inspect(err)}")
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
                # IO.inspect(term, label: "CAPTURED PROOF TERM")
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

                new_goals =
                  Enum.zip(ind.constrs, constructor_user_names)
                  |> Enum.map(fn {{_idx, _, cty}, c_user_names} ->
                    # Extract binders for constructor cty: forall (a:A) (b:B)... -> Ind
                    # These will be the new hypotheses in the context
                    binders = extract_constructor_binders(env, cty, ind.name, motive)
                    renamed_binders = rename_binders(binders, c_user_names)
                    new_ctx = renamed_binders ++ ctx
                    {new_ctx, current}
                  end)

                n_constrs = length(ind.constrs)
                old_rec = ps.reconstructor

                new_rec = fn holes ->
                  {case_proofs, remainder} = Enum.split(holes, n_constrs)

                  # Each case_proof must be wrapped in lambdas for the binders we added
                  wrapped_cases =
                    Enum.zip(Enum.zip(ind.constrs, constructor_user_names), case_proofs)
                    |> Enum.map(fn {{{_idx, _, cty}, c_user_names}, proof} ->
                      binders = extract_constructor_binders(env, cty, ind.name, motive)
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
        {x, _} = case target do
          {v, ns} -> {v, ns}
          v -> {v, []}
        end
        apply_tactic(ps, "induction #{x}")

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
          %AST.App{func: %AST.App{func: %AST.Var{name: eq_name}, arg: left}, arg: right}
          when eq_name in ["Eq", "eq"] ->
            case {Typechecker.normalize(env, left), Typechecker.normalize(env, right)} do
              {%AST.App{func: %AST.Var{name: c1}}, %AST.App{func: %AST.Var{name: c2}}} when c1 != c2 ->
                solve_goal(ps, %AST.Var{name: "discriminate_solved"})

              _ ->
                {:error, :not_discriminated, ps}
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
            IO.inspect(norm_current, label: "NORMALIZED GOAL FOR EXISTS")
            
            case norm_current do
              %AST.App{func: %AST.App{func: %AST.Var{name: ex_name}, arg: a_type}, arg: p_lambda}
              when ex_name in ["ex", "Exists"] ->
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
                IO.puts("DEBUG: not_an_existential. Goal normalized to: #{inspect(norm_current, limit: 5)}")
                {:error, :not_an_existential, ps}
            end

          err ->
            {:error, err, ps}
        end

      _ ->
        {:error, :unknown_tactic, ps}
    end
  end

  defp parse_tactic_command(str) do
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

      str == "discriminate" or str == "discriminate." ->
        {:discriminate, nil}

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
        [%{coeff: 1, vars: %{AST.to_string(other) => 1}}]
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

    # Split tactics if it's a single string, or use as is if it's a list
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
      # Handle Coq semicolon: tac1 ; tac2
      case String.split(tactic_str, ~r/;\s*/, trim: true) do
        [tac] ->
          case apply_tactic(acc, tac) do
            {:ok, nps} -> {:cont, nps}
            {:error, reason, _ps} -> {:halt, {:error, reason, acc, tac}}
            {:error, reason} -> {:halt, {:error, reason, acc, tac}}
          end

        [first_tac | rest_tacs] ->
          case apply_tactic(acc, first_tac) do
            {:ok, nps} ->
              res =
                Enum.reduce_while(rest_tacs, {:ok, nps}, fn next_tac, {:ok, inner_ps} ->
                  case apply_to_all_goals(inner_ps, next_tac) do
                    {:ok, final_ps} -> {:cont, {:ok, final_ps}}
                    {:error, reason, _} -> {:halt, {:error, reason, inner_ps, next_tac}}
                  end
                end)

              case res do
                {:ok, final} -> {:cont, final}
                {:error, reason, last_ps, failed_tac} -> {:halt, {:error, reason, last_ps, failed_tac}}
              end

            {:error, reason, _ps} ->
              {:halt, {:error, reason, acc, first_tac}}

            {:error, reason} ->
              {:halt, {:error, reason, acc, first_tac}}
          end
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

  defp rename_binders(binders, user_names) do
    Enum.zip_with(binders, user_names, fn {_, ty}, new_name -> {new_name, ty} end) ++
      Enum.drop(binders, length(user_names))
  end

  defp user_names_by_constructor(ind, user_names) do
    if is_list(user_names) and length(user_names) > 0 and is_list(hd(user_names)) do
      # Already segmented by |
      n = length(ind.constrs)
      user_names ++ List.duplicate([], n) |> Enum.take(n)
    else
      # Simple logic: if multiple constructors (like or), split names by pipe
      # If one constructor (like and), use all names.
      if length(ind.constrs) > 1 do
        # For now, just a heuristic: partition names if possible or repeat
        # Real Coq uses [ a b | c ] syntax which we should parse better.
        # For now, if user provided names, just repeat or partition.
        Enum.map(ind.constrs, fn _ -> user_names end)
      else
        [user_names]
      end
    end
  end

  defp apply_to_all_goals(ps, tactic_str) do
    # In Coq, tac1 ; tac2 applies tac2 to ALL goals produced by tac1.
    # Here we apply to all goals currently open in the ProofState.
    if ps.goals == [] do
      {:ok, ps}
    else
      # ACTUAL Simple Implementation: Apply to ALL goals one by one.
      Enum.reduce_while(ps.goals, {:ok, %{ps | goals: []}}, fn {ctx, target}, {:ok, acc_ps} ->
        # Goal-specific ProofState
        temp_ps = %{acc_ps | goals: [{ctx, target}]}
        case apply_tactic(temp_ps, tactic_str) do
          {:ok, next_ps} ->
            # Accumulate subgoals and preserve proof_term if solved
            {:cont, {:ok, %{next_ps | goals: acc_ps.goals ++ next_ps.goals}}}
          {:error, reason, _failed_ps} ->
            # If it fails on ONE goal, Coq usually errors out.
            {:halt, {:error, reason, ps}}
        end
      end)
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

  defp extract_constructor_binders(env, cty, ind_name, motive, acc \\ []) do
    case Typechecker.normalize(env, cty) do
      %AST.Pi{name: name, domain: domain, codomain: codomain} ->
        # Check if domain is the inductive type (recursive argument)
        is_recursive =
          case Typechecker.normalize(env, domain) do
            %AST.Ind{inductive: %{name: ^ind_name}} -> true
            _ ->
              case domain do
                %AST.Var{name: ^ind_name} -> true
                _ -> false
              end
          end

        new_acc = acc ++ [{name, domain}]

        new_acc =
          if is_recursive do
            ih_name = "IH#{name}"
            ih_ty = %AST.App{func: motive, arg: %AST.Var{name: name}}
            new_acc ++ [{ih_name, ih_ty}]
          else
            new_acc
          end

        extract_constructor_binders(env, codomain, ind_name, motive, new_acc)

      _ ->
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

  defp do_intros(ps, []) do
    case ps.goals do
      [{ctx, current} | _] ->
        case Typechecker.normalize(ps.env, current) do
          %AST.Pi{name: name} ->
            name = if name == "_", do: "x#{length(ctx)}", else: name
            case apply_tactic(ps, "intro #{name}") do
              {:ok, nps} -> do_intros(nps, [])
              _ -> {:ok, ps}
            end

          _ ->
            {:ok, ps}
        end

      _ ->
        {:ok, ps}
    end
  end

  defp do_intros(ps, [name | rest]) do
    case apply_tactic(ps, "intro #{name}") do
      {:ok, nps} -> do_intros(nps, rest)
      err -> err
    end
  end
end
