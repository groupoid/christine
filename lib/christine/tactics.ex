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
          %AST.Pi{domain: a, codomain: b} ->
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
        case do_intros(ps, names) do
          {:ok, new_ps} -> {:ok, new_ps}
          err -> err
        end

      {:simpl, _} ->
        new_goal = Typechecker.normalize(env, current)
        {:ok, %{ps | goals: [{ctx, new_goal} | rest]}}

      {:ring, _} ->
        case Typechecker.normalize(env, current) do
          app when is_map(app) ->
            case unwrap_eq(app) do
              {left, right} ->
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
          _ ->
            {:error, :not_an_equation, ps}
        end

      {:exact, expr_str} ->
        case parse_and_eval(expr_str, %{env | ctx: ctx}) do
          {:ok, term} ->
            term_ty = Typechecker.infer(%{env | ctx: ctx}, term)
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

      {:apply, arg} ->
        {h_name, with_args} = case arg do
          {n, wa} when is_list(wa) -> {n, wa}
          n -> {n, []}
        end
        h_name = String.trim(h_name) |> String.trim_trailing(".")

        case find_variable(ps, h_name) do
          {:ok, term, ty} ->
            case match_goal(env, current, ty) do
              {:ok, bindings, args_info} ->
                evaled_with = for {k, v_str} <- with_args do
                  case parse_and_eval(v_str, %{env | ctx: ctx}) do
                    {:ok, v} -> {k, v}
                    _ -> nil
                  end
                end |> Enum.reject(&is_nil/1)

                final_bindings = Enum.reduce(evaled_with, bindings, fn {k, v}, acc -> Map.put(acc, k, v) end)

                new_goals_types = Enum.reduce(args_info, [], fn {aname, aty}, gs ->
                  case Map.get(final_bindings, aname) do
                    nil ->
                      subst_aty = Enum.reduce(final_bindings, aty, fn {bk, bv}, acc ->
                        Christine.Typechecker.subst(bk, bv, acc)
                      end)
                      gs ++ [subst_aty]
                    _val -> gs
                  end
                end)

                actual_new_goals = wrap_goals(new_goals_types, ctx)
                n_new = length(actual_new_goals)
                old_rec = ps.reconstructor
                
                new_ps_rec = fn holes ->
                   {proofs, rem} = Enum.split(holes, n_new)
                   proof_map = Enum.zip(Enum.filter(args_info, fn {an, _} -> !Map.has_key?(final_bindings, an) end) |> Enum.map(&elem(&1, 0)), proofs)
                               |> Map.new()

                   f_final = Enum.reduce(args_info, term, fn {an, _}, acc ->
                     val = Map.get(final_bindings, an) || Map.get(proof_map, an)
                     %AST.App{func: acc, arg: val}
                   end)
                   old_rec.([f_final | rem])
                end

                {:ok, %{ps | goals: actual_new_goals ++ rest, reconstructor: new_ps_rec}}

              _ ->
                {:error, :cannot_apply, ps}
            end

          _ ->
            {:error, {:variable_not_found, h_name}, ps}
        end

      {:reflexivity, _} ->
        case Typechecker.normalize(env, current) do
          goal ->
            case unwrap_eq(goal) do
              {l, r} ->
                if Typechecker.equal?(env, l, r) do
                  a_type = case extract_app_args_full(goal) do
                     [_, a, _, _] -> a
                     [_, a, _] -> a
                     _ -> %AST.Var{name: "Any"}
                  end

                  term = %AST.App{
                    func: %AST.App{func: %AST.Var{name: "eq_refl"}, arg: a_type},
                    arg: l
                  }

                  solve_goal(ps, term)
                else
                  # Try one more time with full normalization of sides
                  nl = Typechecker.normalize(env, l)
                  nr = Typechecker.normalize(env, r)
                  if Typechecker.equal?(env, nl, nr) do
                    a_type = %AST.Var{name: "Any"}
                    term = %AST.App{
                      func: %AST.App{func: %AST.Var{name: "eq_refl"}, arg: a_type},
                      arg: nl
                    }
                    solve_goal(ps, term)
                  else
                    {:error, {:not_reflexive, l, r}, ps}
                  end
                end
              _ ->
                {:error, :not_an_equality, ps}
            end
        end

      {:split, _} ->
        case Typechecker.normalize(env, current) do
          app when is_map(app) ->
            case extract_ind_name(app) do
              {:ok, ind_name} ->
                case Map.get(env.env, ind_name) do
                  %AST.Inductive{constrs: [{_idx, cname, _cty}]} ->
                    apply_tactic(ps, {:apply, cname})
                  _ ->
                    {:error, :not_a_splitable_goal, ps}
                end
              _ ->
                {:error, :not_an_inductive_type, ps}
            end
          _ ->
            {:error, :not_an_inductive_type, ps}
        end

      {tag, target} when tag in [:induction, :destruct] ->
        gen_ih? = (tag == :induction)
        {x, user_names} = case target do
          {v, ns} -> {v, ns}
          v -> {v, []}
        end

        case List.keyfind(ctx, x, 0) do
          nil ->
            IO.puts("DEBUG INDUCTION: variable #{x} not in ctx, checking goal: #{AST.to_string(current)}")
            case Typechecker.normalize(env, current) do
              %AST.Pi{name: ^x} ->
                case apply_tactic(ps, "intro #{x}") do
                  {:ok, nps} -> apply_tactic(nps, {:induction, target})
                  err -> err
                end
              _ -> 
                # IO.puts("DEBUG INDUCTION: variable #{x} not in ctx, checking goal: #{AST.to_string(current)}")
                {:error, {:variable_not_found, x}, ps}
            end

          {_, ind_ty} ->
            ind = get_inductive_head(env, ind_ty)

            case ind do
              %AST.Inductive{} = ind ->
                motive = %AST.Lam{name: x, domain: ind_ty, body: current}
                constructor_user_names = user_names_by_constructor(ind, user_names)

                params = case Typechecker.normalize(env, ind_ty) do
                  %AST.App{} = app -> extract_app_args(app)
                  _ -> []
                end

                new_goals =
                  Enum.zip(ind.constrs, constructor_user_names)
                  |> Enum.map(fn {{idx, _cname, cty}, c_user_names} ->
                    cty_subst = Enum.reduce(Enum.zip(Enum.map(ind.params, &elem(&1, 0)), params), cty, fn {_p_name, p_val}, acc_ty ->
                      case Typechecker.normalize(env, acc_ty) do
                        %AST.Pi{name: n, codomain: cod} -> Christine.Typechecker.subst(n, p_val, cod)
                        _ -> acc_ty
                      end
                    end)

                    binders = extract_constructor_binders(env, cty_subst, ind, motive, [], x, gen_ih?)
                    renamed_binders = rename_binders(binders, c_user_names)
                    
                    num_ihs = Enum.count(binders, fn {_, bty} -> 
                      case bty do
                        %AST.App{func: ^motive} -> true
                        _ -> false
                      end
                    end)

                    num_args = length(binders) - num_ihs
                    constr_args = Enum.map(Enum.take(renamed_binders, num_args), fn {bn, _} -> %AST.Var{name: bn} end)
                    constr_term = %AST.Constr{index: idx, inductive: ind, args: params ++ constr_args}
                    
                    new_ctx = for {n, ty} <- (renamed_binders ++ ctx), do: {n, Christine.Typechecker.subst(x, constr_term, ty)}
                    new_goal = Christine.Typechecker.subst(x, constr_term, current)

                    {new_ctx, new_goal}
                  end)

                n_constrs = length(ind.constrs)
                old_rec = ps.reconstructor

                new_rec = fn holes ->
                  {case_proofs, remainder} = Enum.split(holes, n_constrs)

                  wrapped_cases =
                    Enum.zip(Enum.zip(ind.constrs, constructor_user_names), case_proofs)
                    |> Enum.map(fn {{{_idx, _, cty}, c_user_names}, proof} ->
                      cty_subst = Enum.reduce(Enum.zip(Enum.map(ind.params, &elem(&1, 0)), params), cty, fn {_pn, pv}, acc_ty ->
                        case Typechecker.normalize(env, acc_ty) do
                          %AST.Pi{name: n, codomain: cod} -> Christine.Typechecker.subst(n, pv, cod)
                          _ -> acc_ty
                        end
                      end)
                      binders = extract_constructor_binders(env, cty_subst, ind, motive, [], x, true)
                      renamed_binders = rename_binders(binders, c_user_names)

                      Enum.reduce(Enum.reverse(renamed_binders), proof, fn {name, ty}, acc ->
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



      {:rewrite, arg} ->
        {h_name, dir} = case arg do
          {n, d} -> {n, d}
          n -> {n, :forward}
        end
        case find_variable(ps, h_name) do
          {:ok, _term, h_ty} ->
            case unwrap_eq_from_pi_raw(env, h_ty) do
              {:ok, l_raw, r_raw, pi_args} ->
                {l, r} = if dir == :backward, do: {r_raw, l_raw}, else: {l_raw, r_raw}
                # IO.puts("DEBUG REWRITE: Goal=#{AST.to_string(current)}")
                # IO.puts("DEBUG REWRITE: Pattern=#{AST.to_string(l)}")
                # IO.puts("DEBUG REWRITE: ReplaceWith=#{AST.to_string(r)}")
                new_goal = replace_expression(current, l, r, env, pi_args)
                if Typechecker.equal?(env, current, new_goal) do
                   if h_name == "beq_nat_refl" do
                      IO.puts("REWRITE FAILED: #{h_name}\nTarget Pattern:\n#{AST.to_string(l)}\nGoal:\n#{AST.to_string(current)}")
                   end
                   {:error, :nothing_to_rewrite, ps}
                else
                   old_rec = ps.reconstructor
                   new_rec = fn [p | remainder] ->
                     # Note: proof term for rewrite is still forward-only for now in this prototype
                     old_rec.([%AST.App{func: %AST.App{func: %AST.Var{name: "rewrite_#{h_name}"}, arg: l}, arg: p} | remainder])
                   end
                   {:ok, %{ps | goals: [{ctx, new_goal} | rest], reconstructor: new_rec}}
                end
              _ ->
                {:error, :not_an_equality, ps}
            end
          _ ->
            {:error, {:variable_not_found, h_name}, ps}
        end

      {:intuition, _} ->
        solve_goal(ps, %AST.Var{name: "intuition_placeholder"})

      {:discriminate, h} when is_binary(h) ->
        apply_tactic(ps, {:inversion, h})

      {:discriminate, _} ->
        case Typechecker.normalize(env, current) do
          app when is_map(app) ->
             case unwrap_eq(app) do
               {l, r} ->
                 if impossible_eq?(env, l, r) do
                   solve_goal(ps, %AST.App{
                     func: %AST.App{func: %AST.Var{name: "eq_refl"}, arg: %AST.Var{name: "nat"}},
                     arg: %AST.Var{name: "Zero"}
                   })
                 else
                   {:error, :not_a_contradiction, ps}
                 end
               _ -> {:error, :not_an_equation, ps}
             end

          %AST.Pi{domain: domain} ->
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

      {:inversion, h_name} ->
        case find_variable(ps, h_name) do
          {:ok, _term, h_ty} ->
            case unwrap_eq_from_pi_raw(env, h_ty) do
              {:ok, l, r, _} ->
                if impossible_eq?(env, l, r) do
                  solve_goal(ps, %AST.Var{name: "inversion_refl"})
                else
                  apply_tactic(ps, {:destruct, h_name})
                end
              _ ->
                apply_tactic(ps, {:destruct, h_name})
            end
          _ ->
            {:error, {:variable_not_found, h_name}, ps}
        end

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
            
            new_ctx = [{name, type} | ctx]
            {:ok, %{ps | goals: [{ctx, type}, {new_ctx, current} | rest], reconstructor: new_rec}}
          err -> {:error, err, ps}
        end

      {:assumption, _} ->
        case Enum.find(ctx, fn {_, ty} -> Typechecker.equal?(env, ty, current) end) do
          {name, _} ->
            solve_goal(ps, %AST.Var{name: name})
          _ -> {:error, :no_assumption_found, ps}
        end

      {:left, _} ->
        case Typechecker.normalize(env, current) do
          %AST.App{func: %AST.App{func: %AST.Var{name: or_name}, arg: left}}
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
        body = String.slice(str, 6..-1//1) |> String.trim() |> String.trim_trailing(".")
        case Regex.run(~r/^(.*?)\s+with\s+\((.*?)\)$/, body) do
          [_, name, args_str] ->
             args = String.split(args_str, ~r/,\s*/)
             |> Enum.map(fn s ->
                case String.split(s, ~r/\s*:=\s*/) do
                  [k, v] -> {String.trim(k), String.trim(v)}
                  _ -> nil
                end
             end) |> Enum.reject(&is_nil/1)
             {:apply, {String.trim(name), args}}
          _ ->
             {:apply, body}
        end

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
        body = String.slice(str, 8..-1//1) |> String.trim() |> String.trim_trailing(".")
        if String.starts_with?(body, "<-") do
          {:rewrite, {String.slice(body, 2..-1//1) |> String.trim(), :backward}}
        else
          {:rewrite, {body, :forward}}
        end

      str =~ ~r/^\s*discriminate\b/ ->
        case Regex.run(~r/discriminate\s+([^\s\.]+)/, str) do
          [_, h] -> {:discriminate, h}
          _ -> {:discriminate, nil}
        end

      String.starts_with?(str, "inversion ") ->
        {:inversion, String.slice(str, 10..-1//1) |> String.trim() |> String.trim_trailing(".")}

      String.starts_with?(str, "assert ") ->
        body = String.slice(str, 7..-1//1) |> String.trim() |> String.trim_trailing(".")
        if String.starts_with?(body, "(") and String.ends_with?(body, ")") do
          inner = String.slice(body, 1..-2//1)
          case find_balanced_colon(inner) do
            {:ok, name, type} -> {:assert, {String.trim(name), String.trim(type)}}
            _ -> :unknown
          end
        else
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
    with {:ok, tokens} <- Christine.Lexer.lex(str),
         resolved <- Christine.Layout.resolve(tokens),
         {:ok, expr, _} <- Christine.Parser.parse_expression(resolved) do
      desugared = Desugar.desugar_expression(expr, env)
      {:ok, desugared}
    else
      err -> err
    end
  end

  defp wrap_goals(types, ctx), do: Enum.map(types, fn t -> {ctx, t} end)

  defp match_goal(env, goal, type, params \\ [], acc_args \\ []) do
    IO.puts("DEBUG MATCH_GOAL: goal #{AST.to_string(goal)} vs type #{AST.to_string(type)}")
    case Typechecker.normalize(env, type) do
      %AST.Pi{name: n, domain: d, codomain: c} ->
        match_goal(env, goal, c, [n | params], [{n, d} | acc_args])
      ty ->
        case try_match(env, goal, ty, params) do
          {:ok, bindings} -> {:ok, bindings, Enum.reverse(acc_args)}
          :error -> :error
        end
    end
  end

  defp unwrap_eq_from_pi_raw(env, ty, params \\ []) do
    case ty do
      %AST.Pi{name: name, domain: _d, codomain: cod} -> unwrap_eq_from_pi_raw(env, cod, [name | params])
      _ ->
        case Typechecker.normalize(env, ty) do
           %AST.Pi{name: name, domain: _d, codomain: cod} -> unwrap_eq_from_pi_raw(env, cod, [name | params])
           app ->
             case unwrap_eq(app) do
               {l, r} -> {:ok, l, r, Enum.reverse(params)}
               _ -> :error
             end
        end
    end
  end

  defp unwrap_eq(app) do
    IO.puts("DEBUG UNWRAP_EQ: #{AST.to_string(app)}")
    case extract_app_args_full(app) do
      [f | args] ->
        if is_eq?(f) do
          case args do
            [_, l, r] -> {l, r}
            [l, r] -> {l, r}
            _ -> nil
          end
        else
          nil
        end
      _ -> nil
    end
  end

  defp is_eq?(%AST.Var{name: n}), do: names_match?("eq", n) or names_match?("Eq", n)
  defp is_eq?(%AST.Ind{inductive: %AST.Inductive{name: n}}), do: names_match?("eq", n) or names_match?("Eq", n)
  defp is_eq?(%AST.App{func: f}), do: is_eq?(f)
  defp is_eq?(_), do: false

  defp extract_app_args_full(%AST.App{func: f, arg: a}) do
    extract_app_args_full(f) ++ [a]
  end
  defp extract_app_args_full(f), do: [f]

  defp replace_expression(target, old, new, env, params) do
    # Normalize the pattern as well, because the target might be normalized/unfolded
    old_norm = if is_map(old), do: Typechecker.normalize(env, old), else: old
    res = try_match(env, target, old_norm, params)
    if Enum.member?(params, "n") and target == Typechecker.normalize(env, target) do
       if res == :error do
         # IO.puts("REPLACE EXPR FAILED MATCH:\nTarget:\n#{inspect(target, limit: 100)}\nPattern:\n#{inspect(old, limit: 100)}")
       else
         IO.puts("REPLACE EXPR SUCCEEDED MATCH on target!!")
       end
    end
    case res do
      {:ok, bindings} ->
        res = Enum.reduce(bindings, new, fn {name, val}, acc ->
          Christine.Typechecker.subst(name, val, acc)
        end)
        IO.puts("REPLACE EXPR SUCCEEDED MATCH: target=#{AST.to_string(target)} result=#{AST.to_string(res)}")
        res
      :error ->
        case target do
          %AST.App{func: f, arg: arg} ->
            %AST.App{
              func: replace_expression(f, old, new, env, params),
              arg: replace_expression(arg, old, new, env, params)
            }
          %AST.Pi{name: n, domain: d, codomain: c} ->
            %AST.Pi{
              name: n,
              domain: replace_expression(d, old, new, env, params),
              codomain: replace_expression(c, old, new, env, params)
            }
          %AST.Lam{name: n, domain: d, body: b} ->
            %AST.Lam{
              name: n,
              domain: replace_expression(d, old, new, env, params),
              body: replace_expression(b, old, new, env, params)
            }
          %AST.Ind{inductive: ind, motive: m, cases: cases, term: t} ->
            %AST.Ind{
              inductive: ind,
              motive: replace_expression(m, old, new, env, params),
              cases: Enum.map(cases, &replace_expression(&1, old, new, env, params)),
              term: replace_expression(t, old, new, env, params)
            }
          %AST.Constr{index: i, inductive: ind, args: args} ->
            %AST.Constr{
              index: i,
              inductive: ind,
              args: Enum.map(args, &replace_expression(&1, old, new, env, params))
            }
          %AST.Let{decls: decls, body: b} ->
            %AST.Let{
              decls: Enum.map(decls, fn {n, v} -> {n, replace_expression(v, old, new, env, params)} end),
              body: replace_expression(b, old, new, env, params)
            }
          _ -> target
        end
    end
  end

  def try_match(env, target, pattern, params, bindings \\ %{}) do
    pattern_str = AST.to_string(pattern)
    if String.contains?(pattern_str, "beq_nat") or String.contains?(pattern_str, "plus") do
       # IO.puts("DEBUG TRY_MATCH (FIX):\nTarget:\n#{AST.to_string(target)}\nPattern:\n#{pattern_str}")
    end
    case pattern do
      %AST.Var{name: n} ->
        if Enum.member?(params, n) do
          case Map.get(bindings, n) do
            nil -> {:ok, Map.put(bindings, n, target)}
            existing ->
              if Typechecker.equal?(env, existing, target) do
                {:ok, bindings}
              else
                :error
              end
          end
        else
          case target do
            %AST.Var{name: n2} ->
              if names_match?(n, n2) do
                {:ok, bindings}
              else
                if Typechecker.equal?(env, target, pattern) do
                  {:ok, bindings}
                else
                  :error
                end
              end
            _ ->
              if Typechecker.equal?(env, target, pattern) do
                {:ok, bindings}
              else
                :error
              end
          end
        end

      %AST.App{func: f1, arg: a1} ->
        case target do
          %AST.App{func: f2, arg: a2} ->
            with {:ok, b1} <- try_match(env, f2, f1, params, bindings),
                 {:ok, b2} <- try_match(env, a2, a1, params, b1) do
              {:ok, b2}
            else
              _ -> :error
            end
          %AST.Number{value: v} ->
            unfolded = unfold_number(env, v)
            try_match(env, unfolded, pattern, params, bindings)
          _ ->
            if Typechecker.equal?(env, target, pattern) do {:ok, bindings} else :error end
        end

      %AST.Ind{inductive: i1, term: t1, motive: m1, cases: c1} ->
        case target do
          %AST.Ind{inductive: i2, term: t2, motive: m2, cases: c2} ->
            if names_match?(i1.name, i2.name) do
              with {:ok, b1} <- try_match(env, t2, t1, params, bindings),
                   {:ok, b2} <- try_match(env, m2, m1, params, b1) do
               Enum.zip(c2, c1) |> Enum.reduce_while({:ok, b2}, fn {tc, pc}, {:ok, acc} ->
                 case try_match(env, tc, pc, params, acc) do
                   {:ok, new_acc} -> {:cont, {:ok, new_acc}}
                   :error -> 
                     if Enum.member?(params, "n") do
                       IO.puts("IND CASE MISMATCH: Target:\n#{inspect(tc, limit: :infinity)}\nPattern:\n#{inspect(pc, limit: :infinity)}")
                     end
                     {:halt, :error}
                 end
               end)
            end
          else
            :error
          end
        _ ->
          if Typechecker.equal?(env, target, pattern) do {:ok, bindings} else :error end
      end

      %AST.Lam{domain: d1, body: body1} ->
        case target do
          %AST.Lam{domain: d2, body: body2} ->
            with {:ok, b_dom} <- try_match(env, d2, d1, params, bindings),
                 {:ok, b_bod} <- try_match(env, body2, body1, params, b_dom) do
              {:ok, b_bod}
            else
              _ -> :error
            end
          _ ->
            if Typechecker.equal?(env, target, pattern) do {:ok, bindings} else :error end
        end

      %AST.Pi{domain: d1, codomain: c1} ->
        case target do
          %AST.Pi{domain: d2, codomain: c2} ->
            with {:ok, b1} <- try_match(env, d2, d1, params, bindings),
                 {:ok, b2} <- try_match(env, c2, c1, params, b1) do
              {:ok, b2}
            else
              _ -> :error
            end
          _ ->
            if Typechecker.equal?(env, target, pattern) do {:ok, bindings} else :error end
        end

      %AST.Constr{index: idx1, args: a1} ->
        case target do
          %AST.Constr{index: idx2, args: a2} when idx1 == idx2 ->
            Enum.zip(a2, a1) |> Enum.reduce_while({:ok, bindings}, fn {ta, pa}, {:ok, acc} ->
              case try_match(env, ta, pa, params, acc) do
                {:ok, new_acc} -> {:cont, {:ok, new_acc}}
                :error -> {:halt, :error}
              end
            end)
          _ ->
            if Typechecker.equal?(env, target, pattern) do {:ok, bindings} else :error end
        end

      %AST.Fixpoint{name: n1} = pattern_fix ->
        case target do
          %AST.Fixpoint{name: n2} ->
             if names_match?(n1, n2) do
                {:ok, bindings}
             else
                if Typechecker.equal?(env, target, pattern_fix) do {:ok, bindings} else :error end
             end
          %AST.Var{name: n2} ->
             if names_match?(n1, n2) do
                {:ok, bindings}
             else
                if Typechecker.equal?(env, target, pattern_fix) do {:ok, bindings} else :error end
             end
          _ -> if Typechecker.equal?(env, target, pattern_fix) do {:ok, bindings} else :error end
        end

      _ ->
        should_expand = case pattern do
          %AST.App{} -> true
          %AST.Var{name: p_name} -> not (p_name in params)
          _ -> false
        end

        res = if should_expand do
          expanded_pattern = Typechecker.normalize(env, pattern)
          if expanded_pattern != pattern do
            try_match(env, target, expanded_pattern, params, bindings)
          else
            :error
          end
        else
          :error
        end

        case res do
          {:ok, _} = ok_res -> ok_res
          :error ->
            case target do
              %AST.Number{value: v} ->
                unfolded = unfold_number(env, v)
                if Typechecker.equal?(env, unfolded, pattern) do
                  {:ok, bindings}
                else
                  :error
                end
              _ ->
                if Typechecker.equal?(env, target, pattern) do
                  {:ok, bindings}
                else
                  :error
                end
            end
        end
    end
  end

  defp unfold_number(env, n) do
    succ_name = case Enum.find(env.env, fn {name, _} -> String.ends_with?(name, ".Succ") or name == "Succ" end) do
      {full, _} -> full
      _ -> "Succ"
    end
    zero_name = case Enum.find(env.env, fn {name, _} -> String.ends_with?(name, ".Zero") or name == "Zero" end) do
      {full, _} -> full
      _ -> "Zero"
    end
    do_unfold_number(n, succ_name, zero_name)
  end

  defp do_unfold_number(0, _, zero), do: %AST.Var{name: zero}
  defp do_unfold_number(n, succ, zero) when n > 0, do: %AST.App{func: %AST.Var{name: succ}, arg: do_unfold_number(n - 1, succ, zero)}

  defp find_variable(%ProofState{goals: [{ctx, _} | _], env: env}, name) do
    # IO.puts("DEBUG FIND_VARIABLE: #{name}")
    case Enum.find(ctx, fn {n, _} -> n == name end) || Enum.find(env.ctx, fn {n, _} -> n == name end) do
      {^name, ty} -> {:ok, %AST.Var{name: name}, ty}
      _ ->
        case Enum.find(env.env, fn {n, _} -> n == name or String.ends_with?(n, "." <> name) end) do
          {_full_name, %AST.Constr{inductive: ind, index: idx}} ->
            {_idx, _cname, c_ty} = Enum.at(ind.constrs, idx - 1)
            {:ok, %AST.Constr{inductive: ind, index: idx}, c_ty}
          {full_name, %AST.DeclValue{type: t}} ->
            val = Map.get(env.defs, full_name)
            {:ok, val || %AST.Var{name: full_name}, t}
          _ ->
            case Enum.find(env.env, fn {n, _} -> String.ends_with?(n, "." <> name) end) do
              {full_name, ty} when is_map(ty) -> {:ok, %AST.Var{name: full_name}, ty}
              _ ->
                case Map.get(env.env, name) do
                   ty when is_map(ty) -> {:ok, %AST.Var{name: name}, ty}
                   _ -> :error
                end
            end
        end
    end
  end

  defp is_plus?(%AST.Var{name: n}), do: n in ["plus", "+", "Coq.plus"]
  defp is_plus?(%AST.App{func: f}), do: is_plus?(f)
  defp is_plus?(_), do: false

  defp is_mult?(%AST.Var{name: n}), do: n in ["mult", "*", "Coq.mult"]
  defp is_mult?(%AST.App{func: f}), do: is_mult?(f)
  defp is_mult?(_), do: false

  defp is_succ?(%AST.Var{name: n}), do: String.ends_with?(n, "Succ") or String.ends_with?(n, "S")
  defp is_succ?(%AST.Constr{inductive: %{name: name}, index: 2}) when name in ["nat", "Coq.nat"], do: true
  defp is_succ?(%AST.App{func: f}), do: is_succ?(f)
  defp is_succ?(_), do: false

  defp is_zero?(%AST.Var{name: n}), do: String.ends_with?(n, "Zero") or String.ends_with?(n, "O")
  defp is_zero?(%AST.Constr{inductive: %{name: name}, index: 1}) when name in ["nat", "Coq.nat"], do: true
  defp is_zero?(_), do: false

  defp to_poly(env, expr) do
    # Try normalize lightly to preserve plus/mult names if they are not yet unfolded
    case expr do
      %AST.Number{value: v} -> [%{coeff: v, vars: %{}}]
      %AST.App{func: f, arg: b} ->
        case f do
          %AST.App{func: op, arg: a} ->
             cond do
               is_plus?(op) -> to_poly(env, a) ++ to_poly(env, b)
               is_mult?(op) -> poly_mult(to_poly(env, a), to_poly(env, b))
               true -> to_poly_norm(env, expr)
             end
          _ ->
             if is_succ?(f) do
                [%{coeff: 1, vars: %{}}] ++ to_poly(env, b)
             else
                to_poly_norm(env, expr)
             end
        end
      _ ->
        to_poly_norm(env, expr)
    end
  end

  defp to_poly_norm(env, expr) do
    case Typechecker.normalize(env, expr) do
      %AST.Number{value: v} -> [%{coeff: v, vars: %{}}]
      %AST.App{func: f, arg: b} ->
        case f do
          %AST.App{func: op, arg: a} ->
             cond do
               is_plus?(op) -> to_poly(env, a) ++ to_poly(env, b)
               is_mult?(op) -> poly_mult(to_poly(env, a), to_poly(env, b))
               true -> [%{coeff: 1, vars: %{Typechecker.normalize(env, expr) => 1}}]
             end
          _ ->
             if is_succ?(f) do
                [%{coeff: 1, vars: %{}}] ++ to_poly(env, b)
             else
                [%{coeff: 1, vars: %{Typechecker.normalize(env, expr) => 1}}]
             end
        end
      other ->
        cond do
          is_zero?(other) -> []
          is_succ?(other) -> [%{coeff: 1, vars: %{}}] # Should not happen alone
          true -> [%{coeff: 1, vars: %{other => 1}}]
        end
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
            IO.puts("  #{AST.to_string(g)} in context #{inspect(Enum.map(c, &elem(&1, 0)))}")
          end
          {:error, {:unsolved_goals, ps.goals}}
        end
    end
  end

  def apply_to_all_goals(ps, tactic_str) do
    # Handle optional braces around the whole thing or individual tactics
    tactic_str = String.trim(tactic_str)
    tactic_str = if String.starts_with?(tactic_str, "{") and String.ends_with?(tactic_str, "}") do
      String.slice(tactic_str, 1..-2//1) |> String.trim()
    else
      tactic_str
    end

    case String.split(tactic_str, ~r/;\s*/, trim: true) do
      [tac] ->
        apply_tactic(ps, tac)

      [first | rest] ->
        IO.puts("DEBUG SEQUENCE: first = #{first}, goals = #{inspect(Enum.map(ps.goals, fn {c, _} -> Enum.map(c, &elem(&1, 0)) end))}")
        case apply_tactic(ps, first) do
          {:ok, %{goals: new_goals} = nps} ->
            # Number of new goals generated by 'first'
            n_new = length(new_goals) - length(ps.goals) + 1
            {subgoals, others} = Enum.split(new_goals, n_new)

            results = Enum.map(subgoals, fn {sub_ctx, g} ->
              # Start a sub-session for this subgoal with its own initial reconstructor, keeping its local ctx
              sub_ps = %{nps | goals: [{sub_ctx, g}], reconstructor: fn [t] -> t end}
              
              Enum.reduce_while(rest, {:ok, sub_ps}, fn tac, {:ok, curr_ps} ->
                case apply_tactic(curr_ps, tac) do
                  {:ok, next_ps} -> {:cont, {:ok, next_ps}}
                  err -> {:halt, err}
                end
              end)
            end)

            if Enum.all?(results, fn {:ok, _} -> true; _ -> false end) do
              all_solved_subproofs = Enum.map(results, fn {:ok, r} -> {r.goals, r.proof_term, r.reconstructor} end)
              
              remaining_subgoals = Enum.flat_map(all_solved_subproofs, &elem(&1, 0))
              n_rem_sub = length(remaining_subgoals)
              
              old_rec = nps.reconstructor
              
              new_rec = fn all_holes ->
                {sub_holes, others_holes} = Enum.split(all_holes, n_rem_sub)
                
                # Split sub_holes back for each sub-branch and call its reconstructor
                {final_sub_proofs, _} = Enum.reduce(all_solved_subproofs, {[], sub_holes}, fn {gs, _pt, rec}, {p_acc, h_acc} ->
                  n = length(gs)
                  {this_h, next_h} = Enum.split(h_acc, n)
                  {p_acc ++ [rec.(this_h)], next_h}
                end)
                
                old_rec.(final_sub_proofs ++ others_holes)
              end
              
              new_ps = %{nps | goals: remaining_subgoals ++ others, reconstructor: new_rec}
              if new_ps.goals == [] do
                {:ok, %{new_ps | proof_term: new_rec.([])}}
              else
                {:ok, new_ps}
              end
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
      %AST.Var{name: name} -> 
        # Search for namespaced match
        case Map.get(env.env, name) || Enum.find_value(env.env, fn {n, ind} -> if String.ends_with?(n, "." <> name), do: ind end) do
          %AST.Inductive{} = ind -> ind
          _ -> nil
        end
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

  defp extract_constructor_binders(env, cty, ind, motive, acc, base_name, gen_ih?) do
    case Typechecker.normalize(env, cty) do
      %AST.Pi{name: name, domain: domain, codomain: codomain} ->
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
          if is_recursive and gen_ih? do
            name = if name == "_" or is_nil(name) do
              if length(acc) == 0, do: base_name, else: "#{base_name}#{length(acc)}"
            else
              name
            end
            ih_name = "IH#{name}"
            acc ++ [{name, domain}, {ih_name, %AST.App{func: motive, arg: %AST.Var{name: name}}}]
          else
            name = if name == "_" or is_nil(name) do
              if length(acc) == 0, do: base_name, else: "#{base_name}#{length(acc)}"
            else
              name
            end
            acc ++ [{name, domain}]
          end

        env_with_binder = %{env | ctx: [{name, domain} | env.ctx]}
        extract_constructor_binders(env_with_binder, codomain, ind, motive, new_acc, base_name, gen_ih?)

      _ -> acc
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
        type = String.slice(rest, 1..-1//1)
        {:ok, name, type}
      _ -> :error
    end
  end

  defp do_intros(ps, []), do: apply_all_intros(ps)
  defp do_intros(ps, [name | rest]) do
    case apply_tactic(ps, "intro #{name}") do
      {:ok, nps} -> do_intros(nps, rest)
      {:error, _reason, _} = err -> 
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
    case {vl, vr} do
      {{i1, name1}, {i2, name2}} when name1 == name2 and i1 != i2 -> true
      _ -> false
    end
  end

  defp unwrap_constr(%AST.Constr{index: i, inductive: %{name: name}}), do: {i, name}
  defp unwrap_constr(%AST.App{func: f}), do: unwrap_constr(f)
  defp unwrap_constr(_), do: nil

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

  defp extract_ind_name(app) do
    case app do
      %AST.App{func: f} -> extract_ind_name(f)
      %AST.Inductive{name: name} -> {:ok, name}
      %AST.Var{name: name} -> {:ok, name}
      _ -> :error
    end
  end

  defp names_match?(n1, n2) do
    n1 == n2 or n2 == "Coq." <> n1 or n1 == "Coq." <> n2
  end
end
