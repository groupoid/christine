defmodule Christine.Codegen do
  @moduledoc """
  Translates Christine.AST into Erlang Abstract Format.
  """
  alias Christine.AST

  def generate(
        %AST.Module{name: mod_name, declarations: decls},
        env \\ %Christine.Typechecker.Env{}
      ) do
    current_mod = String.to_atom(mod_name)
    functions = Enum.flat_map(decls, &generate_decl(&1, env, current_mod))

    module_attr = {:attribute, 1, :module, current_mod}
    export_all = {:attribute, 1, :compile, :export_all}

    forms = [module_attr, export_all] ++ functions ++ [{:eof, 1}]
    {:ok, forms}
  end

  defp generate_decl(%AST.Inductive{constrs: constrs}, _env, _mod) do
    Enum.map(constrs, fn {idx, name, ty} ->
      body = generate_constr_body(idx, ty, [])
      clause = {:clause, 1, [], [], [body]}
      {:function, 1, String.to_atom(name), 0, [clause]}
    end)
  end

  defp generate_decl(%AST.DeclValue{name: name, expr: expr}, env, mod) do
    if expr do
      clause = {:clause, 1, [], [], [generate_expr(expr, %{}, 0, env, mod) |> elem(0)]}
      [{:function, 1, String.to_atom(name), 0, [clause]}]
    else
      []
    end
  end

  defp generate_decl(
         %AST.DeclForeign{name: name, erl_mod: mod, erl_func: func, type: _ty},
         _env,
         _mod
       ) do
    args = [{:var, 1, :X1}]

    call =
      {:call, 1, {:remote, 1, {:atom, 1, String.to_atom(mod)}, {:atom, 1, String.to_atom(func)}},
       args}

    [{:function, 1, String.to_atom(name), 1, [{:clause, 1, args, [], [call]}]}]
  end

  defp generate_decl(_, _, _), do: []

  defp generate_constr_body(idx, %AST.Pi{codomain: next}, vars) do
    v_name = {:var, 1, String.to_atom("C#{length(vars) + 1}")}

    {:fun, 1,
     {:clauses, [{:clause, 1, [v_name], [], [generate_constr_body(idx, next, [v_name | vars])]}]}}
  end

  defp generate_constr_body(idx, _, vars) do
    {:tuple, 1, [{:integer, 1, idx} | Enum.reverse(vars)]}
  end

  # Returns {erl_expr, next_counter}
  defp generate_expr(%AST.Var{name: name}, local_env, counter, env, current_mod) do
    expr =
      if Map.has_key?(local_env, name) do
        {:var, 1, Map.get(local_env, name)}
      else
        case Map.get(env.name_to_mod, name) do
          nil ->
            {:atom, 1, String.to_atom(name)}

          mod_str ->
            mod = String.to_atom(mod_str)

            if mod == current_mod do
              if Map.has_key?(env.defs, name) do
                {:call, 1, {:atom, 1, String.to_atom(name)}, []}
              else
                {:atom, 1, String.to_atom(name)}
              end
            else
              if Map.has_key?(env.defs, name) do
                {:call, 1, {:remote, 1, {:atom, 1, mod}, {:atom, 1, String.to_atom(name)}}, []}
              else
                {:atom, 1, String.to_atom(name)}
              end
            end
        end
      end

    {expr, counter}
  end

  defp generate_expr(%AST.Universe{level: i}, _local_env, counter, _env, _mod) do
    {{:integer, 1, i}, counter}
  end

  defp generate_expr(%AST.Pi{}, _local_env, counter, _env, _mod), do: {{:atom, 1, :pi}, counter}

  defp generate_expr(%AST.Lam{name: x, body: body}, local_env, counter, env, mod) do
    # Use unique variable name derived from counter to avoid Erlang name collisions
    erl_name = String.to_atom("V#{counter}")
    erl_x = {:var, 1, erl_name}
    new_local_env = Map.put(local_env, x, erl_name)
    {body_expr, counter2} = generate_expr(body, new_local_env, counter + 1, env, mod)

    expr =
      {:fun, 1, {:clauses, [{:clause, 1, [erl_x], [], [body_expr]}]}}

    {expr, counter2}
  end

  defp generate_expr(%AST.App{func: f, arg: arg}, local_env, counter, env, mod) do
    {f_expr, counter1} = generate_expr(f, local_env, counter, env, mod)
    {arg_expr, counter2} = generate_expr(arg, local_env, counter1, env, mod)

    expr =
      case f_expr do
        {:atom, _, _} = a ->
          {:tuple, 1, [a, arg_expr]}

        {:tuple, _, elements} = t ->
          if Enum.at(elements, 0) |> elem(0) == :atom do
            {:tuple, 1, elements ++ [arg_expr]}
          else
            {:call, 1, t, [arg_expr]}
          end

        other ->
          {:call, 1, other, [arg_expr]}
      end

    {expr, counter2}
  end

  defp generate_expr(%AST.Constr{index: j, args: args}, local_env, counter, env, mod) do
    {arg_exprs, counter2} =
      Enum.reduce(args, {[], counter}, fn arg, {acc, c} ->
        {e, c2} = generate_expr(arg, local_env, c, env, mod)
        {acc ++ [e], c2}
      end)

    {{:tuple, 1, [{:integer, 1, j} | arg_exprs]}, counter2}
  end

  defp generate_expr(%AST.Let{decls: decls, body: body}, local_env, counter, env, mod) do
    {new_local_env, matches, counter2} =
      Enum.reduce(decls, {local_env, [], counter}, fn {name, expr}, {lenv, acc, c} ->
        erl_name = String.to_atom("V#{c}")
        erl_var = {:var, 1, erl_name}
        {expr_erl, c2} = generate_expr(expr, lenv, c + 1, env, mod)
        new_lenv = Map.put(lenv, name, erl_name)
        {new_lenv, acc ++ [{:match, 1, erl_var, expr_erl}], c2}
      end)

    {body_expr, counter3} = generate_expr(body, new_local_env, counter2, env, mod)
    {{:block, 1, matches ++ [body_expr]}, counter3}
  end

  defp generate_expr(%AST.Ind{inductive: ind, cases: cases, term: t}, local_env, counter, env, mod) do
    ind_func_name = String.to_atom("F_ind#{counter}")
    ind_var = {:var, 1, ind_func_name}

    {t_expr, counter1} = generate_expr(t, local_env, counter + 1, env, mod)

    if ind.constrs == [] do
      # Empty inductive - just crash
      {{:call, 1, {:atom, 1, :error}, [{:atom, 1, :empty_induction}]}, counter1}
    else
      {clauses, counter2} =
        Enum.zip(ind.constrs, cases)
        |> Enum.reduce({[], counter1}, fn {{idx, _cname, c_ty}, case_expr}, {clause_acc, c} ->
          arg_types = get_arg_types(c_ty)
          n_args = length(arg_types)

          arg_var_names =
            if n_args > 0,
              do: Enum.map(0..(n_args - 1), fn i -> String.to_atom("A#{c + i}") end),
              else: []

          arg_vars = Enum.map(arg_var_names, fn vn -> {:var, 1, vn} end)
          next_c = c + n_args

          new_local_env =
            Enum.reduce(arg_var_names, local_env, fn vn, acc ->
              Map.put(acc, Atom.to_string(vn), vn)
            end)

          pattern = {:tuple, 1, [{:integer, 1, idx} | arg_vars]}

          case_args =
            Enum.zip(arg_vars, arg_types)
            |> Enum.flat_map(fn {a_v, a_ty} ->
              is_rec = is_recursive_type(a_ty, ind.name)
              ih_v = if is_rec, do: {:call, 1, ind_var, [a_v]}, else: {:atom, 1, :unused_ih}
              [a_v, ih_v]
            end)

          {case_erl, next_c2} = generate_expr(case_expr, new_local_env, next_c, env, mod)
          case_body = apply_lam(case_erl, case_args)
          new_clause = {:clause, 1, [pattern], [], [case_body]}
          {clause_acc ++ [new_clause], next_c2}
        end)

      named_fun = {:named_fun, 1, ind_func_name, clauses}
      {{:call, 1, named_fun, [t_expr]}, counter2}
    end
  end

  defp generate_expr(_, _local_env, counter, _env, _mod) do
    {{:atom, 1, :unsupported}, counter}
  end

  defp get_arg_types(%AST.Pi{domain: d, codomain: c}), do: [d | get_arg_types(c)]
  defp get_arg_types(_), do: []

  defp is_recursive_type(%AST.Var{name: name}, ind_name), do: name == ind_name
  defp is_recursive_type(%AST.App{func: f}, ind_name), do: is_recursive_type(f, ind_name)
  defp is_recursive_type(%AST.Pi{codomain: c}, ind_name), do: is_recursive_type(c, ind_name)
  defp is_recursive_type(_, _), do: false

  defp apply_lam(lam, []), do: lam

  defp apply_lam(lam, [arg | rest]) do
    apply_lam({:call, 1, lam, [arg]}, rest)
  end
end
