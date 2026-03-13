defmodule Christine.Typechecker do
  alias Christine.AST

  @doc """
  Typing environment contains:
  - env: map of (name -> inductive)
  - ctx: list of (name, type)
  - defs: map of (name -> term)
  - deadline: monotonic time limit in ms
  """
  defmodule Env do
    defstruct env: %{}, ctx: [], defs: %{}, name_to_mod: %{}, deadline: nil, last_decl: nil
  end

  def check_module(%AST.Module{declarations: decls}, %Env{} = env) do
    Enum.reduce_while(decls, :ok, fn
      %AST.Inductive{} = ind, _acc ->
        infer(env, ind)
        {:cont, :ok}
      %AST.DeclValue{name: name, expr: expr}, _acc ->
        case infer(env, expr) do
          {:error, reason} = err ->
            IO.puts("Type error in #{name}: #{inspect(reason)}")
            {:halt, err}
          _ty ->
            {:cont, :ok}
        end
      _, acc ->
        {:cont, acc}
    end)
  end

  def infer(_e, nil), do: %AST.Universe{level: 0}
  def infer(%Env{} = e, %AST.Var{name: name}) do
    if name == "Any" or name == "U-1" do
      %AST.Var{name: "Any"}
    else
      case List.keyfind(e.ctx, name, 0) do
        {^name, ty} -> ty
        nil ->
          if Map.has_key?(e.defs, name) do
            %AST.Var{name: "Any"}
          else
            case Map.get(e.env, name) do
              %AST.Inductive{} = ind -> infer(e, ind)
              _ -> {:error, {:unbound_variable, name}}
            end
          end
      end
    end
  end
  def infer(%Env{}, %AST.Universe{level: i}), do: %AST.Universe{level: i + 1}
  def infer(%Env{}, %AST.Inductive{level: level}), do: %AST.Universe{level: level + 1}
  def infer(%Env{} = e, %AST.Constr{index: j, inductive: d, args: args}) do
    case Enum.find(d.constrs, fn {idx, _, _} -> idx == j end) do
      {^j, _name, ty} ->
         ty_subst = subst_many(d.params, ty)
         infer_ctor(e, ty_subst, args)
      _ -> {:error, {:constructor_not_found, j, d.name}}
    end
  end
  def infer(%Env{} = e, %AST.Ind{inductive: _d, motive: p, cases: _cases, term: t}) do
    case infer(e, p) do
      %AST.Pi{name: x, domain: _a, codomain: b} -> subst(x, t, b)
      other -> {:error, {:motive_not_pi, other}}
    end
  end
  def infer(%Env{} = e, %AST.Pi{name: x, domain: a, codomain: b}) do
    u_a = universe_level(e, a)
    u_b = universe_level(%{e | ctx: [{x, a} | e.ctx]}, b)
    %AST.Universe{level: Kernel.max(u_a, u_b)}
  end
  def infer(%Env{} = e, %AST.Lam{name: x, domain: domain, body: body}) do
    %AST.Pi{name: x, domain: domain, codomain: infer(%{e | ctx: [{x, domain} | e.ctx]}, body)}
  end
  def infer(%Env{} = e, %AST.Fixpoint{domain: ty, body: body}) do
    check(e, body, ty)
    ty
  end
  def infer(%Env{} = e, %AST.App{func: f, arg: arg}) do
    case infer(e, f) do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        check(e, arg, a)
        subst(x, arg, b)
      %AST.Var{name: "Any"} -> %AST.Var{name: "Any"}
      %AST.Universe{} -> %AST.Universe{level: 0}
      other -> {:error, {:application_requires_pi, other}}
    end
  end
  def infer(%Env{} = e, %AST.Let{decls: decls, body: body}) do
    new_env = Enum.reduce(decls, e, fn {name, expr}, acc ->
      ty = infer(acc, expr)
      %{acc | ctx: [{name, ty} | acc.ctx], defs: Map.put(acc.defs, name, expr)}
    end)
    infer(new_env, body)
  end
  def infer(%Env{}, %AST.Number{}), do: %AST.Var{name: "Number"}
  def infer(%Env{}, %AST.String{}), do: %AST.Var{name: "String"}

  def check(%Env{} = _e, _t, %AST.Var{name: "Any"}), do: :ok
  def check(%Env{} = e, t, ty) do
    inferred = infer(e, t)
    if inferred == %AST.Var{name: "Any"} or equal?(e, inferred, ty) do
      :ok
    else
      {:error, {:type_mismatch, inferred, ty}}
    end
  end

  def universe_level(_e, %AST.Var{name: "Any"}), do: 0
  def universe_level(e, t) do
    case normalize(e, t) do
      %AST.Universe{level: i} -> i
      _ -> 0
    end
  end

  def equal?(e, t1, t2) do
    n1 = normalize(e, t1)
    n2 = normalize(e, t2)
    res = structural_equal?(e, n1, n2)
    if !res do
       # Christine.Debug.log("DEBUG EQUAL? FAIL:\n  l: #{AST.to_string(n1)} (inspect: #{inspect(n1)})\n  r: #{AST.to_string(n2)} (inspect: #{inspect(n2)})")
    end
    res
  end

  defp structural_equal?(_e, t1, t2) do
    t1 == t2
  end
 
  def normalize(e, t) do
    # Prevent infinite recursion by checking a deadline/depth if needed, 
    # but here we rely on structural properties and the fixpoint body guard.
    deadline = e.deadline || System.monotonic_time(:millisecond) + 60_000
    e = %{e | deadline: deadline}
    
    red = reduce(e, t)
    
    case red do
      %AST.App{func: f, arg: arg} -> 
        n_f = normalize(e, f)
        n_arg = normalize(e, arg)
        # If normalizing func turned it into a Lambda, we might need more reduction
        case n_f do
          %AST.Lam{name: x, body: b} -> normalize(e, subst(x, n_arg, b))
          _ -> %AST.App{func: n_f, arg: n_arg}
        end

      %AST.Lam{name: x, domain: a, body: b} -> 
        %AST.Lam{name: x, domain: normalize(e, a), body: normalize(e, b)}

      %AST.Pi{name: x, domain: a, codomain: b} ->
        %AST.Pi{name: x, domain: normalize(e, a), codomain: normalize(e, b)}

      %AST.Ind{inductive: d, motive: p, cases: cases, term: t_val} ->
        %AST.Ind{inductive: d, 
                 motive: normalize(e, p), 
                 cases: Enum.map(cases, &normalize(e, &1)), 
                 term: normalize(e, t_val)}

      %AST.Fixpoint{name: n, domain: d, body: b, args: args} ->
        # IMPORTANT: Do NOT normalize the body 'b' to avoid infinite loops with circular subst
        %AST.Fixpoint{name: n, 
                      domain: normalize(e, d), 
                      body: b, 
                      args: Enum.map(args, &normalize(e, &1))}

      %AST.Constr{index: i, inductive: ind, args: args} ->
        %AST.Constr{index: i, inductive: ind, args: Enum.map(args, &normalize(e, &1))}

      %AST.Let{decls: decls, body: b} ->
        # Let should have been reduced away by 'reduce', but just in case
        new_defs = Enum.reduce(decls, e.defs, fn {n, expr}, acc -> Map.put(acc, n, expr) end)
        normalize(%{e | defs: new_defs}, b)

      _ -> red
    end
  end

  def reduce(e, t, fuel \\ 500_000)
  def reduce(_e, t, 0), do: t
  def reduce(e, t, fuel) do
    if e.deadline && System.monotonic_time(:millisecond) > e.deadline, do: raise "Timeout"
    do_reduce(e, t, fuel)
  end

  defp do_reduce(e, %AST.App{func: f, arg: arg}, fuel) do
    f_red = reduce(e, f, fuel - 1)
    case f_red do
      %AST.Lam{name: x, body: body} -> reduce(e, subst(x, arg, body), fuel - 1)
      %AST.Fixpoint{args: applied_args} = fix ->
        red_arg = reduce(e, arg, fuel - 1)
        all_args = applied_args ++ [red_arg]
        case try_unfold_fixpoint(e, fix, all_args, fuel - 1) do
          {:ok, unfolded} -> reduce(e, unfolded, fuel - 1)
          :blocked -> %{fix | args: all_args}
        end
      %AST.Constr{index: i, inductive: d, args: args} ->
        %AST.Constr{index: i, inductive: d, args: args ++ [reduce(e, arg, fuel - 1)]}
      _ -> %AST.App{func: f_red, arg: arg}
    end
  end
  defp do_reduce(e, %AST.Ind{inductive: ind_def, cases: cases, term: term} = ind, fuel) do
    target = reduce(e, term, fuel - 1)
    case target do
      %AST.Constr{index: j, args: args} ->
        case Enum.find(ind_def.constrs, fn {idx, _, _} -> idx == j end) do
          {^j, _cname, c_sig} ->
            res = apply_args(e, Enum.at(cases, j - 1), args, c_sig, ind)
            reduce(e, res, fuel - 1)
          _ -> ind
        end
      %AST.Number{value: v} -> reduce(e, %{ind | term: unfold_number(e, v)}, fuel - 1)
      %AST.Var{} -> %{ind | term: target}
      _ -> %{ind | term: target}
    end
  end
  defp do_reduce(e, %AST.Var{name: name} = t, fuel) do
    case Map.get(e.defs, name) do
      nil -> case Map.get(e.env, name) do
               %AST.Inductive{} = ind -> ind
               _ -> t
             end
      %AST.Fixpoint{} = f -> f
      val -> reduce(e, val, fuel - 1)
    end
  end
  defp do_reduce(e, %AST.Let{decls: decls, body: body}, fuel) do
    new_defs = Enum.reduce(decls, e.defs, fn {n, expr}, acc -> Map.put(acc, n, expr) end)
    reduce(%{e | defs: new_defs}, body, fuel - 1)
  end
  defp do_reduce(_e, t, _fuel), do: t

  defp try_unfold_fixpoint(e, %AST.Fixpoint{name: s_name, body: body} = fix, args, fuel) do
    # Fixpoint body is Lam(arg1, Lam(arg2, ...))
    # We substitute s_name with the Fixpoint itself for recursion
    {actual_body, params} = collect_lams(subst(s_name, %{fix | args: []}, body))
    
    n_params = length(params)
    n_args = length(args)
    Christine.Debug.log("DEBUG TRY_UNFOLD #{fix.name}: params=#{n_params} args=#{n_args}")

    if n_args >= n_params and n_params > 0 do
      subst_map = Enum.zip(params, Enum.take(args, n_params))
      unfolded_base = Enum.reduce(subst_map, actual_body, fn {p, a}, acc -> subst(p, a, acc) end)
      # Ensure args are wrapped if we have more than params
      unfolded = if n_args > n_params do
        Enum.reduce(Enum.drop(args, n_params), unfolded_base, fn a, acc -> %AST.App{func: acc, arg: a} end)
      else
        unfolded_base
      end
      
      case unfolded_base do
        %AST.Ind{term: t} ->
          # If the term being matched on is not a constructor, unfold is blocked
          red_t = reduce(e, t, fuel - 1)
          Christine.Debug.log("DEBUG TRY_UNFOLD #{fix.name} Ind term=#{AST.to_string(t)} red=#{AST.to_string(red_t)}")
          case red_t do
            %AST.Constr{} -> 
              {:ok, unfolded}
            %AST.Number{} -> 
              {:ok, unfolded}
            _ -> 
              Christine.Debug.log("DEBUG UNFOLD BLOCKED (Ind term): #{fix.name} term=#{AST.to_string(red_t)}")
              :blocked
          end
        _ -> 
           {:ok, unfolded}
      end
    else
      :blocked
    end
  end

  defp collect_lams(%AST.Lam{name: x, body: b}), do: (fn {bb, pp} -> {bb, [x | pp]} end).(collect_lams(b))
  defp collect_lams(t), do: {t, []}

  defp apply_args(e, f, args, c_sig, ind) do
    do_apply_args(e, f, args, c_sig, ind, length(ind.inductive.params))
  end
  defp do_apply_args(_e, f, [], _ty_sig, _ind, _n_skip), do: f
  defp do_apply_args(e, f, [arg | rest], ty_sig, %AST.Ind{} = ind, n_skip) do
    {arg_name, arg_domain, next_sig} = case ty_sig do
      %AST.Pi{name: n, domain: d, codomain: c} -> {n, d, c}
      _ -> {nil, nil, ty_sig}
    end
    updated_next_sig = if arg_name && next_sig, do: subst(arg_name, arg, next_sig), else: next_sig
    if n_skip > 0 do
      do_apply_args(e, f, rest, updated_next_sig, ind, n_skip - 1)
    else
      is_recursive = case arg_domain do
        %AST.Var{name: n} -> n == ind.inductive.name
        %AST.App{func: %AST.Var{name: n}} -> n == ind.inductive.name
        _ -> false
      end
      if is_recursive do
        ih = %AST.Ind{ind | term: arg}
        do_apply_args(e, %AST.App{func: %AST.App{func: f, arg: arg}, arg: ih}, rest, updated_next_sig, ind, 0)
      else
        do_apply_args(e, %AST.App{func: f, arg: arg}, rest, updated_next_sig, ind, 0)
      end
    end
  end

  def subst(x, v, t) do
    case t do
      %AST.Var{name: ^x} -> v
      %AST.App{func: f, arg: arg} -> %AST.App{func: subst(x, v, f), arg: subst(x, v, arg)}
      %AST.Lam{name: n, domain: d, body: b} ->
        if n == x, do: %AST.Lam{name: n, domain: subst(x, v, d), body: b},
        else: %AST.Lam{name: n, domain: subst(x, v, d), body: subst(x, v, b)}
      %AST.Pi{name: n, domain: d, codomain: c} ->
        if n == x, do: %AST.Pi{name: n, domain: subst(x, v, d), codomain: c},
        else: %AST.Pi{name: n, domain: subst(x, v, d), codomain: subst(x, v, c)}
      %AST.Ind{inductive: d, motive: p, cases: cases, term: tm} ->
        %AST.Ind{inductive: d, motive: subst(x, v, p), cases: Enum.map(cases, &subst(x, v, &1)), term: subst(x, v, tm)}
      %AST.Fixpoint{name: n, domain: d, body: b, args: args} ->
        if n == x, do: t, else: %AST.Fixpoint{name: n, domain: subst(x, v, d), body: subst(x, v, b), args: Enum.map(args, &subst(x, v, &1))}
      %AST.Constr{index: i, inductive: d, args: args} ->
        %AST.Constr{index: i, inductive: d, args: Enum.map(args, &subst(x, v, &1))}
      %AST.Let{decls: decls, body: b} ->
        new_decls = Enum.map(decls, fn {n, e} -> {n, subst(x, v, e)} end)
        if Enum.any?(decls, fn {n, _} -> n == x end), do: %AST.Let{decls: new_decls, body: b},
        else: %AST.Let{decls: new_decls, body: subst(x, v, b)}
      _ -> t
    end
  end

  defp subst_many([], t), do: t
  defp subst_many([{x, _} | rest], t), do: subst_many(rest, subst(x, %AST.Var{name: x}, t))

  defp infer_ctor(_e, ty, []), do: ty
  defp infer_ctor(e, %AST.Pi{name: x, codomain: c}, [arg | rest]) do
    infer_ctor(e, subst(x, arg, c), rest)
  end

  def unfold_number(_e, 0), do: %AST.Constr{index: 1, inductive: %AST.Inductive{name: "nat"}}
  def unfold_number(e, n) when n > 0 do
    %AST.Constr{index: 2, inductive: %AST.Inductive{name: "nat"}, args: [unfold_number(e, n - 1)]}
  end

  def unwrap_eq(term) do
    case term do
      %AST.App{} = term ->
        {f, args} = collect_app_args(term)
        {head_name, total_args} = case f do
          %AST.Var{name: n} -> {n, args}
          %AST.Inductive{name: n, params: p} -> {n, Enum.map(p, &elem(&1, 1)) ++ args}
          _other -> {nil, []}
        end
        is_eq = head_name && (AST.names_match?("eq", head_name) or AST.names_match?("Eq", head_name) or head_name == "Coq.Init.Logic.eq")
        if is_eq do
           if length(total_args) >= 2 do
              {Enum.at(total_args, -2), Enum.at(total_args, -1)}
           else
              nil
           end
        else
           nil
        end
      _ -> nil
    end
  end

  def collect_app_args(%AST.App{func: f, arg: a}) do
    {ff, args} = collect_app_args(f)
    {ff, args ++ [a]}
  end
  def collect_app_args(t), do: {t, []}
end
