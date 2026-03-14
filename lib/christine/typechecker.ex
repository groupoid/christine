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
    defstruct env: %{}, ctx: [], defs: %{}, global_ctx: %{}, name_to_mod: %{}, next_id: 0, deadline: nil, verbose: false, last_decl: nil
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
          case find_def(e, name) do
            %AST.Fixpoint{domain: ty} when ty != nil -> ty
            _ ->
              case find_global_ty(e, name) do
                nil ->
                   case Map.get(e.env, name) do
                     %AST.Inductive{} = ind -> infer(e, ind)
                     _ -> {:error, {:unbound_variable, name}}
                   end
                 ty -> ty
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
    case reduce(e, infer(e, p)) do
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
    case reduce(e, infer(e, f)) do
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
    if e.verbose do
       IO.puts("      DEBUG EQUAL?:\n      L: #{inspect(t1, limit: :infinity)}\n      R: #{inspect(t2, limit: :infinity)}")
    end
    if e.verbose do
       # IO.puts("  DEBUG EQUAL?: t1=#{AST.to_string(t1)} vs t2=#{AST.to_string(t2)}")
    end
    deadline = e.deadline || System.monotonic_time(:millisecond) + 10_000
    e = %{e | deadline: deadline}
    n1 = normalize(e, t1)
    n2 = normalize(e, t2)
    
    if structural_equal?(e, n1, n2) do
      true
    else
      if e.verbose do
         # IO.puts("  DEBUG EQUAL? STRUCTURAL FAILED. n1_type=#{inspect(n1.__struct__)} n2_type=#{inspect(n2.__struct__)}")
      end
      case {n1, n2} do
        {%AST.App{func: f1}, _} ->
          args = collect_app_args_list(n1)
          case find_fixpoint(e, f1) do
            %AST.Fixpoint{} = f ->
              case try_unfold_fixpoint_force_n(e, f, args, 1) do
                {:ok, unfolded} -> equal?(e, unfolded, n2)
                :blocked -> do_equal?(e, n1, n2, 100)
              end
            _ -> do_equal?(e, n1, n2, 100)
          end
        {_, %AST.App{func: f2}} ->
          args = collect_app_args_list(n2)
          case find_fixpoint(e, f2) do
            %AST.Fixpoint{} = f ->
              case try_unfold_fixpoint_force_n(e, f, args, 1) do
                {:ok, unfolded} -> equal?(e, n1, unfolded)
                :blocked -> do_equal?(e, n1, n2, 100)
              end
            _ -> do_equal?(e, n1, n2, 100)
          end
        {%AST.Fixpoint{args: args} = f, _} when args != [] ->
          case try_unfold_fixpoint_force_n(e, f, args, 1) do
            {:ok, unfolded} -> equal?(e, unfolded, n2)
            :blocked -> do_equal?(e, n1, n2, 100)
          end
        {_, %AST.Fixpoint{args: args} = f} when args != [] ->
          case try_unfold_fixpoint_force_n(e, f, args, 1) do
            {:ok, unfolded} -> equal?(e, n1, unfolded)
            :blocked -> do_equal?(e, n1, n2, 100)
          end
        _ ->
          do_equal?(e, n1, n2, 100)
      end
    end
  end

  defp do_equal?(e, n1, n2, fuel) do
    if fuel <= 0 do
      structural_equal?(e, n1, n2)
    else
      if structural_equal?(e, n1, n2) do
        true
      else
        case {n1, n2} do
          {%AST.App{func: f1, arg: a1}, %AST.App{func: f2, arg: a2}} ->
            (do_equal?(e, f1, f2, fuel) and do_equal?(e, a1, a2, fuel)) or
            (do_equal?(e, f1, f2, fuel - 1) and do_equal?(e, a1, a2, fuel - 1))
          {%AST.Pi{name: x1, domain: d1, codomain: c1}, %AST.Pi{name: _x2, domain: d2, codomain: c2}} ->
            do_equal?(e, d1, d2, fuel) and do_equal?(%{e | ctx: [{x1, d1} | e.ctx]}, c1, c2, fuel)
          {%AST.Lam{name: x1, domain: d1, body: b1}, %AST.Lam{name: _x2, domain: d2, body: b2}} ->
            do_equal?(e, d1, d2, fuel) and do_equal?(%{e | ctx: [{x1, d1} | e.ctx]}, b1, b2, fuel)
          {%AST.Lam{name: x, body: b}, f} ->
            # Eta: \x. f x == f
            case b do
              %AST.App{func: ^f, arg: %AST.Var{name: ^x}} -> true
              _ -> false
            end
          {f, %AST.Lam{name: x, body: b}} ->
            # Eta: f == \x. f x
            case b do
              %AST.App{func: ^f, arg: %AST.Var{name: ^x}} -> true
              _ -> false
            end
          _ -> false
        end
      end
    end
  end

  def structural_equal?(e, t1, t2) do
    case {t1, t2} do
      {%AST.Var{name: n1}, %AST.Var{name: n2}} -> AST.names_match?(n1, n2)
      {%AST.Universe{level: l1}, %AST.Universe{level: l2}} -> l1 == l2
      {%AST.App{func: f1, arg: a1}, %AST.App{func: f2, arg: a2}} ->
        structural_equal?(e, f1, f2) and structural_equal?(e, a1, a2)
      {%AST.Pi{name: _, domain: d1, codomain: c1}, %AST.Pi{name: _, domain: d2, codomain: c2}} ->
        structural_equal?(e, d1, d2) and structural_equal?(e, c1, c2)
      {%AST.Lam{name: _, domain: d1, body: b1}, %AST.Lam{name: _, domain: d2, body: b2}} ->
        structural_equal?(e, d1, d2) and structural_equal?(e, b1, b2)
      {%AST.Inductive{name: n1}, %AST.Inductive{name: n2}} -> AST.names_match?(n1, n2)
      {%AST.Constr{index: i1, args: a1}, %AST.Constr{index: i2, args: a2}} ->
        # We also need to check if they belong to the same inductive type, 
        # but comparing by index+args is usually enough if we are in the same context.
        # Strict version:
        i1 == i2 and length(a1) == length(a2) and 
        Enum.zip(a1, a2) |> Enum.all?(fn {x, y} -> structural_equal?(e, x, y) end)
      {%AST.Fixpoint{name: n1, args: a1}, %AST.Fixpoint{name: n2, args: a2}} ->
        AST.names_match?(n1, n2) and length(a1) == length(a2) and
        Enum.zip(a1, a2) |> Enum.all?(fn {x, y} -> structural_equal?(e, x, y) end)
      {%AST.Ind{term: t1, cases: c1}, %AST.Ind{term: t2, cases: c2}} ->
        structural_equal?(e, t1, t2) and length(c1) == length(c2) and
        Enum.zip(c1, c2) |> Enum.all?(fn {x, y} -> structural_equal?(e, x, y) end)
      {%AST.Number{value: v1}, %AST.Number{value: v2}} -> v1 == v2
      {%AST.String{value: v1}, %AST.String{value: v2}} -> v1 == v2
      {v1, v2} -> v1 == v2
    end
  end

  def normalize(e, t) do
    deadline = e.deadline || System.monotonic_time(:millisecond) + 10_000
    e = %{e | deadline: deadline}
    red = reduce(e, t)
    case red do
      %AST.App{func: f, arg: arg} -> 
        n_f = normalize(e, f)
        n_arg = normalize(e, arg)
        case n_f do
          %AST.Lam{name: x, body: body} -> normalize(e, subst(x, n_arg, body))
          _ -> %AST.App{func: n_f, arg: n_arg}
        end
      %AST.Lam{name: x, domain: a, body: b} -> 
        %AST.Lam{name: x, domain: normalize(e, a), body: normalize(%{e | ctx: [{x, a} | e.ctx]}, b)}
      %AST.Pi{name: x, domain: a, codomain: b} ->
        %AST.Pi{name: x, domain: normalize(e, a), codomain: normalize(%{e | ctx: [{x, a} | e.ctx]}, b)}
      %AST.Ind{inductive: d, motive: p, cases: cases, term: t_val} ->
        %AST.Ind{inductive: d, motive: normalize(e, p), cases: Enum.map(cases, &normalize(e, &1)), term: normalize(e, t_val)}
      %AST.Fixpoint{name: n, domain: d, body: b, args: args} ->
        # Just normalize the accumulated args, don't normalize the body to avoid infinite recursion
        %AST.Fixpoint{name: n, domain: normalize(e, d), body: b, args: Enum.map(args, &normalize(e, &1))}
      %AST.Constr{index: i, inductive: ind, args: args} ->
        %AST.Constr{index: i, inductive: ind, args: Enum.map(args, &normalize(e, &1))}
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
        all_args = applied_args ++ [arg] # Don't reduce arg yet, preserve for potential unfolding
        case try_unfold_fixpoint(e, fix, all_args, fuel - 1) do
          {:ok, unfolded} -> reduce(e, unfolded, fuel - 1)
          :blocked -> 
             # If blocked, reduce the arg and return partially applied fixpoint
             red_arg = reduce(e, arg, fuel - 1)
             %{fix | args: applied_args ++ [red_arg]}
        end
      %AST.Constr{index: i, inductive: d, args: args} ->
        %AST.Constr{index: i, inductive: d, args: args ++ [reduce(e, arg, fuel - 1)]}
      _ -> %AST.App{func: f_red, arg: arg}
    end
  end
  defp do_reduce(e, %AST.Ind{inductive: ind_def, cases: cases, term: term} = ind, fuel) do
    target = reduce(e, term, fuel - 1)
    
    # Handle numbers by unfolding them to constructors for matching
    target = case target do
      %AST.Number{value: v} -> reduce(e, Christine.Typechecker.unfold_number(e, v), fuel - 1)
      _ -> target
    end

    case target do
      %AST.Constr{index: j, args: args} ->
        # Look up inductive if constrs are missing (shallow definition)
        ind_full = if is_nil(ind_def.constrs) or ind_def.constrs == [] do
           Map.get(e.env, ind_def.name) || Enum.find_value(e.env, fn {n, ind} -> if AST.names_match?(n, ind_def.name), do: ind end) || ind_def
        else
           ind_def
        end
        case Enum.find(ind_full.constrs || [], fn {idx, _, _} -> idx == j end) do
          {^j, _cname, c_sig} ->
            res = apply_args(e, Enum.at(cases, j - 1), args, c_sig, %{ind | inductive: ind_full})
            reduce(e, res, fuel - 1)
          _ -> ind
        end
      %AST.Number{value: v} -> reduce(e, %{ind | term: unfold_number(e, v)}, fuel - 1)
      %AST.Var{} -> %{ind | term: target}
      _ -> %{ind | term: target}
    end
  end
  defp do_reduce(e, %AST.Var{name: name} = t, fuel) do
    # Check ctx for local variables or axioms (opaque)
    case List.keyfind(e.ctx, name, 0) do
      {^name, _} -> t
      nil ->
        # Check defs for transparent global definitions
        case find_def(e, name) do
          %AST.Fixpoint{} = f -> f
          nil ->
            # Inductives are opaque types
            case Map.get(e.env, name) do
              %AST.Inductive{} = ind -> ind
              nil ->
                case Map.get(e.name_to_mod, name) do
                  nil -> t
                  mod ->
                     prefix = if mod == "local", do: "", else: mod <> "."
                     Map.get(e.env, prefix <> name) || t
                end
            end
          val -> reduce(e, val, fuel - 1)
        end
    end
  end

  defp do_reduce(e, %AST.Let{decls: decls, body: body}, fuel) do
    new_defs = Enum.reduce(decls, e.defs, fn {n, expr}, acc -> Map.put(acc, n, expr) end)
    reduce(%{e | defs: new_defs}, body, fuel - 1)
  end
  defp do_reduce(_e, t, _fuel), do: t

  defp find_def(e, name) do
    case Map.get(e.defs, name) do
      nil ->
        case Map.get(e.name_to_mod, name) do
          nil -> nil
          mod -> 
             prefix = if mod == "local", do: "", else: mod <> "."
             Map.get(e.defs, prefix <> name)
        end
      val -> val
    end
  end

  defp try_unfold_fixpoint(e, %AST.Fixpoint{name: s_name, body: body} = fix, args, fuel) do
    # Fixpoint body is Lam(arg1, Lam(arg2, ...))
    # We substitute s_name with the Fixpoint itself for recursion
    {actual_body, params} = collect_lams(subst(s_name, %{fix | args: []}, body))
    
    n_params = length(params)
    n_args = length(args)
    # Christine.Debug.log("DEBUG TRY_UNFOLD #{fix.name}: params=#{n_params} args=#{n_args}")

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
          case red_t do
            %AST.Constr{} -> 
              {:ok, unfolded}
            %AST.Number{value: _v} -> 
              {:ok, unfolded}
            _ -> 
              :blocked
          end
        %AST.App{func: f_inner} ->
          # Potential match on another fixpoint or app
          red_f = reduce(e, f_inner, fuel - 1)
          case red_f do
            %AST.Constr{} -> {:ok, unfolded}
            _ -> :blocked
          end
        _ -> 
           :blocked
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
      is_recursive = case normalize(e, arg_domain) do
        %AST.Var{name: n} -> AST.names_match?(n, ind.inductive.name)
        %AST.Inductive{name: n} -> AST.names_match?(n, ind.inductive.name)
        %AST.Pi{codomain: cod} ->
           case head_name(normalize(e, cod)) do
             {:ok, n} -> AST.names_match?(n, ind.inductive.name)
             _ -> false
           end
        term ->
           case head_name(term) do
             {:ok, n} -> AST.names_match?(n, ind.inductive.name)
             _ -> false
           end
      end
      if is_recursive do
        ih = case normalize(e, arg_domain) do
          %AST.Pi{name: yn_raw, domain: yd} ->
            yn = if yn_raw == "_" or yn_raw == "", do: "y", else: yn_raw
            %AST.Lam{name: yn, domain: yd, body: %AST.Ind{ind | term: %AST.App{func: arg, arg: %AST.Var{name: yn}}}}
          _ ->
            %AST.Ind{ind | term: arg}
        end
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
  defp infer_ctor(e, ty, [arg | rest]) do
    case reduce(e, ty) do
      %AST.Pi{name: x, codomain: c} -> infer_ctor(e, subst(x, arg, c), rest)
      other -> {:error, {:constructor_requires_pi, other}}
    end
  end

  defp head_name(%AST.Var{name: n}), do: {:ok, n}
  defp head_name(%AST.Inductive{name: n}), do: {:ok, n}
  defp head_name(%AST.App{func: f}), do: head_name(f)
  defp head_name(_), do: :error

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

  def collect_app_args(%AST.App{func: f, arg: arg}) do
    {head, args} = collect_app_args(f)
    {head, args ++ [arg]}
  end
  def collect_app_args(t), do: {t, []}

  defp collect_app_args_list(t) do
    {_, args} = collect_app_args(t)
    args
  end

  defp find_fixpoint(_e, %AST.Fixpoint{} = f), do: f
  defp find_fixpoint(e, %AST.App{func: f}), do: find_fixpoint(e, f)
  defp find_fixpoint(e, %AST.Var{name: name}) do
     case find_def(e, name) do
       %AST.Fixpoint{} = f -> f
       _ -> nil
     end
  end
  defp find_fixpoint(_, _), do: nil

  defp find_global_ty(e, name) do
    case Map.get(e.global_ctx, name) do
      nil ->
        case Map.get(e.name_to_mod, name) do
          nil -> nil
          mod ->
             prefix = if mod == "local", do: "", else: mod <> "."
             Map.get(e.global_ctx, prefix <> name)
        end
      ty -> ty
    end
  end

  def try_unfold_fixpoint_force_n(_e, %AST.Fixpoint{name: s_name, body: body} = fix, args, _n) do
    {actual_body, params} = collect_lams(subst(s_name, %{fix | args: []}, body))
    n_params = length(params)
    if length(args) >= n_params and n_params > 0 do
      subst_map = Enum.zip(params, Enum.take(args, n_params))
      unfolded_base = Enum.reduce(subst_map, actual_body, fn {p, a}, acc -> subst(p, a, acc) end)
      {:ok, unfolded_base}
    else
      :blocked
    end
  end
end
