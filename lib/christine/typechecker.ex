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

  # Checks all declarations in a module.
  # Expects a desugared module.
  def check_module(%AST.Module{declarations: decls}, %Env{} = env) do
    # First, collect all types/signatures into the context if they aren't there yet.
    # Desugared declarations are either Inductive or DeclValue.
    # For now, we assume all necessary things are in the env or we add them.
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

  def infer(_env, nil), do: %AST.Universe{level: 0}

  def infer(%Env{} = e, %AST.Var{name: name}) do
    if name == "Any" do
      %AST.Var{name: "Any"}
    else
      case List.keyfind(e.ctx, name, 0) do
        {^name, ty} ->
          ty

        nil ->
          # If name has a definition, return Any rather than re-inferring the body.
          # Re-inferring would cause infinite recursion for recursive functions.
          if Map.has_key?(e.defs, name) do
            %AST.Var{name: "Any"}
          else
            case Map.get(e.env, name) do
              %AST.Inductive{} = ind ->
                infer(e, ind)

              _ ->
                {:error, {:unbound_variable, name}}
            end
          end
      end
    end
  end

  def infer(%Env{}, %AST.Universe{level: i}) do
    %AST.Universe{level: i + 1}
  end

  def infer(%Env{} = _e, %AST.Inductive{level: level}) do
    %AST.Universe{level: level + 1}
  end

  def infer(%Env{} = e, %AST.Constr{index: j, inductive: d, args: args}) do
    {^j, _name, ty} = Enum.find(d.constrs, fn {idx, _, _} -> idx == j end)
    ty_subst = subst_many(d.params, ty)
    infer_ctor(e, ty_subst, args)
  end

  def infer(%Env{} = e, %AST.Ind{inductive: _d, motive: p, cases: _cases, term: t}) do
    # IO.inspect(p, label: "IND MOTIVE")
    _t_ty = infer(e, t)

    case infer(e, p) do
      %AST.Pi{name: x, domain: _a, codomain: b} ->
        subst(x, t, b)

      other ->
        {:error, {:motive_not_pi, other}}
    end
  end

  def infer(%Env{} = e, %AST.Pi{name: x, domain: a, codomain: b}) do
    # IO.inspect({a, b}, label: "PI INFER")
    u_a = universe_level(e, a)
    u_b = universe_level(%{e | ctx: [{x, a} | e.ctx]}, b)
    %AST.Universe{level: Kernel.max(u_a, u_b)}
  end

  def infer(%Env{} = e, %AST.Lam{name: x, domain: domain, body: body}) do
    %AST.Pi{name: x, domain: domain, codomain: infer(%{e | ctx: [{x, domain} | e.ctx]}, body)}
  end

  def infer(%Env{} = e, %AST.Fixpoint{name: _n, domain: ty, body: body}) do
    # Check that body has type ty (or is compatible)
    # Note: when checking body, the fixpoint name itself might be used recursively.
    # But desugarer already handles that by putting the fixpoint in defs.
    check(e, body, ty)
    ty
  end

  def infer(%Env{} = e, %AST.App{func: f, arg: arg}) do
    case infer(e, f) do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        check(e, arg, a)
        subst(x, arg, b)

      %AST.Var{name: "Any"} ->
        %AST.Var{name: "Any"}

      %AST.Universe{} ->
        # Type-level application: applying a type constructor (like `eq`, `le`, `and`)
        # to arguments. The result is a type at Prop level (U0 or U-1).
        # This supports Coq-style explicit: `eq nat 3 5`, `le m n`, `and P Q`.
        %AST.Universe{level: 0}

      other ->
        {:error, {:application_requires_pi, other}}
    end
  end

  def infer(%Env{} = e, %AST.Let{decls: decls, body: body}) do
    new_env =
      Enum.reduce(decls, e, fn {name, expr}, acc ->
        ty = infer(acc, expr)
        %{acc | ctx: [{name, ty} | acc.ctx], defs: Map.put(acc.defs, name, expr)}
      end)

    infer(new_env, body)
  end

  def infer(%Env{}, %AST.Number{}) do
    %AST.Var{name: "Number"}
  end

  def infer(%Env{}, %AST.String{}) do
    %AST.Var{name: "String"}
  end

  def check(%Env{} = _e, _t, %AST.Var{name: "Any"}), do: :ok

  def check(%Env{} = e, t, ty) do
    inferred = infer(e, t)

    # Allow Any as inferred type to match everything
    if inferred == %AST.Var{name: "Any"} or equal?(e, inferred, ty) do
      :ok
    else
      # IO.inspect({t, inferred, ty}, label: "TYPE MISMATCH")
      {:error, {:type_mismatch, inferred, ty}}
    end
  end

  def universe_level(_e, %AST.Var{name: "Any"}), do: 0

  def universe_level(e, t) do
    case normalize(e, t) do
      %AST.Universe{level: i} ->
        i

      _ ->
        0
    end
  end

  def equal?(e, t1, t2) do
    n1 = normalize(e, t1)
    n2 = normalize(e, t2)
    res = (n1 == n2)
    # Christine.Debug.log("DEBUG EQUAL?: #{AST.to_string(n1)} == #{AST.to_string(n2)} -> #{res}")
    res
  end

  def normalize(e, t) do
    deadline = e.deadline || System.monotonic_time(:millisecond) + 60_000
    e = %{e | deadline: deadline}
    t_red = reduce(e, t)

    case t_red do
      %AST.App{func: f, arg: arg} ->
        %AST.App{func: normalize(e, f), arg: normalize(e, arg)}

      %AST.Lam{name: x, domain: a, body: b} ->
        %AST.Lam{name: x, domain: normalize(e, a), body: b}

      %AST.Pi{name: x, domain: a, codomain: b} ->
        %AST.Pi{name: x, domain: normalize(e, a), codomain: normalize(e, b)}

      %AST.Ind{inductive: d, motive: p, cases: cases, term: t_val} ->
        %AST.Ind{
          inductive: d,
          motive: normalize(e, p),
          cases: Enum.map(cases, &normalize(e, &1)),
          term: normalize(e, t_val)
        }

      %AST.Fixpoint{name: _n, domain: d, body: b, args: args} = fix ->
        %{fix | domain: normalize(e, d), body: normalize(e, b), args: Enum.map(args, &normalize(e, &1))}

      %AST.Constr{index: i, inductive: d, args: args} ->
        %AST.Constr{index: i, inductive: d, args: Enum.map(args, &normalize(e, &1))}

      _ ->
        t_red
    end
  end

  @spec reduce(any(), any(), any()) :: any()
  def reduce(e, t, fuel \\ 500_000)

  def reduce(_e, t, 0) do
    raise "Out of fuel reducing: #{inspect(t, limit: 20)}"
  end

  def reduce(e, t, fuel) do
    if e.deadline && System.monotonic_time(:millisecond) > e.deadline do
      raise "Timeout reducing: #{inspect(t, limit: 20)}"
    end

    do_reduce(e, t, fuel)
  end

  defp do_reduce(e, %AST.App{func: f, arg: arg}, fuel) do
    f_red = reduce(e, f, fuel - 1)

    case f_red do
      %AST.Lam{name: x, body: body} ->
        reduce(e, subst(x, arg, body), fuel - 1)

      %AST.Fixpoint{body: body, args: applied_args} = fix ->
        # Accumulate the argument
        all_args = applied_args ++ [arg]
        
        # Try to unfold: beta-reduce arguments into body and see if it can reduce an Ind
        case try_unfold_fixpoint(e, body, all_args, fuel - 1) do
          {:ok, unfolded} -> 
            if fix.name in ["plus", "beq_nat", "insert", "count", "mult"] do
               Christine.Debug.log("DEBUG REDUCE FIX OK: #{fix.name} unfolded with #{length(all_args)} args")
            end
            reduce(e, unfolded, fuel - 1)
          :blocked -> 
            if fix.name in ["plus", "beq_nat", "insert", "count", "mult"] do
               Christine.Debug.log("DEBUG REDUCE FIX BLOCKED: #{fix.name} now has #{length(all_args)} args")
            end
            %{fix | args: all_args}
        end

      %AST.Constr{index: i, inductive: d, args: args} ->
        arg_red = reduce(e, arg, fuel - 1)
        %AST.Constr{index: i, inductive: d, args: args ++ [arg_red]}

      _ ->
        %AST.App{func: f_red, arg: arg}
    end
  end

  defp do_reduce(e, %AST.Fixpoint{name: name, body: body, args: args} = f, fuel) do
    if args == [] do
      f
    else
      case try_unfold_fixpoint(e, body, args, fuel - 1) do
        {:ok, unfolded} -> 
          if name in ["plus", "beq_nat", "insert", "count"] do
             Christine.Debug.log("DEBUG REDUCE FIX OK (standalone): #{name} unfolded")
          end
          reduce(e, unfolded, fuel - 1)
        :blocked -> 
          if name in ["plus", "beq_nat", "insert", "count"] do
             # Christine.Debug.log("DEBUG REDUCE FIX BLOCKED (standalone): #{name} with #{length(args)} args")
          end
          f
      end
    end
  end

  defp do_reduce(e, %AST.Ind{inductive: ind_def, motive: _p, cases: cases, term: t} = ind, fuel) do
    case reduce(e, t, fuel - 1) do
      %AST.Constr{index: j, args: args} ->
        # Christine.Debug.log("DEBUG REDUCE IND: constructor #{j} for #{ind_def.name}")
        # Find the constructor's Pi type signature to trace which arguments are recursive
        case Enum.find(ind_def.constrs, fn {idx, _, _} -> idx == j end) do
          {^j, _cname, c_sig} ->
            case_val = Enum.at(cases, j - 1)
            res = apply_args(e, case_val, args, c_sig, ind)
            reduce(e, res, fuel - 1)
          _ ->
            # Christine.Debug.log("DEBUG REDUCE IND FAILED: constructor #{j} not found in #{ind_def.name}")
            ind
        end

      _ ->
        ind
    end
  end

  defp do_reduce(e, %AST.Let{decls: decls, body: body}, fuel) do
    new_defs = Enum.reduce(decls, e.defs, fn {n, expr}, acc -> Map.put(acc, n, expr) end)
    reduce(%{e | defs: new_defs}, body, fuel - 1)
  end

  defp do_reduce(e, %AST.Var{name: name}, fuel) do
    case Map.get(e.defs, name) do
      nil ->
        case Map.get(e.env, name) do
          %AST.Constr{} = c -> c
          _ -> %AST.Var{name: name}
        end

      term ->
        # Only expand Fixpoints (represented as Ind in defs) if they might reduce?
        # For now, let's try to expand only if we are in an App and the arg is a Constr
        # but reduce/2 doesn't know about context.
        # Actually, let's keep it simple: always expand if it's in defs, 
        # BUT Ind reduction itself will handle the blocking if term is not Constr.
        reduce(e, term, fuel - 1)
    end
  end

  defp do_reduce(_e, t, _fuel), do: t

  defp apply_args(e, f, args, c_sig, %AST.Ind{inductive: info} = ind) do
    do_apply_args(e, f, args, c_sig, ind, length(info.params))
  end

  defp do_apply_args(_e, f, [], _ty_sig, _ind, _n_skip), do: f

  defp do_apply_args(e, f, [arg | rest], ty_sig, %AST.Ind{} = ind, n_skip) do
    # Extract domain and update ty_sig via substitution if it's a Pi
    {arg_name, arg_domain, next_sig} =
      case ty_sig do
        %AST.Pi{name: n, domain: d, codomain: c} -> {n, d, c}
        _ -> {nil, nil, ty_sig}
      end

    # Substitute current arg into the rest of the signature (important for dependent types)
    updated_next_sig = if arg_name && next_sig, do: subst(arg_name, arg, next_sig), else: next_sig

    if n_skip > 0 do
      # It's a parameter of the inductive type (e.g. 'A' in 'list A').
      # Skip applying to f (as desugarer patterns only bind constructor-specific args),
      # but still continue to process rest of the args.
      do_apply_args(e, f, rest, updated_next_sig, ind, n_skip - 1)
    else
      # Real constructor argument.
      ind_name = ind.inductive.name

      is_inductive =
        case arg_domain do
          %AST.Var{name: ^ind_name} -> true
          %AST.App{func: %AST.Var{name: ^ind_name}} -> true
          %AST.Pi{codomain: %AST.Var{name: ^ind_name}} -> true
          %AST.Pi{codomain: %AST.App{func: %AST.Var{name: ^ind_name}}} -> true
          _ -> false
        end

      ih =
        if is_inductive do
          case arg_domain do
            %AST.Pi{name: x, domain: a} ->
              # Functional induction: \x -> Ind(ind.term = arg x)
              %AST.Lam{
                name: x,
                domain: a,
                body: %AST.Ind{ind | term: %AST.App{func: arg, arg: %AST.Var{name: x}}}
              }

            _ ->
              # Basic induction
              %AST.Ind{ind | term: arg}
          end
        else
          %AST.Var{name: "unused_ih"}
        end

      f_next = %AST.App{func: f, arg: arg}
      do_apply_args(e, %AST.App{func: f_next, arg: ih}, rest, updated_next_sig, ind, 0)
    end
  end

  def subst_many(params, ty) do
    Enum.reduce(params, ty, fn {name, val}, acc -> subst(name, val, acc) end)
  end

  defp infer_ctor(e, ty, args) do
    Enum.reduce(args, ty, fn arg, acc ->
      case acc do
        %AST.Pi{name: x, domain: a, codomain: b} ->
          check(e, arg, a)
          subst(x, arg, b)

        _ ->
          raise "Too many arguments to constructor"
      end
    end)
  end

  def subst(x, s, %AST.Var{name: name}) do
    if AST.names_match?(x, name), do: s, else: %AST.Var{name: name}
  end

  def subst(x, s, %AST.Pi{name: n, domain: a, codomain: b}) do
    if n == x,
      do: %AST.Pi{name: n, domain: subst(x, s, a), codomain: b},
      else: %AST.Pi{name: n, domain: subst(x, s, a), codomain: subst(x, s, b)}
  end

  def subst(x, s, %AST.Lam{name: n, domain: a, body: b}) do
    if n == x,
      do: %AST.Lam{name: n, domain: subst(x, s, a), body: b},
      else: %AST.Lam{name: n, domain: subst(x, s, a), body: subst(x, s, b)}
  end

  def subst(x, s, %AST.App{func: f, arg: arg}),
    do: %AST.App{func: subst(x, s, f), arg: subst(x, s, arg)}

  def subst(x, s, %AST.Let{decls: decls, body: body}) do
    new_decls = Enum.map(decls, fn {name, expr} -> {name, subst(x, s, expr)} end)
    %AST.Let{decls: new_decls, body: subst(x, s, body)}
  end

  def subst(x, s, %AST.Ind{inductive: d, motive: p, cases: cases, term: t}) do
    %AST.Ind{
      inductive: d,
      motive: subst(x, s, p),
      cases: Enum.map(cases, &subst(x, s, &1)),
      term: subst(x, s, t)
    }
  end

  def subst(x, s, %AST.Constr{index: i, inductive: d, args: args}) do
    %AST.Constr{index: i, inductive: d, args: Enum.map(args, &subst(x, s, &1))}
  end

  def subst(x, s, %AST.Fixpoint{name: n, domain: d, body: b, args: args} = f) do
    new_args = Enum.map(args, &subst(x, s, &1))
    # Fixpoint name might shadow x, but usually it's a global name.
    if n == x do
      %{f | domain: subst(x, s, d), args: new_args}
    else
      %{f | domain: subst(x, s, d), body: subst(x, s, b), args: new_args}
    end
  end

  def subst(_, _, t), do: t

  defp count_lams(%AST.Lam{body: b}), do: 1 + count_lams(b)
  defp count_lams(_), do: 0

  defp try_unfold_fixpoint(e, body, args, fuel) do
    num_lams = count_lams(body)
    if length(args) < num_lams do
      :blocked
    else
      {unfold_args, extra_args} = Enum.split(args, num_lams)
      
      unfolded_inner = Enum.reduce(unfold_args, body, fn arg, acc ->
        case acc do
          %AST.Lam{name: x, body: b} -> subst(x, arg, b)
          _ -> %AST.App{func: acc, arg: arg}
        end
      end)
      
      unfolded = Enum.reduce(extra_args, unfolded_inner, fn arg, acc ->
        %AST.App{func: acc, arg: arg}
      end)

      case find_first_ind(unfolded) do
        {:ok, %AST.Ind{term: t} = _ind} ->
          case reduce(e, t, fuel) do
             %AST.Constr{} -> {:ok, unfolded}
             _other -> :blocked
          end
        :none -> 
          {:ok, unfolded}
      end
    end
  end

  defp find_first_ind(term) do
    case term do
      %AST.Ind{} = ind -> {:ok, ind}
      %AST.App{func: f} -> find_first_ind(f)
      %AST.Lam{body: b} -> find_first_ind(b)
      %AST.Pi{codomain: b} -> find_first_ind(b)
      %AST.Let{body: b} -> find_first_ind(b)
      _ -> :none
    end
  end
end
