defmodule Christine.Compiler do
  @moduledoc """
  Main entry point for the Christine compiler.
  """
  alias Christine.{Lexer, Layout, Parser, Desugar, Codegen, AST}

  def compile_module(source, opts \\ []) do
    with {:ok, tokens} <- Lexer.lex(source),
         resolved <- Layout.resolve(tokens),
         {:ok, ast, _rest} <- Parser.parse(resolved) do
      env = resolve_imports(ast, %Christine.Typechecker.Env{}, opts)
      env = collect_local_names(ast, env)
      desugared = Desugar.desugar(ast, env)

      final_env =
        populate_local_env(desugared, %{
          env
          | ctx: [
              {"Number", %AST.Universe{level: 0}},
              {"String", %AST.Universe{level: 0}} | env.ctx
            ]
        })

      typecheck_res =
        if Keyword.get(opts, :typecheck, true) do
          case Christine.Typechecker.check_module(desugared, final_env) do
            :ok -> :ok
            {:error, reason} ->
              IO.puts("TYPE ERROR: #{inspect(reason)}")
              {:error, {:type_error, reason}}
          end
        else
          :ok
        end

      if typecheck_res == :ok and Keyword.get(opts, :check_only, false) do
        {:ok, desugared.name, :check_only}
      else
        try do
          with :ok <- typecheck_res,
               {:ok, forms} <- Codegen.generate(desugared, env) do
            case :compile.forms(forms, [:return_errors, :debug_info]) do
              {:ok, mod, bin} -> {:ok, mod, bin}
              {:error, errors, warnings} -> {:error, {:erl_compile, errors, warnings}}
            end
          end
        rescue
          e ->
            IO.puts("COMPILER CRASH: #{inspect(e)}")
            IO.puts(Exception.format(:error, e, __STACKTRACE__))
            {:error, {:compiler_crash, e}}
        end
      end
    else
      err -> err
    end
  end

  defp populate_local_env(%AST.Module{name: _mod_name, declarations: decls}, env) do
    Enum.reduce(decls, env, fn
      %AST.DeclValue{name: n, expr: e, type: t, tactics: tacs}, acc ->
        if tacs do
          case Christine.Tactics.solve_with_tactics(n, t, tacs, acc) do
            {:ok, term} ->
              %{acc | ctx: [{n, t} | acc.ctx], defs: Map.put(acc.defs, n, term), last_decl: n}
            {:error, reason} ->
              IO.puts("Tactic error in #{n}: #{inspect(reason)}")
              %{acc | ctx: [{n, t} | acc.ctx], last_decl: n}
          end
        else
          if e do
            ty = Christine.Typechecker.infer(acc, e)
            %{acc | defs: Map.put(acc.defs, n, e), ctx: [{n, ty} | acc.ctx], last_decl: n}
          else
            %{acc | ctx: [{n, t} | acc.ctx], last_decl: n}
          end
        end

      %AST.Inductive{} = ind, acc ->
        new_env_map = Map.put(acc.env, ind.name, ind)
        new_defs = add_constructors(ind, acc.defs)
        new_ctx = add_constructors_to_ctx(ind, acc.ctx)
        %{acc | env: new_env_map, defs: new_defs, ctx: new_ctx, last_decl: ind.name}

      {:module_start, _name}, acc -> acc
      {:section_start, _name}, acc -> acc

      {:command, :check_kw, expr}, acc ->
        ty = try do Christine.Typechecker.infer(acc, expr) rescue e -> {:error, {:typechecker_crash, Exception.message(e)}} end
        IO.puts("Check: #{AST.to_string(expr)} : #{AST.to_string(ty)}")
        acc

      {:command, :eval_kw, expr}, acc ->
        res = try do Christine.Typechecker.normalize(acc, expr) rescue e -> {:error, {:eval_crash, Exception.message(e)}} end
        IO.puts("Eval: #{AST.to_string(expr)} = #{AST.to_string(res)}")
        acc

      {:command, :search_kw, %AST.Var{name: name}}, acc ->
        IO.puts("Search results for #{name}:")
        for {n, ty} <- acc.ctx, String.contains?(n, name) do
          ty_str = try do AST.to_string(ty) rescue _ -> "<complex type>" end
          IO.puts("  #{n} : #{ty_str}")
        end
        acc

      {:command, :print_kw, %AST.Var{name: name}}, acc ->
        case List.keyfind(acc.ctx, name, 0) do
          nil -> IO.puts("#{name} is not defined")
          {_, ty} ->
            term = Map.get(acc.defs, name)
            AST.print_declaration(name, ty, term)
        end
        acc

      {:proof, tacs}, acc ->
        if acc.last_decl do
          n = acc.last_decl
          case List.keyfind(acc.ctx, n, 0) do
            {_, ty} ->
              case Christine.Tactics.solve_with_tactics(n, ty, tacs, acc) do
                {:ok, term} -> %{acc | defs: Map.put(acc.defs, n, term)}
                {:error, _reason} -> acc
              end
            _ -> acc
          end
        else
          acc
        end

      _, acc -> acc
    end)
  end

  defp collect_local_names(%AST.Module{name: mod_name, declarations: decls}, env) do
    new_mapping =
      Enum.reduce(decls, env.name_to_mod, fn
        %AST.DeclValue{name: n}, acc -> Map.put(acc, n, mod_name)
        %AST.Inductive{name: n, constrs: cs}, acc ->
          acc = Map.put(acc, n, mod_name)
          Enum.reduce(cs, acc, fn {_, cn, _}, a -> Map.put(a, cn, mod_name) end)
        _, acc -> acc
      end)
    %{env | name_to_mod: new_mapping}
  end

  def resolve_imports(%AST.Module{name: mod_name, declarations: decls}, env, opts) do
    env = if mod_name not in ["Prelude", "Coq"] do
      case load_module_to_env("Coq", env, opts) do
        {:ok, new_env} -> new_env
        _ -> env
      end
    else env end

    env = if mod_name not in ["Prelude", "Coq"] do
      case load_module_to_env("Prelude", env, opts) do
        {:ok, new_env} -> new_env
        _ -> env
      end
    else env end

    Enum.reduce(decls, env, fn
      {:import, name}, acc ->
        case load_module_to_env(name, acc, opts) do
          {:ok, new_env} -> new_env
          _ -> acc
        end
      _, acc -> acc
    end)
  end

  def load_module_to_env(mod_name, env, opts \\ []) do
    case find_module_path(mod_name) do
      {:ok, path} ->
        source = File.read!(path)
        with {:ok, tokens} <- Lexer.lex(source),
             resolved <- Layout.resolve(tokens),
             {:ok, %AST.Module{} = mod, _} <- Parser.parse(resolved) do
          env_with_imports = resolve_imports(mod, env, opts)
          new_env = Enum.reduce(mod.declarations, env_with_imports, fn
            %AST.DeclValue{} = v, acc ->
              desugared_v = Desugar.desugar_decl(v, acc)
              {expr, val_ty} = cond do
                desugared_v.tactics ->
                  case Christine.Tactics.solve_with_tactics(desugared_v.name, desugared_v.type, desugared_v.tactics, acc) do
                    {:ok, term} -> {term, desugared_v.type}
                    {:error, reason} ->
                      IO.puts("Tactic error in #{desugared_v.name}: #{inspect(reason)}")
                      {nil, desugared_v.type}
                  end
                desugared_v.expr -> {desugared_v.expr, Christine.Typechecker.infer(acc, desugared_v.expr)}
                true -> {nil, desugared_v.type}
              end
              new_defs = if expr, do: Map.put(acc.defs, desugared_v.name, expr), else: acc.defs
              %{acc | defs: new_defs, name_to_mod: Map.put(acc.name_to_mod, desugared_v.name, mod_name), ctx: [{desugared_v.name, val_ty} | acc.ctx], last_decl: desugared_v.name}
            %AST.DeclData{} = data, acc ->
              desugared_ind = Desugar.desugar_decl(data, acc)
              new_env_map = Map.put(acc.env, desugared_ind.name, desugared_ind)
              new_defs = add_constructors(desugared_ind, acc.defs)
              new_ctx = add_constructors_to_ctx(desugared_ind, acc.ctx)
              new_names = Map.put(acc.name_to_mod, desugared_ind.name, mod_name)
              new_names = Enum.reduce(desugared_ind.constrs, new_names, fn {_, cn, _}, a -> Map.put(a, cn, mod_name) end)
              %{acc | env: new_env_map, defs: new_defs, ctx: new_ctx, name_to_mod: new_names, last_decl: desugared_ind.name}
            {:proof, tacs}, acc ->
              if acc.last_decl do
                n = acc.last_decl
                case List.keyfind(acc.ctx, n, 0) do
                  {_, ty} ->
                    case Christine.Tactics.solve_with_tactics(n, ty, tacs, acc) do
                      {:ok, term} -> %{acc | defs: Map.put(acc.defs, n, term)}
                      {:error, _reason} -> acc
                    end
                  _ -> acc
                end
              else acc end
            _, acc -> acc
          end)
          {:ok, new_env}
        else err -> {:error, err} end
      nil -> {:error, :module_not_found}
    end
  end

  def find_module_path(mod_name) do
    path1 = "priv/christine/" <> String.replace(mod_name, ".", "/") <> ".christine"
    path2 = "test/christine/" <> String.replace(mod_name, ".", "/") <> ".christine"
    cond do
      File.exists?(path1) -> {:ok, path1}
      File.exists?(path2) -> {:ok, path2}
      true -> nil
    end
  end

  defp add_constructors(ind, defs) do
    Enum.reduce(ind.constrs, defs, fn {idx, name, ty}, acc ->
      term = make_constr_term(idx, ind, ty, [])
      Map.put(acc, name, term)
    end)
  end

  defp add_constructors_to_ctx(ind, ctx) do
    Enum.reduce(ind.constrs, ctx, fn {_, name, ty}, acc -> [{name, ty} | acc] end)
  end

  defp make_constr_term(idx, ind, ty, vars) do
    case ty do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        name = if x == "_", do: "a#{length(vars)}", else: x
        %AST.Lam{name: name, domain: a, body: make_constr_term(idx, ind, b, [name | vars])}
      _ ->
        args = Enum.reverse(vars) |> Enum.map(fn n -> %AST.Var{name: n} end)
        %AST.Constr{index: idx, inductive: ind, args: args}
    end
  end

  def load_binary(mod, bin) do
    :code.load_binary(mod, ~c"#{mod}.beam", bin)
  end
end
