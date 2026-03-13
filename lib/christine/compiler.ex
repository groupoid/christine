defmodule Christine.Compiler do
  @moduledoc """
  Main entry point for the Christine compiler.
  """
  alias Christine.{Lexer, Layout, Parser, Desugar, Codegen, AST}

  def compile_module(source, opts \\ []) do
    with {:ok, tokens} <- Lexer.lex(source),
         resolved <- Layout.resolve(tokens),
         {:ok, ast, _rest} <- Parser.parse(resolved) do
      loaded = Keyword.get(opts, :loaded, MapSet.new())
      deadline = System.monotonic_time(:millisecond) + Keyword.get(opts, :timeout, 10_000)
      
      with {:ok, env} <- resolve_imports(ast, %Christine.Typechecker.Env{deadline: deadline}, Keyword.put(opts, :loaded, loaded)) do
        env = collect_local_names(ast, env)
        desugared = Desugar.desugar(ast, env)

        final_env_res =
          populate_local_env(desugared, %{
            env
            | ctx: [
                {"Number", %AST.Universe{level: 0}},
                {"String", %AST.Universe{level: 0}} | env.ctx
              ]
          })

        case final_env_res do
          {:error, reason} -> {:error, reason}
          {:ok, final_env} ->
            typecheck_res =
              if Keyword.get(opts, :typecheck, true) do
                case Christine.Typechecker.check_module(desugared, final_env) do
                  :ok -> :ok
                  {:error, reason} -> {:error, {:type_error, reason}}
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
                e -> {:error, {:compiler_crash, e, __STACKTRACE__}}
              end
            end
        end
      end
    else
      err -> err
    end
  end

  def populate_local_env(%AST.Module{name: _mod_name, declarations: decls}, env, prefix \\ nil) do
    Enum.reduce_while(decls, {:ok, env}, fn decl, {:ok, acc} ->
      case decl do
        %AST.DeclValue{name: n, expr: e, type: t, tactics: tacs} ->
          n_full = if prefix, do: prefix <> "." <> n, else: n
          Christine.Debug.log("DEBUG: Defining #{n_full}")
          if tacs do
            case Christine.Tactics.solve_with_tactics(n_full, t, tacs, acc) do
              {:ok, term} ->
                {:cont, {:ok, %{acc | global_ctx: Map.put(acc.global_ctx, n_full, t), defs: Map.put(acc.defs, n_full, term), last_decl: n_full}}}
              {:error, reason} ->
                {:halt, {:error, {:tactic_error, n_full, reason}}}
            end
          else
            if e do
              ty = Christine.Typechecker.infer(acc, e)
              {:cont, {:ok, %{acc | defs: Map.put(acc.defs, n_full, e), global_ctx: Map.put(acc.global_ctx, n_full, ty), last_decl: n_full}}}
            else
              {:cont, {:ok, %{acc | ctx: [{n_full, t} | acc.ctx], last_decl: n_full}}}
            end
          end

        %AST.Inductive{} = ind ->
          n_full = if prefix, do: prefix <> "." <> ind.name, else: ind.name
          Christine.Debug.log("DEBUG: Defining Inductive #{n_full}")
          # Constructors also need to be prefixed
          ind_named = %{ind | name: n_full}
          new_env_map = Map.put(acc.env, n_full, ind_named)
          
          # Add constructors with both namespaced and short name?
          # Actually load_module_to_env should handle name_to_mod mapping
          new_defs = add_constructors(ind_named, acc.defs)
          new_ctx = add_constructors_to_ctx(ind_named, acc.ctx)
          {:cont, {:ok, %{acc | env: new_env_map, defs: new_defs, ctx: new_ctx, last_decl: n_full}}}

        {:module_start, _name} -> {:cont, {:ok, acc}}
        {:section_start, _name} -> {:cont, {:ok, acc}}

        {:command, :check_kw, expr} ->
          ty = try do Christine.Typechecker.infer(acc, expr) rescue e -> {:error, {:typechecker_crash, Exception.message(e)}} end
          Christine.Debug.log("DEBUG Check: #{AST.to_string(expr)} : #{AST.to_string(ty)}")
          {:cont, {:ok, acc}}

        {:command, :eval_kw, expr} ->
          res = try do Christine.Typechecker.normalize(acc, expr) rescue e -> {:error, {:eval_crash, Exception.message(e)}} end
          Christine.Debug.log("DEBUG Eval: #{AST.to_string(expr)} = #{AST.to_string(res)}")
          {:cont, {:ok, acc}}

        {:command, :print_kw, %AST.Var{name: name}} ->
          case List.keyfind(acc.ctx, name, 0) do
            nil -> Christine.Debug.log("DEBUG #{name} is not defined")
            {_, ty} ->
              term = Map.get(acc.defs, name)
              AST.print_declaration(name, ty, term)
          end
          {:cont, {:ok, acc}}

        {:proof, tacs} ->
          if acc.last_decl do
            n = acc.last_decl
            case List.keyfind(acc.ctx, n, 0) do
              {_, ty} ->
                case Christine.Tactics.solve_with_tactics(n, ty, tacs, acc) do
                  {:ok, term} -> {:cont, {:ok, %{acc | defs: Map.put(acc.defs, n, term)}}}
                  {:error, reason} -> {:halt, {:error, {:tactic_error, n, reason}}}
                end
              _ -> {:cont, {:ok, acc}}
            end
          else
            {:cont, {:ok, acc}}
          end

        _ -> {:cont, {:ok, acc}}
      end
    end)
  end

  def collect_local_names(%AST.Module{declarations: decls}, env, prefix \\ "local") do
    new_mapping = Enum.reduce(decls, env.name_to_mod, fn
      %AST.DeclValue{name: n}, acc -> Map.put(acc, n, prefix)
      %AST.DeclData{name: n, constructors: constrs}, acc ->
        acc2 = Map.put(acc, n, prefix)
        Enum.reduce(constrs, acc2, fn {cn, _, _}, a -> Map.put(a, cn, prefix) end)
      %AST.Inductive{name: n, constrs: constrs}, acc ->
        acc2 = Map.put(acc, n, prefix)
        Enum.reduce(constrs, acc2, fn {_, cn, _}, a -> Map.put(a, cn, prefix) end)
      _, acc -> acc
    end)
    %{env | name_to_mod: new_mapping}
  end

  def resolve_imports(%AST.Module{name: mod_name, declarations: decls}, env, opts) do
    loaded = Keyword.get(opts, :loaded, MapSet.new())
    if MapSet.member?(loaded, mod_name) do
      {:ok, env}
    else
      # We need to accumulate BOTH env and loaded set
      initial_state = {:ok, env, MapSet.put(loaded, mod_name)}
      
      res = with {:ok, env1, loaded1} <- maybe_load_implicit_acc("Coq", mod_name, env, initial_state),
                 {:ok, env2, loaded2} <- maybe_load_implicit_acc("Prelude", mod_name, env1, {:ok, env1, loaded1}) do
        
        Enum.reduce_while(decls, {:ok, env2, loaded2}, fn
          {:import, name}, {:ok, acc_env, acc_loaded} ->
            opts_with_loaded = Keyword.put(opts, :loaded, acc_loaded)
            case load_module_to_env(name, acc_env, opts_with_loaded) do
              {:ok, new_env} -> 
                # After loading, we need to know what was added to 'loaded'
                # But load_module_to_env doesn't return it. 
                # However, it MUST have added 'name' (and its deps).
                # We'll just assume it's in env now.
                {:cont, {:ok, new_env, MapSet.put(acc_loaded, name)}}
              {:error, reason} -> {:halt, {:error, {:failed_to_import, name, reason}}}
            end
          _, acc -> {:cont, acc}
        end)
      end

      case res do
        {:ok, final_env, _final_loaded} -> {:ok, final_env}
        err -> err
      end
    end
  end

  defp maybe_load_implicit_acc(target, current, env, {:ok, _prev_env, loaded_set}) do
    if target == current or current in ["Coq", "Prelude"] or MapSet.member?(loaded_set, target) do
      {:ok, env, loaded_set}
    else
      case load_module_to_env(target, env, loaded: loaded_set) do
        {:ok, new_env} -> {:ok, new_env, MapSet.put(loaded_set, target)}
        {:error, :module_not_found} -> {:ok, env, loaded_set}
        {:error, reason} -> {:error, reason}
      end
    end
  end

  def load_module_to_env(mod_name, env, opts \\ []) do
    loaded = Keyword.get(opts, :loaded, MapSet.new())
    if MapSet.member?(loaded, mod_name) do
       {:ok, env}
    else
      case find_module_path(mod_name) do
        {:ok, path} ->
          source = File.read!(path)
          new_opts = Keyword.put(opts, :loaded, MapSet.put(loaded, mod_name))
          try do
            with {:ok, tokens} <- Lexer.lex(source),
                 resolved <- Layout.resolve(tokens),
                 {:ok, %AST.Module{} = mod, _} <- Parser.parse(resolved),
                 {:ok, env_with_imports} <- resolve_imports(mod, env, new_opts) do
              
              env_with_locals = collect_local_names(mod, env_with_imports, mod_name)
              case populate_local_env(Desugar.desugar(mod, env_with_locals), env_with_locals, mod_name) do
                {:ok, new_env} -> {:ok, new_env}
                {:error, reason} -> {:error, reason}
              end
            else
              err -> {:error, err}
            end
          rescue
            e in ErlangError ->
              case e.original do
                {:error, reason} -> {:error, reason}
                _ -> {:error, {:compiler_crash, e, __STACKTRACE__}}
              end
            e -> {:error, {:compiler_crash, e, __STACKTRACE__}}
          catch
            {:error, reason} -> {:error, reason}
          end
        nil -> {:error, :module_not_found}
      end
    end
  end

  def find_module_path(mod_name) do
    filename = String.replace(mod_name, ".", "/") <> ".christine"
    
    # Try direct first
    paths = [
      "priv/christine/" <> filename,
      "test/christine/" <> filename
    ]
    
    case Enum.find(paths, &File.exists?/1) do
      path when is_binary(path) -> {:ok, path}
      nil ->
        # Try recursive search if not found directly
        short_name = hd(Enum.reverse(String.split(mod_name, "."))) <> ".christine"
        search_dirs = ["priv/christine", "test/christine"]
        
        Enum.find_value(search_dirs, fn dir ->
           if File.dir?(dir) do
             Path.wildcard("#{dir}/**/#{short_name}") |> List.first()
           else
             nil
           end
        end)
        |> case do
          nil -> nil
          path -> {:ok, path}
        end
    end
  end

  defp add_constructors(ind, defs) do
    Enum.reduce(ind.constrs, defs, fn {idx, name, ty}, acc ->
      term = make_constr_term(idx, ind, ty, [])
      acc
      |> Map.put(ind.name <> "." <> name, term)
      |> Map.put(name, term)
    end)
  end

  defp add_constructors_to_ctx(ind, ctx) do
    Enum.reduce(ind.constrs, ctx, fn {_, name, ty}, acc -> [{ind.name <> "." <> name, ty}, {name, ty} | acc] end)
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
