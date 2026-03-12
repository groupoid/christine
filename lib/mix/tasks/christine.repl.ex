defmodule Mix.Tasks.Christine.Repl do
  use Mix.Task

  alias Christine.{Lexer, Layout, Parser, Desugar, Typechecker, AST}


  @shortdoc "Christine interactive REPL with Tactics"
  def run(_) do
    IO.puts("🧊 Christine Theorem Prover version 0.3.11 [Coq 6.3 Syntax]\n" <>
            "Copyright (c) 2016-2026 Groupoid Infinity\n" <>
            "https://groupoid.github.io/christine/\n"
            )
    env = %Typechecker.Env{}

    paths = Path.wildcard("{priv,test}/christine/**/*.christine")

    env =
      Enum.reduce(paths, env, fn path, acc_env ->
        parts = Path.split(path)

        mod_parts =
          parts
          |> Enum.drop_while(&(&1 != "christine"))
          |> Enum.drop(1)
          |> List.update_at(-1, &Path.rootname/1)

        mod_name = Enum.join(mod_parts, ".")

        case load_module(mod_name, acc_env) do
          {:ok, new_env} ->
            IO.puts("Loaded: #{mod_name}")
            new_env

          _ ->
            acc_env
        end
      end)

    loop(env, nil)
  end

  defp loop(env, proof_state) do
    prompt = if proof_state, do: "Proof> ", else: "Christine> "
    input = IO.gets(prompt)

    case input do
      nil ->
        :ok

      ":q\n" ->
        :ok

      "\n" ->
        loop(env, proof_state)

      _ ->
        input = String.trim(input)

        cond do
          String.starts_with?(input, ~w[Theorem Lemma Corollary]) ->
            case start_proof(input, env) do
              {:ok, ps, new_env} ->
                loop(new_env, ps)

              {:error, err} ->
                IO.puts("Error: #{inspect(err)}")
                loop(env, nil)
            end

          # Print name. — show stored term and type (Coq 6.3 style)
          Regex.match?(~r/^Print\s+\S+\.?$/, input) ->
            name = input |> String.replace_prefix("Print", "") |> String.trim() |> String.trim_trailing(".")

            # Check active proof session first
            if proof_state && proof_state.name == name do
              ty_val = if proof_state.goals == [], do: proof_state.target, else: proof_state.target
              Christine.AST.print_declaration(name, ty_val, proof_state.proof_term)
            else
              # Check env
              case List.keyfind(env.ctx, name, 0) do
                {_, ty} ->
                  term = Map.get(env.defs, name)
                  Christine.AST.print_declaration(name, ty, term)

                _ ->
                  IO.puts("#{name} is not defined")
              end
            end

            loop(env, proof_state)

          proof_state != nil ->
            handle_tactic(input, env, proof_state)

          true ->
            try do
              case eval(input, env) do
                {:ok, result} ->
                  str = try do
                    AST.to_string(result)
                  rescue
                    _ -> inspect(result, limit: 10, pretty: false)
                  end
                  IO.puts("Result: #{str}")

                {:error, {:eval_crash, msg}} ->
                  IO.puts("Error: #{msg}")

                {:error, err} ->
                  IO.puts("Error: #{inspect(err, limit: 5)}")
              end
            rescue
              e ->
                IO.puts("Error: #{Exception.message(e)}")
            end
            loop(env, nil)
        end
    end
  end

  defp start_proof(input, env) do
    with {:ok, tokens} <- Lexer.lex(input),
         resolved <- Layout.resolve(tokens),
         {:ok, decls, _} <- Parser.parse_declaration(resolved),
         # parse_declaration may return a list of decls since parse_def_theorem change
         [%AST.DeclValue{name: name, type: target_syn} | _] <- List.wrap(decls) do

      IO.puts("Proof started for #{name}")
      desugared_target = Desugar.desugar_expression(target_syn, env)
      ps = Christine.Tactics.start_proof(name, desugared_target, env)
      # Register the theorem in the context immediately so it is visible to Print.
      new_env = %{env | ctx: [{name, desugared_target} | env.ctx]}
      {:ok, ps, new_env}
    else
      err -> {:error, err}
    end
  end

  defp handle_tactic(input, env, ps) do
    input = String.trim(input)

    case input do
      "Qed." ->
        if ps.goals == [] do
          IO.puts("Proof complete!")
          # Persist the proof term if we have one.
          new_env = if ps.proof_term do
            %{env | defs: Map.put(env.defs, ps.name, ps.proof_term)}
          else
            env
          end
          loop(new_env, nil)
        else
          IO.puts("Error: Proof not finished. Remaining goals: #{length(ps.goals)}")
          loop(env, ps)
        end

      _ ->
        case Christine.Tactics.apply_tactic(ps, input) do
          {:ok, new_ps} ->
            if new_ps.goals == [] do
              IO.puts("All goals solved!")
            else
              IO.puts("#{length(new_ps.goals)} goals remaining.")
            end

            loop(env, new_ps)

          {:error, reason, _} ->
            IO.puts("Error: #{inspect(reason)}")
            loop(env, ps)
        end
    end
  end

  defp load_module(mod_name, env) do
    # Delegate to the Compiler's module loader which properly populates
    # both ctx (types) and defs (expressions) including for constructors.
    case Christine.Compiler.load_module_to_env(mod_name, env, []) do
      {:ok, new_env} -> {:ok, new_env}
      {:error, :module_not_found} -> {:error, :module_not_found}
      {:error, reason} -> {:error, reason}
    end
  end


  defp eval(input, env) do
    input = String.trim(input)

    if input == "" do
      {:error, :empty_input}
    else
      try do
        with {:ok, tokens} <- Lexer.lex(input),
             resolved <- Layout.resolve(tokens),
             {:ok, expr, _} <- Parser.parse_expression(resolved) do
          desugared = Desugar.desugar_expression(expr, env)
          {:ok, Typechecker.normalize(env, desugared)}
        else
          err -> {:error, err}
        end
      rescue
        e -> {:error, {:eval_crash, Exception.message(e)}}
      end
    end
  end
end
