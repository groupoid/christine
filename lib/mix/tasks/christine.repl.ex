defmodule Mix.Tasks.Christine.Repl do
  use Mix.Task

  alias Christine.{Lexer, Layout, Parser, Desugar, Typechecker, AST}

  defmodule ProofState do
    defstruct [:target, :ctx, :env, :solved, :goals]
  end

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
          String.starts_with?(input, "Theorem") ->
            case start_proof(input, env) do
              {:ok, ps} ->
                loop(env, ps)

              {:error, err} ->
                IO.puts("Error: #{inspect(err)}")
                loop(env, nil)
            end

          proof_state != nil ->
            handle_tactic(input, env, proof_state)

          true ->
            case eval(input, env) do
              {:ok, result} ->
                IO.puts("Result: #{AST.to_string(result)}")
                loop(env, nil)

              {:error, err} ->
                IO.puts("Error: #{inspect(err)}")
                loop(env, nil)
            end
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
      {:ok, Christine.Tactics.start_proof(desugared_target, env)}
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
          loop(env, nil)
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
      with {:ok, tokens} <- Lexer.lex(input),
           resolved <- Layout.resolve(tokens),
           {:ok, expr, _} <- Parser.parse_expression(resolved) do
        desugared = Desugar.desugar_expression(expr, env)
        {:ok, Typechecker.normalize(env, desugared)}
      else
        err -> {:error, err}
      end
    end
  end
end
