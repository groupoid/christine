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
         {:ok, %AST.DeclValue{name: name, binders: _params, type: target_syn}, _} <-
           Parser.parse_declaration(resolved) do
      # In unified parser, theorems might result in a Pi directly or have params.
      # parse_declaration forTheorem name : type. returns DeclValue with type=type.

      IO.puts("Proof started for #{name}")
      # Desugar target type
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
    path1 = "priv/christine/" <> String.replace(mod_name, ".", "/") <> ".christine"
    path2 = "test/christine/" <> String.replace(mod_name, ".", "/") <> ".christine"
    path = if File.exists?(path1), do: path1, else: path2

    if File.exists?(path) do
      source = File.read!(path)

      with {:ok, tokens} <- Lexer.lex(source),
           resolved <- Layout.resolve(tokens),
           {:ok, %AST.Module{} = mod, _} <- Parser.parse(resolved) do
        {new_defs, new_types} =
          Enum.reduce(mod.declarations, {env.defs, env.env}, fn
            %AST.DeclValue{} = v, {d_acc, t_acc} ->
              current_env = %{env | defs: d_acc, env: t_acc}
              desugared_v = Desugar.desugar_decl(v, current_env)
              {Map.put(d_acc, desugared_v.name, desugared_v.expr), t_acc}

            %AST.DeclData{} = data, {d_acc, t_acc} ->
              current_env = %{env | defs: d_acc, env: t_acc}
              desugared_ind = Desugar.desugar_decl(data, current_env)
              new_t_acc = Map.put(t_acc, desugared_ind.name, desugared_ind)
              new_d_acc = add_constructors(desugared_ind, d_acc)
              {new_d_acc, new_t_acc}

            _, acc ->
              acc
          end)

        {:ok, %{env | defs: new_defs, env: new_types}}
      else
        err -> {:error, err}
      end
    else
      {:error, :module_not_found}
    end
  end

  defp add_constructors(ind, defs) do
    Enum.reduce(ind.constrs, defs, fn {idx, name, ty}, acc ->
      term = make_constr_term(idx, ind, ty, [])
      Map.put(acc, name, term)
    end)
  end

  def make_constr_term(idx, ind, ty, vars) do
    case ty do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        name = if x == "_", do: "a#{length(vars)}", else: x
        %AST.Lam{name: name, domain: a, body: make_constr_term(idx, ind, b, [name | vars])}

      _ ->
        args = Enum.reverse(vars) |> Enum.map(fn n -> %AST.Var{name: n} end)
        %AST.Constr{index: idx, inductive: ind, args: args}
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
