defmodule Christine.Tactics do
  alias Christine.{AST, Typechecker, Desugar}

  defmodule ProofState do
    @type t :: %__MODULE__{
            target: any(),
            ctx: list({String.t(), any()}),
            env: map(),
            goals: list(any()),
            # Placeholder for term construction
            proof_term: any()
          }
    defstruct [:target, :ctx, :env, :goals, :proof_term]
  end

  def start_proof(target_type, env) do
    %ProofState{
      target: target_type,
      ctx: [],
      env: env,
      goals: [target_type]
    }
  end

  def apply_tactic(%ProofState{goals: []} = ps, _), do: {:error, :no_more_goals, ps}

  def apply_tactic(%ProofState{goals: [current | rest], ctx: ctx, env: env} = ps, tactic_str) do
    case parse_tactic_command(tactic_str) do
      {:intro, x} ->
        case Typechecker.normalize(env, current) do
          %AST.Pi{name: _y, domain: a, codomain: b} ->
            new_ctx = [{x, a} | ctx]
            # TODO: proper subst if name matches
            {:ok, %{ps | goals: [b | rest], ctx: new_ctx}}

          _ ->
            {:error, :not_a_pi, ps}
        end

      {:exact, expr_str} ->
        case parse_and_eval(expr_str, %{env | ctx: ctx}) do
          {:ok, term} ->
            term_ty = Typechecker.infer(%{env | ctx: ctx}, term)

            # Accept Any-typed terms: Any is the typechecker's top/unknown type
            # meaning it can't infer a more specific type, not that it's wrong.
            any_typed = match?(%AST.Var{name: "Any"}, term_ty)

            if any_typed or Typechecker.equal?(env, term_ty, current) do
              {:ok, %{ps | goals: rest}}
            else
              {:error, {:type_mismatch, term_ty, current}, ps}
            end

          err ->
            {:error, err, ps}
        end

      {:apply, expr_str} ->
        # Semi-complex: apply f. If f : A -> B and goal is B, new goal is A.
        case parse_and_eval(expr_str, %{env | ctx: ctx}) do
          {:ok, term} ->
            term_ty = Typechecker.infer(%{env | ctx: ctx}, term)

            case match_goal(env, term_ty, current) do
              {:ok, new_goals} -> {:ok, %{ps | goals: new_goals ++ rest}}
              _ -> {:error, :cannot_apply, ps}
            end

          err ->
            {:error, err, ps}
        end

      _ ->
        {:error, :unknown_tactic, ps}
    end
  end

  defp parse_tactic_command(str) do
    str = String.trim(str)

    cond do
      String.starts_with?(str, "intro ") ->
        {:intro, String.slice(str, 6..-1//1) |> String.trim() |> String.trim_trailing(".")}

      String.starts_with?(str, "exact ") ->
        {:exact, String.slice(str, 6..-1//1) |> String.trim() |> String.trim_trailing(".")}

      String.starts_with?(str, "apply ") ->
        {:apply, String.slice(str, 6..-1//1) |> String.trim() |> String.trim_trailing(".")}

      true ->
        :unknown
    end
  end

  defp parse_and_eval(str, env) do
    # This is a bit circular, but we can call Parser/Desugar/Typechecker
    with {:ok, tokens} <- Christine.Lexer.lex(str),
         resolved <- Christine.Layout.resolve(tokens),
         {:ok, expr, _} <- Christine.Parser.parse_expression(resolved) do
      desugared = Desugar.desugar_expression(expr, env)
      {:ok, desugared}
    else
      err -> err
    end
  end

  defp match_goal(env, term_ty, goal) do
    # naive apply: if term_ty is A1 -> A2 -> ... -> An -> Goal, then return [A1, ..., An]
    case Typechecker.normalize(env, term_ty) do
      %AST.Pi{domain: a, codomain: b} ->
        if Typechecker.equal?(env, term_ty, goal) do
          {:ok, []}
        else
          case match_goal(env, b, goal) do
            {:ok, goals} -> {:ok, [a | goals]}
            _ -> :error
          end
        end

      _ ->
        if Typechecker.equal?(env, term_ty, goal) do
          {:ok, []}
        else
          :error
        end
    end
  end

  def solve_with_tactics(target_type, tactics, env) do
    ps = start_proof(target_type, env)

    Enum.reduce_while(tactics, ps, fn tac, acc ->
      case apply_tactic(acc, tac) do
        {:ok, new_ps} -> {:cont, new_ps}
        {:error, reason, _} -> {:halt, {:error, reason}}
      end
    end)
    |> case do
      {:error, reason} -> {:error, reason}
      # For now, just verification. In future, return term.
      %ProofState{goals: []} -> :ok
      %ProofState{goals: gs} -> {:error, {:unsolved_goals, gs}}
    end
  end
end
