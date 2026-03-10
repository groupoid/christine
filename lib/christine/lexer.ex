defmodule Christine.Lexer do
  @moduledoc """
  Lexer for Christine (Coq 8.2-like syntax).
  """

  def lex(input) do
    lex(String.to_charlist(input), 1, 1, [])
  end

  defp lex([], _line, _col, acc), do: {:ok, Enum.reverse(acc)}

  defp lex([?\n | rest], line, _col, acc), do: lex(rest, line + 1, 1, acc)
  defp lex([?\s | rest], line, col, acc), do: lex(rest, line, col + 1, acc)
  defp lex([?\r | rest], line, col, acc), do: lex(rest, line, col, acc)
  defp lex([?\t | rest], line, col, acc), do: lex(rest, line, col + 4, acc)

  # Comments (Coq style (* *) or -- for now, keeping -- to avoid breaking logic)
  defp lex([?(, ?* | rest], line, col, acc) do
    {rest2, line2, col2} = skip_comment(rest, line, col + 2)
    lex(rest2, line2, col2, acc)
  end

  defp lex([?-, ?- | rest], line, col, acc) do
    rest2 = Enum.drop_while(rest, fn c -> c != ?\n end)
    lex(rest2, line, col, acc)
  end

  # Arrow, Backslash
  defp lex([?-, ?> | rest], line, col, acc),
    do: lex(rest, line, col + 2, [{:arrow, line, col} | acc])

  defp lex([?\\ | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:backslash, line, col} | acc])

  # Special symbols
  defp lex([?( | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:left_paren, line, col} | acc])

  defp lex([?) | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:right_paren, line, col} | acc])

  defp lex([?[ | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:left_square, line, col} | acc])

  defp lex([?] | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:right_square, line, col} | acc])

  defp lex([?{ | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:left_brace, line, col} | acc])

  defp lex([?} | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:right_brace, line, col} | acc])

  defp lex([?| | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:pipe, line, col} | acc])

  defp lex([?., ?. | rest], line, col, acc),
    do: lex(rest, line, col + 2, [{:dotdot, line, col} | acc])

  defp lex([?. | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:dot, line, col} | acc])

  defp lex([?, | rest], line, col, acc), do: lex(rest, line, col + 1, [{:comma, line, col} | acc])

  defp lex([?; | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:semicolon, line, col} | acc])

  # Numbers
  defp lex([c | rest], line, col, acc) when c >= ?0 and c <= ?9 do
    {num_chars, rest2} = take_while([c | rest], fn x -> x >= ?0 and x <= ?9 end)
    num = List.to_integer(num_chars)
    lex(rest2, line, col + length(num_chars), [{:number, line, col, num} | acc])
  end

  # Identifiers and Keywords
  defp lex([c | rest], line, col, acc)
       when (c >= ?a and c <= ?z) or (c >= ?A and c <= ?Z) or c == ?_ do
    {ident_chars, rest2} = take_ident([c | rest])
    ident = List.to_string(ident_chars)

    case ident do
      "Module" ->
        lex(rest2, line, col + String.length(ident), [{:module, line, col} | acc])

      "Definition" ->
        lex(rest2, line, col + String.length(ident), [{:definition, line, col} | acc])

      "Theorem" ->
        lex(rest2, line, col + String.length(ident), [{:theorem, line, col} | acc])

      "Proof" ->
        lex(rest2, line, col + String.length(ident), [{:proof_kw, line, col} | acc])

      "Qed" ->
        lex(rest2, line, col + String.length(ident), [{:qed, line, col} | acc])

      "Inductive" ->
        lex(rest2, line, col + String.length(ident), [{:inductive_kw, line, col} | acc])

      "forall" ->
        lex(rest2, line, col + String.length(ident), [{:forall, line, col} | acc])

      "fun" ->
        lex(rest2, line, col + String.length(ident), [{:fun_kw, line, col} | acc])

      "match" ->
        lex(rest2, line, col + String.length(ident), [{:match_kw, line, col} | acc])

      "with" ->
        lex(rest2, line, col + String.length(ident), [{:with_kw, line, col} | acc])

      "end" ->
        lex(rest2, line, col + String.length(ident), [{:end_kw, line, col} | acc])

      "Type" ->
        lex(rest2, line, col + String.length(ident), [{:type_kw, line, col} | acc])

      "Prop" ->
        lex(rest2, line, col + String.length(ident), [{:prop_kw, line, col} | acc])

      "import" ->
        lex(rest2, line, col + String.length(ident), [{:import, line, col} | acc])

      "let" ->
        lex(rest2, line, col + String.length(ident), [{:let, line, col} | acc])

      "in" ->
        lex(rest2, line, col + String.length(ident), [{:in, line, col} | acc])

      _ ->
        lex(rest2, line, col + String.length(ident), [{:ident, line, col, ident} | acc])
    end
  end

  # Operators
  defp lex([c | rest], line, col, acc)
       when c in [?=, ?|, ?:, ?<, ?>, ?+, ?-, ?*, ?/, ?%, ?^, ?&, ?!, ?$, ?#, ?@, ??] do
    {op_chars, rest2} =
      take_while([c | rest], fn x ->
        x in [?=, ?|, ?:, ?<, ?>, ?+, ?-, ?*, ?/, ?%, ?^, ?&, ?!, ?$, ?#, ?@, ??]
      end)

    op = List.to_string(op_chars)

    token =
      case op do
        ":=" -> {:assign, line, col}
        "=>" -> {:fat_arrow, line, col}
        "|" -> {:pipe, line, col}
        ":" -> {:colon, line, col}
        "->" -> {:arrow, line, col}
        _ -> {:operator, line, col, op}
      end

    lex(rest2, line, col + String.length(op), [token | acc])
  end

  # Strings
  defp lex([?" | rest], line, col, acc) do
    {str_chars, rest2} = take_string(rest)

    lex(rest2, line, col + length(str_chars) + 2, [
      {:string, line, col, List.to_string(str_chars)} | acc
    ])
  end

  defp lex([c | _rest], line, col, _acc) do
    {:error, "Unexpected character: #{<<c::utf8>>} at #{line}:#{col}"}
  end

  defp skip_comment([?*, ?) | rest], line, col), do: {rest, line, col + 2}
  defp skip_comment([?\n | rest], line, _col), do: skip_comment(rest, line + 1, 1)
  defp skip_comment([_ | rest], line, col), do: skip_comment(rest, line, col + 1)
  defp skip_comment([], line, col), do: {[], line, col}

  defp take_ident([c | rest])
       when (c >= ?a and c <= ?z) or (c >= ?A and c <= ?Z) or (c >= ?0 and c <= ?9) or c == ?_ or
              c == ?' do
    {rest_ident, rest2} = take_ident(rest)
    {[c | rest_ident], rest2}
  end

  defp take_ident(rest), do: {[], rest}

  defp take_while([], _), do: {[], []}

  defp take_while([c | rest], f) do
    if f.(c) do
      {matched, remaining} = take_while(rest, f)
      {[c | matched], remaining}
    else
      {[], [c | rest]}
    end
  end

  defp take_string([?" | rest]), do: {[], rest}

  defp take_string([?\\, c | rest]) do
    {s, r} = take_string(rest)
    {[?\\, c | s], r}
  end

  defp take_string([c | rest]) do
    {s, r} = take_string(rest)
    {[c | s], r}
  end

  defp take_string([]), do: {[], []}
end
