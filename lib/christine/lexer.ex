defmodule Christine.Lexer do
  @moduledoc """
  Lexer for Christine (Coq 6.3-like syntax).
  """

  def lex(input) do
    normalized =
      input
      |> String.replace("\u2019", "'")
      |> String.replace("\u2212", "-")
      |> String.replace("\u2013", "-")
      |> String.replace("\u2014", "-")
      |> String.replace("\u02DC", "~")
      |> String.replace("\u02D8", "~") # Small tilde
      |> String.replace("\u00A0", " ")

    lex(String.to_charlist(normalized), 1, 1, [])
  end

  defp lex([], _line, _col, acc), do: {:ok, Enum.reverse(acc)}

  defp lex([?\n | rest], line, _col, acc), do: lex(rest, line + 1, 1, acc)
  defp lex([?\s | rest], line, col, acc), do: lex(rest, line, col + 1, acc)
  defp lex([?\r | rest], line, col, acc), do: lex(rest, line, col, acc)
  defp lex([?\t | rest], line, col, acc), do: lex(rest, line, col + 4, acc)
  # Smart quotes and dashes from PDF copy-paste (mapping to ASCII)
  defp lex([0x2019 | rest], line, col, acc), do: lex(rest, line, col + 1, [{:ident, line, col, "'"} | acc])
  defp lex([0x02DC | rest], line, col, acc), do: lex(rest, line, col + 1, [{:operator, line, col, "~"} | acc])
  defp lex([0x2212 | rest], line, col, acc), do: lex(rest, line, col + 1, [{:operator, line, col, "-"} | acc])
  defp lex([0x2013 | rest], line, col, acc), do: lex(rest, line, col + 1, [{:operator, line, col, "-"} | acc])
  defp lex([0x2014 | rest], line, col, acc), do: lex(rest, line, col + 1, [{:operator, line, col, "-"} | acc])

  # Comments (Coq style (* *) or -- for now, keeping -- to avoid breaking logic)
  defp lex([?(, ?* | rest], line, col, acc) do
    {rest2, line2, col2} = skip_comment(rest, line, col + 2, 1)
    lex(rest2, line2, col2, acc)
  end

  defp lex([?-, ?- | rest], line, col, acc) do
    rest2 = Enum.drop_while(rest, fn c -> c != ?\n end)
    lex(rest2, line, col, acc)
  end

  # Special symbols and multi-char operators
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

  defp lex([?, | rest], line, col, acc), do: lex(rest, line, col + 1, [{:comma, line, col} | acc])

  defp lex([?; | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:semicolon, line, col} | acc])

  defp lex([?., ?. | rest], line, col, acc),
    do: lex(rest, line, col + 2, [{:operator, line, col, ".."} | acc])

  defp lex([?. | rest], line, col, acc),
    do: lex(rest, line, col + 1, [{:dot, line, col} | acc])

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

    token =
      case ident do
        "Module" -> {:module, line, col}
        "Section" -> {:section, line, col}
        "Variable" -> {:variable, line, col}
        "Hypothesis" -> {:hypothesis, line, col}
        "Definition" -> {:definition, line, col}
        "definition" -> {:definition, line, col}
        "Theorem" -> {:theorem, line, col}
        "theorem" -> {:theorem, line, col}
        "Axiom" -> {:axiom, line, col}
        "axiom" -> {:axiom, line, col}
        "Parameter" -> {:axiom, line, col}
        "Conjecture" -> {:axiom, line, col}
        "Lemma" -> {:lemma, line, col}
        "Remark" -> {:remark, line, col}
        "Fact" -> {:fact, line, col}
        "Fixpoint" -> {:fixpoint, line, col}
        "Notation" -> {:notation, line, col}
        "Proof" -> {:proof_kw, line, col}
        "Qed" -> {:qed, line, col}
        "Inductive" -> {:inductive_kw, line, col}
        "forall" -> {:forall, line, col}
        "exists" -> {:exists, line, col}
        "fun" -> {:fun_kw, line, col}
        "match" -> {:match_kw, line, col}
        "with" -> {:with_kw, line, col}
        "end" -> {:end_kw, line, col}
        "Type" -> {:type_kw, line, col}
        "Set" -> {:type_kw, line, col}
        "Prop" -> {:prop_kw, line, col}
        "import" -> {:import, line, col}
        "Require" -> {:require, line, col}
        "Import" -> {:import_kw, line, col}
        "Check" -> {:check_kw, line, col}
        "Print" -> {:print_kw, line, col}
        "Eval" -> {:eval_kw, line, col}
        "Search" -> {:search_kw, line, col}
        "let" -> {:let, line, col}
        "in" -> {:in, line, col}
        "if" -> {:if_kw, line, col}
        "then" -> {:then_kw, line, col}
        "else" -> {:else_kw, line, col}
        _ -> {:ident, line, col, ident}
      end

    lex(rest2, line, col + String.length(ident), [token | acc])
  end

  # Operators
  defp lex([?-, ?> | rest], line, col, acc), do: lex(rest, line, col + 2, [{:arrow, line, col} | acc])
  defp lex([0x2212, ?> | rest], line, col, acc), do: lex(rest, line, col + 2, [{:arrow, line, col} | acc])
  defp lex([?-, ?\s, ?> | rest], line, col, acc), do: lex(rest, line, col + 3, [{:arrow, line, col} | acc])
  defp lex([0x2212, ?\s, ?> | rest], line, col, acc), do: lex(rest, line, col + 3, [{:arrow, line, col} | acc])

  defp lex([c | rest], line, col, acc)
       when c in [?=, ?|, ?:, ?<, ?>, ?+, ?-, ?*, ?/, ?%, ?^, ?&, ?!, ?$, ?#, ?@, ??, ?\\, ?~] do
    {op_chars, rest2} =
      take_while([c | rest], fn x ->
        x in [?=, ?|, ?:, ?<, ?>, ?+, ?-, ?*, ?/, ?%, ?^, ?&, ?!, ?$, ?#, ?@, ??, ?\\, ?~]
      end)

    op = List.to_string(op_chars)

    token =
      case op do
        ":=" -> {:assign, line, col}
        "=>" -> {:fat_arrow, line, col}
        "|" -> {:pipe, line, col}
        ":" -> {:colon, line, col}
        "->" -> {:arrow, line, col}
        "<-" -> {:back_arrow, line, col}
        "<->" -> {:iff, line, col}
        "\\/" -> {:or_kw, line, col}
        "/\\" -> {:and_kw, line, col}
        "::" -> {:cons, line, col}
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

  defp skip_comment(rest, line, col, depth)
  defp skip_comment(rest, line, col, 0), do: {rest, line, col}

  defp skip_comment([?(, ?* | rest], line, col, depth),
    do: skip_comment(rest, line, col + 2, depth + 1)

  defp skip_comment([?*, ?) | rest], line, col, depth),
    do: skip_comment(rest, line, col + 2, depth - 1)

  defp skip_comment([?\n | rest], line, _col, depth), do: skip_comment(rest, line + 1, 1, depth)
  defp skip_comment([_ | rest], line, col, depth), do: skip_comment(rest, line, col + 1, depth)
  defp skip_comment([], line, col, _depth), do: {[], line, col}

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
