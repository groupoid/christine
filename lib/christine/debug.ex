defmodule Christine.Debug do
  def log(msg, opts \\ []) do
    verbose = opts[:verbose] || Application.get_env(:christine, :verbose, false)
    if verbose do
      IO.puts(msg)
    end
  end

  def print_term(label, term, opts \\ []) do
    verbose = opts[:verbose] || Application.get_env(:christine, :verbose, false)
    if verbose do
      IO.puts("#{label}:\n#{Christine.AST.to_string(term)}")
    end
  end
end
