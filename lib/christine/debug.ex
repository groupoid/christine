defmodule Christine.Debug do
  def log(msg, _opts \\ []), do: IO.puts(msg)

  def info(msg, opts \\ []) do
    if Application.get_env(:christine, :verbose, false) do
      indent = String.duplicate(" ", opts[:indent] || 0)
      log("#{indent}#{IO.ANSI.cyan()}#{msg}#{IO.ANSI.reset()}", opts)
    end
  end

  def success(msg, opts \\ []) do
    if Application.get_env(:christine, :verbose, false) do
      indent = String.duplicate(" ", opts[:indent] || 0)
      log("#{indent}#{IO.ANSI.green()}#{msg}#{IO.ANSI.reset()}", opts)
    end
  end

  def warn(msg, opts \\ []) do
    if Application.get_env(:christine, :verbose, false) do
      indent = String.duplicate(" ", opts[:indent] || 0)
      log("#{indent}#{IO.ANSI.yellow()}#{msg}#{IO.ANSI.reset()}", opts)
    end
  end

  def error(msg, opts \\ []) do
    if Application.get_env(:christine, :verbose, false) do
      indent = String.duplicate(" ", opts[:indent] || 0)
      log("#{indent}#{IO.ANSI.red()}#{msg}#{IO.ANSI.reset()}", opts)
    end
  end

  def delta(msg, opts \\ []) do
    if Application.get_env(:christine, :verbose, false) do
      indent = String.duplicate(" ", opts[:indent] || 4)
      log("#{indent}#{IO.ANSI.cyan()}#{IO.ANSI.faint()}Δ #{msg}#{IO.ANSI.reset()}", opts)
    end
  end

  def print(msg, opts \\ []) do
    indent_size = opts[:indent] || 4
    indent = if Application.get_env(:christine, :verbose, false), do: String.duplicate(" ", indent_size), else: ""
    log("#{indent}#{msg}", opts)
  end

  def print_term(label, term) do
    print("#{IO.ANSI.bright()}#{label}:#{IO.ANSI.reset()}\n#{Christine.AST.to_string(term)}", indent: 0)
  end
end
