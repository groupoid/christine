defmodule Mix.Tasks.Christine.Test do
  use Mix.Task

  @shortdoc "Run Christine tests"
  def run(args) do
    {opts, remaining, _} = OptionParser.parse(args, switches: [verbose: :boolean])
    if opts[:verbose], do: Application.put_env(:christine, :verbose, true)

    IO.puts("Running Christine tests...")

    test_files =
      if remaining != [] do
        Enum.flat_map(remaining, fn arg ->
          if File.dir?(arg), do: Path.wildcard("#{arg}/**/*.christine"), else: [arg]
        end)
      else
        Path.wildcard("test/christine/**/*.christine")
      end

    results =
      Enum.map(test_files, fn file ->
        IO.puts("  Testing #{file}... ")
        source = File.read!(file)
        mod_name = Path.basename(file, ".christine")

        try do
          case Christine.Compiler.compile_module(source, source_path: file, verbose: !!opts[:verbose]) do
            {:ok, mod, _bin} ->
              IO.puts("OK (#{mod})")
              :ok

            {:error, reason} ->
              IO.puts("ERROR(#{mod_name})")
              print_error(reason, 1)
              :error
          end
        rescue
          e ->
            IO.puts("FAILED(#{mod_name})")
            if Application.get_env(:christine, :verbose) do
               IO.puts(Exception.format(:error, e, __STACKTRACE__))
            else
               IO.puts("  Internal Error: #{Exception.message(e)}. Use --verbose for details.")
            end
            :error
        end
      end)

    if Enum.any?(results, fn r -> r == :error end) do
      exit({:shutdown, 1})
    end
  end

  defp print_error(reason, indent) do
    prefix = String.duplicate("  ", indent)
    case reason do
      {:tactic_error, decl, r} ->
        IO.puts("#{prefix}Tactic error in #{decl}:")
        print_error(r, indent + 1)
      {:type_error, r} ->
        IO.puts("#{prefix}Type error:")
        print_error(r, indent + 1)
      {:failed_to_import, mod, r} ->
        IO.puts("#{prefix}Failed to import #{mod}:")
        print_error(r, indent + 1)
      {:failed_to_load_implicit, mod, r} ->
        IO.puts("#{prefix}Failed to load implicit prelude #{mod}:")
        print_error(r, indent + 1)
      {:compiler_crash, e, stack} ->
        IO.puts("#{prefix}Compiler crashed: #{inspect(e)}")
        if Application.get_env(:christine, :verbose) do
          IO.puts(Exception.format(:error, e, stack))
        end
      r ->
        IO.puts("#{prefix}#{inspect(r)}")
    end
  end
end
