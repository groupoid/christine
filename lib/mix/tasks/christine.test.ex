defmodule Mix.Tasks.Christine.Test do
  use Mix.Task

  @shortdoc "Run Christine tests"
  def run(args) do
    {opts, remaining, _} = OptionParser.parse(args, switches: [verbose: :boolean])
    if opts[:verbose], do: Application.put_env(:christine, :verbose, true)

    IO.puts("#{IO.ANSI.bright()}Running Christine tests...#{IO.ANSI.reset()}")
    start_time = System.monotonic_time()

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
        IO.puts(
          "#{IO.ANSI.cyan()}⚙#{IO.ANSI.reset()} Testing #{IO.ANSI.bright()}#{file}#{IO.ANSI.reset()}... "
        )

        source = File.read!(file)
        mod_name = Path.basename(file, ".christine")

        try do
          case Christine.Compiler.compile_module(source,
                 source_path: file,
                 verbose: !!opts[:verbose]
               ) do
            {:ok, mod, _bin} ->
              IO.puts("#{IO.ANSI.green()}✓ OK#{IO.ANSI.reset()} (#{mod})")
              {:ok, file}

            {:error, reason} ->
              IO.puts("#{IO.ANSI.red()}✗ ERROR#{IO.ANSI.reset()}(#{mod_name})")
              print_error(reason, 2)
              {:error, file}
          end
        rescue
          e ->
            IO.puts("#{IO.ANSI.red()}✗ FAILED#{IO.ANSI.reset()}(#{mod_name})")

            if Application.get_env(:christine, :verbose) do
              IO.puts(Exception.format(:error, e, __STACKTRACE__))
            else
              IO.puts(
                "    #{IO.ANSI.red()}Internal Error:#{IO.ANSI.reset()} #{Exception.message(e)}. Use --verbose for details."
              )
            end

            {:error, file}
        end
      end)

    end_time = System.monotonic_time()
    duration = System.convert_time_unit(end_time - start_time, :native, :millisecond) / 1000

    successes = Enum.count(results, &match?({:ok, _}, &1))
    failures = Enum.count(results, &match?({:error, _}, &1))
    total = length(results)

    IO.puts("\n#{String.duplicate("─", 40)}")
    IO.puts("#{IO.ANSI.bright()}Test Summary:#{IO.ANSI.reset()}")
    IO.puts("  Total:     #{total}")
    IO.puts("  #{IO.ANSI.green()}Success:   #{successes}#{IO.ANSI.reset()}")

    if failures == 0 do
      IO.puts("  Failures:  #{failures}")
    else
      IO.puts("  #{IO.ANSI.red()}Failures:  #{failures}#{IO.ANSI.reset()}")
    end

    IO.puts("  Duration:  #{Float.round(duration, 2)}s")
    IO.puts("#{String.duplicate("─", 40)}")

    if failures > 0 do
      exit({:shutdown, 1})
    end
  end

  defp print_error(reason, indent) do
    prefix = String.duplicate("  ", indent)

    case reason do
      {:tactic_error, decl, r} ->
        IO.puts("#{prefix}#{IO.ANSI.red()}Tactic error#{IO.ANSI.reset()} in #{decl}:")
        print_error(r, indent + 1)

      {:type_error, r} ->
        IO.puts("#{prefix}#{IO.ANSI.red()}Type error:#{IO.ANSI.reset()}")
        print_error(r, indent + 1)

      {:failed_to_import, mod, r} ->
        IO.puts("#{prefix}#{IO.ANSI.red()}Failed to import#{IO.ANSI.reset()} #{mod}:")
        print_error(r, indent + 1)

      {:failed_to_load_implicit, mod, r} ->
        IO.puts(
          "#{prefix}#{IO.ANSI.red()}Failed to load implicit prelude#{IO.ANSI.reset()} #{mod}:"
        )

        print_error(r, indent + 1)

      {:compiler_crash, e, stack} ->
        IO.puts("#{prefix}#{IO.ANSI.red()}Compiler crashed:#{IO.ANSI.reset()} #{inspect(e)}")

        if Application.get_env(:christine, :verbose) do
          IO.puts(Exception.format(:error, e, stack))
        end

      r ->
        IO.puts("#{prefix}#{inspect(r)}")
    end
  end
end
