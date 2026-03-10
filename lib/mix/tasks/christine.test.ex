defmodule Mix.Tasks.Christine.Test do
  use Mix.Task

  @shortdoc "Run Christine tests"
  def run(_) do
    IO.puts("Running Christine tests...")

    test_files = Path.wildcard("test/christine/**/*.christine")

    results =
      Enum.map(test_files, fn file ->
        IO.write("  Testing #{file}... ")
        source = File.read!(file)

        case Christine.Compiler.compile_module(source, source_path: file) do
          {:ok, mod, _bin} ->
            IO.puts("OK (#{mod})")
            :ok

          {:error, reason} ->
            IO.puts("FAILED: #{inspect(reason)}")
            :error
        end
      end)

    failures = Enum.count(results, &(&1 == :error))

    if failures > 0 do
      IO.puts("\n#{failures} tests failed.")
      System.halt(1)
    else
      IO.puts("\nAll Christine tests passed.")
    end
  end
end
