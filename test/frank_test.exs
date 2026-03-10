defmodule ChristineTest do
  use ExUnit.Case
  alias Christine.Compiler

  test "compile Samples.Christine" do
    source = File.read!("test/Christine/Samples.Christine")
    assert {:ok, mod, bin} = Compiler.compile_module(source)
    assert is_atom(mod)
    assert is_binary(bin)
  end

  test "lexer basics" do
    assert {:ok, tokens} = Christine.Lexer.lex("module Test where\n  f x = x")
    assert Enum.any?(tokens, fn t -> elem(t, 0) == :module end)
  end

  test "typechecker basics" do
    alias Christine.Typechecker
    alias Christine.AST
    env = %Typechecker.Env{ctx: [{"x", %AST.Universe{level: 0}}]}
    term = %AST.Var{name: "x"}
    assert %AST.Universe{level: 0} = Typechecker.infer(env, term)
  end

  test "W-type sample compilation" do
    source = """
    module WTest where
    data Empty =
    data Unit = tt
    data Bool = False | True
    data W A B = Sup (x:A) (f:B x -> W A B)
    """

    assert {:ok, _mod, _bin} = Compiler.compile_module(source)
  end
end
