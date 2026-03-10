defmodule ChristineTest do
  use ExUnit.Case
  alias Christine.Compiler

  test "compile Samples.christine" do
    source = File.read!("test/christine/Samples.christine")
    assert {:ok, mod, bin} = Compiler.compile_module(source)
    assert is_atom(mod)
    assert is_binary(bin)
  end

  test "lexer basics" do
    assert {:ok, tokens} = Christine.Lexer.lex("Module Test. Definition f (x: Nat) : Nat := x.")
    assert Enum.any?(tokens, fn t -> elem(t, 0) == :module end)
    assert Enum.any?(tokens, fn t -> elem(t, 0) == :definition end)
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
    Module WTest.
    Inductive Empty := .
    Inductive Unit := tt.
    Inductive Bool := | False | True.
    Inductive W (A: Type) (B: forall (x: A), Type) :=
    | Sup (x: A) (f: forall (y: B x), W A B).
    """

    assert {:ok, _mod, _bin} = Compiler.compile_module(source)
  end
end
