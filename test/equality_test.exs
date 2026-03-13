defmodule Christine.EqualityTest do
  use ExUnit.Case
  alias Christine.AST
  alias Christine.Typechecker

  setup do
    # Define nat
    nat = %AST.Inductive{
      name: "nat",
      params: [],
      level: 0,
      constrs: [
        {1, "Zero", %AST.Var{name: "nat"}},
        {2, "Succ", %AST.Pi{name: "_", domain: %AST.Var{name: "nat"}, codomain: %AST.Var{name: "nat"}}}
      ]
    }

    bool = %AST.Inductive{name: "bool", params: [], level: 0, constrs: [{1, "false", %AST.Var{name: "bool"}}, {2, "true", %AST.Var{name: "bool"}}]}

    # beq_nat definition (1-arg fixpoint returning lambda)
    # Christine's Ind node ALWAYS passes the IH for recursive arguments.
    # In nat, Succ has 1 argument (nat) which is recursive.
    # So the Succ branch takes (n_sub, ih_n_sub).
    
    branch_zero_body = %AST.Lam{
      name: "m",
      domain: %AST.Var{name: "nat"},
      body: %AST.Ind{
        inductive: nat,
        motive: %AST.Var{name: "Any"},
        term: %AST.Var{name: "m"},
        cases: [
          %AST.Var{name: "true"},
          %AST.Lam{name: "m_sub", domain: %AST.Var{name: "nat"}, body: %AST.Var{name: "false"}}
        ]
      }
    }

    branch_succ_body = %AST.Lam{
      name: "n_sub",
      domain: %AST.Var{name: "nat"},
      body: %AST.Lam{
        name: "ih_n_sub", # IH passed by Christine's Typechecker
        domain: %AST.Var{name: "Any"},
        body: %AST.Lam{
          name: "m",
          domain: %AST.Var{name: "nat"},
          body: %AST.Ind{
            inductive: nat,
            motive: %AST.Var{name: "Any"},
            term: %AST.Var{name: "m"},
            cases: [
              %AST.Var{name: "false"},
              %AST.Lam{name: "m_sub", domain: %AST.Var{name: "nat"}, body: 
                # beq_nat_n_sub_m_sub is exactly the IH!
                %AST.App{func: %AST.Var{name: "ih_n_sub"}, arg: %AST.Var{name: "m_sub"}}
              }
            ]
          }
        }
      }
    }

    beq_nat_body = %AST.Lam{
      name: "n",
      domain: %AST.Var{name: "nat"},
      body: %AST.Ind{
        inductive: nat,
        motive: %AST.Var{name: "Any"},
        term: %AST.Var{name: "n"},
        cases: [branch_zero_body, branch_succ_body]
      }
    }

    beq_nat_fix = %AST.Fixpoint{name: "beq_nat", domain: %AST.Var{name: "Any"}, body: beq_nat_body, args: []}

    env = %Typechecker.Env{
      env: %{"nat" => nat, "bool" => bool},
      defs: %{"beq_nat" => beq_nat_fix},
      global_ctx: %{"beq_nat" => %AST.Var{name: "Any"}, "true" => %AST.Var{name: "bool"}, "false" => %AST.Var{name: "bool"}},
      ctx: [{"n", %AST.Var{name: "nat"}}]
    }

    {:ok, env: env, nat: nat, bz: branch_zero_body, bs: branch_succ_body}
  end

  test "basic nat equality", %{env: env, nat: nat} do
    zero = %AST.Constr{index: 1, inductive: nat, args: []}
    assert Typechecker.equal?(env, zero, zero)
    
    one = %AST.Constr{index: 2, inductive: nat, args: [zero]}
    assert Typechecker.equal?(env, one, one)
    assert not Typechecker.equal?(env, zero, one)
  end

  test "beq_nat n n (unreduced) == expanded", %{env: env, nat: nat, bz: bz, bs: bs} do
    # LHS: beq_nat n
    lhs1 = %AST.App{func: %AST.Var{name: "beq_nat"}, arg: %AST.Var{name: "n"}}
    
    expected_unfolded_n = %AST.Ind{
      inductive: nat,
      motive: %AST.Var{name: "Any"},
      term: %AST.Var{name: "n"},
      cases: [bz, bs]
    }
    
    assert Typechecker.equal?(env, lhs1, expected_unfolded_n)
  end

  test "eta-equality check", %{env: env} do
    # \x -> f x == f
    f_ty = %AST.Pi{name: "x", domain: %AST.Var{name: "nat"}, codomain: %AST.Var{name: "nat"}}
    env_eta = %{env | ctx: [{"f", f_ty} | env.ctx]}
    eta_lhs = %AST.Lam{name: "x", domain: %AST.Var{name: "nat"}, body: %AST.App{func: %AST.Var{name: "f"}, arg: %AST.Var{name: "x"}}}
    eta_rhs = %AST.Var{name: "f"}

    assert Typechecker.equal?(env_eta, eta_lhs, eta_rhs)
  end
end
