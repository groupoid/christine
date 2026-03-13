defmodule Christine.ExtensiveEqualityTest do
  use ExUnit.Case
  alias Christine.AST
  alias Christine.Typechecker

  setup do
    # Basic definitions
    nat = %AST.Inductive{
      name: "Nat",
      params: [],
      level: 0,
      constrs: [
        {1, "Zero", %AST.Var{name: "Nat"}},
        {2, "Succ", %AST.Pi{name: "n", domain: %AST.Var{name: "Nat"}, codomain: %AST.Var{name: "Nat"}}}
      ]
    }

    bool = %AST.Inductive{
      name: "Bool",
      params: [],
      level: 0,
      constrs: [
        {1, "False", %AST.Var{name: "Bool"}},
        {2, "True", %AST.Var{name: "Bool"}}
      ]
    }

    env = %Typechecker.Env{
      env: %{"Nat" => nat, "Bool" => bool},
      defs: %{},
      ctx: []
    }

    {:ok, env: env, nat: nat, bool: bool}
  end

  test "test_universe consistency", %{env: env} do
    u0 = %AST.Universe{level: 0}
    u1 = %AST.Universe{level: 1}
    
    # Type0 : Type1
    assert Typechecker.equal?(env, Typechecker.infer(env, u0), u1)
  end

  test "test_eta-equality", %{env: env} do
    # \x -> f x == f
    f_ty = %AST.Pi{name: "x", domain: %AST.Universe{level: 0}, codomain: %AST.Universe{level: 0}}
    ctx = [{"f", f_ty}]
    env_eta = %{env | ctx: ctx}
    
    t1 = %AST.Lam{name: "x", domain: %AST.Universe{level: 0}, body: %AST.App{func: %AST.Var{name: "f"}, arg: %AST.Var{name: "x"}}}
    t2 = %AST.Var{name: "f"}
    
    assert Typechecker.equal?(env_eta, t1, t2)
  end

  test "plus evaluation", %{env: env, nat: nat} do
    plus_fix = %AST.Fixpoint{
      name: "plus",
      domain: %AST.Var{name: "Any"},
      body: %AST.Lam{
        name: "m",
        domain: %AST.Var{name: "Nat"},
        body: %AST.Lam{
          name: "n",
          domain: %AST.Var{name: "Nat"},
          body: %AST.Ind{
            inductive: nat,
            motive: %AST.Pi{name: "_", domain: %AST.Var{name: "Nat"}, codomain: %AST.Var{name: "Nat"}},
            term: %AST.Var{name: "n"},
            cases: [
              %AST.Var{name: "m"},
              %AST.Lam{name: "k", domain: %AST.Var{name: "Nat"}, body: 
                %AST.Lam{name: "ih", domain: %AST.Var{name: "Nat"}, body:
                  %AST.Constr{index: 2, inductive: nat, args: [%AST.Var{name: "ih"}]}
                }
              }
            ]
          }
        }
      },
      args: []
    }
    
    env_plus = %{env | defs: %{"plus" => plus_fix}, global_ctx: %{"plus" => %AST.Var{name: "Any"}}}
    
    zero = %AST.Constr{index: 1, inductive: nat, args: []}
    one = %AST.Constr{index: 2, inductive: nat, args: [zero]}
    two = %AST.Constr{index: 2, inductive: nat, args: [one]}
    three = %AST.Constr{index: 2, inductive: nat, args: [two]}
    
    # 2 + 1 = 3
    expr = %AST.App{func: %AST.App{func: %AST.Var{name: "plus"}, arg: two}, arg: one}
    result = Typechecker.normalize(env_plus, expr)
    
    assert Typechecker.equal?(env_plus, result, three)
  end

  test "list_length evaluation", %{env: env, nat: nat} do
    # List (A: U0)
    list_ind = %AST.Inductive{
      name: "List",
      params: [{"A", %AST.Universe{level: 0}}],
      level: 0,
      constrs: [
        {1, "Nil", %AST.Pi{name: "A", domain: %AST.Universe{level: 0}, codomain: %AST.App{func: %AST.Var{name: "List"}, arg: %AST.Var{name: "A"}}}},
        {2, "Cons", %AST.Pi{name: "A", domain: %AST.Universe{level: 0}, codomain:
          %AST.Pi{name: "x", domain: %AST.Var{name: "A"}, codomain: 
            %AST.Pi{name: "xs", domain: %AST.App{func: %AST.Var{name: "List"}, arg: %AST.Var{name: "A"}}, codomain:
              %AST.App{func: %AST.Var{name: "List"}, arg: %AST.Var{name: "A"}}
            }
          }
        }}
      ]
    }
    
    env_list = %{env | env: Map.put(env.env, "List", list_ind)}
    
    # length : forall A, List A -> Nat
    length_fix = %AST.Fixpoint{
      name: "length",
      domain: %AST.Var{name: "Any"},
      body: %AST.Lam{
        name: "A",
        domain: %AST.Universe{level: 0},
        body: %AST.Lam{
          name: "l",
          domain: %AST.App{func: %AST.Var{name: "List"}, arg: %AST.Var{name: "A"}},
          body: %AST.Ind{
            inductive: list_ind,
            motive: %AST.Pi{name: "_", domain: %AST.App{func: %AST.Var{name: "List"}, arg: %AST.Var{name: "A"}}, codomain: %AST.Var{name: "Nat"}},
            term: %AST.Var{name: "l"},
            cases: [
              %AST.Constr{index: 1, inductive: nat, args: []}, # Zero
              %AST.Lam{name: "x", domain: %AST.Var{name: "A"}, body:
                %AST.Lam{name: "xs", domain: %AST.App{func: %AST.Var{name: "List"}, arg: %AST.Var{name: "A"}}, body:
                  %AST.Lam{name: "ih", domain: %AST.Var{name: "Nat"}, body:
                    %AST.Constr{index: 2, inductive: nat, args: [%AST.Var{name: "ih"}]} # Succ ih
                  }
                }
              }
            ]
          }
        }
      },
      args: []
    }
    
    env_len = %{env_list | defs: %{"length" => length_fix}, global_ctx: %{"length" => %AST.Var{name: "Any"}}}
    
    nat_type = %AST.Var{name: "Nat"}
    zero_nat = %AST.Constr{index: 1, inductive: nat, args: []}
    succ_zero = %AST.Constr{index: 2, inductive: nat, args: [zero_nat]}
    
    nil_list = %AST.Constr{index: 1, inductive: list_ind, args: [ nat_type ]}
    l1 = %AST.Constr{index: 2, inductive: list_ind, args: [ nat_type, succ_zero, nil_list ]}
    l2 = %AST.Constr{index: 2, inductive: list_ind, args: [ nat_type, zero_nat, l1 ]}
    
    # length Nat l2 == 2
    expr = %AST.App{func: %AST.App{func: %AST.Var{name: "length"}, arg: nat_type}, arg: l2}
    result = Typechecker.normalize(env_len, expr)
    
    two_nat = %AST.Constr{index: 2, inductive: nat, args: [%AST.Constr{index: 2, inductive: nat, args: [zero_nat]}]}
    assert Typechecker.equal?(env_len, result, two_nat)
  end

  test "WNat evaluation", %{env: env, nat: nat, bool: bool} do
    # Empty
    empty_ind = %AST.Inductive{name: "Empty", params: [], level: 0, constrs: []}
    # Unit
    unit_ind = %AST.Inductive{name: "Unit", params: [], level: 0, constrs: [{1, "tt", %AST.Var{name: "Unit"}}]}
    tt = %AST.Constr{index: 1, inductive: unit_ind, args: []}
    
    # W (A: Type) (B: A -> Type)
    w_ind = %AST.Inductive{
      name: "W",
      params: [{"A", %AST.Universe{level: 0}}, {"B", %AST.Pi{name: "_", domain: %AST.Var{name: "A"}, codomain: %AST.Universe{level: 0}}}],
      level: 0,
      constrs: [
        {1, "Sup", %AST.Pi{name: "A", domain: %AST.Universe{level: 0}, codomain:
          %AST.Pi{name: "B", domain: %AST.Pi{name: "_", domain: %AST.Var{name: "A"}, codomain: %AST.Universe{level: 0}}, codomain:
            %AST.Pi{name: "x", domain: %AST.Var{name: "A"}, codomain:
              %AST.Pi{name: "f", domain: %AST.Pi{name: "y", domain: %AST.App{func: %AST.Var{name: "B"}, arg: %AST.Var{name: "x"}}, codomain: %AST.App{func: %AST.App{func: %AST.Var{name: "W"}, arg: %AST.Var{name: "A"}}, arg: %AST.Var{name: "B"}}}, codomain:
                %AST.App{func: %AST.App{func: %AST.Var{name: "W"}, arg: %AST.Var{name: "A"}}, arg: %AST.Var{name: "B"}}
              }
            }
          }
        }}
      ]
    }
    
    # B_nat(False) = Empty, B_nat(True) = Unit
    b_nat = %AST.Lam{name: "b", domain: %AST.Var{name: "Bool"}, body:
      %AST.Ind{
        inductive: bool,
        motive: %AST.Pi{name: "_", domain: %AST.Var{name: "Bool"}, codomain: %AST.Universe{level: 0}},
        term: %AST.Var{name: "b"},
        cases: [ %AST.Var{name: "Empty"}, %AST.Var{name: "Unit"} ]
      }
    }
    
    env_w = %{env | 
      env: env.env |> Map.put("Empty", empty_ind) |> Map.put("Unit", unit_ind) |> Map.put("W", w_ind),
      defs: %{"B_nat" => b_nat},
      global_ctx: %{"B_nat" => %AST.Var{name: "Any"}},
      ctx: [{"Empty", %AST.Universe{level: 0}}, {"Unit", %AST.Universe{level: 0}}]
    }
    
    # zero_w = Sup Bool B_nat False (fun e -> match e with end)
    false_bool = %AST.Constr{index: 1, inductive: bool, args: []}
    true_bool = %AST.Constr{index: 2, inductive: bool, args: []}
    
    zero_w = %AST.Constr{index: 1, inductive: w_ind, args: [
      %AST.Var{name: "Bool"}, 
      %AST.Var{name: "B_nat"},
      false_bool,
      %AST.Lam{name: "e", domain: %AST.Var{name: "Empty"}, body: %AST.Ind{inductive: empty_ind, motive: %AST.Var{name: "Any"}, term: %AST.Var{name: "e"}, cases: []}}
    ]}
    
    # to_nat_w = \w -> match w with Sup x f ih -> match x with False -> Zero | True -> Succ (ih tt)
    to_nat_w = %AST.Fixpoint{
      name: "to_nat_w",
      domain: %AST.Var{name: "Any"},
      body: %AST.Lam{
        name: "w",
        domain: %AST.App{func: %AST.App{func: %AST.Var{name: "W"}, arg: %AST.Var{name: "Bool"}}, arg: %AST.Var{name: "B_nat"}},
        body: %AST.Ind{
          inductive: w_ind,
          motive: %AST.Pi{name: "_", domain: %AST.App{func: %AST.App{func: %AST.Var{name: "W"}, arg: %AST.Var{name: "Bool"}}, arg: %AST.Var{name: "B_nat"}}, codomain: %AST.Var{name: "Nat"}},
          term: %AST.Var{name: "w"},
          cases: [
            # Case Sup x f ih
            %AST.Lam{name: "x", domain: %AST.Var{name: "Bool"}, body:
              %AST.Lam{name: "f", domain: %AST.Pi{name: "_", domain: %AST.App{func: %AST.Var{name: "B_nat"}, arg: %AST.Var{name: "x"}}, codomain: %AST.App{func: %AST.App{func: %AST.Var{name: "W"}, arg: %AST.Var{name: "Bool"}}, arg: %AST.Var{name: "B_nat"}}}, body:
                %AST.Lam{name: "ih", domain: %AST.Pi{name: "y", domain: %AST.App{func: %AST.Var{name: "B_nat"}, arg: %AST.Var{name: "x"}}, codomain: %AST.Var{name: "Nat"}}, body:
                  %AST.Ind{
                    inductive: bool,
                    motive: %AST.Pi{name: "_", domain: %AST.Var{name: "Bool"}, codomain: %AST.Var{name: "Nat"}},
                    term: %AST.Var{name: "x"},
                    cases: [
                      %AST.Constr{index: 1, inductive: nat, args: []}, # Zero
                      %AST.Constr{index: 2, inductive: nat, args: [%AST.App{func: %AST.Var{name: "ih"}, arg: tt}]} # Succ (ih tt)
                    ]
                  }
                }
              }
            }
          ]
        }
      },
      args: []
    }
    
    env_eval = %{env_w | defs: Map.put(env_w.defs, "to_nat_w", to_nat_w), global_ctx: Map.put(env_w.global_ctx, "to_nat_w", %AST.Var{name: "Any"})}
    
    # to_nat_w zero_w == Zero
    res_zero = Typechecker.normalize(env_eval, %AST.App{func: %AST.Var{name: "to_nat_w"}, arg: zero_w})
    assert Typechecker.equal?(env_eval, res_zero, %AST.Constr{index: 1, inductive: nat, args: []})
    
    # succ_w n = Sup Bool B_nat True (fun _ -> n)
    succ_w_zero = %AST.Constr{index: 1, inductive: w_ind, args: [
      %AST.Var{name: "Bool"}, 
      %AST.Var{name: "B_nat"},
      true_bool,
      %AST.Lam{name: "u", domain: %AST.Var{name: "Unit"}, body: zero_w}
    ]}
    
    # to_nat_w (succ_w zero_w) == Succ Zero
    res_one = Typechecker.normalize(env_eval, %AST.App{func: %AST.Var{name: "to_nat_w"}, arg: succ_w_zero})
    assert Typechecker.equal?(env_eval, res_one, %AST.Constr{index: 2, inductive: nat, args: [%AST.Constr{index: 1, inductive: nat, args: []}]})
  end

  test "beq_nat n n equality", %{env: env, nat: nat, bool: bool} do
    # beq_nat n m = match n with Zero -> match m with Zero -> true | Succ _ -> false end ...
    beq_nat_fix = %AST.Fixpoint{
      name: "beq_nat",
      body: %AST.Lam{name: "n", domain: %AST.Var{name: "Nat"}, body:
        %AST.Lam{name: "m", domain: %AST.Var{name: "Nat"}, body:
          %AST.Ind{
            inductive: nat,
            motive: %AST.Pi{name: "_", domain: %AST.Var{name: "Nat"}, codomain: %AST.Var{name: "Bool"}},
            term: %AST.Var{name: "n"},
            cases: [
              # Case Zero
              %AST.Ind{
                inductive: nat,
                motive: %AST.Pi{name: "_", domain: %AST.Var{name: "Nat"}, codomain: %AST.Var{name: "Bool"}},
                term: %AST.Var{name: "m"},
                cases: [
                  %AST.Constr{index: 2, inductive: bool, args: []}, # True
                  %AST.Lam{name: "_", domain: %AST.Var{name: "Nat"}, body: %AST.Constr{index: 1, inductive: bool, args: []}} # False
                ]
              },
              # Case Succ k
              %AST.Lam{name: "k", domain: %AST.Var{name: "Nat"}, body:
                %AST.Lam{name: "ih", domain: %AST.Var{name: "Bool"}, body:
                  %AST.Ind{
                    inductive: nat,
                    motive: %AST.Pi{name: "_", domain: %AST.Var{name: "Nat"}, codomain: %AST.Var{name: "Bool"}},
                    term: %AST.Var{name: "m"},
                    cases: [
                      %AST.Constr{index: 1, inductive: bool, args: []}, # False
                      %AST.Lam{name: "j", domain: %AST.Var{name: "Nat"}, body:
                        # Recursive call: beq_nat k j
                        %AST.App{func: %AST.App{func: %AST.Var{name: "beq_nat"}, arg: %AST.Var{name: "k"}}, arg: %AST.Var{name: "j"}}
                      }
                    ]
                  }
                }
              }
            ]
          }
        }
      }
    }

    env_beq = %{env | defs: %{"beq_nat" => beq_nat_fix}, global_ctx: %{"beq_nat" => %AST.Var{name: "Any"}}, ctx: [{"n", %AST.Var{name: "Nat"}}] }
    
    # LHS: beq_nat n n (unreduced)
    lhs = %AST.App{func: %AST.App{func: %AST.Var{name: "beq_nat"}, arg: %AST.Var{name: "n"}}, arg: %AST.Var{name: "n"}}
    
    # RHS: result of unfolding beq_nat with n, n (2 steps)
    {:ok, unfolded} = Typechecker.try_unfold_fixpoint_force_n(env_beq, beq_nat_fix, [%AST.Var{name: "n"}, %AST.Var{name: "n"}], 2)
    rhs = Typechecker.normalize(env_beq, unfolded)
    
    # beq_nat n n == (match n ...)
    assert Typechecker.equal?(env_beq, lhs, rhs)
  end
end
