Christine: Calculus of Inductive Constructions
==============================================

<img src="https://christine.groupoid.space/img/christine.jpg" height=400>

## Abstract

**Christine** is CoC+CIC tactical theorem prover implemented in OCaml, constitutes a minimal core for a dependently-typed lambda calculus,
constrained to exclude pattern matching, let-bindings, implicit arguments, modules, namespaces, and function extensionality.
It encompasses universes, dependent products `Pi`, and `Inductive` types with strict positivity enforcement.
Its mathematical properties, focusing on correctness, soundness, totality, canonicity, decidability and related
attributes relevant to formal mathematics are being analyzed.

## Introduction

The type checker operates over a term syntax comprising:

* `Universe i`: Type universes with level `i ∈ ℕ`.
* `Pi (x, A, B)`: Dependent function, where `A : Universe i` and `B : Universe j` under `x : A`.
  `Lam (x, A, t)`: Lambda abstraction with totality enforced.
  `App (f, a)`: Function application.
* `Inductive d`: Inductive types with intros `Constr` and eliminator `Ind`.

The typing judgment `Γ ⊢ t : T` is defined via `infer` and `check` functions,
with definitional equality `Γ ⊢ t = t'` implemented via `equal`.

## Syntax

```OCaml
type term =
  | Var of name | Universe of level
  | Pi of name * term * term | Lam of name * term * term | App of term * term
  | Inductive of inductive | Constr of int * inductive * term list
  | Elim of inductive * term * term list * term
```

## Semantics

### Syntactic Equality `equal`

Structural equality of terms under an environment and context.

The function implements judgmental equality with substitution to handle bound variables,
avoiding explicit α-conversion by assuming fresh names (a simplification
over full de Bruijn indices [3]). The recursive descent ensures congruence,
but lacks normalization, making it weaker than CIC’s definitional equality,
which includes β-reduction.

* **Terminal Cases**: Variables `Var x` are equal if names match; universes `Universe i` if levels are identical.
* **Resursive Cases**: `App (f, arg)` requires equality of function and argument.
`Pi (x, a, b)` compares domains and codomains, adjusting for variable renaming via substitution.
`Inductive d` checks name, level, and parameters.
`Constr` and `Elim` compare indices, definitions, and arguments/cases.
* Default: Returns false for mismatched constructors.

**Theorem**. Equality is reflexive, symmetric, and transitive modulo
α-equivalence (cf. [1], Section 2). For `Pi (x, a, b)` and `Pi (y, a', b')`,
equality holds if `a = a'` and `b[x := Var x] = b'[y := Var x]`,
ensuring capture-avoiding substitution preserves meaning.

### Context Variables Lookup `lookup_var`

Retrieve a variable’s type from the context.
Context are the objects in the Substitutions categories.

* Searches `ctx` for `(x, ty)` using `List.assoc`.
* Returns `Some ty` if found, `None` otherwise.

**Theorem**: Context lookup is well-defined under uniqueness
of names (cf. [1], Section 3). If `ctx = Γ, x : A, Δ`,
then `lookup_var ctx x = Some A`.

### Substitution Calculus `subst`

Substitute term `s` for variable `x` in term `t`.
Substitutions are morphisms in Substitution categorties.

The capture-avoiding check `if x = y` prevents variable capture
but assumes distinct bound names, a simplification over full
renaming or de Bruijn indices. For Elim, substituting in the
motive and cases ensures recursive definitions remain sound,
aligning with CIC’s eliminator semantics.

* `Var`: Replaces `x` with `s`, leaves others unchanged.
* `Pi/Lam`: Skips substitution if bound variable shadows `x`, else recurses on domain and body.
* `App/Constr/Elim`: Recurses on subterms.
* `Inductive`: No substitution (assumes no free variables).

**Theorem**. Substitution preserves typing (cf. [13], Lemma 2.1).
If `Γ ⊢ t : T` and `Γ ⊢ s : A`, then `Γ ⊢ t[x := s] : T[x := s]`
under suitable conditions on x.

### Inductive Instantiation `apply_inductive`

Instantiate an inductive type’s constructors with parameters, used only in `infer_Ind`.

This function ensures type-level parametricity, critical for
polymorphic inductives like List A. The fold-based substitution
avoids explicit recursion, leveraging OCaml’s functional style,
but assumes args are well-typed, deferring validation to infer.

* Validates argument count against d.params.
* Substitutes each parameter into constructor types using subst_param.

**Theorem**: Parameter application preserves inductiveness (cf. [4], Section 4).
If `D` is an inductive type with parameters `P`, then `D[P]` is
well-formed with substituted constructors.

### Infer Contstructor `infer_ctor`

Validate constructor arguments against its type.

This function implements the dependent application rule for constructors,
ensuring each argument satisfies the constructor’s domain type in sequence.
The recursive descent mirrors the structure of `Pi` types, where `ty` is peeled
layer by the layer, and `subst x arg b` updates the type for the next argument.

* Recursively matches `ty` (a Pi chain) with `args`, checking each argument and substituting.
* Returns the final type when all arguments are consumed.

**Theorem**. Constructor typing is preserved (cf. [1], Section 4, Application Rule; [1], Section 4.3).
If `ctx ⊢ c : Π (x:A), B` and `ctx ⊢ a : A`, then `ctx ⊢ c a : B[x := a]`.

### Infer General Induction `infer_Ind`

Type-check an dependent elimination (induction principle) over inductive type `d`.

This function implements the dependent elimination rule of CIC,
generalizing both computation (e.g., plus : `Nat → Nat → Nat`)
and proof (e.g., `nat_elim : Πx:Nat.Type0`). The check `equal env ctx t_ty a`
ensures the motive’s domain aligns with the target, while `compute_case_type`
constructs the induction principle by injecting `App (p, var)`
as the hypothesis type for recursive occurrences, mirroring the
fixpoint-style eliminators of CIC [1]. The flexibility in result_ty
avoids hardcoding it to D, supporting higher-type motives (e.g., Type0).

**Theorem**. Elimination preserves typing (cf. [1], Section 4.5; Elimination Rule for Inductive Types). For an inductive type `D`
with constructors `c_j`, if `ctx ⊢ t : D` and `ctx ⊢ P : D → Type_i`,
and each case case_j has type `Πx:A_j.P(c_j x)` where `A_j` are
the argument types of `c_j` (including recursive hypotheses), then `ctx ⊢ Ind(D, P, cases, t) : P t`.

### Infer Equality Induction `infer_J`

Ensuring `J (ty, a, b, c, d, p)` has type `c a b p by` validating the motive,
base case, and path against CIC’s equality elimination rule.

The `infer_J` function implements the dependent elimination rule for identity
types in the Calculus of Inductive Constructions (CIC), enabling proofs and
computations over equality (e.g., `symmetry : Π a b : ty, Π p : Id (ty, a, b), Id(ty, b, a)`).
It type-checks the term `J (ty, a, b, c, d, p)` by ensuring 
`ty : Universe 0` is the underlying type, `a : ty` and `b : ty` are endpoints,
`c : Π (x:ty), Π (y:ty), Π (p: Id(ty, x, y)), Type0` is a motive over all paths,
`d : Π (x:ty), c x x (Refl x)` handles the reflexive case,
and `p : Id(ty, a, b)` is the path being eliminated.
The function constructs fresh variables to define the motive
and base case types, checks each component, and returns `c a b p` (normalized),
reflecting the result of applying the motive to the specific path. 

**Theorem**. For an environment `env` and context `ctx`, given a type `A : Type_i`,
terms `a : A`, `b : A`, a motive `C : Π (x:A), Π (y:A), Π(p:Id(A, x, y)),Type_j`,
a base case `d : Π(x:A), C x x (Refl x)`, and a path `p : Id(A, a, b)`, the
term `J (A, a, b, C, d, p)` is well-typed with type `C a b p`. (Reference:
CIC [1], Section 4.5; Identity Type Elimination Rule).

### Type Inference `infer`

Infer the type of term `t` in context `ctx` and environment `env`.

For `Pi` and `Lam`, universe levels ensure consistency
(e.g., `Type i : Type (i + 1)`), while `Elim` handles induction,
critical for dependent elimination. Note that lambda agrument should be typed
for easier type synthesis [13].

### Check Universes `check_universe`

Ensure `t` is a universe, returning its level.
Infers type of `t`, expects `Universe i`.

This auxiliary enforces universe hierarchy, preventing
paradoxes (e.g., Type : Type). It relies on infer,
assuming its correctness, and throws errors for
non-universe types, aligning with ITT’s stratification.

**Theorem**: Universe checking is decidable (cf. [13]).
If `ctx ⊢ t : Universe i`, then `check_universe env ctx t = i`.

### Check `check`

Check that `t` has type `ty`.

* `Lam`: Ensures the domain is a type, extends the context, and checks the body against the codomain.
* `Constr`: Infers the constructor’s type and matches it to the expected inductive type.
* `Elim`: Computes the elimination type via check_elim and verifies it equals ty.
* Default: Infers t’s type, normalizes ty, and checks equality.

The function leverages bidirectional typing: specific cases (e.g., `Lam`)
check directly, while the default case synthesizes via infer and compares
with a normalized ty, ensuring definitional equality (β-reduction).
Completeness hinges on normalize terminating (ITT’s strong normalization)
and equal capturing judgmental equality.

**Theorem**. Type checking is complete (cf. [1], Normalization).
If `ctx ⊢ t : T` in the type theory, then `check env ctx t T` succeeds,
assuming normalization and sound inference.

### Branch Evaluation `apply_case`

Apply a case branch to constructor arguments, used only in `reduce`.

This function realizes CIC’s ι-reduction for inductive eliminators [1], where
a case branch is applied to constructor arguments, including recursive hypotheses.
For Nat’s succ in plus, `ty = Πn:Nat.Nat`, `case = λk.λih.succ ih`, and `args = [n]`.
The recursive check `a = Inductive d` triggers for `n : Nat`, computing `ih = Elim(Nat, Π_:Nat.Nat, [m; λk.λih.succ ih], n)`,
ensuring `succ ih : Nat`. The nested apply_term handles multi-argument lambdas
(e.g., k and ih), avoiding explicit uncurrying, while substitution preserves
typing per CIC’s rules.

**Theorem**. Case application is sound (cf. [1] Elimination Typing).
If `case : Πx:A.P(c x)` and `args` match `A`, then `apply_case env ctx d p cases case ty args`
yields a term of type `P(c args)`.

### One-step β-reductor `reduce`

Perform one-step β-reduction or inductive elimination.

The function implements a one-step reduction strategy combining ITT’s β-reduction 
with CIC’s ι-reduction for inductives. The `App (Lam, arg)` case directly applies
substitution, while `Elim (Constr)` uses `apply_case` to handle induction,
ensuring recursive calls preserve typing via the motive p. The `Pi` case,
though unconventional, supports type-level computation, consistent with CIC’s flexibility. 

* `App (Lam, arg)`: Substitutes arg into the lambda body (β-reduction).
* `App (Pi, arg)`: Substitutes arg into the codomain (type-level β-reduction).
* `App (f, arg)`: Reduces f, then arg if f is unchanged.
* `Elim (d, p, cases, Constr)`: Applies the appropriate case to constructor arguments, computing recursive calls (ι-reduction).
* `Elim (d, p, cases, t')`: Reduces the target `t'`.
* `Constr`: Reduces arguments.
* Default: Returns unchanged.

**Theorem**. Reduction preserves typing (cf. [8], Normalization Lemma, Subject Reduction).
If `ctx ⊢ t : T` and `t → t'` via β-reduction or inductive elimination, then `ctx ⊢ t' : T`.

### Normalization `normalize`

This function fully reduces a term t to its normal form by iteratively
applying one-step reductions via reduce until no further changes occur,
ensuring termination for well-typed terms.

This function implements strong normalization, a cornerstone of MLTT [9]
and CIC [1], where all reduction sequences terminate. The fixpoint
iteration relies on reduce’s one-step reductions (β for lambdas, ι
for inductives), with equal acting as the termination oracle.
For `plus 2 2`, it steps to `succ succ succ succ zero`, terminating at a constructor form.

**Theorem**. Normalization terminates (cf. [1]. Strong Normalization via CIC).
Every well-typed term in the system has a ormal form under β- and ι-reductions.

## Conclusion

Per’s elegance rests on firm theoretical ground. Here, we reflect on key meta-theorems for Classical MLTT with General Inductive Types, drawing from CIC’s lineage:

* **Soundness and Completeness**: Per’s type checker is sound—every term it accepts has a type under MLTT’s rules [Paulin-Mohring, 1996].
  This ensures that every term accepted by Christineis typable in the underlying theory.
  Relative to the bidirectional type checking algorithm, context is appropriately managed [Harper & Licata, 2007].
  The interplay of inference and checking modes guarantees this property.
* **Canonicity, Normalization, and Totality**: Canonicity guarantees that every closed term of type `Nat` normalizes
  to `zero` or `succ n` [Martin-Löf, 1984]. Per’s normalize achieves strong normalization—every term reduces to a
  unique normal form—thanks to CIC’s strict positivity [Coquand & Paulin-Mohring, 1990]. Totality follows: all
  well-typed functions terminate, as seen in list_length reducing to `succ (succ zero)`.
* **Consistency and Decidability**: Consistency ensures no proof of ⊥ exists, upheld by normalization and the
  absence of paradoxes like Girard’s [Girard, 1972]. Type checking is decidable in Per, as our algorithm
  terminates for well-formed inputs, leveraging CIC’s decidable equality [Asperti et al., 2009].
* **Conservativity and Initiality**: Christineis conservative over simpler systems like System F, adding dependent
  types without altering propositional truths [Pfenning & Paulin-Mohring, 1989]. Inductive types like Nat satisfy
  initiality—every algebra morphism from Nat to another structure is uniquely defined—ensuring categorical universality [Dybjer, 1997].

### Soundness

* Definition: Type preservation and logical consistency hold.
* Formal Statement: 1) If `Γ ⊢ t : T` and `infer t = t'`, then `Γ ⊢ t' : T`;
  2) No `t` exists such that `Γ ⊢ t : Id (Universe 0, Universe 0, Universe 1)`.
* Proof: Preservation via terminating reduce; consistency via positivity and intensionality.
* Status: Sound, inforced by rejecting non-total lambdas.

### Completeness

* Definition: The type checker captures all well-typed terms of MLTT within its bidirectional framework.
* Formal Statement: If `Γ ⊢ 𝑡 : T`, then `infer Δ Γ 𝑡 = T` or `check Δ Γ 𝑡 T` holds under suitable `Δ`.
* Status: Complete relative to the implemented algorithm.

### Canonicity

* Definition: Reduction reaches a normal form; equality is decidable.
* Formal Statement: `equal Δ Γ t t'` terminates, reflecting normalize’s partial eta and beta reductions in `normnalize`.
* Status: Satisfied within the scope of implemented reductions.

### Totality

* Definition: All well-typed constructs terminate under reduction.
* Formal Statement: 1) For `Inductive d : Universe i`, each `Constr (j, d, args)` is total;
  2) For `t : T` with `Ind` or `J`, `reduce t` terminates;
  3) For `Lam (x, A, t) : Pi (x, A, B)`, `reduce (App (Lam (x, A, t), a))` terminates for all `a : A`;
  4) `normalize Δ Γ t` terminates.

### Consistency

The system is logically consistent, meaning no term `t` exists such that `Γ ⊢ t : ⊥`.
This is upheld by normalization and the absence of paradoxes such as Girard's [Girard, 1972].

### Decidability

* Definition: Type checking and equality are computable.
* Formal Statement: `infer` and `check` terminate with a type or `TypeError`.
* Status: Decidable, enhanced by termination checks on lambda expressions.

## Artefact

```
$ mix christine.repl
🧊 Christine Theorem Prover version 0.3.11 [Coq 6.3 Syntax]
Copyright (c) 2016-2026 Groupoid Infinity
https://groupoid.github.io/christine/

Loaded: Data.Bool
Loaded: Data.Eq
Loaded: Data.Fin
Loaded: Data.List
Loaded: Data.Nat
Loaded: Data.Sigma
Loaded: Data.Tree
Loaded: Data.Unit
Loaded: Data.Vec
Loaded: Data.W
Loaded: Prelude
Loaded: Samples
Loaded: Test.List
Loaded: Test.Pythagorean
Loaded: Test.W
Christine> Theorem plus_0_n : forall (n: Nat), Eq Nat (plus Zero n) n.
Proof started for plus_0_n
Proof> intro n.
Proof> exact (Refl Nat n n).
Goal solved!
Proof> Qed.
Proof complete!
Christine> test_W
Result: (ind_Bool(Bool)) True unused_ih (\u -> succ_w zero_w) unused_ih
Christine>
```

## CIC

[1]. Coquand, T., & Paulin-Mohring, C. Inductively defined types. 1990. <br>
[2]. Christine Paulin-Mohring. Inductive Definitions in the System Coq. Rules and Properties. 1992.<br>
[3]. <a href="https://inria.hal.science/hal-01094195/document">Christine Paulin-Mohring. Introduction to the Calculus of Inductive Constructions.</a> 2014.<br>
[4]. <a href="https://www.cs.cmu.edu/%7Efp/papers/mfps89.pdf">Frank Pfenning, Christine Paulin-Mohring. Inductively Defined Types in the Calculus of Construction</a> 1989.<br>
[5]. <a href="https://www.cs.unibo.it/~sacerdot/PAPERS/sadhana.pdf"> A. Asperti, W. Ricciotti, C. Sacerdoti Coen, E. Tassi. A compact kernel for the calculus of inductive constructions.</a><br>
[6]. P.Dybjer. Inductive families. 1997. <br>
[7]. R.Harper, D.Licata. Mechanizing metatheory in a logical framework. 2007.<br>
[8]. M.Bezem, T.Coquand, P.Dybjer, M.Escardó. <a href="https://arxiv.org/pdf/2212.03284">Type Theory with Explicit Universe Polymorphism</a> 2024.<br>

## MLTT

[9]. Martin-Löf, P. Intuitionistic Type Theory. 1980.<br>
[10]. Thierry Coquand. An Algorithm for Type-Checking Dependent Types. 1996. <br>

## PTS

[11]. N. G. de Bruijn. Lambda Calculus Notation with Nameless Dummies. 1972. <br>
[12]. J.-Y. Girard. Interprétation fonctionnelle et élimination des coupures. 1972. <br>
[13]. Thierry Coquand, Gerard Huet. <a href="https://core.ac.uk/download/pdf/82038778.pdf">The Calculus of Constructions</a>. 1988.<br>

## Author

Namdak Tonpa
