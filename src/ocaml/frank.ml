(* 1989 Frank Pfenning and Christine Paulin-Mohring: CoC + CIC
   Copyright (c) Groupoїd la Infini
 *)

let trace: bool = false

type term =
    | Var of string
    | Universe of int
    | Pi of string * term * term
    | Lam of string * term * term
    | App of term * term
    | Inductive of inductive
    | Constr of int * inductive * term list
    | Ind of inductive * term * term list * term

and inductive = {
    name : string;
    params : (string * term) list;
    level : int;
    constrs : (int * term) list
}

exception TypeError of string

type error =
    | ApplyCaseTermMismatch
    | ApplyCaseCtorArgMismatch
    | InferUnboundVariable of string
    | InferNegativeUniverse of int
    | InferBoundVariableNoPositive of string
    | InferApplicationRequiresPi
    | InferCtorNegative of int
    | InferCtorInvalidArgumentType of int
    | InferCtorInvalidType of int * string
    | InferCtorTooManyArgs
    | IndWrongCases
    | IndElimTargetMismatch
    | IndMotiveExpetsPi
    | IndMotiveDomainMismatch
    | IndParametersMismatch
    | CheckUniverseExpected
    | CheckPiDomainMismatch
    | CheckUniverseLevelMismatch of int * int
    | CheckCtorTypeMismatch
    | CheckElimTypeMismatch
    | CheckTypeError

exception Error of error

type env = (string * inductive) list
type context = (string * term) list
type subst_map = (string * term) list

let empty_env : env = []
let empty_ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

let rec is_lam = function | Lam _ -> true | _ -> false

let rec subst_many m t =
    match t with
    | Var x -> (try List.assoc x m with Not_found -> t)
    | Pi (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Pi (x, subst_many m a, subst_many m' b)
    | Lam (x, d, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Lam (x, subst_many m d, subst_many m' b)
    | App (f, arg) -> App (subst_many m f, subst_many m arg)
    | Inductive d -> Inductive d
    | Constr (j, d, args) -> Constr (j, d, List.map (subst_many m) args)
    | Ind (d, p, cases, t') -> Ind (d, subst_many m p, List.map (subst_many m) cases, subst_many m t')
    | _ -> t

let subst x s t = subst_many [(x, s)] t

let rec lookup_var ctx x =
    try Some (List.assoc x ctx) with Not_found -> None

let rec equal env ctx t1' t2' =
    let t1 = normalize env ctx t1' in
    let t2 = normalize env ctx t2' in
    equal' env ctx t1 t2

and equal' env ctx t1 t2 =
    match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i <= j
    | Pi (x, a, b), Pi (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Lam (x, d, b), Lam (y, d', b') -> equal' env ctx d d' && equal' env (add_var ctx x d) b (subst y (Var x) b')
    | Lam (x, d, b), t when not (is_lam t) -> let x_var = Var x in equal' env ctx b (App (t, x_var)) && (match infer env ctx t with | Pi (y, a, b') -> equal' env ctx d a | _ -> false)
    | t, Lam (x, d, b) when not (is_lam t) -> let x_var = Var x in equal' env ctx (App (t, x_var)) b && (match infer env ctx t with | Pi (y, a, b') -> equal' env ctx a d | _ -> false)
    | App (f, arg), App (f', arg') -> equal' env ctx f f' && equal' env ctx arg arg'
    | Inductive d1, Inductive d2 -> d1.name = d2.name && d1.level = d2.level && List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal' env ctx t1 t2) d1.params d2.params
    | Constr (j, d1, args1), Constr (k, d2, args2) -> j = k && d1.name = d2.name && List.for_all2 (equal' env ctx) args1 args2
    | Ind (d1, p1, cases1, t1), Ind (d2, p2, cases2, t2) -> d1.name = d2.name && equal' env ctx p1 p2 && List.for_all2 (equal' env ctx) cases1 cases2 && equal' env ctx t1 t2
    | _ -> t1 = t2

and normalize env ctx t =
    let t' = reduce env ctx t in
    if equal' env ctx t t' then t else normalize env ctx t'

and apply_case env ctx d p cases case ty args =
    let rec apply ty args_acc remaining_args =
    match ty, remaining_args with
    | Pi (x, a, b), arg :: rest ->
        let b' = subst x arg b in
        let rec_arg =
          if equal env ctx a (Inductive d) then
            match arg with
            | Constr (j, d', sub_args) when d.name = d'.name -> Some (reduce env ctx (Ind (d, p, cases, arg)))
            | _ -> None
          else None
        in
        let new_args_acc = match rec_arg with | Some r -> r :: arg :: args_acc | None -> arg :: args_acc in
        apply b' new_args_acc rest
    | Pi (_, _, b), [] -> raise (Error ApplyCaseCtorArgMismatch)
    | _, [] ->
        let rec apply_term t args =
          match t, args with
          | Lam (x, _, body), arg :: rest -> apply_term (subst x arg body) rest
          | t, [] -> t
          | _ -> raise (Error ApplyCaseTermMismatch)
        in apply_term case (List.rev args_acc)
    | _ -> raise (Error ApplyCaseCtorArgMismatch)
    in apply ty [] args

and reduce env ctx t =
    match t with
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (Pi (x, a, b), arg) -> subst x arg b
    | App (f, arg) -> let f' = reduce env ctx f in let arg' = reduce env ctx arg in App (f', arg')
    | Ind (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
      let case = List.nth cases (j - 1) in let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
      apply_case env ctx d p cases case cj_subst args
    | Ind (d, p, cases, t') -> let t'' = reduce env ctx t' in let reduced_ind = Ind (d, p, cases, t'') in (match t'' with | Constr _ -> reduce env ctx reduced_ind | _ -> reduced_ind)
    | Constr (j, d, args) -> let args' = List.map (reduce env ctx) args in if args = args' then t else Constr (j, d, args')
    | _ -> t

and pos x t =
    match t with
    | Var y -> y = x
    | Universe _ -> false
    | Pi (y, a, b) -> pos x a || (y <> x && pos x b)
    | Lam (y, a, t') -> pos x a || (y <> x && pos x t')
    | App (f, a) -> pos x f || pos x a
    | Inductive d -> List.exists (fun (_, ty) -> pos x ty) d.constrs
    | Constr (_, _, args) -> List.exists (pos x) args
    | Ind (_, p, cases, t') -> pos x p || List.exists (pos x) cases || pos x t'

and is_positive env ctx ty ind_name =
    match ty with
    | Pi (x, a, b) -> 
        let rec neg ty' =
          match ty' with
          | Inductive d when d.name = ind_name -> true
          | Pi (x', a', b') -> neg a' || neg b'
          | App (f, arg) -> neg f || neg arg
          | _ -> false
        in not (neg a) && is_positive env (add_var ctx x a) b ind_name
    | Inductive d when d.name = ind_name -> true
    | _ -> true

and infer env ctx t =
    let res = match t with
    | Var x -> (match lookup_var ctx x with | Some ty -> ty | None -> raise (Error (InferUnboundVariable x)))
    | Universe i -> if i < 0 then raise (Error (InferNegativeUniverse i)); Universe (i + 1)
    | Pi (x, a, b) -> let i = check_universe env ctx a in let ctx' = add_var ctx x a in let j = check_universe env ctx' b in Universe (max i j)
    | Lam (x, domain, body) -> 
        check env ctx domain (infer env ctx domain); 
        if not (pos x body) then raise (Error (InferBoundVariableNoPositive x));
        Pi (x, domain, infer env (add_var ctx x domain) body)
    | App (f, arg) -> (match infer env ctx f with | Pi (x, a, b) -> check env ctx arg a; subst x arg b | _ -> raise (Error InferApplicationRequiresPi))
    | Inductive d -> 
      let ind_name = d.name in
      List.iter (fun (j, ty) -> 
        let rec check_pos ty' =
            match ty' with
            | Pi (x, a, b) -> 
                (try let _ = infer env ctx a in () with _ -> raise (Error (InferCtorInvalidArgumentType j)));
                if not (is_positive env ctx a ind_name) then 
                  raise (Error (InferCtorNegative j));
                check_pos b
            | Inductive d' when d'.name = ind_name -> ()
            | _ -> raise (Error (InferCtorInvalidType (j, d.name)))
        in check_pos ty
      ) d.constrs;
      Universe d.level
    | Constr (j, d, args) -> let cj = List.assoc j d.constrs in let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in infer_ctor env ctx cj_subst args
    | Ind (d, p, cases, t') -> infer_Ind env ctx d p cases t'
    in normalize env ctx res

and infer_ctor env ctx ty args =
    let rec check_args ty args_acc = function
    | [] -> ty
    | arg :: rest ->
        (match ty with
         | Pi (x, a, b) -> check env ctx arg a; check_args (subst x arg b) (arg :: args_acc) rest
         | _ -> raise (Error InferCtorTooManyArgs))
    in check_args ty [] args

and infer_Ind env ctx d p cases t' =
    if List.length cases <> List.length d.constrs then raise (Error IndWrongCases);
    let t_ty = infer env ctx t' in
    let d_applied = apply_inductive d (List.map snd d.params) in
    if not (equal env ctx t_ty d_applied) then raise (Error IndElimTargetMismatch);
    let (x, a, b) = match p with
    | Pi (x, a, b) -> (x, a, b)
    | _ -> raise (Error IndMotiveExpetsPi) in ignore(check_universe env ctx (infer env ctx p));
    if not (equal env ctx t_ty a) then raise (Error IndMotiveDomainMismatch);
    let result_ty = subst x t' b in
    if (trace) then (print_Ind d p cases t' 0);
    List.iteri (fun j case ->
      let j_idx = j + 1 in
      let cj = List.assoc j_idx d.constrs in
      let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params (List.map snd d.params) in
      let rec compute_case_type ty ctx_acc =
        match ty with
        | Pi (x, a, b) ->
            let var = Var x in let ctx' = add_var ctx_acc x a in let b_ty = compute_case_type b ctx' in
            if equal env ctx a d_applied then Pi (x, a, Pi ("ih", App (p, var), b_ty)) else Pi (x, a, b_ty)
        | Inductive d' when d'.name = d.name -> b
        | _ -> raise (Error (InferCtorInvalidType (j, d.name)))
      in
      let expected_ty = compute_case_type cj_subst ctx in
      check env ctx case expected_ty
    ) cases;
    result_ty

and apply_inductive d args =
    if List.length d.params <> List.length args then raise (Error IndParametersMismatch);
    let subst_param t = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t d.params args
    in Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

and check_universe env ctx t =
    match infer env ctx t with
    | Universe i -> i
    | _ -> raise (Error CheckUniverseExpected)

and check env ctx t ty =
    match t, ty with
    | Universe i, Universe j -> if i < 0 then raise (Error (InferNegativeUniverse i)); if i > j then raise (Error (CheckUniverseLevelMismatch (i,j)));
    | Pi (x, a, b), Pi (y, a', b') -> if not (equal env ctx a a') then raise (Error CheckPiDomainMismatch); let ctx' = add_var ctx x a in check env ctx' b (subst y (Var x) b')
    | Lam (x, domain, body), Pi (y, a, b) -> check env ctx domain (infer env ctx domain); let b_subst = subst y (Var x) b in check env (add_var ctx x domain) body b_subst
    | Constr (j, d, args), Inductive d' when d.name = d'.name -> let inferred = infer env ctx t in if not (equal env ctx inferred ty) then raise (Error CheckCtorTypeMismatch)
    | Ind (d, p, cases, t'), ty -> let inferred = infer_Ind env ctx d p cases t' in if not (equal env ctx inferred ty) then raise (Error CheckElimTypeMismatch)
    | _, _ ->
        let inferred = infer env ctx t in
        let ty' = normalize env ctx ty in
        match inferred, ty' with
        | Universe i, Universe j when i >= j -> ()
        | _ -> if not (equal env ctx inferred ty') then raise (Error CheckTypeError)

and print_Ind d p cases t' depth =
    print_string (d.name ^ ".Ind "); print_term_depth (depth + 1) p;
    print_string " ["; List.iteri (fun i c -> if i > 0 then print_string "; "; print_term_depth (depth + 1) c) cases; print_string "] ";
    print_term_depth (depth + 1) t'

and print_term_depth depth t =
    if depth > 10 then print_string "<deep>"
    else match t with
    | Var x -> print_string x
    | Universe i -> print_string ("U_" ^ string_of_int i)
    | Pi (x, a, b) -> print_string ("Π (" ^ x ^ " : "); print_term_depth (depth + 1) a; print_string "), "; print_term_depth (depth + 1) b
    | Lam (x, _, body) -> print_string ("λ (" ^ x ^ "), "); print_term_depth (depth + 1) body
    | App (f, arg) -> print_string "("; print_term_depth (depth + 1) f; print_string " "; print_term_depth (depth + 1) arg; print_string ")"
    | Inductive d -> print_string d.name
    | Constr (i, d, args) -> print_string d.name; print_string ("." ^ (string_of_int i) ^ " "); List.iteri (fun j c -> if j > 0 then print_string "; "; print_term_depth (depth + 1) c) args
    | Ind (d, p, cases, t') -> print_Ind d p cases t' depth

and print_term t = print_term_depth 0 t

let string_of_error = function
    | ApplyCaseTermMismatch -> "Case application mismatch: too few arguments for lambda"
    | ApplyCaseCtorArgMismatch -> "Constructor argument mismatch"
    | InferUnboundVariable x -> "Unbound variable " ^ x
    | InferNegativeUniverse i -> "Negative Universe level " ^ (string_of_int i)
    | InferBoundVariableNoPositive x -> "Bound variable " ^ x ^ " has no positive occurrence in lambda body; potential non-termination"
    | InferApplicationRequiresPi -> "Application requires a Pi type"
    | InferCtorNegative i -> "Negative occurrence in constructor " ^ string_of_int i
    | InferCtorInvalidArgumentType i -> "Invalid argument type in constructor " ^ string_of_int i
    | InferCtorInvalidType (i, typeName) -> "Constructor " ^ string_of_int i ^ " type must be " ^ typeName
    | InferCtorTooManyArgs -> "Too many arguments to constructor"
    | IndWrongCases -> "Number of cases doesn't match constructors"
    | IndElimTargetMismatch -> "Elimination target type mismatch"
    | IndMotiveExpetsPi -> "Motive must be a Pi type"
    | IndMotiveDomainMismatch -> "Target type does not match motive domain"
    | IndParametersMismatch -> "Parameter mismatch in inductive type"
    | CheckUniverseExpected -> "Expected a universe"
    | CheckPiDomainMismatch -> "Pi domain mismatch"
    | CheckUniverseLevelMismatch (i, j) -> "Universe level mismatch " ^ string_of_int i ^ ", " ^ string_of_int j
    | CheckCtorTypeMismatch -> "Constructor type mismatch"
    | CheckElimTypeMismatch -> "Elimination type mismatch"
    | CheckTypeError ->  "Type Mismatch Error"

let empty_def = { name = "Empty"; params = []; level = 0; constrs = [] }

let nat_def = {
  name = "Nat"; params = []; level = 0;
  constrs = [
    (1, Inductive { name = "Nat"; params = []; level = 0; constrs = [] });
    (2, Pi ("n", Inductive { name = "Nat"; params = []; level = 0; constrs = [] },
           Inductive { name = "Nat"; params = []; level = 0; constrs = [] }))]
}

let list_def (a : term) = {
  name = "List"; params = [("A", a)]; level = 0;
  constrs = [
    (1, Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = [] });
    (2, Pi ("x", a, Pi ("xs", Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = [] },
                        Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = [] }))) ]
}

let tree_def a = {
  name = "Tree";
  params = [("A", a)];
  level = 0;
  constrs = [
    (1, Inductive { name = "Tree"; params = [("A", a)]; level = 0; constrs = [] });
    (2, Pi ("x", a,
           Pi ("l", Inductive { name = "Tree"; params = [("A", a)]; level = 0; constrs = [] },
               Pi ("r", Inductive { name = "Tree"; params = [("A", a)]; level = 0; constrs = [] },
                   Inductive { name = "Tree"; params = [("A", a)]; level = 0; constrs = [] }))))
  ]
}

let empty_ind = Inductive empty_def
let nat_ind = Inductive nat_def
let list_ind = Inductive (list_def (Universe 0))
let tree_ind = Inductive (tree_def (Inductive nat_def))

let leaf = Constr (1, tree_def (Universe 0), [Inductive nat_def ])
let node n l r = Constr (2, tree_def (Universe 0), [n; l; r])
let sample_tree = node (Constr (1, nat_def, [])) leaf leaf

let env = [("Empty", empty_def);
           ("Nat", nat_def);
           ("List", list_def (Universe 0));
           ("Tree", tree_def (Inductive nat_def))]

let list_length =
    Lam ("l", list_ind,
      Ind ((list_def (Universe 0)),
          Pi ("_", list_ind, nat_ind),
          [ Constr (1, nat_def, []);
            Lam ("x", Universe 0,
              Lam ("xs", list_ind,
                Lam ("ih", nat_ind,
                  Constr (2, nat_def, [Var "ih"]))))],
          Var "l"))

let sample_list =
    Constr (2, list_def (Universe 0),
      [Constr (1, nat_def, []);
       Constr (2, list_def (Universe 0),
         [Constr (2, nat_def, [Constr (1, nat_def, [])]);
          Constr (1, list_def (Universe 0), [])])])

let plus = Lam ("m", nat_ind, Lam ("n", nat_ind,
           Ind (nat_def,
                Pi ("_", nat_ind, nat_ind),
                [Var "m"; Lam ("k", nat_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"])))],
                Var "n")))

let plus_ty = Pi ("m", nat_ind, Pi ("n", nat_ind, nat_ind))

let nat_elim =
    Ind (nat_def,
         Pi ("x", nat_ind, Universe 0),
         [Inductive nat_def; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],
         Constr (1, nat_def, []))

let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"]))

let test_eta () =
    let ctx = [("f", Pi ("x", Universe 0, Universe 0))] in
    let t1 = Lam ("x", Universe 0, App (Var "f", Var "x")) in
    let t2 = Var "f" in
    assert (equal empty_env ctx t1 t2);
    if trace then (Printf.printf "Eta test: "; print_term t1; print_string " = "; print_term t2; print_endline " (passed)");
    Printf.printf "Pi Eta-expansion PASSED.\n"

let test_universe () =
    let ctx = [] in
    let t1 = Universe 0 in
    assert (equal empty_env ctx (infer empty_env ctx t1) (Universe 1));
    check empty_env ctx (Universe 0) (Universe 1);
    check empty_env ctx (Universe 0) (Universe 0);
    begin try let _ = check env ctx (Universe 1) (Universe 0) in assert false with _ -> () end;
    begin try let _ = infer empty_env ctx (Universe (-1)) in assert false with _ -> () end;
    if trace then (Printf.printf "Universe test: Type0 : Type1 (passed)\n");
    Printf.printf "Universe Consistency PASSED\n"

let test_positivity () =
    let bad_def = {
        name = "Bad"; params = []; level = 0;
        constrs = [(1, Pi ("x", Pi ("y", Inductive { name = "Bad"; params = []; level = 0; constrs = [] }, Universe 0), 
                       Inductive { name = "Bad"; params = []; level = 0; constrs = [] }))] } in
    let env = [("Nat", nat_def); ("List", list_def (Universe 0)); ("Bad", bad_def)] in
    assert (match infer env empty_ctx (Inductive nat_def) with | Universe _ -> true | _ -> false);
    assert (match infer env empty_ctx (Inductive (list_def (Universe 0))) with | Universe _ -> true | _ -> false);
    try let _ = infer env empty_ctx (Inductive bad_def) in assert false with Error x -> Printf.printf "Positivity check caught: %s\n" (string_of_error x);
    print_string "Positivity Checking PASSED.\n"

let test_edge_cases () =
    let env = [("Nat", nat_def)] in
    try let _ = infer env empty_ctx (Inductive { name = "X"; params = []; level = 0;
                   constrs = [(1, Pi ("x", Var "Y", Inductive { name = "X"; params = []; level = 0; constrs = [] }))] }) in
        assert false with Error x ->  Printf.printf "Caught unbound type: %s\n" (string_of_error x);
    print_string "Unboundness Checking PASSED.\n"

let test_lambda_totality () =
    let env = [("Nat", nat_def)] in
    let ctx = empty_ctx in
    let valid = Lam ("x", Inductive nat_def, Var "x") in
    assert (match infer env ctx valid with | Pi (_, _, _) -> true | _ -> false);
    try let _ = infer env ctx (Lam ("x", Inductive nat_def, App (Var "x", Constr (1, nat_def, [])))) in assert false
    with Error x -> Printf.printf "Caught non-total lambda: %s\n" (string_of_error x);
    print_string "Lambda Totality PASSED.\n"

let test_basic_setup () =
    let ctx : context = [] in
    let zero = Constr (1, nat_def, []) in
    let one = Constr (2, nat_def, [zero]) in
    let two = Constr (2, nat_def, [one]) in
    let len = App (list_length, sample_list) in
    let add_term = App (App (plus, two), two) in
    let absurd = Lam ("e", empty_ind, Ind (empty_def, Pi ("_", empty_ind, Inductive nat_def), [], Var "e")) in
    begin
        Printf.printf "eval absurd = "; print_term (normalize env ctx absurd); print_endline "";
        Printf.printf "eval Tree.leaf = "; print_term leaf; print_endline "";
        Printf.printf "eval Nat.add(2,2) = "; print_term (normalize env ctx add_term); print_endline "";
        Printf.printf "eval List.length(list) = "; print_term (normalize env ctx len); print_endline "";
        Printf.printf "Nat.Ind = "; print_term nat_elim; print_endline "";
        Printf.printf "Nat.succ : "; print_term (infer env ctx succ); print_endline "";
        Printf.printf "Nat.plus : "; print_term (infer env ctx plus); print_endline "";
        Printf.printf "Nat.Ind : "; print_term (infer env ctx nat_elim); print_endline "";
        print_endline "REALITY CHECK PASSED\n"
    end

let test () =
    test_universe ();
    test_eta ();
    test_positivity ();
    test_edge_cases ();  
    test_lambda_totality ();
    test_basic_setup ()

let () = test ()
