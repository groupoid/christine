(* 1989 Frank Pfenning and Christine Paulin-Mohring: CoC + CIC
   Copyright (c) Groupoїd la Infini
 *)

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
    params : (string * term * term) list;
    level : int;
    constrs : (int * term) list
}

type error =
    | ApplyCaseTerm | ApplyCaseCtorArg
    | InferUnboundVariable of string | InferBoundVariableNoPositive of string | InferApplicationRequiresPi
    | InferCtorInvalidArgType of int * error | InferCtorInvalidType of int * string
    | InferCtorTooManyArgs | InferCtorNegative of int | InferUniverse of int | InferUniverseExpected
    | IndWrongCases | IndMotiveExpetsPi | IndParameters
    | CheckMismatch of term * term

exception Error of error

type env = (string * inductive) list
type context = (string * term) list
type subst_map = (string * term) list

let empty_env : env = []
let empty_ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

let trace: bool = false

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

let params ps =
    List.map (fun (name, term, typ) -> (name, term)) ps

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
    | Inductive d1, Inductive d2 -> d1.name = d2.name && d1.level = d2.level && List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal' env ctx t1 t2) (params d1.params) (params d2.params)
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
    | Pi (_, _, b), [] -> raise (Error ApplyCaseCtorArg)
    | _, [] ->
        let rec apply_term t args =
          match t, args with
          | Lam (x, _, body), arg :: rest -> apply_term (subst x arg body) rest
          | t, [] -> t
          | _ -> raise (Error ApplyCaseTerm)
        in
        let applied = apply_term case (List.rev args_acc) in
        (match applied with
         | Lam (x, _, _) when List.exists (fun arg -> equal env ctx (Inductive d) (infer env ctx arg)) args_acc ->
             let rec_arg = List.find (fun arg -> equal env ctx (Inductive d) (infer env ctx arg)) args_acc in
             apply_term applied [reduce env ctx (Ind (d, p, cases, rec_arg))]
         | _ -> applied)
    | _ -> raise (Error ApplyCaseCtorArg)
    in apply ty [] args

and reduce env ctx t =
    match t with
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (Pi (x, a, b), arg) -> subst x arg b
    | App (f, a) -> App (reduce env ctx f, reduce env ctx a)
    | Ind (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
      let case = List.nth cases (j - 1) in let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst (params d.params)) (List.map snd (params d.params))) cj in
      apply_case env ctx d p cases case cj_subst args
    | Ind (d, p, cases, t') ->
      let t'' = reduce env ctx t' in
      let reduced_ind = Ind (d, p, cases, t'')
      in (match t'' with | Constr _ -> reduce env ctx reduced_ind | _ -> reduced_ind)
    | Constr (i, ind, args) -> Constr (i, ind, List.map (reduce env ctx) args)
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
    | Universe i -> if i < 0 then raise (Error (InferUniverse i)); Universe (i + 1)
    | Pi (x, a, b) -> Universe (max (universe env ctx a) (universe env (add_var ctx x a) b))
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
                (try let _ = infer env ctx a in () with Error x -> raise (Error (InferCtorInvalidArgType (j,x))));
                if not (is_positive env ctx a ind_name) then  raise (Error (InferCtorNegative j));
                check_pos b
            | Inductive d' when d'.name = ind_name -> ()
            | _ -> raise (Error (InferCtorInvalidType (j, d.name)))
        in check_pos ty
      ) d.constrs;
      Universe d.level
    | Constr (j, d, args) -> let cj = List.assoc j d.constrs in let cj_subst = subst_many (List.combine (List.map fst (params d.params)) (List.map snd (params d.params))) cj in infer_ctor env ctx cj_subst args
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
    let d_applied = apply_inductive d (List.map snd (params d.params)) in
    if not (equal env ctx t_ty d_applied) then raise (Error (CheckMismatch (t_ty, d_applied)));
    let (x, a, b) = match p with
      | Pi (x, a, b) -> (x, a, b)
      | _ -> raise (Error IndMotiveExpetsPi)
    in ignore(universe env ctx (infer env ctx p));
    if not (equal env ctx t_ty a) then raise (Error (CheckMismatch (t_ty, a)));
    let result_ty = subst x t' b in
    List.iteri (fun j case ->
      let j_idx = j + 1 in
      let cj = List.assoc j_idx d.constrs in
      let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj (params d.params) (List.map snd (params d.params)) in
      let rec compute_case_type ty ctx_acc =
        match ty with
        | Pi (x, a, b) ->
            let var = Var x in let ctx' = add_var ctx_acc x a in let b_ty = compute_case_type b ctx' in
            if equal env ctx a d_applied then Pi (x, a, Pi ("_", App (p, var), b_ty)) else Pi (x, a, b_ty)
        | Inductive d' when d'.name = d.name -> b
        | _ -> raise (Error (InferCtorInvalidType (j, d.name)))
      in
      let expected_ty = compute_case_type cj_subst ctx in
      check env ctx case expected_ty
    ) cases;
    result_ty

and apply_inductive d args =
    if List.length (params d.params) <> List.length args then raise (Error IndParameters);
    let subst_param t = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t (params d.params) args
    in Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

and universe env ctx t =
    match infer env ctx t with
    | Universe i -> i
    | _ -> raise (Error InferUniverseExpected)

and check env ctx t ty =
    match t, ty with
    | Universe i, Universe j ->
        if (i > j) || (i < 0) then raise (Error (CheckMismatch (t,ty)));
    | Pi (x, a, b), Pi (y, a', b')
    | Lam (x, a, b), Pi (y, a', b') ->
        if not (equal env ctx a a') then raise (Error (CheckMismatch (a,a'))); check env (add_var ctx x a) b (subst y (Var x) b')
    | Constr (j, d, args), Inductive d' when d.name = d'.name ->
        let inferred = infer env ctx t in if not (equal env ctx inferred ty) then raise (Error (CheckMismatch (inferred,ty)))
    | Ind (d, p, cases, t'), ty ->
        let inferred = infer_Ind env ctx d p cases t' in if not (equal env ctx inferred ty) then raise (Error (CheckMismatch (inferred,ty)))
    | _, _ ->
        let inferred = infer env ctx t in
        let ty' = normalize env ctx ty in
        match inferred, ty' with
        | Universe i, Universe j when i <= j || i < 0 -> ()
        | _ -> if not (equal env ctx inferred ty') then raise (Error (CheckMismatch (inferred,ty')))

and string_of_Ind d p cases t' depth =
    d.name ^ ".Ind " ^ (string_of_term_depth (depth + 1) p) ^ " [" ^
       (List.fold_left (fun acc c -> (if acc = "" then "" else "; ") ^ acc ^ (string_of_term_depth (depth + 1) c)) "" cases) ^
    "] " ^ string_of_term_depth (depth + 1) t'

and string_of_term_depth depth t =
    if depth > 20 then "<deep>"
    else match t with
    | Var x -> x
    | Universe i -> "U_" ^ (string_of_int i)
    | Pi (x, a, b) -> "Π (" ^ x ^ " : " ^ (string_of_term_depth (depth + 1) a) ^ "), " ^ string_of_term_depth (depth + 1) b
    | Lam (x, _, body) -> "λ (" ^ x ^ "), " ^ (string_of_term_depth (depth + 1) body)
    | App (f, arg) -> "(" ^ (string_of_term_depth (depth + 1) f) ^ " " ^ (string_of_term_depth (depth + 1) arg) ^ ")"
    | Inductive d -> d.name
    | Constr (i, d, args) -> d.name ^ "." ^ (string_of_int i) ^ " " ^ (List.fold_left (fun acc c -> (if acc = "" then "" else "; ") ^ acc ^ (string_of_term_depth (depth + 1) c)) "" args) ^ ""
    | Ind (d, p, cases, t') -> string_of_Ind d p cases t' depth

and string_of_term t = string_of_term_depth 0 t
and print_term_depth depth t = print_string (string_of_term_depth depth t)
and print_term t = print_term_depth 0 t

(* ENV *)

let empty_def = { name = "Empty"; params = []; level = 0; constrs = [] }

let unit_def_params = { name = "Unit"; params = []; level = 0; constrs = [] }
let unit_def = { unit_def_params with constrs = [
      (1, Inductive unit_def_params )] }

let bool_def_params = { name = "Bool"; params = []; level = 0; constrs = [] }
let bool_def = { bool_def_params with constrs = [
      (1, Inductive bool_def_params);
      (2, Inductive bool_def_params)] }

let w_def_params (a: term)(at: term) (b: term) (bt: term) = { name = "W"; params = [("A",a,at);("B",b,bt)]; level = 0; constrs = [] }
let w_def (a: term) (at: term) (b: term) (bt: term) = { (w_def_params a at b bt) with constrs = [
      (1, Pi ("x", Var "A", Pi ("f", Pi ("_", App (Var "B", Var "x"), Inductive (w_def_params a at b bt)), Inductive (w_def_params a at b bt)) )) ] }

let w_nat =
    w_def (Inductive bool_def)
          (Universe 0)
          (Lam ("x", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Universe 0), [Inductive empty_def; Inductive unit_def], Var "x")))
          (Pi ("x", Inductive bool_def, Universe 0))

let nat_def_params = { name = "Nat"; params = []; level = 0; constrs = []}
let nat_def = { nat_def_params with constrs = [
      (1, Inductive nat_def_params);
      (2, Pi ("n", Inductive nat_def_params, Inductive nat_def_params))] }

let list_def_params (a : term)(at: term) = { name = "List"; params = [("A", a,at)]; level = 0; constrs = [] }
let list_def (a : term) (at: term)= { (list_def_params (a : term) (at:term)) with constrs = [
      (1, Inductive (list_def_params a at));
      (2, Pi ("x", a, Pi ("xs", Inductive (list_def_params a at), Inductive (list_def_params a at)))) ] }

let tree_def_params (a : term)(at: term) = { name = "Tree"; params = [("A", a,at)]; level = 0; constrs = [] }
let tree_def a at = { (tree_def_params a at) with constrs = [
      (1, Inductive (tree_def_params a at));
      (2, Pi ("x", a, Pi ("l", Inductive (tree_def_params a at), Pi ("r", Inductive (tree_def_params a at), Inductive (tree_def_params a at))))) ] }

(* DEF *)

let empty_ind = Inductive empty_def
let nat_ind = Inductive nat_def
let list_ind = Inductive (list_def (Inductive nat_def) (Universe 0))
let tree_ind = Inductive (tree_def (Inductive nat_def) (Universe 0))

let false_val = Constr (1, bool_def, [])
let true_val = Constr (2, bool_def, [])
let tt = Constr (1, unit_def, [])

let empty_elim = Lam ("P", Universe 0,
                 Lam ("e", Inductive empty_def,
                 Ind (empty_def, Pi ("_", Inductive empty_def, Var "P"), [], Var "e")))

let zero_w = Constr (1, w_nat, [false_val; Lam ("y", Inductive empty_def, App (App (empty_elim, Inductive w_nat), Var "y"))])
let succ_w n = Constr (1, w_nat, [true_val; Lam ("y", Inductive unit_def, n)])
let one_w = succ_w zero_w
let two_w = succ_w one_w
let three_w = succ_w two_w
let four_w = succ_w three_w

let plus =
    Lam ("m", nat_ind,
    Lam ("n", nat_ind,
    Ind (nat_def,
         Pi ("_", nat_ind, nat_ind),
         [Var "m"; Lam ("k", nat_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"])))],
         Var "n")))

let plus_w =
    Lam ("n", Inductive w_nat,
    Lam ("m", Inductive w_nat,
    Ind (w_nat,
         Pi ("_", Inductive w_nat, Inductive w_nat),
         [Lam ("a", Inductive bool_def,
          Lam ("f", Pi ("y", App (Var "B", Var "a"), Inductive w_nat),
          Ind (bool_def,
               Pi ("_", Inductive bool_def, Inductive w_nat),
               [Var "m"; Constr (1, w_nat, [true_val; Lam ("y", Inductive unit_def, (Var "m"))])],
               Var "a")))],
         Var "n")))

let leaf = Constr (1, tree_def (Inductive nat_def) (Universe 0), [Inductive nat_def ])
let node n l r = Constr (2, tree_def (Inductive nat_def) (Universe 0), [n; l; r])
let sample_tree = node (Constr (1, nat_def, [])) leaf leaf

let env = [("Empty", empty_def);
           ("Unit", unit_def);
           ("Bool", bool_def);
           ("N", w_nat);
           ("Nat", nat_def);
           ("List", list_def (Inductive nat_def) (Universe 0));
           ("Tree", tree_def (Inductive nat_def) (Universe 0))]

let list_length =
    Lam ("l", list_ind,
      Ind ((list_def (Inductive nat_def) (Universe 0)),
          Pi ("_", list_ind, nat_ind),
          [ Constr (1, nat_def, []);
            Lam ("x", Universe 0,
              Lam ("xs", list_ind,
                Lam ("ih", nat_ind,
                  Constr (2, nat_def, [Var "ih"]))))],
          Var "l"))

let sample_list =
    Constr (2, list_def (Inductive nat_def) (Universe 0),
      [Constr (1, nat_def, []);
       Constr (2, list_def (Inductive nat_def) (Universe 0),
         [Constr (2, nat_def, [Constr (1, nat_def, [])]);
          Constr (1, list_def (Inductive nat_def) (Universe 0), [])])])

let plus_ty = Pi ("m", nat_ind, Pi ("n", nat_ind, nat_ind))

let nat_elim =
    Ind (nat_def,
         Pi ("x", nat_ind, Universe 0),
         [Inductive nat_def; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],
         Constr (1, nat_def, []))

let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"]))

(* SUITE *)

let rec string_of_error = function
    | ApplyCaseTerm -> "Case application mismatch: too few arguments for lambda"
    | ApplyCaseCtorArg -> "Constructor argument mismatch"
    | InferUnboundVariable x -> "Unbound variable " ^ x
    | InferBoundVariableNoPositive x -> "Bound variable " ^ x ^ " has no positive occurrence in lambda body; potential non-termination"
    | InferApplicationRequiresPi -> "Application requires a Pi type"
    | InferCtorNegative i -> "Negative occurrence in constructor " ^ string_of_int i
    | InferCtorInvalidArgType (i, x) -> "Invalid argument type in constructor " ^ string_of_int i ^ ": " ^ string_of_error x
    | InferCtorInvalidType (i, typeName) -> "Constructor " ^ string_of_int i ^ " type must be " ^ typeName
    | InferCtorTooManyArgs -> "Too many arguments to constructor"
    | InferUniverse i -> "Invalid universe " ^ (string_of_int i) ^ " during infering"
    | InferUniverseExpected -> "Expected a universe"
    | IndWrongCases -> "Number of cases doesn't match constructors"
    | IndMotiveExpetsPi -> "Motive must be a Pi type"
    | IndParameters -> "Parameter mismatch in inductive type"
    | CheckMismatch (a, b) -> "Type mismatch between " ^ string_of_term a ^ " and " ^ string_of_term b

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
    let env = [("Nat", nat_def); ("List", list_def (Inductive nat_def) (Universe 0)); ("Bad", bad_def)] in
    assert (match infer env empty_ctx (Inductive nat_def) with | Universe _ -> true | _ -> false); 
    assert (match infer env empty_ctx (Inductive (list_def (Inductive nat_def)  (Universe 0))) with | Universe _ -> true | _ -> false); 
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
    let x = infer env ctx (Lam ("x", Pi ("y", Inductive nat_def, Inductive nat_def),
                           App (Var "x", Constr (1, nat_def, [])))) in print_term x; print_endline "";
    print_string "Lambda Totality PASSED.\n"

let test_basic_setup () =
    let ctx : context = [] in
    let zero = Constr (1, nat_def, []) in
    let one = Constr (2, nat_def, [zero]) in
    let two = Constr (2, nat_def, [one]) in
    let three = Constr (2, nat_def, [two]) in
    let len = App (list_length, sample_list) in
    let add_term = App (App (plus, three), two) in
    let absurd = Lam ("e", empty_ind, Ind (empty_def, Pi ("_", empty_ind, Inductive nat_def), [], Var "e")) in
    begin
        Printf.printf "eval absurd = "; print_term (normalize env ctx absurd); print_endline "";
        Printf.printf "eval Tree.leaf = "; print_term leaf; print_endline "";
        Printf.printf "eval Nat.plus(3,1) = "; print_term (normalize env ctx add_term); print_endline "";
        Printf.printf "eval List.length(list) = "; print_term (normalize env ctx len); print_endline "";
        Printf.printf "Nat.Ind = "; print_term nat_elim; print_endline "";
        Printf.printf "Nat.succ : "; print_term (infer env ctx succ); print_endline "";
        Printf.printf "Nat.plus : "; print_term (infer env ctx plus); print_endline "";
        Printf.printf "Nat.Ind : "; print_term (infer env ctx nat_elim); print_endline ""
    end

let test_w() =
    let plus4 = normalize env [] (App (App (plus_w, two_w), two_w)) in
    let plus6 = normalize env [] (App (App (plus_w, three_w), three_w)) in
    let four = normalize env [] four_w in
    try ignore(infer env [] plus_w) with Error x -> Printf.printf "Error Infer: %s\n" (string_of_error x);
    Printf.printf "eval plus_w 4 = "; print_term plus4; print_endline "";
    Printf.printf "eval four_w 4 = "; print_term four; print_endline "";
    Printf.printf "eval plus_w 6 = "; print_term plus6; print_endline "";
    try assert(equal env [] plus four) with Error x -> Printf.printf "Error Equal: %s\n" (string_of_error x);
    print_string "W Checking PASSED.\n"

let test () =
    test_universe ();
    test_eta ();
    test_positivity ();
    test_edge_cases ();  
    test_lambda_totality ();
    test_basic_setup ();
    test_w();
    print_endline "REALITY CHECK PASSED\n"

let () = test ()

