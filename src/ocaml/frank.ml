(* 1989 (c) Frank Pfenning and Christine Paulin-Mohring *)
(* 2025 (c) Groupoїd la Infini *)
(*
    1) VERIFIER    270
    2) SERIALIZER  30
    3) LIBRARY     320
    4) ENV         15
    5) SAMPLES     70
    6) SUITE       130
    7) RUNNER      20
*)

(* VERIFIER *)

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
    constrs : (int * term) list }

type error =
    | ApplyCaseTerm | ApplyCaseCtorArg
    | InferUnboundVariable of string | InferBoundVariableNoPositive of string | InferApplicationRequiresPi
    | InferCtorInvalidArgType of int * error | InferCtorInvalidType of int * string * term
    | InferCtorTooManyArgs | InferCtorNegative of int | InferUniverse of int | InferUniverseExpected of term
    | IndWrongCases | IndMotiveExpetsPi | IndParameters
    | CheckMismatch of int * term * term | NormalizationDepthExceeded of term

exception Error of error

type env = (string * inductive) list
type context = (string * term) list
type subst_map = (string * term) list

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
let ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx
let trace: bool = false
let rec is_lam = function | Lam _ -> true | _ -> false
let rec lookup_var ctx x = try Some (List.assoc x ctx) with Not_found -> None
let params ps = List.map (fun (name, term, typ) -> (name, term)) ps

let rec equal' env ctx t1 t2 =
    match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i = j
    | Pi (x, a, b), Pi (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Lam (x, d, b), Lam (y, d', b') -> equal' env ctx d d' && equal' env (add_var ctx x d) b (subst y (Var x) b')
    | Lam (x, d, b), t when not (is_lam t) -> let x_var = Var x in equal' env ctx b (App (t, x_var)) && (match infer env ctx t with | Pi (y, a, b') -> equal' env ctx d a | _ -> false)
    | t, Lam (x, d, b) when not (is_lam t) -> let x_var = Var x in equal' env ctx (App (t, x_var)) b && (match infer env ctx t with | Pi (y, a, b') -> equal' env ctx a d | _ -> false)
    | App (f, arg), App (f', arg') -> equal' env ctx f f' && equal' env ctx arg arg'
    | Inductive d1, Inductive d2 -> d1.name = d2.name && d1.level = d2.level && List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal' env ctx t1 t2) (params d1.params) (params d2.params)
    | Constr (j, d1, args1), Constr (k, d2, args2) -> j = k && d1.name = d2.name && List.for_all2 (equal' env ctx) args1 args2
    | Ind (d1, p1, cases1, t1), Ind (d2, p2, cases2, t2) -> d1.name = d2.name && equal' env ctx p1 p2 && List.for_all2 (equal' env ctx) cases1 cases2 && equal' env ctx t1 t2
    | _ -> t1 = t2

and equal env ctx t1' t2' = equal' env ctx (normalize env ctx t1') (normalize env ctx t2')
and normalize env ctx t = normalize' env ctx 0 t

and universe env ctx t =
    match normalize env ctx t with
    | Inductive d -> let inferred = infer env ctx (Inductive d) in (match inferred with | Universe i -> i | _ -> raise (Error (InferUniverseExpected t)))
    | Universe i -> i
    | Pi (x, a, b) -> max (universe env ctx a) (universe env (add_var ctx x a) b)
    | Lam (_, a, b) -> max (universe env ctx a) (universe env (add_var ctx "_" a) b)
    | App (f, _) -> (match normalize env ctx f with | Pi (_, _, b) -> universe env ctx b | _ -> raise (Error InferApplicationRequiresPi))
    | Constr (_, d, _) -> (match infer env ctx t with | Universe i -> i | _ -> d.level)
    | Ind (d, _, _, t') -> universe env ctx t'
    | Var x -> (match lookup_var ctx x with | Some ty -> universe env ctx ty | None -> raise (Error (InferUnboundVariable x)))

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
        let domain_ty = infer env ctx domain in
        check env ctx domain domain_ty;
        Pi (x, domain, infer env (add_var ctx x domain) body)
    | App (f, arg) -> (match infer env ctx f with | Pi (x, a, b) -> check env ctx arg a; subst x arg b | _ -> raise (Error InferApplicationRequiresPi))
    | Inductive d ->
      List.iter (fun (name, term, typ) -> check env ctx term typ) d.params;
      let param_subst = List.combine (List.map fst (params d.params)) (List.map snd (params d.params)) in
      let constr_levels = List.map (fun (_, ty) -> universe env ctx (subst_many param_subst ty)) d.constrs in
      let param_levels = List.map (fun (_, _, typ) -> universe env ctx typ) d.params in
      let max_level = List.fold_left max d.level (param_levels @ constr_levels) in
      List.iter (fun (j, ty) ->
        let rec check_pos ty' ctx' =
            match ty' with
            | Pi (x, a, b) ->
                let a_ty = infer env ctx' a in
                if not (is_positive env ctx' a d.name) then raise (Error (InferCtorNegative j));
                check_pos b (add_var ctx' x a_ty)
            | Inductive d' when d'.name = d.name -> ()
            | _ -> raise (Error (InferCtorInvalidType (j, d.name, ty')))
        in check_pos ty ctx
      ) d.constrs;
      Universe max_level
    | Constr (j, d, args) ->
      let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst (params d.params)) (List.map snd (params d.params))) cj in
      let result = infer_ctor env ctx cj_subst args in
      result
    | Ind (d, p, cases, t') -> infer_Ind env ctx d p cases t'
    in let _ = if (trace) then Printf.printf "Infer %s -> %s\n" (string_of_term t) (string_of_term res) else ()
    in let normalized = normalize env ctx res
    in normalized

and infer_ctor env ctx ty args =
    let rec check_args ty args_acc remaining_args ctx =
        match ty, remaining_args with
        | Pi (x, a, b), arg :: rest ->
            let arg_ty = infer env ctx arg in
            check env ctx arg a;
            let ctx' = add_var ctx x arg_ty in
            check_args (subst x arg b) (arg :: args_acc) rest ctx'
        | Pi (_, _, _), [] -> raise (Error (InferCtorTooManyArgs))
        | _, arg :: _ -> raise (Error (InferCtorTooManyArgs))
        | Inductive d, [] -> ty
        | _ -> ty
    in check_args ty [] args ctx

and infer_Ind env ctx d p cases t' =
    if List.length cases <> List.length d.constrs then raise (Error IndWrongCases);
    let t_ty = infer env ctx t' in
    let d_applied = apply_inductive env ctx d (List.map snd (params d.params)) in
    if not (equal env ctx t_ty d_applied) then raise (Error (CheckMismatch (2, t_ty, d_applied)));
    let (x, a, b) = match p with
      | Pi (x, a, b) -> (x, a, b)
      | _ -> raise (Error IndMotiveExpetsPi)
    in ignore(universe env ctx (infer env ctx p));
    if not (equal env ctx t_ty a) then raise (Error (CheckMismatch (3, t_ty, a)));
    let result_ty = subst x t' b in
    List.iteri (fun j case ->
      let j_idx = j + 1 in
      let cj = List.assoc j_idx d.constrs in
      let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj (params d.params) (List.map snd (params d.params)) in
      let rec compute_case_type ty ctx_acc =
        match ty with
        | Pi (x, a, b) ->
            let var = Var x in let ctx' = add_var ctx_acc x a in
            let b_ty = compute_case_type b ctx' in
            if equal env ctx a d_applied then Pi (x, a, Pi ("_", App (p, var), b_ty)) else Pi (x, a, b_ty)
        | Inductive d' when d'.name = d.name -> b
        | _ when equal env ctx ty d_applied -> b
        | _ -> raise (Error (InferCtorInvalidType (j, d.name, ty)))
      in
      let expected_ty = compute_case_type cj_subst ctx in
      if (trace) then Printf.printf "Checking case %d: %s against %s\n" j (string_of_term case) (string_of_term expected_ty);
      check env ctx case expected_ty
    ) cases;
    if (trace) then Printf.printf "infer_Ind result: %s\n" (string_of_term result_ty);
    result_ty

and apply_inductive env ctx d args =
    if List.length (params d.params) <> List.length args then raise (Error IndParameters);
    List.iter2 (fun (_, _, typ) arg -> check env ctx arg typ) d.params args;
    let subst_param t = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t (params d.params) args
    in Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

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
         | Lam (x, _, body) when List.exists (fun arg -> equal env ctx (Inductive d) (infer env ctx arg)) args_acc ->
             let rec_arg = List.find (fun arg -> equal env ctx (Inductive d) (infer env ctx arg)) args_acc in
             if not (pos x body) then raise (Error (ApplyCaseTerm));
             apply_term applied [reduce env ctx (Ind (d, p, cases, rec_arg))]
         | _ -> applied)
    | _ -> raise (Error ApplyCaseCtorArg)
    in apply ty [] args

and normalize' env ctx depth t =
    if depth > 100 then raise (Error (NormalizationDepthExceeded t));
    let t' = reduce env ctx t in (if equal' env ctx t t' then t else normalize env ctx t')

and reduce env ctx t =
    match t with
    | Lam (x, a, b) -> Lam (x, reduce env ctx a, reduce env (add_var ctx x a) b)
    | Pi (x, a, b) -> Pi (x, reduce env ctx a, reduce env (add_var ctx x a) b)
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (Pi (x, a, b), arg) -> subst x arg b
    | App (f, a) -> let f' = reduce env ctx f in (match f' with | Lam (x, _, b) -> reduce env ctx (subst x a b) | _ -> App (f', reduce env ctx a))
    | Ind (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
      let case = List.nth cases (j - 1) in let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst (params d.params)) (List.map snd (params d.params))) cj in
      reduce env ctx (apply_case env ctx d p cases case cj_subst args)
    | Ind (d, p, cases, t') ->
      let t'' = reduce env ctx t' in
      let reduced_ind = Ind (d, p, cases, t'')
      in (match t'' with | Constr _ -> reduced_ind | _ -> reduced_ind)
    | Constr (i, ind, args) -> Constr (i, ind, List.map (reduce env ctx) args)
    | _ -> t

and check env ctx t ty =
    match t, ty with
    | Constr (j, d, args), Inductive d' when d.name = d'.name ->
        let inferred = infer env ctx t in
        if not (equal env ctx inferred ty) then raise (Error (CheckMismatch (6, inferred, ty)))
    | Universe i, Universe j ->
        if (i > j) || (i < 0) then raise (Error (CheckMismatch (4, t, ty)));
    | Pi (x, a, b), Pi (y, a', b')
    | Lam (x, a, b), Pi (y, a', b') ->
        if not (equal env ctx a a') then raise (Error (CheckMismatch (5, a, a')));
        let ctx' = add_var ctx x a in
        let b'_subst = subst y (Var x) b' in
        check env ctx' b b'_subst
    | Ind (d, p, cases, t'), ty ->
        let inferred = infer_Ind env ctx d p cases t' in
        if not (equal env ctx inferred ty) then raise (Error (CheckMismatch (7, inferred, ty)))
    | _, _ ->
        let inferred = infer env ctx t in
        let ty' = normalize env ctx ty in
        match inferred, ty' with
        | Universe i, Universe j when i <= j -> ()
        | _ -> if not (equal env ctx inferred ty') then raise (Error (CheckMismatch (8, inferred, ty')))

(* SERIALIZER *)

and string_of_Ind d p cases t' depth =
    d.name ^ ".Ind " ^ (string_of_term_depth (depth + 1) p) ^ " [" ^
       (List.fold_left (fun acc c -> acc ^ (string_of_term_depth (depth + 1) c) ^ ";") "" cases) ^
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

(* LIBRARY *)

(* Empty *)

let empty_def = { name = "Empty"; params = []; level = 0; constrs = [] }
let empty_ind = Inductive empty_def
let empty_elim = Lam ("P", Universe 0, Lam ("e", Inductive empty_def, Ind (empty_def, Pi ("_", Inductive empty_def, Var "P"), [], Var "e")))

(* Unit *)

let unit_def_params = { name = "Unit"; params = []; level = 0; constrs = [] }
let unit_def = { unit_def_params with constrs = [
      (1, Inductive unit_def_params )] }
let tt = Constr (1, unit_def, [])

(* Bool *)

let bool_def_params = { name = "Bool"; params = []; level = 0; constrs = [] }
let bool_def = { bool_def_params with constrs = [
      (1, Inductive bool_def_params);
      (2, Inductive bool_def_params)] }
let false_val = Constr (1, bool_def, [])
let true_val = Constr (2, bool_def, [])

(* Nat *)

let nat_def_params = { name = "Nat"; params = []; level = 0; constrs = []}
let nat_def = { nat_def_params with constrs = [
      (1, Inductive nat_def_params);
      (2, Pi ("n", Inductive nat_def_params, Inductive nat_def_params))] }
let nat_ind = Inductive nat_def
let nat_elim = Ind (nat_def, Pi ("x", nat_ind, Universe 0), [Inductive nat_def; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],  Constr (1, nat_def, []))
let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"]))
let zero = Constr (1, nat_def, [])
let one = Constr (2, nat_def, [zero])
let two = Constr (2, nat_def, [one])
let three = Constr (2, nat_def, [two])
let four = Constr (2, nat_def, [three])
let five = Constr (2, nat_def, [four])
let six = Constr (2, nat_def, [five])
let seven = Constr (2, nat_def, [six])
let bool_elim = Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Inductive nat_def), [zero; Constr (2, nat_def, [zero])], Var "s"))

(* List *)

let list_def_params (a : term)(at: term) = { name = "List"; params = [("A", a,at)]; level = 0; constrs = [] }
let list_def (a : term) (at: term)= { (list_def_params (a : term) (at:term)) with constrs = [
      (1, Inductive (list_def_params a at));
      (2, Pi ("x", a, Pi ("xs", Inductive (list_def_params a at), Inductive (list_def_params a at)))) ] }
let list_ind = Inductive (list_def (Inductive nat_def) (Universe 0))

(* Tree *)

let tree_def_params (a : term)(at: term) = { name = "Tree"; params = [("A", a,at)]; level = 0; constrs = [] }
let tree_def a at = { (tree_def_params a at) with constrs = [
      (1, Inductive (tree_def_params a at));
      (2, Pi ("x", a, Pi ("l", Inductive (tree_def_params a at), Pi ("r", Inductive (tree_def_params a at), Inductive (tree_def_params a at))))) ] }
let tree_ind = Inductive (tree_def (Inductive nat_def) (Universe 0))
let leaf = Constr (1, tree_def (Inductive nat_def) (Universe 0), [Inductive nat_def ])
let node n l r = Constr (2, tree_def (Inductive nat_def) (Universe 0), [n; l; r])

(* Fin *)

let fin_def_params (n: term) (nt: term) = { name = "Fin"; params = [("n", n, nt)]; level = 0; constrs = [] }
let fin_def n nt = {
    (fin_def_params n nt) with constrs = [
        (1, Pi ("n", (Inductive nat_def), Inductive (fin_def_params n nt)));
        (2, Pi ("n", (Inductive nat_def), (Pi ("k", Inductive (fin_def_params n nt), Inductive (fin_def_params n nt))))) ] }
let fin_ind = Inductive (fin_def (one) (Inductive nat_def))
let fzero = Constr (1, fin_def (one) (Inductive nat_def), [one])

(* Vec *)

let vec_def_params a at n nt = { name = "Vec"; params = [("A", a, at); ("n", n, nt)]; level = 0; constrs = [] }
let vec_def a at n nt = { (vec_def_params a at n nt) with constrs = [
      (1, Inductive (vec_def_params a at n nt));
      (2, Pi ("x", a, Pi ("xs", Inductive (vec_def_params a at n nt), Inductive (vec_def_params a at (App (succ, n)) nt)))) ] }
let vec_ind = Inductive (vec_def (Inductive nat_def) (Universe 0) (Constr (2, nat_def, [Constr (1, nat_def, [])])) (Inductive nat_def))
let vnil = Constr (1, (vec_def (Inductive nat_def) (Universe 0) (Constr (1, nat_def, [])) (Universe 0)), [])
let vcons = Constr (2, (vec_def (Inductive nat_def) (Universe 0) (Constr (1, nat_def, [])) (Universe 0)), [zero; vnil])

(* W *)

let w_def_params (a: term) (at: term) (b: term) (bt: term) = { name = "N"; params = [("A", a, at);("B", b, bt)]; level = 0; constrs = [] }
let w_def (a: term) (at: term) (b: term) (bt: term) = { (w_def_params a at b bt) with constrs = [
      (1, Pi ("z", a, Pi ("f", Pi ("_", App (b, Var "z"), Inductive (w_def_params a at b bt)), Inductive (w_def_params a at b bt)) )) ] }

(* N *)

let w_nat = {
      (w_def (Inductive bool_def)
      (Universe 0)
      (Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Universe 0), [Inductive empty_def; Inductive unit_def], Var "s")))
      (Pi ("x", Inductive bool_def, Universe 0))) with name = "N" }

let zero_w  = Constr (1, { w_nat with name = "N" }, [false_val; Lam ("y", Inductive empty_def, App (App (empty_elim, Inductive { w_nat with name = "N" } ), Var "y"))])
let succ_w  = Lam("d", Inductive w_nat, Constr (1, { w_nat with name = "N" }, [true_val; Lam ("y", Inductive unit_def, Var "d")]))
let one_w   = normalize [] [] (App (succ_w,zero_w))
let two_w   = normalize [] [] (App (succ_w,one_w))
let three_w = normalize [] [] (App (succ_w,two_w))
let four_w  = normalize [] [] (App (succ_w,three_w))
let five_w  = normalize [] [] (App (succ_w,four_w))
let six_w   = normalize [] [] (App (succ_w,five_w))
let seven_w = normalize [] [] (App (succ_w,six_w))

(* ENV *)

let env = [("Empty", Inductive empty_def);
           ("Unit", Inductive unit_def);
           ("Bool", Inductive bool_def);
           ("Fin", Inductive (fin_def (one) (Inductive nat_def)));
           ("N", Inductive w_nat);
           ("B", Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Universe 0), [Inductive empty_def; Inductive unit_def], Var "s")));
           ("Nat", Inductive nat_def);
           ("VecNat0", Inductive (vec_def (Inductive nat_def) (Universe 0) (Constr (1, nat_def, [])) (Inductive nat_def)));
           ("VecNat1", Inductive (vec_def (Inductive nat_def) (Universe 0) (Constr (2, nat_def, [Constr (1, nat_def, [])])) (Inductive nat_def)));
           ("List", Inductive (list_def (Inductive nat_def) (Universe 0)));
           ("Tree", Inductive (tree_def (Inductive nat_def) (Universe 0)))]

(* SAMPLES *)

let plus =
    Lam ("m", nat_ind,
    Lam ("n", nat_ind,
    Ind (nat_def,
         Pi ("_", nat_ind, nat_ind),
         [Var "m"; Lam ("k", nat_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"])))],
         Var "n")))

let plus_ty = Pi ("m", nat_ind, Pi ("n", nat_ind, nat_ind))

let plus_w =
    let b_term = Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Universe 0), [Inductive empty_def; Inductive unit_def], Var "s")) in
    Lam ("n", Inductive w_nat,
    Lam ("m", Inductive w_nat,
    Ind (w_nat,
         Pi ("_", Inductive w_nat, Inductive w_nat),
         [Lam ("a", Inductive bool_def,
          Lam ("f", Pi ("y", App (b_term, Var "a"), Inductive w_nat),
          Ind (bool_def,
               Pi ("_", Inductive bool_def, Inductive w_nat),
               [Var "m"; App (succ_w, App (Var "f", Var "a"))],
               Var "a")))],
         Var "n")))

let to_nat_w =
    let b_term = Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Universe 0), [Inductive empty_def; Inductive unit_def], Var "s")) in
    Lam ("w", Inductive w_nat,
    Ind (w_nat,
         Pi ("_", Inductive w_nat, Inductive nat_def),
         [Lam ("z", Inductive bool_def,
          Lam ("f", Pi ("y", App (b_term, Var "z"), Inductive w_nat),
          Ind (bool_def,
               Pi ("_", Inductive bool_def, Inductive nat_def),
               [zero; one],
               Var "z")))],
         Var "w"))

let from_nat_w =
    Lam ("n", Inductive nat_def,
    Ind (nat_def,
         Pi ("_", Inductive nat_def, Inductive w_nat),
         [zero_w; Lam ("k", Inductive nat_def, Lam ("ih", Inductive w_nat, App (succ, Var "ih")))],
         Var "n"))

let plus_w_correct =
    Lam ("n", Inductive w_nat,
    Lam ("m", Inductive w_nat,
    App (from_nat_w, App (App (plus, App (to_nat_w, Var "n")), App (to_nat_w, Var "m")))))

let sample_tree = node (Constr (1, nat_def, [])) leaf leaf

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

(* SUITE *)

let rec string_of_error = function
    | ApplyCaseTerm -> "Case application mismatch: too few arguments for lambda"
    | ApplyCaseCtorArg -> "Constructor argument mismatch"
    | InferUnboundVariable x -> "Unbound variable " ^ x
    | InferBoundVariableNoPositive x -> "Bound variable " ^ x ^ " has no positive occurrence in lambda body; potential non-termination"
    | InferApplicationRequiresPi -> "Application requires a Pi type"
    | InferCtorNegative i -> "Negative occurrence in constructor " ^ string_of_int i
    | InferCtorInvalidArgType (i, x) -> "Invalid argument type in constructor " ^ string_of_int i ^ ": " ^ string_of_error x
    | InferCtorInvalidType (i, typeName, ty) -> "Constructor " ^ string_of_int i ^ " should belong to type " ^ typeName ^ " not " ^ (string_of_term ty)
    | InferCtorTooManyArgs -> "Too many arguments to constructor"
    | InferUniverse i -> "Invalid universe " ^ (string_of_int i) ^ " during infering"
    | InferUniverseExpected x -> "This type should belong to a Universe: " ^ (string_of_term x)
    | IndWrongCases -> "Number of cases doesn't match constructors"
    | IndMotiveExpetsPi -> "Motive must be a Pi type"
    | IndParameters -> "Parameter mismatch in inductive type"
    | CheckMismatch (i, a, b) -> "Type mismatch (" ^ (string_of_int i) ^ ") between " ^ string_of_term a ^ " and " ^ string_of_term b
    | NormalizationDepthExceeded t -> "Normalization exceeded depth limit: " ^ string_of_term t

let test_eta () =
    let ctx = [("f", Pi ("x", Universe 0, Universe 0))] in
    let t1 = Lam ("x", Universe 0, App (Var "f", Var "x")) in
    let t2 = Var "f" in
    assert (equal [] ctx t1 t2);
    if trace then (Printf.printf "Eta test: "; print_term t1; print_string " = "; print_term t2; print_endline " (passed)");
    Printf.printf "Pi Eta-expansion PASSED.\n"

let test_universe () =
    let t1 = Universe 0 in
    assert (equal [] ctx (infer [] ctx t1) (Universe 1));
    check [] ctx (Universe 0) (Universe 1);
    check [] ctx (Universe 0) (Universe 0);
    begin try let _ = check [] ctx (Universe 1) (Universe 0) in assert false with _ -> () end;
    begin try let _ = infer [] ctx (Universe (-1)) in assert false with _ -> () end;
    if trace then (Printf.printf "Universe test: Type0 : Type1 (passed)\n");
    Printf.printf "Universe Consistency PASSED\n"

let test_positivity () =
    let bad_def = {
        name = "Bad"; params = []; level = 0;
        constrs = [(1, Pi ("x", Pi ("y", Inductive { name = "Bad"; params = []; level = 0; constrs = [] }, Universe 0),
                       Inductive { name = "Bad"; params = []; level = 0; constrs = [] }))] } in
    let env = [("Nat", nat_def); ("List", list_def (Inductive nat_def) (Universe 0)); ("Bad", bad_def)] in
    assert (match infer env ctx (Inductive nat_def) with | Universe _ -> true | _ -> false);
    assert (match infer env ctx (Inductive (list_def (Inductive nat_def)  (Universe 0))) with | Universe _ -> true | _ -> false);
    try let _ = infer env ctx (Inductive bad_def) in assert false with Error x -> Printf.printf "Positivity check caught: %s\n" (string_of_error x);
    print_string "Positivity Checking PASSED.\n"

let test_edge_cases () =
    let env = [("Nat", nat_def)] in
    try let _ = infer env ctx (Inductive { name = "X"; params = []; level = 0;
                   constrs = [(1, Pi ("x", Var "Y", Inductive { name = "X"; params = []; level = 0; constrs = [] }))] }) in
        assert false with Error x ->  Printf.printf "Caught unbound type: %s\n" (string_of_error x);
    print_string "Unboundness Checking PASSED.\n"

let test_lambda_typing () =
    let env = [("Nat", nat_def)] in
    let id = Lam ("x", Inductive nat_def, Var "x") in
    assert (match infer env ctx id with | Pi (_, Inductive d1, Inductive d2) when d1.name = "Nat" && d2.name = "Nat" -> true | _ -> false);
    let const = Lam ("x", Inductive nat_def, Constr (1, nat_def, [])) in
    assert (match infer env ctx const with | Pi (_, Inductive d1, Inductive d2) when d1.name = "Nat" && d2.name = "Nat" -> true | _ -> false);
    let apply = Lam ("f", Pi ("y", Inductive nat_def, Inductive nat_def),  App (Var "f", Constr (1, nat_def, []))) in
    assert (match infer env ctx apply with | Pi (_, Pi (_, Inductive d1, Inductive d2), Inductive d3) when d1.name = "Nat" && d2.name = "Nat" && d3.name = "Nat" -> true | _ -> false);
    Printf.printf "Identity: "; print_term (infer env ctx id); print_endline "";
    Printf.printf "Constant: "; print_term (infer env ctx const); print_endline "";
    Printf.printf "Apply: "; print_term (infer env ctx apply); print_endline "";
    try let _ = infer env ctx (Lam ("x", Inductive nat_def, App (Var "x", Constr (1, nat_def, [])))) in assert false
    with Error x -> Printf.printf "Caught requires Pi: %s\n" (string_of_error x);
    let x = infer env ctx (Lam ("x", Pi ("y", Inductive nat_def, Inductive nat_def), App (Var "x", Constr (1, nat_def, [])))) in print_term x; print_endline "";
    Printf.printf "Lambda Typing PASSED\n"

let test_basic_setup () =
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
        Printf.printf "eval Nat.plus(3,2) = "; print_term (normalize env ctx add_term); print_endline "";
        Printf.printf "eval List.length(list) = "; print_term (normalize env ctx len); print_endline "";
        Printf.printf "Nat.Ind = "; print_term nat_elim; print_endline "";
        Printf.printf "Nat.succ : "; print_term (infer env ctx succ); print_endline "";
        Printf.printf "Nat.plus : "; print_term (infer env ctx plus); print_endline "";
        Printf.printf "Nat.Ind : "; print_term (infer env ctx nat_elim); print_endline ""
    end

let test_robustness () =
    let env = [("Nat", nat_def)] in
    let infinite_ind = Ind (nat_def, Pi ("x", nat_ind, nat_ind), [Lam ("x", nat_ind, Ind (nat_def, Pi ("x", nat_ind, nat_ind), [], Var "x"))], Constr (1, nat_def, [])) in
    try let _ = normalize env [] infinite_ind in assert false with _ -> Printf.printf "Caught wrong infinite Induction\n";
    let under_applied = Constr (2, nat_def, []) in
    try let _ = infer env [] under_applied in assert false with Error (InferCtorTooManyArgs) -> Printf.printf "Caught under-applied constructor\n";
    Printf.printf "Robustness PASSED\n"

let test_fin_vec () =
    (try Printf.printf "Fin 1: "; print_term (infer env ctx fzero); print_endline "" with Error x -> Printf.printf "Catch: %s\n" (string_of_error x));
    (try Printf.printf "Vec Nat 0: "; print_term (infer env ctx vnil); print_endline "";
         Printf.printf "Vec Nat 1: "; print_term (infer env ctx vcons); print_endline "" with Error x -> Printf.printf "Catch: %s\n" (string_of_error x));
    Printf.printf "Fin and Vec PASSED\n"

let test_w() =
    let plus4w = normalize env [] (App (App (plus_w, two_w), two_w)) in
    let plus6w = normalize env [] (App (App (plus_w, three_w), three_w)) in
    let four4  = normalize env [] (App (to_nat_w, four_w)) in begin
        Printf.printf "eval plus4w 4 = "; print_term plus4w; print_endline "";
        Printf.printf "eval plus6w 6 = "; print_term plus6w; print_endline "";
        Printf.printf "eval four4w 4 = "; print_term four_w; print_endline "";
        Printf.printf "eval conv4  4 = "; print_term four4;  print_endline "";
        Printf.printf "zero_w : "; print_term (infer env [] zero_w); print_endline "";
        Printf.printf "succ_w : "; print_term (infer env [] succ_w); print_endline "";
        Printf.printf "w_nat : "; print_term (infer env [] (Inductive w_nat)); print_endline "";
        Printf.printf "Four4 : "; print_term (normalize env [] four4); print_endline "";
        try Printf.printf "plus_w : "; print_term (infer env [] plus_w); print_endline ""
        with Error x -> Printf.printf "Catch: %s\n" (string_of_error x);
        Printf.printf "to_nat_w : "; print_term (infer env [] to_nat_w); print_endline "";
    end;
    if (equal env [] plus4w four_w) then Printf.printf "W Checking PASSED\n" else Printf.printf "W Checking FAILED (plus4w <> four_w)\n"

let test_false() =
    try let ty = infer env [] false_val in Printf.printf "false_val type: %s\n" (string_of_term ty)
    with Error x -> Printf.printf "False Error: %s\n" (string_of_error x)

let test_bool() =
    try (Printf.printf "bool_elim : "; print_term (infer env [] bool_elim); print_endline "")
    with Error x -> Printf.printf "Catch: %s\n" (string_of_error x)

(* RUNNER *)

let test () =
    test_universe ();
    test_eta ();
    test_positivity ();
    test_edge_cases ();
    test_lambda_typing ();
    test_basic_setup ();
    test_false();
    test_robustness ();
    test_fin_vec ();
    test_bool();
    test_w();
    print_endline "REALITY CHECK PASSED\n"

let () = test ()

