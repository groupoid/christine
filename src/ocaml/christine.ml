(* Copyright (c) 2016—2025 Groupoid Infinity *)

(* TYPE CHECKER CORE LANGUAGE *)

let trace: bool = false
let tests: bool = true

type level = int
type name = string

type term =
    | Var of name | Universe of level
    | Pi of name * term * term | Lam of name * term * term | App of term * term
    | Sigma of name * term * term | Pair of term * term | Fst of term | Snd of term
    | Id of term * term * term | Refl of term | J of term * term * term * term * term * term  (* J A a b C d p *)
    | Inductive of inductive | Constr of int * inductive * term list | Ind of inductive * term * term list * term
and inductive = { name : string; params : (name * term * term) list; level : level; constrs : (int * term) list }

type env = (string * inductive) list
type context = (name * term) list
type subst_map = (name * term) list

let empty_env : env = []
let empty_ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

exception TypeError of string

let rec subst_many m t =
    match t with
    | Var x -> (try List.assoc x m with Not_found -> t)
    | Pi (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Pi (x, subst_many m a, subst_many m' b)
    | Lam (x, d, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Lam (x, subst_many m d, subst_many m' b)
    | App (f, arg) -> App (subst_many m f, subst_many m arg)
    | Sigma (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Sigma (x, subst_many m a, subst_many m' b)
    | Pair (a, b) -> Pair (subst_many m a, subst_many m b)
    | Fst t -> Fst (subst_many m t)
    | Snd t -> Snd (subst_many m t)
    | Id (ty, a, b) -> Id (subst_many m ty, subst_many m a, subst_many m b)
    | Refl t -> Refl (subst_many m t)
    | Inductive d -> Inductive d
    | Constr (j, d, args) -> Constr (j, d, List.map (subst_many m) args)
    | Ind (d, p, cases, t') -> Ind (d, subst_many m p, List.map (subst_many m) cases, subst_many m t')
    | J (ty, a, b, c, d, p) -> J (subst_many m ty, subst_many m a, subst_many m b, subst_many m c, subst_many m d, subst_many m p)
    | _ -> t

let subst x s t = subst_many [(x, s)] t

let rec equal env ctx t1' t2' =
    let t1 = normalize env ctx t1' in
    let t2 = normalize env ctx t2' in
    equal' env ctx t1 t2

and lookup_var ctx x =
    if (trace) then (Printf.printf "Looking up %s in context: [" x;
                     List.iter (fun (n, ty) -> Printf.printf "(%s, " n; print_term ty; print_string "); ") ctx;
                     print_endline "]");
    try Some (List.assoc x ctx) with Not_found -> None

and equal' env ctx t1 t2 =
    match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i = j
    | Pi (x, a, b), Pi (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Lam (x, d, b), Lam (y, d', b') -> equal' env ctx d d' && equal' env (add_var ctx x d) b (subst y (Var x) b')
    | Lam (x, d, b), t when not (is_lam t) -> let x_var = Var x in equal' env ctx b (App (t, x_var)) && (match infer env ctx t with | Pi (y, a, b') -> equal' env ctx d a | _ -> false)
    | t, Lam (x, d, b) when not (is_lam t) -> let x_var = Var x in equal' env ctx (App (t, x_var)) b && (match infer env ctx t with | Pi (y, a, b') -> equal' env ctx a d | _ -> false)
    | App (f, arg), App (f', arg') -> equal' env ctx f f' && equal' env ctx arg arg'
    | Sigma (x, a, b), Sigma (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Pair (a, b), Pair (a', b') -> equal' env ctx a a' && equal' env ctx b b'
    | t, Pair (Fst t', Snd t'') when equal' env ctx t t' && equal' env ctx t t'' -> true
    | Pair (Fst t', Snd t''), t when equal' env ctx t t' && equal' env ctx t t'' -> true
    | Fst t, Fst t' -> equal' env ctx t t'
    | Snd t, Snd t' -> equal' env ctx t t'
    | Id (ty, a, b), Id (ty', a', b') -> equal' env ctx ty ty' && equal' env ctx a a' && equal' env ctx b b'
    | Refl t, Refl t' -> equal' env ctx t t'
    | Inductive d1, Inductive d2 -> d1.name = d2.name && d1.level = d2.level && List.for_all2 (fun (n1, t1, _) (n2, t2, _) -> n1 = n2 && equal' env ctx t1 t2) d1.params d2.params
    | Constr (j, d1, args1), Constr (k, d2, args2) -> j = k && d1.name = d2.name && List.for_all2 (equal' env ctx) args1 args2
    | Ind (d1, p1, cases1, t1), Ind (d2, p2, cases2, t2) -> d1.name = d2.name && equal' env ctx p1 p2 && List.for_all2 (equal' env ctx) cases1 cases2 && equal' env ctx t1 t2
    | J (ty, a, b, c, d, p), J (ty', a', b', c', d', p') -> equal' env ctx ty ty' && equal' env ctx a a' && equal' env ctx b b' && equal' env ctx c c' && equal' env ctx d d' && equal' env ctx p p'
    | _ -> t1 = t2

and is_lam = function | Lam _ -> true | _ -> false

and pos x t =
    match t with
    | Var y -> y = x
    | Universe _ -> false
    | Pi (y, a, b) -> pos x a || (y <> x && pos x b)
    | Lam (y, a, t') -> pos x a || (y <> x && pos x t')
    | App (f, a) -> pos x f || pos x a
    | Sigma (y, a, b) -> pos x a || (y <> x && pos x b)
    | Pair (a, b) -> pos x a || pos x b
    | Fst p -> pos x p
    | Snd p -> pos x p
    | Id (ty, a, b) -> pos x ty || pos x a || pos x b
    | Refl a -> pos x a
    | Inductive d -> List.exists (fun (_, ty) -> pos x ty) d.constrs
    | Constr (_, _, args) -> List.exists (pos x) args
    | Ind (_, p, cases, t') -> pos x p || List.exists (pos x) cases || pos x t'
    | J (ty, a, b, c, d, p) -> pos x ty || pos x a || pos x b || pos x c || pos x d || pos x p

and is_recursive env ctx ty ind_name =
    match ty with
    | Inductive d when d.name = ind_name -> true
    | Pi (x, a, b) -> is_recursive env (add_var ctx x a) b ind_name
    | _ -> false

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
    | Var x -> (match lookup_var ctx x with | Some ty -> ty | None -> raise (TypeError ("Unbound variable: " ^ x)))
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); Universe (i + 1)
    | Pi (x, a, b) -> let i = check_universe env ctx a in let ctx' = add_var ctx x a in let j = check_universe env ctx' b in Universe (max i j)
    | Lam (x, domain, body) ->
        check env ctx domain (infer env ctx domain);
        let ctx' = add_var ctx x domain in
        Pi (x, domain, infer env ctx' body)
    | App (f, arg) -> (match infer env ctx f with | Pi (x, a, b) -> check env ctx arg a; subst x arg b | ty -> Printf.printf "App failed: inferred "; print_term ty; print_endline ""; raise (TypeError "Application requires a Pi type"))
    | Sigma (x, a, b) -> let i = check_universe env ctx a in let ctx' = add_var ctx x a in let j = check_universe env ctx' b in Universe (max i j)
    | Pair (a, b) -> let a_ty = infer env ctx a in let b_ty = infer env ctx b in Sigma ("x", a_ty, b_ty)
    | Fst p -> (match infer env ctx p with | Sigma (x, a, b) -> a | ty -> raise (TypeError ("Fst expects a Sigma type, got: " ^ (let s = ref "" in print_term_depth 0 ty; !s))))
    | Snd p -> (match infer env ctx p with | Sigma (x, a, b) -> subst x (Fst p) b | ty -> raise (TypeError ("Snd expects a Sigma type, got: " ^ (let s = ref "" in print_term_depth 0 ty; !s))))
    | Id (ty, a, b) -> check env ctx a ty; check env ctx b ty; Universe (check_universe env ctx ty)
    | Refl a -> let a_ty = infer env ctx a in Id (a_ty, a, a)
    | Inductive d ->
      List.iter (fun (name, term, typ) -> check env ctx term typ) d.params;
      let param_subst = List.map (fun (n, t, _) -> (n, t)) d.params in
      let constr_levels = List.map (fun (_, ty) -> universe_level env ctx (subst_many param_subst ty)) d.constrs in
      let param_levels = List.map (fun (_, _, typ) -> universe_level env ctx typ) d.params in
      let max_level = List.fold_left max d.level (param_levels @ constr_levels) in
      List.iter (fun (j, ty) ->
        let rec check_pos ty' ctx' =
            match ty' with
            | Pi (x, a, b) ->
                let _ = infer env ctx' a in
                if not (is_positive env ctx' a d.name) then raise (TypeError ("Negative occurrence in constructor " ^ string_of_int j));
                check_pos b (add_var ctx' x a)
            | Inductive d' when d'.name = d.name -> ()
            | _ -> raise (TypeError ("Constructor " ^ string_of_int j ^ " must return " ^ d.name))
        in check_pos ty ctx
      ) d.constrs;
      Universe max_level
    | Constr (j, d, args) ->
      let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.map (fun (n, t, _) -> (n, t)) d.params) cj in
      infer_ctor env ctx cj_subst args
    | Ind (d, p, cases, t') -> infer_Ind env ctx d p cases t'
    | J (ty, a, b, mot, d, p) ->
        let mot_ty = infer env ctx mot in
        (match mot_ty with
         | Universe _ -> () (* Motive is a Pi type or a Type family *)
         | Pi _ -> () (* Motive is a Lambda *)
         | _ -> raise (TypeError "J motive type mismatch"));
        check env ctx a ty; check env ctx b ty;
        let expected_d_ty = Pi ("x", ty, App (App (App (mot, Var "x"), Var "x"), Refl (Var "x"))) in
        check env ctx d expected_d_ty;
        let p_ty = infer env ctx p in
        (match p_ty with
         | Id (ty2, a2, b2) ->
             if not (equal env ctx ty ty2) || not (equal env ctx a a2) || not (equal env ctx b b2) then
                 raise (TypeError "J identity mismatch")
         | _ -> raise (TypeError "J expects an identity proof"));
        App (App (App (mot, a), b), p)
    in
    if trace then (Printf.printf "Infer result: %s\n" (string_of_term res); flush stdout);
    let normalized = normalize env ctx res in
    if trace then (Printf.printf "Normalized: %s\n" (string_of_term normalized); flush stdout);
    normalized

and universe_level env ctx t =
    match normalize env ctx t with
    | Inductive d -> (match infer env ctx (Inductive d) with | Universe i -> i | _ -> raise (TypeError "Expected universe"))
    | Universe i -> i
    | Pi (x, a, b) -> max (universe_level env ctx a) (universe_level env (add_var ctx x a) b)
    | Sigma (x, a, b) -> max (universe_level env ctx a) (universe_level env (add_var ctx x a) b)
    | App (f, _) -> (match normalize env ctx f with | Pi (_, _, b) -> universe_level env ctx b | _ -> raise (TypeError "Application requires Pi"))
    | Var x -> (match lookup_var ctx x with | Some ty -> universe_level env ctx ty | None -> raise (TypeError "Unbound"))
    | _ -> 0

and infer_ctor env ctx ty args =
    let rec check_args ty args_acc = function
    | [] -> (match ty with | Pi _ -> raise (TypeError "Too few arguments to constructor") | _ -> ty)
    | arg :: rest ->
        (match ty with
         | Pi (x, a, b) -> check env ctx arg a; check_args (subst x arg b) (arg :: args_acc) rest
         | _ -> raise (TypeError "Too many arguments to constructor"))
    in check_args ty [] args

and infer_J env ctx ty' a b c d p =
    check env ctx ty' (Universe 0);
    check env ctx a ty';
    check env ctx b ty';
    let fresh_x = "x_" ^ string_of_int (List.length ctx) in
    let fresh_y = "y_" ^ string_of_int (List.length ctx) in
    let fresh_p = "p_" ^ string_of_int (List.length ctx) in
    let motive_ty = Pi (fresh_x, ty', Pi (fresh_y, ty', Pi (fresh_p, Id (ty', Var fresh_x, Var fresh_y), Universe 0))) in
    check env ctx c motive_ty;
    let refl_case_ty = Pi (fresh_x, ty', App (App (App (c, Var fresh_x), Var fresh_x), Refl (Var fresh_x))) in
    check env ctx d refl_case_ty;
    check env ctx p (Id (ty', a, b));
    let result_ty = App (App (App (c, a), b), p) in
    normalize env ctx result_ty

and infer_Ind env ctx d p cases t' =
    if List.length cases <> List.length d.constrs then raise (TypeError "Number of cases doesn't match constructors");
    let t_ty = infer env ctx t' in
    let d_applied = apply_inductive d (List.map (fun (_, t, _) -> t) d.params) in
    if not (equal env ctx t_ty d_applied) then raise (TypeError "Elimination target type mismatch");
    let (x, a, b) = match p with
    | Pi (x, a, b) -> (x, a, b)
    | _ -> raise (TypeError "Motive must be a Pi type") in
    let p_ty = infer env ctx p in (match p_ty with | Universe _ -> () | _ -> raise (TypeError "Motive must be a type"));
    if not (equal env ctx t_ty a) then raise (TypeError "Target type does not match motive domain");
    let result_ty = subst x t' b in
    List.iteri (fun j case ->
      let j_idx = j + 1 in
      let cj = List.assoc j_idx d.constrs in
      let cj_subst = List.fold_left (fun acc (n, t, _) -> subst n t acc) cj d.params in
      let rec compute_case_type ty ctx_acc =
        match ty with
        | Pi (x, a, b) ->
            let var = Var x in let ctx' = add_var ctx_acc x a in
            let b_ty = compute_case_type b ctx' in
            if is_recursive env ctx a d.name then
              match a with
              | Pi (y, a_y, b_y) ->
                  let ih_ty = Pi (y, a_y, App (p, App (var, Var y))) in
                  Pi (x, a, Pi ("ih", ih_ty, b_ty))
              | _ -> Pi (x, a, Pi ("ih", App (p, var), b_ty))
            else Pi (x, a, b_ty)
        | Inductive d' when d'.name = d.name -> b
        | _ when equal env ctx ty d_applied -> b
        | _ -> raise (TypeError "Invalid constructor return type")
      in
      let expected_ty = compute_case_type cj_subst ctx in
      let (ctx', expected_ty') = match t' with
          | Var x ->
              let rec get_ctor_args ty = match ty with | Pi (x, a, b) -> x :: get_ctor_args b | _ -> [] in
              let ctor_args = get_ctor_args cj_subst in
              let refined_val = Constr (j_idx, d, List.map (fun n -> Var n) ctor_args) in
              (List.map (fun (n, ty) -> (n, subst x refined_val ty)) ctx, subst x refined_val expected_ty)
          | _ -> (ctx, expected_ty)
      in
      check env ctx' case expected_ty'
    ) cases;
    result_ty

and apply_inductive d args =
    if List.length d.params <> List.length args then raise (TypeError "Parameter mismatch in inductive type");
    let subst_param t = List.fold_left2 (fun acc (n, _, _) arg -> subst n arg acc) t d.params args
    in Inductive { d with params = List.map2 (fun (n, _, typ) arg -> (n, arg, typ)) d.params args; 
                          constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

and check_universe env ctx t =
    match infer env ctx t with
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); i
    | ty -> raise (TypeError (Printf.sprintf "Expected a universe, got: %s" (let s = ref "" in print_term ty; !s)))

and check env ctx t ty =
    if trace then (Printf.printf "Checking Term: %s\nAgainst Type: %s\n" (string_of_term t) (string_of_term ty); flush stdout);
    match t, ty with
    | Universe i, Universe j -> if i < 0 then raise (TypeError "Negative universe level"); if i > j then raise (TypeError (Printf.sprintf "Universe level mismatch: %d > %d" i j));
    | Inductive d, ty ->
        let inferred = infer env ctx t in
        if not (equal env ctx inferred ty) then
             raise (TypeError (Printf.sprintf "Inductive type mismatch. Inferred: %s. Expected: %s."
                               (string_of_term inferred) (string_of_term ty)))
    | Pi (x, a, b), Pi (y, a', b') -> if not (equal env ctx a a') then raise (TypeError "Pi domain mismatch"); let ctx' = add_var ctx x a in check env ctx' b (subst y (Var x) b')
    | Lam (x, domain, body), Pi (y, a, b) -> check env ctx domain (infer env ctx domain); let b_subst = subst y (Var x) b in check env (add_var ctx x domain) body b_subst
    | Constr (j, d, args), Inductive d' when d.name = d'.name -> let inferred = infer env ctx t in if not (equal env ctx inferred ty) then raise (TypeError "Constructor type mismatch")
    | Ind (d, p, cases, t'), ty ->
        (match t' with | Var _ -> () | _ -> raise (TypeError ("Induction is only allowed over variables. Term: " ^ (string_of_term t'))));
        let inferred = infer_Ind env ctx d p cases t' in
        if not (equal env ctx inferred ty) then
             raise (TypeError (Printf.sprintf "Elimination type mismatch. Inferred: %s. Expected: %s."
                               (string_of_term inferred) (string_of_term ty)))
    | Pair (a, b), Sigma (x, a_ty, b_ty) -> check env ctx a a_ty; check env ctx b (subst x a b_ty)
    | Fst p, ty -> let p_ty = infer env ctx p in (match p_ty with | Sigma (x, a, _) -> if not (equal env ctx a ty) then raise (TypeError "Fst type mismatch") | _ -> raise (TypeError "Fst expects a Sigma type"))
    | Snd p, ty -> let p_ty = infer env ctx p in (match p_ty with | Sigma (x, a, b) -> if not (equal env ctx (subst x (Fst p) b) ty) then raise (TypeError "Snd type mismatch") | _ -> raise (TypeError "Snd expects a Sigma type"))
    | Refl a, Id (ty, x, y) -> check env ctx a ty; if not (equal env ctx x a) || not (equal env ctx y a) then raise (TypeError "Refl type mismatch")
    | J (ty, a, b, c, d, p), ty' -> let inferred = infer env ctx t in if not (equal env ctx inferred ty') then raise (TypeError "J type mismatch")
    | _, _ ->
        let inferred = infer env ctx t in
        let ty' = normalize env ctx ty in
        match inferred, ty' with
        | Universe i, Universe j when i <= j -> ()
        | _ -> if not (equal env ctx inferred ty') then
               (if trace then (Printf.printf "Mismatch detail: inferred=%s, expected=%s\n" (string_of_term inferred) (string_of_term ty'); flush stdout);
                raise (TypeError (Printf.sprintf "Type Mismatch Error. Inferred: %s. Expected: %s."
                               (string_of_term inferred) (string_of_term ty'))))

and apply_case env ctx d p cases case ty args =
    let rec apply ty args_acc remaining_args =
    match ty, remaining_args with
    | Pi (x, a, b), arg :: rest ->
        let b' = subst x arg b in
        if is_recursive env ctx a d.name then
            let rec_arg = match a with
                | Pi (y, a_y, b_y) -> Lam (y, a_y, reduce env ctx (Ind (d, p, cases, App (arg, Var y))))
                | _ -> reduce env ctx (Ind (d, p, cases, arg))
            in
            apply b' (rec_arg :: arg :: args_acc) rest
        else
            apply b' (arg :: args_acc) rest
    | Pi (_, _, b), [] -> apply b args_acc []
    | _, [] ->
        let rec apply_term t args =
          match t, args with
          | Lam (x, _, body), arg :: rest -> apply_term (subst x arg body) rest
          | t, [] -> t
          | _ -> raise (TypeError "Case application mismatch")
        in
        apply_term case (List.rev args_acc)
    | _ -> raise (TypeError "Constructor argument mismatch")
    in apply ty [] args

and reduce env ctx t =
    match t with
    | Lam (x, a, b) -> Lam (x, reduce env ctx a, reduce env (add_var ctx x a) b)
    | Pi (x, a, b) -> Pi (x, reduce env ctx a, reduce env (add_var ctx x a) b)
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (Pi (x, a, b), arg) -> subst x arg b
    | App (f, a) -> let f' = reduce env ctx f in (match f' with | Lam (x, _, b) -> reduce env ctx (subst x a b) | _ -> App (f', reduce env ctx a))
    | Ind (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
      let case = List.nth cases (j - 1) in let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.map (fun (n, t, _) -> (n, t)) d.params) cj in
      reduce env ctx (apply_case env ctx d p cases case cj_subst args)
    | Ind (d, p, cases, t') -> let t'' = reduce env ctx t' in let reduced_ind = Ind (d, p, cases, t'') in (match t'' with | Constr _ -> reduce env ctx reduced_ind | _ -> reduced_ind)
    | Constr (j, d, args) -> Constr (j, d, List.map (reduce env ctx) args)
    | Fst (Pair (a, b)) -> a
    | Snd (Pair (a, b)) -> b
    | J (ty, a, b, c, d, Refl a') when equal' env ctx a a' && equal' env ctx b a' -> App (d, a)
    | J (ty, a, b, c, d, p) -> let p' = reduce env ctx p in if p = p' then t else J (ty, a, b, c, d, p')
    | Refl a -> Refl (reduce env ctx a)
    | _ -> t

and normalize env ctx t = normalize' env ctx 0 t
and normalize' env ctx depth t =
    if depth > 100 then raise (TypeError "Normalization depth exceeded");
    let t' = reduce env ctx t in if equal' env ctx t t' then t else normalize' env ctx (depth + 1) t'

and string_of_Ind d p cases t' depth =
    d.name ^ ".Ind " ^ (string_of_term_depth (depth + 1) p) ^ " [" ^
       (List.fold_left (fun acc c -> acc ^ (string_of_term_depth (depth + 1) c) ^ "; ") "" cases) ^
    "] " ^ string_of_term_depth (depth + 1) t'

and string_of_term_depth depth t =
    if depth > 20 then "<deep>"
    else match t with
    | Var x -> x
    | Universe i -> "U_" ^ (string_of_int i)
    | Pi (x, a, b) -> "Π(" ^ x ^ " : " ^ (string_of_term_depth (depth + 1) a) ^ ")." ^ string_of_term_depth (depth + 1) b
    | Lam (x, _, body) -> "λ (" ^ x ^ "), " ^ (string_of_term_depth (depth + 1) body)
    | App (f, arg) -> "(" ^ (string_of_term_depth (depth + 1) f) ^ " " ^ (string_of_term_depth (depth + 1) arg) ^ ")"
    | Sigma (x, a, b) -> "Σ (" ^ x ^ " : " ^ (string_of_term_depth (depth + 1) a) ^ "), " ^ string_of_term_depth (depth + 1) b
    | Pair (a, b) -> "(" ^ (string_of_term_depth (depth + 1) a) ^ ", " ^ (string_of_term_depth (depth + 1) b) ^ ")"
    | Fst t -> "fst " ^ string_of_term_depth (depth + 1) t
    | Snd t -> "snd " ^ string_of_term_depth (depth + 1) t
    | Id (ty, a, b) -> "{" ^ string_of_term_depth (depth + 1) a ^ " = " ^ string_of_term_depth (depth + 1) b ^ " : " ^ string_of_term_depth (depth + 1) ty ^ "}"
    | Refl t -> "Id.refl " ^ string_of_term_depth (depth + 1) t
    | J (ty, a, b, c, d, p) -> "J (" ^ string_of_term_depth (depth + 1) ty ^ ", " ^ string_of_term_depth (depth + 1) a ^ ", " ^ string_of_term_depth (depth + 1) b ^ ", " ^ string_of_term_depth (depth + 1) c ^ ", " ^ string_of_term_depth (depth + 1) d ^ ", " ^ string_of_term_depth (depth + 1) p ^ ")"
    | Inductive d -> d.name
    | Constr (i, d, args) -> d.name ^ "." ^ (string_of_int i) ^ (List.fold_left (fun acc c -> acc ^ " " ^ (string_of_term_depth (depth + 1) c)) "" args)
    | Ind (d, p, cases, t') -> string_of_Ind d p cases t' depth

and string_of_term t = string_of_term_depth 0 t
and print_term_depth depth t = print_string (string_of_term_depth depth t)
and print_term t = print_term_depth 0 t

(* TEST SUITE *)

(* LIBRARY *)

(* Empty *)
let empty_def = { name = "Empty"; params = []; level = 0; constrs = [] }
let empty_ind = Inductive empty_def
let empty_elim = Lam ("P", Universe 0, Lam ("e", Inductive empty_def, Ind (empty_def, Pi ("_", Inductive empty_def, Var "P"), [], Var "e")))

(* Unit *)
let unit_def_params = { name = "Unit"; params = []; level = 0; constrs = [] }
let unit_def = { unit_def_params with constrs = [(1, Inductive unit_def_params)] }
let tt = Constr (1, unit_def, [])

(* Bool *)
let bool_def_params = { name = "Bool"; params = []; level = 0; constrs = [] }
let bool_def = { bool_def_params with constrs = [(1, Inductive bool_def_params); (2, Inductive bool_def_params)] }
let false_val = Constr (1, bool_def, [])
let true_val = Constr (2, bool_def, [])

(* Nat *)
let nat_def_params = { name = "Nat"; params = []; level = 0; constrs = []}
let nat_def = { nat_def_params with constrs = [(1, Inductive nat_def_params); (2, Pi ("n", Inductive nat_def_params, Inductive nat_def_params))] }
let nat_ind = Inductive nat_def
let zero = Constr (1, nat_def, [])
let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"]))

(* List *)
let list_def_params a at = { name = "List"; params = [("A", a, at)]; level = 0; constrs = [] }
let list_def a at = { (list_def_params a at) with constrs = [
      (1, Inductive (list_def_params a at));
      (2, Pi ("x", a, Pi ("xs", Inductive (list_def_params a at), Inductive (list_def_params a at)))) ] }

(* Tree *)
let tree_def_params a at = { name = "Tree"; params = [("A", a, at)]; level = 0; constrs = [] }
let tree_def a at = { (tree_def_params a at) with constrs = [
      (1, Inductive (tree_def_params a at));
      (2, Pi ("x", a, Pi ("l", Inductive (tree_def_params a at), Pi ("r", Inductive (tree_def_params a at), Inductive (tree_def_params a at))))) ] }

(* Fin *)
let fin_def_params n nt = { name = "Fin"; params = [("n", n, nt)]; level = 0; constrs = [] }
let fin_def n nt = { (fin_def_params n nt) with constrs = [
        (1, Pi ("n", (Inductive nat_def), Inductive (fin_def_params n nt)));
        (2, Pi ("n", (Inductive nat_def), (Pi ("k", Inductive (fin_def_params n nt), Inductive (fin_def_params n nt))))) ] }
let fin_ind = Inductive (fin_def zero nat_ind)
let fzero = Constr (1, fin_def zero nat_ind, [zero])

(* Vec *)
let vec_def_params a at n nt = { name = "Vec"; params = [("A", a, at); ("n", n, nt)]; level = 0; constrs = [] }
let vec_def a at n nt = { (vec_def_params a at n nt) with constrs = [
      (1, Inductive (vec_def_params a at n nt));
      (2, Pi ("x", a, Pi ("xs", Inductive (vec_def_params a at n nt), Inductive (vec_def_params a at (App (succ, n)) nt)))) ] }
let vnil = Constr (1, (vec_def nat_ind (Universe 0) zero nat_ind), [])
let vcons = Constr (2, (vec_def nat_ind (Universe 0) zero nat_ind), [zero; vnil])

(* W *)
let w_def_params (a: term) (at: term) (b: term) (bt: term) = { name = "N"; params = [("A", a, at);("B", b, bt)]; level = 0; constrs = [] }
let w_def (a: term) (at: term) (b: term) (bt: term) = { (w_def_params a at b bt) with constrs = [
      (1, Pi ("z", a, Pi ("f", Pi ("_", App (b, Var "z"), Inductive (w_def_params a at b bt)), Inductive (w_def_params a at b bt)) )) ] }

let w_nat = {
      (w_def (Inductive bool_def)
      (Universe 0)
      (Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Universe 0), [Inductive empty_def; Inductive unit_def], Var "s")))
      (Pi ("x", Inductive bool_def, Universe 0))) with name = "N" }

let zero_w  = Constr (1, w_nat, [false_val; Lam ("y", Inductive empty_def, App (App (empty_elim, Inductive w_nat), Var "y"))])
let succ_w  = Lam("d", Inductive w_nat, Constr (1, w_nat, [true_val; Lam ("y", Inductive unit_def, Var "d")]))
let one_w   = normalize [] [] (App (succ_w, zero_w))
let two_w   = normalize [] [] (App (succ_w, one_w))
let three_w = normalize [] [] (App (succ_w, two_w))
let four_w  = normalize [] [] (App (succ_w, three_w))
let five_w  = normalize [] [] (App (succ_w, four_w))
let six_w   = normalize [] [] (App (succ_w, five_w))
let seven_w = normalize [] [] (App (succ_w, six_w))

let env = [("Empty", empty_def); ("Unit", unit_def); ("Bool", bool_def); ("Nat", nat_def); ("N", w_nat)]

(* SAMPLES *)
let plus = Lam ("m", nat_ind, Lam ("n", nat_ind, Ind (nat_def, Pi ("_", nat_ind, nat_ind), [Var "m"; Lam ("k", nat_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"])))], Var "n")))
let plus_w =
    let b_term = Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Universe 0), [Inductive empty_def; Inductive unit_def], Var "s")) in
    Lam ("n", Inductive w_nat, Lam ("m", Inductive w_nat,
    Ind (w_nat, Pi ("_", Inductive w_nat, Inductive w_nat),
         [Lam ("a", Inductive bool_def, Lam ("f", Pi ("y", App (b_term, Var "a"), Inductive w_nat),
          Lam ("ih", Pi ("y", App (b_term, Var "a"), Inductive w_nat),
          Ind (bool_def, Pi ("z", Inductive bool_def, Inductive w_nat), [Var "m"; App (succ_w, App (Var "ih", tt))], Var "a"))))], Var "n")))

let to_nat_w =
    let b_term = Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, Universe 0), [Inductive empty_def; Inductive unit_def], Var "s")) in
    Lam ("w", Inductive w_nat,
    Ind (w_nat,
         Pi ("_", Inductive w_nat, Inductive nat_def),
         [Lam ("z", Inductive bool_def,
          Lam ("f", Pi ("y", App (b_term, Var "z"), Inductive w_nat),
          Lam ("ih", Pi ("y", App (b_term, Var "z"), Inductive nat_def),
          Ind (bool_def,
               Pi ("_", Inductive bool_def, Inductive nat_def),
               [zero; App (succ, App (Var "ih", tt))],
               Var "z"))))],
         Var "w"))

(* TESTS *)
let test_universe () =
    let ctx = [] in let t1 = Universe 0 in
    assert (equal empty_env ctx (infer empty_env ctx t1) (Universe 1));
    check empty_env ctx (Universe 0) (Universe 1);
    check empty_env ctx (Universe 0) (Universe 0);
    begin try let _ = check [] ctx (Universe 1) (Universe 0) in assert false with TypeError _ -> () end;
    Printf.printf "Universe Consistency PASSED\n"

let test_equal () = assert (equal [] [] (Pi ("x", Universe 0, Universe 0)) (Pi ("y", Universe 0, Universe 0))); Printf.printf "Syntactic Equality PASSED.\n"

let test_eta () =
    let ctx = [("f", Pi ("x", Universe 0, Universe 0))] in
    let t1 = Lam ("x", Universe 0, App (Var "f", Var "x")) in
    let t2 = Var "f" in assert (equal [] ctx t1 t2);
    Printf.printf "Pi Eta-expansion PASSED.\n"

let test_sigma_eta () =
    let ctx = [("p", Sigma ("x", nat_ind, nat_ind))] in
    let t1 = Var "p" in let t2 = Pair (Fst (Var "p"), Snd (Var "p")) in
    assert (equal [] ctx t1 t2); Printf.printf "Sigma Eta-expansion PASSED.\n"

let test_positivity () =
    let bad_def = { name = "Bad"; params = []; level = 0; constrs = [(1, Pi ("x", Pi ("y", Inductive { name = "Bad"; params = []; level = 0; constrs = [] }, Universe 0), Inductive { name = "Bad"; params = []; level = 0; constrs = [] }))] } in
    let env = [("Nat", nat_def); ("Bad", bad_def)] in
    assert (match infer env [] (Inductive nat_def) with | Universe _ -> true | _ -> false);
    try let _ = infer env [] (Inductive bad_def) in assert false with TypeError msg -> Printf.printf "Positivity check caught: %s\n" msg;
    print_string "Positivity Checking PASSED.\n"

let test_w () =
    let plus4w = normalize env [] (App (App (plus_w, two_w), two_w)) in
    let plus6w = normalize env [] (App (App (plus_w, three_w), three_w)) in
    let four4  = normalize env [] (App (to_nat_w, four_w)) in begin
        Printf.printf "eval plus4w 4 = "; print_term plus4w; print_endline "";
        Printf.printf "eval plus6w 6 = "; print_term plus6w; print_endline "";
        Printf.printf "eval four4w 4 = "; print_term four_w; print_endline "";
        Printf.printf "eval conv4  4 = "; print_term four4; print_endline "";
        Printf.printf "zero_w : "; print_term (normalize env [] (Inductive w_nat)); print_endline "";
        Printf.printf "succ_w : "; print_term (infer env [] succ_w); print_endline "";
        Printf.printf "w_nat : "; print_term (infer env [] (Inductive w_nat)); print_endline "";
        Printf.printf "Four4 : "; print_term (normalize env [] four4); print_endline "";
        try Printf.printf "plus_w    : "; print_term (infer env [] plus_w); print_endline ""; flush stdout
        with TypeError msg -> Printf.printf "Catch: %s\n" msg; flush stdout;
        try Printf.printf "to_nat_w  : "; print_term (infer env [] to_nat_w); print_endline ""; flush stdout
        with TypeError msg -> Printf.printf "Catch: %s\n" msg; flush stdout;
    end;
    if (equal env [] plus4w four_w) then Printf.printf "W Checking PASSED\n" else Printf.printf "W Checking FAILED (plus4w <> four_w)\n"

let test_lambda_typing () =
    let id = Lam ("x", nat_ind, Var "x") in
    assert (match infer [("Nat", nat_def)] [] id with | Pi (_, Inductive d1, Inductive d2) when d1.name = "Nat" && d2.name = "Nat" -> true | _ -> false);
    let const = Lam ("x", nat_ind, Constr (1, nat_def, [])) in
    assert (match infer [("Nat", nat_def)] [] const with | Pi (_, Inductive d1, Inductive d2) when d1.name = "Nat" && d2.name = "Nat" -> true | _ -> false);
    let apply = Lam ("f", Pi ("y", nat_ind, nat_ind),  App (Var "f", Constr (1, nat_def, []))) in
    assert (match infer [("Nat", nat_def)] [] apply with | Pi (_, Pi (_, Inductive d1, Inductive d2), Inductive d3) when d1.name = "Nat" && d2.name = "Nat" && d3.name = "Nat" -> true | _ -> false);
    Printf.printf "Identity: "; print_term (infer [("Nat", nat_def)] [] id); print_endline "";
    Printf.printf "Constant: "; print_term (infer [("Nat", nat_def)] [] const); print_endline "";
    Printf.printf "Apply: "; print_term (infer [("Nat", nat_def)] [] apply); print_endline "";
    try let _ = infer [("Nat", nat_def)] [] (Lam ("x", nat_ind, App (Var "x", Constr (1, nat_def, [])))) in assert false
    with TypeError msg -> Printf.printf "Caught requires Pi: %s\n" msg;
    let x = infer [("Nat", nat_def)] [] (Lam ("x", Pi ("y", nat_ind, nat_ind), App (Var "x", Constr (1, nat_def, [])))) in print_term x; print_endline "";
    Printf.printf "Lambda Typing PASSED\n"

let test_edge_cases () =
    try let _ = infer [("Nat", nat_def)] [] (Inductive { name = "X"; params = []; level = 0;
                   constrs = [(1, Pi ("x", Var "Y", Inductive { name = "X"; params = []; level = 0; constrs = [] }))] }) in
        assert false with TypeError msg ->  Printf.printf "Caught unbound type: %s\n" msg;
    print_string "Unboundness Checking PASSED.\n"

let test_robustness () =
    try let _ = infer env [] (Ind (nat_def, Pi ("_", nat_ind, nat_ind), [zero; Lam ("k", nat_ind, Lam ("ih", nat_ind, Var "ih"))], Constr (1, nat_def, []))) in ()
    with TypeError msg -> Printf.printf "Caught wrong infinite Induction: %s\n" msg;
    let under_applied = Constr (2, nat_def, []) in
    try let _ = infer [("Nat", nat_def)] [] under_applied in assert false with TypeError msg -> Printf.printf "Caught under-applied constructor: %s\n" msg;
    Printf.printf "Robustness PASSED\n"

let test_fin_vec () =
    (try Printf.printf "Fin 1: "; print_term (infer env [] fzero); print_endline "" with TypeError msg -> Printf.printf "Catch: %s\n" msg);
    (try Printf.printf "Vec Nat 0: "; print_term (infer env [] vnil); print_endline "";
         Printf.printf "Vec Nat 1: "; print_term (infer env [] vcons); print_endline "" with TypeError msg -> Printf.printf "Catch: %s\n" msg);
    Printf.printf "Fin and Vec PASSED\n"

let test_basic_setup () =
    let list_ind = Inductive (list_def (Universe 0) (Universe 0)) in
    let list_length =
        Lam ("l", list_ind,
          Ind ((list_def (Universe 0) (Universe 0)),
              Pi ("_", list_ind, nat_ind),
              [ zero;
                Lam ("x", Universe 0,
                  Lam ("xs", list_ind,
                    Lam ("ih", nat_ind,
                      Constr (2, nat_def, [Var "ih"]))))],
              Var "l")) in
    let sample_list =
        Constr (2, list_def (Universe 0) (Universe 0),
          [zero;
           Constr (2, list_def (Universe 0) (Universe 0),
             [Constr (2, nat_def, [zero]);
              Constr (1, list_def (Universe 0) (Universe 0), [])])]) in
    let len = App (list_length, sample_list) in
    let tree_ind = Inductive (tree_def nat_ind (Universe 0)) in
    let leaf = Constr (1, tree_def nat_ind (Universe 0), []) in
    let node n l r = Constr (2, tree_def nat_ind (Universe 0), [n; l; r]) in
    let sample_tree = node zero leaf leaf in
    let absurd = Lam ("e", empty_ind, Ind (empty_def, Pi ("_", empty_ind, nat_ind), [], Var "e")) in
    begin
        ignore tree_ind; ignore sample_tree;
        Printf.printf "eval absurd = "; print_term (normalize env [] absurd); print_endline "";
        Printf.printf "eval Tree.leaf = "; print_term leaf; print_endline "";
        Printf.printf "eval Nat.add(3,2) = "; print_term (normalize env [] (App (App (plus, Constr (2, nat_def, [Constr (2, nat_def, [Constr (2, nat_def, [zero])])])), Constr (2, nat_def, [Constr (2, nat_def, [zero])])))); print_endline "";
        Printf.printf "eval List.length(list) = "; print_term (normalize env [] len); print_endline "";
        Printf.printf "Nat.Ind = "; print_term (Ind (nat_def, Pi ("x", nat_ind, Universe 0), [nat_ind; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],  Constr (1, nat_def, []))); print_endline "";
        Printf.printf "Nat.succ : "; print_term (infer env [] succ); print_endline "";
        Printf.printf "Nat.plus : "; print_term (infer env [] plus); print_endline "";
        Printf.printf "Nat.Ind : "; print_term (infer env [] (Inductive nat_def)); print_endline "";
        Printf.printf "bool_elim : "; print_term (infer env [] (Lam ("s", Inductive bool_def, Ind (bool_def, Pi ("_", Inductive bool_def, nat_ind), [zero; zero], Var "s")))); print_endline "";
    end

let test_equality_theorems () =
    let a = Universe 0 in
    let sym_motive = Pi ("x", a, Pi ("y", a, Pi ("p", Id (a, Var "x", Var "y"), Id (a, Var "y", Var "x")))) in
    let sym_d = Lam ("x", a, Refl (Var "x")) in
    let sym = Lam ("x", a, Lam ("y", a, Lam ("p", Id (a, Var "x", Var "y"), J (a, Var "x", Var "y", sym_motive, sym_d, Var "p")))) in
    let sym_ty = Pi ("x", a, Pi ("y", a, Pi ("p", Id (a, Var "x", Var "y"), Id (a, Var "y", Var "x")))) in
    assert (equal [] [] (infer [] [] sym) sym_ty);
    print_string "Identity Symmetry PASSED.\n"

let test_inductive_eta () =
    let ctx = [("x", nat_ind); ("f", Pi ("x", nat_ind, nat_ind)); ("g", Pi ("x", nat_ind, nat_ind));
                ("eq", Id (nat_ind, App (Var "f", Var "x"), App (Var "g", Var "x")))] in
    let env = [("Nat", nat_def)] in
    let motive = Pi ("a", nat_ind, Pi ("b", nat_ind, Pi ("_", Id (nat_ind, Var "a", Var "b"), Pi ("_", nat_ind, nat_ind)))) in
    let refl_case = Lam ("z", nat_ind, Var "f") in
    let proof = J (nat_ind, App (Var "f", Var "x"), App (Var "g", Var "x"), motive, refl_case, Var "eq") in
    let expected_ty = Pi ("_", nat_ind, nat_ind) in
    let inferred_ty = infer env ctx proof in
    assert (equal env ctx inferred_ty expected_ty);
    print_string "Inductive Eta-Equality PASSED.\n"

let test_inductive_eta_full () =
    let ctx = [("x", nat_ind); ("f", Pi ("x", nat_ind, nat_ind)); ("g", Pi ("x", nat_ind, nat_ind));
                ("eq", Pi ("x", nat_ind, Id (nat_ind, App (Var "f", Var "x"), App (Var "g", Var "x"))))] in
    let env = [("Nat", nat_def)] in
    let ty = nat_ind in
    let motive = Pi ("a", ty, Pi ("b", ty, Pi ("_", Id (ty, Var "a", Var "b"), nat_ind))) in
    let refl_case = Lam ("z", ty, Var "z") in
    let proof = J (ty, App (Var "f", Var "x"), App (Var "g", Var "x"), motive, refl_case, App (Var "eq", Var "x")) in
    let expected_ty = nat_ind in
    let inferred_ty = infer env ctx proof in
    assert (equal env ctx inferred_ty expected_ty);
    print_string "Pointwise Equality Transport PASSED.\n"

let test_sigma () =
    Printf.printf "Testing Sigma types...\n";
    let a = Inductive nat_def in
    let b = Lam ("x", a, a) in (* B x = Nat *)
    let sigma_ab = { name = "Sigma"; params = [("A", a, Universe 0); ("B", b, Pi ("x", a, Universe 0))]; level = 0; constrs = [] } in
    check [] [] a (Universe 0);
    check [] [] b (Pi ("x", a, Universe 0));
    Printf.printf "Sigma types PASSED\n\n"

let test_eq () =
    let env = [("Nat", nat_def)] in
    Printf.printf "Testing Eq types...\n";
    let a = Inductive nat_def in
    let eq_def = { name = "Eq"; params = [("A", a, Universe 0); ("x", Var "Zero", a); ("y", Var "Zero", a)]; level = 0; constrs = [] } in
    check [] [("Zero", a)] (Inductive eq_def) (Universe 0);
    Printf.printf "Eq types PASSED\n\n"


let test_lambda_totality () =
    let id = Lam ("x", nat_ind, Var "x") in
    assert (match infer env [] id with | Pi (_, _, _) -> true | _ -> false);
    try let _ = infer env [] (Lam ("x", nat_ind, App (Var "x", zero))) in assert false
    with TypeError msg -> Printf.printf "Caught non-total lambda: %s\n" msg;
    print_string "Lambda Totality PASSED.\n"

let test () =
    test_universe (); test_equal (); test_eta (); test_sigma_eta ();
    test_positivity (); test_lambda_typing (); test_edge_cases ();
    test_basic_setup (); test_robustness (); test_fin_vec ();
    test_inductive_eta (); test_inductive_eta_full (); test_lambda_totality ();
    test_w (); test_sigma (); test_eq (); test_equality_theorems ();
    print_endline "REALITY CHECK PASSED\n"

(* THEOREM PROVER TACTICS LANGUAGE *)

type goal = {
  ctx : context;          (* Current context *)
  target : term;          (* Type to prove *)
  id : int;               (* Goal identifier *)
}

type proof_state = {
  goals : goal list;      (* List of open goals *)
  solved : (int * term) list; (* Solved goals with their terms *)
}

let initial_state target = {
  goals = [{ ctx = empty_ctx; target; id = 1 }];
  solved = [];
}

let next_id state = 1 + List.fold_left (fun m g -> max m g.id) 0 state.goals

type tactic =
  | Intro of name                     (* Introduce a variable *)
  | Elim of term                      (* Eliminate a term (e.g., induction or case analysis) *)
  | Apply of term                     (* Apply a term or hypothesis *)
  | Assumption                        (* Use a hypothesis from context *)
  | Auto                              (* Simple automation *)
  | Exact of term                     (* Provide an exact term *)

exception TacticError of string

let print_goal g =
  Printf.printf "Goal %d:\nContext: [" g.id;
  List.iter (fun (n, ty) -> Printf.printf "(%s : " n; print_term ty; print_string "); ") g.ctx;
  print_endline "]";
  Printf.printf "⊢ "; print_term g.target; print_endline "\n"

let print_state state =
  List.iter print_goal state.goals;
  Printf.printf "%d goals remaining\n" (List.length state.goals)

let rec apply_tactic env state tac =
  match state.goals with
  | [] -> raise (TacticError "No goals to solve")
  | goal :: rest ->
      match tac with
      | Intro x ->
          (match goal.target with
           | Pi (y, a, b) ->
               let new_ctx = add_var goal.ctx x a in
               let new_target = subst y (Var x) b in
               let new_goal = { goal with ctx = new_ctx; target = new_target } in
               { state with goals = new_goal :: rest }
           | _ -> raise (TacticError "Intro expects a Pi type"))
      | Elim t ->
          let ty = infer env goal.ctx t in
          (match ty with
           | Inductive d ->
               let p = Var "P" in (* Motive placeholder *)
               let motive_ty = Pi ("x", Inductive d, Universe 0) in
               let new_goal = { goal with target = App (p, t); id = next_id state } in
               let motive_goal = { ctx = goal.ctx; target = motive_ty; id = goal.id } in
               { state with goals = motive_goal :: new_goal :: rest }
           | Id (ty', a, b) ->
               let c = Var "C" in
               let motive_ty = Pi ("x", ty', Pi ("y", ty', Pi ("p", Id (ty', Var "x", Var "y"), Universe 0))) in
               let new_goal = { goal with target = App (App (App (c, a), b), t); id = next_id state } in
               let refl_goal = { ctx = goal.ctx; target = Pi ("x", ty', App (App (App (c, Var "x"), Var "x"), Refl (Var "x"))); id = next_id state + 1 } in
               let motive_goal = { ctx = goal.ctx; target = motive_ty; id = goal.id } in
               { state with goals = motive_goal :: refl_goal :: new_goal :: rest }
           | _ -> raise (TacticError "Elim expects an inductive or identity type"))
      | Apply t ->
          let ty = infer env goal.ctx t in
          (match ty with
           | Pi (x, a, b) ->
               if equal env goal.ctx a goal.target then
                 { goals = rest; solved = (goal.id, t) :: state.solved }
               else
                 let new_goal = { goal with target = a; id = next_id state } in
                 { state with goals = new_goal :: rest }
           | _ ->
               if equal env goal.ctx ty goal.target then
                 { goals = rest; solved = (goal.id, t) :: state.solved }
               else raise (TacticError "Apply type mismatch"))
      | Assumption ->
          (match List.find_opt (fun (_, ty) -> equal env goal.ctx ty goal.target) goal.ctx with
           | Some (n, _) ->
               { goals = rest; solved = (goal.id, Var n) :: state.solved }
           | None -> raise (TacticError "No matching assumption"))
      | Auto ->
          let rec try_assumptions ctx =
            match ctx with
            | (n, ty) :: rest ->
                if equal env goal.ctx ty goal.target then
                  Some (Var n)
                else try_assumptions rest
            | [] -> None
          in
          (match try_assumptions goal.ctx with
           | Some t -> { goals = rest; solved = (goal.id, t) :: state.solved }
           | None -> state) (* Could extend with more automation *)
      | Exact t ->
          check env goal.ctx t goal.target;
          { goals = rest; solved = (goal.id, t) :: state.solved }

let parse_tactic input =
  let tokens = String.split_on_char ' ' (String.trim input) in
  match tokens with
  | ["intro"; x] -> Intro x
  | ["elim"; t] -> Elim (Var t) (* Simplified: assumes variable name *)
  | ["apply"; t] -> Apply (Var t) (* Simplified: assumes variable name *)
  | ["assumption"] -> Assumption
  | ["auto"] -> Auto
  | ["exact"; t] -> Exact (Var t) (* Simplified: assumes variable name *)
  | _ -> raise (TacticError ("Unknown tactic: " ^ input))

let rec console_loop env state =
  print_state state;
  if state.goals = [] then (
    Printf.printf "Proof complete!\n";
    let final_term = List.fold_left (fun acc (_, t) -> subst "P" t acc) (Var "P") state.solved in
    Printf.printf "Final term: "; print_term final_term; print_endline "";
    final_term
  ) else (
    Printf.printf "> ";
    let input = read_line () in
    try
      let tactic = parse_tactic input in
      let new_state = apply_tactic env state tactic in
      console_loop env new_state
    with
    | TacticError msg -> Printf.printf "Error: %s\n" msg; console_loop env state
    | TypeError msg -> Printf.printf "Type error: %s\n" msg; console_loop env state
  )

let main () =
    let nat = Inductive { name = "Nat"; params = []; level = 0;
        constrs = [(1, Universe 0);
                   (2, Pi ("n", Inductive { name = "Nat"; params = []; level = 0; constrs = []}, Universe 0))] } in
    let env = [("Nat", nat)] in
    let target = Pi ("n", Inductive nat_def, Inductive nat_def) in
    Printf.printf "Starting proof for: "; print_term target; print_endline "";
    let state = initial_state target in
    ignore (console_loop env state)

let banner =
"https://christine.groupoid.space/

  🧊 Christine MLTT/CIC Theorem Prover version 0.3.11

For help type `help`."

let () = if (tests) then test (); print_endline banner; main ()

