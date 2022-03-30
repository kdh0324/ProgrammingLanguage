(*
 * Call-by-value reduction   
 *)

open Uml

exception NotImplemented 
exception Stuck

let freshVarCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s = 
    let _ = freshVarCounter := !freshVarCounter + 1
    in
    s ^ "__" ^ (string_of_int (!freshVarCounter))

(*
 * get an union of sets s1 and s2 : 'a list -> 'a list -> 'a list
 *)
let rec union s1 s2 =
    match s1 with
    | [] -> s2
    | h :: t -> union t (h :: List.filter (fun x -> x <> h) s2)

(*
 * get a set of fresh variables from expression e : exp -> var list
 *)
let rec getFV e =
    match e with
    | Var v -> [v]
    | Lam (v, e1) -> List.filter (fun s -> s <> v) (getFV e1)
    | App (e1, e2) -> union (getFV e1) (getFV e2)

(*
 * swap variables x and y in expression e : var -> var -> exp -> exp
 *)
let rec swap x y e =
    match e with
    | Var v -> if x = v then Var y else if y = v then Var x else Var v
    | Lam (v, e1) -> Lam ((if x = v then y else if y = v then x else v), swap x y e1)
    | App (e1, e2) -> App (swap x y e1, swap x y e2)

(*
 * substitute expression e' for every occurrence of variable x in expression e : exp -> var -> exp -> exp
 *)
let rec substitute e' x e =
    match e with
    | Var v -> if x = v then e' else e
    | Lam (v, e1) ->
        if x = v then e
        else if not (List.mem v (getFV e')) then Lam (v, substitute e' x e1)
        else
            let v' = getFreshVariable v
            in Lam (v', substitute e' x (swap v v' e1))
    | App (e1, e2) -> App (substitute e' x e1, substitute e' x e2)

(*
 * implement a single step with reduction using the call-by-value strategy.
 *)
 let rec stepv e = 
  let rec fv e' = 
    match e' with
      Var var -> [var]
    | Lam (var, exp) -> List.filter (fun v -> v <> var) (fv exp)
    | App (exp1, exp2) ->
      let rec union l1 l2 =
        match l1 with
        | [] -> l2
        | h :: t -> union t (h :: List.filter (fun x -> x <> h) l2)
      in union (fv exp1) (fv exp2)
  in
  let rec subs e1 x e2 = 
    match e2 with
      Var var ->
        if var = x then e1
        else e2
    | Lam (var, exp) ->
        if x = var then e2
        else if List.mem var (fv e1) then
          let new_var = getFreshVariable var in
          let new_exp = subs (Var new_var) var exp in
          Lam (new_var, subs e1 x new_exp)
        else Lam (var, subs e1 x exp)
    | App (exp1, exp2) -> 
        let s1 = subs e1 x exp1 in
        let s2 = subs e1 x exp2 in
        App (s1, s2)
  in
  match e with
    App (Lam (var1, exp1), Lam (var2, exp2)) ->
      subs (Lam (var2, exp2)) var1 exp1
  | App (Lam (var, exp1), exp2) ->
      App (Lam (var, exp1), stepv exp2)
  | App (exp1, exp2) ->
      App (stepv exp1, exp2)
  | _ -> raise Stuck
  

(*
 * implement a single step with reduction using the call-by-name strategy.
 *)
let rec stepn e =
    match e with
    | App (Lam (v, e1), e2) -> substitute e2 v e1
    | App (e1, e2) -> App (stepn e1, e2)
    | _ -> raise Stuck

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
    let rec steps e = 
        match (stepOpt stepf e) with 
          None -> Stream.from (fun _ -> None)
        | Some e' -> Stream.icons e' (steps e')
    in 
    Stream.icons e (steps e)
