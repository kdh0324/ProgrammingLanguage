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

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

