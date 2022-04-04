open Tml

exception TypeError

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)
type context = var -> tp

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 *)

let createEmptyContext () = fun _ -> raise TypeError

(* val typing : context -> Tml.exp -> Tml.tp *)
let rec typing cxt e = 
  match e with
    Var v -> cxt v
  | Lam (v, t, exp) ->
      let newCxt = fun x -> if x = v then t else cxt x in
      Fun (t, typing newCxt exp)
  | App (exp1, exp2) ->
      let tp1 = typing cxt exp1 in
      (match tp1 with
        Fun (t1, t2) -> 
          let tp2 = typing cxt exp2 in
          if tp1 = tp2 then t2
          else raise TypeError
      | _ -> raise TypeError)
  | Pair (exp1, exp2) -> Prod (typing cxt exp1, typing cxt exp2)
  | Fst exp ->
      (match exp with
        Pair (e1, _) -> typing cxt e1
      | _ -> raise TypeError)
  | Snd exp ->
      (match exp with
        Pair (_, e2) -> typing cxt e2
      | _ -> raise TypeError)
  | Eunit -> Unit
  | Inl (exp, t) -> Sum (typing cxt exp, t)
  | Inr (exp, t) -> Sum (t, typing cxt exp)
  | Case (exp, v1, exp1, v2, exp2) ->
      let tp = typing cxt exp in
      (match tp with
        Sum (t1, t2) ->
          let newCxt = 
            fun x -> 
              if x = v1 then t1 
              else if x = v2 then t2 
              else cxt x in
          let tp1 = typing newCxt exp1 in
          let tp2 = typing newCxt exp2 in
          if tp1 = tp2 then tp1
          else raise TypeError
      | _ -> raise TypeError)
  | Fix (v, t, exp) ->
      let newCxt = fun x -> if x = v then t else cxt x in
      let tp = typing newCxt exp in
      if tp = t then tp
      else raise TypeError
  | True 
  | False -> Bool
  | Ifthenelse (exp1, exp2, exp3) ->
      let tp1 = typing cxt exp1 in
      (match tp1 with
        Bool ->
          let tp2 = typing cxt exp2 in
          let tp3 = typing cxt exp3 in
          if tp2 = tp3 then tp2
          else raise TypeError
      | _ -> raise TypeError)
  | Num _ -> Int
  | Plus
  | Minus -> Fun (Prod (Int, Int), Int)
  | Eq -> Fun (Prod (Int, Int), Bool)

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None
