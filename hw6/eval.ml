open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = NOT_IMPLEMENT_ENV
 and value = NOT_IMPLEMENT_VALUE
 and frame = NOT_IMPLEMENT_FRAME

(* Define your own empty environment *)
let emptyEnv = NOT_IMPLEMENT_ENV

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp _ = raise NotImplemented

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
let texp2exp texp = 
  let rec find l v =
    match l with
      [] -> 0
    | h::t ->
      if h = v then 0
      else (find t v) + 1
    in
  let rec helper te s = 
    match te with
      Tvar v -> 
        if List.mem v s then (Ind(find s v), s)
        else (Ind(find (s @ [v]) v), (s @ [v]))
    | Tlam (v, tp, te') ->
			let result = helper te' (v::s) in
			(Lam(fst result), List.tl (snd result))
    | Tapp (te1, te2) -> 
      let result2 = helper te2 s in
      let result1 = helper te1 (snd result2) in
      (App(fst result1, fst result2), snd result1)
    | Tpair (te1, te2) -> 
      let result2 = helper te2 s in
      let result1 = helper te1 (snd result2) in
      (Pair(fst result1, fst result2), snd result1)
    | Tfst te' -> 
      let result = helper te' s in
      (Fst(fst result), snd result)
    | Tsnd te' -> 
      let result = helper te' s in
      (Snd(fst result), snd result)
    | Teunit -> (Eunit, s)
    | Tinl (te', tp) -> 
      let result = helper te' s in
      (Inl(fst result), snd result)
    | Tinr (te', tp) -> 
      let result = helper te' s in
      (Inr(fst result), snd result)
    | Tcase (te', v1, te1, v2, te2) -> 
      let result2 = helper te2 (v2::s) in
      let result1 = helper te1 (v1::List. tl (snd result2)) in
      let result' = helper te' (List.tl (snd result1)) in
      (Case(fst result', fst result1, fst result2), snd result')
    | Tfix (v, tp, te') -> 
      let result = helper te' (v::s) in
      (Fix(fst result), List.tl (snd result))
    | Ttrue -> (True, s)
    | Tfalse -> (False, s)
    | Tifthenelse (te', te1, te2) -> 
      let result2 = helper te2 s in
      let result1 = helper te1 (snd result2) in
      let result' = helper te' (snd result1) in
      (Ifthenelse(fst result', fst result1, fst result2), snd result')
    | Tnum v -> (Num(v), s)
    | Tplus -> (Plus, s)
    | Tminus -> (Minus, s)
    | Teq -> (Eq, s)
  in 
  let e, _ = helper texp [] in e
(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   
let rec step1 e = 
  let rec shift i n e' =
    match e' with
      App (e1, e2) -> App(shift i n e1, shift i n e2)
    | Lam e'' -> Lam(shift (i + 1) n e'')
    | Ind m ->
      if m >= i then Ind(m + n)
      else Ind(m)
    | Pair (e1, e2) -> Pair(shift i n e1, shift i n e2)
    | Fst e'' -> Fst(shift i n e'')
    | Snd e'' -> Snd(shift i n e'')
    | Inl e'' -> Inl(shift i n e'')
    | Inr e'' -> Inr(shift i n e'')
    | Fix e'' -> Fix(shift i (n + 1) e'')
    | Case (e'', e1, e2) -> Case(shift i n e'', shift i (n + 1) e1, shift i (n + 1) e2)
    | Ifthenelse (e'', e1, e2) -> Ifthenelse(shift i n e'', shift i n e1, shift i n e2)
    | _ -> e'
    in
  let rec subs n e1 e2 =
    match e1 with
      App (e11, e12) -> App(subs n e11 e2, subs n e12 e2)
    | Lam e' -> Lam(subs (n + 1) e' e2)
    | Ind m ->
      if m < n then Ind(m)
      else if m > n then Ind(m - 1)
      else shift 0 n e2
    | Pair (e11, e12) -> Pair(subs n e11 e2, subs n e12 e2)
    | Fst e' -> Fst(subs n e' e2)
    | Snd e' -> Snd(subs n e' e2)
    | Inl e' -> Inl(subs n e' e2)
    | Inr e' -> Inr(subs n e' e2)
    | Fix e' -> Fix(subs (n + 1) e' e2)
    | Case (e', e11, e12) -> Case(subs n e' e2, subs (n + 1) e11 e2, subs (n + 1) e12 e2)
    | Ifthenelse (e', e11, e12) -> Ifthenelse(subs n e' e2, subs n e11 e2, subs n e12 e2)
    | _ -> e1
    in
  match e with
    App (Plus, App (Num n1, Num n2)) -> Num(n1 + n2)
  | App (Minus, App (Num n1, Num n2)) -> 
    if n1 >= n2 then Num(n1 - n2)
    else Num(0)
  | App (Eq, App (Num n1, Num n2)) -> 
    if n1 = n2 then True
    else False
  | App (Lam e1, e2) -> (try App(Lam(e1), step1 e2) with Stuck -> subs 0 e1 e2)
  | App (e1, e2) -> App(step1 e1, e2)
  | Pair (e1, e2) -> Pair(step1 e1, step1 e2)
  | Fst e' -> Fst(step1 e')
  | Snd e' -> Snd(step1 e')
  | Inl e' -> Inl(step1 e')
  | Inr e' -> Inr(step1 e')
  | Case (Inl (e'), e1, e2) -> e1
  | Case (Inr (e'), e1, e2) -> e2
  | Case (e', e1, e2) -> Case(step1 e', e1, e2)
  | Fix e' -> subs 0 (Fix e') e'
  | Ifthenelse (True, e1, e2) -> e1
  | Ifthenelse (False, e1, e2) -> e2
  | Ifthenelse (e', e1, e2) -> Ifthenelse(step1 e', e1, e2)
  | _ -> raise Stuck

(* Problem 3. 
 * step2 : state -> state *)
let step2 _ = raise NotImplemented
                    
(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st = match st with
    Anal_ST(_,_,exp,_) -> "Analysis : ???"
  | Return_ST(_,_,_) -> "Return : ??? "

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
