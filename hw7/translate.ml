open Mach
open Mono 

exception NotImplemented
exception NotMatched
exception NotDeclared

(* location *)
type loc =
    L_INT of int          (* integer constant *)
  | L_BOOL of bool        (* boolean constant *)
  | L_UNIT                (* unit constant *)
  | L_STR of string       (* string constant *)
  | L_ADDR of Mach.addr   (* at the specified address *)
  | L_REG of Mach.reg     (* at the specified register *)
  | L_DREF of loc * int   (* at the specified location with the specified offset *)

type venv = (Mono.avid, loc) Dict.dict  (* variable environment *)
let venv0 : venv = Dict.empty           (* empty variable environment *)

type env = venv * int
let env0 : env = (venv0, 0)

let (failure_label : label) = "Fail"
let temp_label = fun () -> "_Temp_" ^ labelNew () ^ "_"
let fun_label = fun () -> "_Function_" ^ labelNew () ^ "_"
let con_label = fun avid -> "_Constructor_" ^ avid ^ "_"

(* val loc2rvalue : loc -> Mach.code * rvalue *)
let rec loc2rvalue l = match l with
    L_INT i -> (Mach.code0, Mach.INT i)
  | L_BOOL b -> (Mach.code0, Mach.BOOL b)
  | L_UNIT -> (Mach.code0, Mach.UNIT)
  | L_STR s -> (Mach.code0, Mach.STR s)
  | L_ADDR a -> (Mach.code0, Mach.ADDR a)
  | L_REG r -> (Mach.code0, Mach.REG r)
  | L_DREF (L_ADDR a, i) -> (Mach.code0, Mach.REFADDR (a, i))
  | L_DREF (L_REG r, i) -> (Mach.code0, Mach.REFREG (r, i))
  | L_DREF (l, i) ->
     let (code, rvalue) = loc2rvalue l in
     (Mach.cpost code [Mach.MOVE (Mach.LREG Mach.tr, rvalue)], Mach.REFREG (Mach.tr, i))

(*
 * helper functions for debugging
 *)
(* val loc2str : loc -> string *)
let rec loc2str l = match l with 
    L_INT i -> "INT " ^ (string_of_int i)
  | L_BOOL b -> "BOOL " ^ (string_of_bool b)
  | L_UNIT -> "UNIT"
  | L_STR s -> "STR " ^ s
  | L_ADDR (Mach.CADDR a) -> "ADDR " ^ ("&" ^ a)
  | L_ADDR (Mach.HADDR a) -> "ADDR " ^ ("&Heap_" ^ (string_of_int a))
  | L_ADDR (Mach.SADDR a) -> "ADDR " ^ ("&Stack_" ^ (string_of_int a))
  | L_REG r -> 
     if r = Mach.sp then "REG SP"
     else if r = Mach.bp then "REG BP"
     else if r = Mach.cp then "REG CP"
     else if r = Mach.ax then "REG AX"
     else if r = Mach.bx then "REG BX"
     else if r = Mach.tr then "REG TR"
     else if r = Mach.zr then "REG ZR"
     else "R[" ^ (string_of_int r) ^ "]"
  | L_DREF (l, i) -> "DREF(" ^ (loc2str l) ^ ", " ^ (string_of_int i) ^ ")"

(*
 * Generate code for Abstract Machine MACH 
 *)
 (* 
  * tr: function address
  * cp: constructor address
  * r29: temporary reg
  *)
let prepare_code = ref code0
let push_cnt = ref 0
let pop_cnt = ref 0
let heap_cnt = ref 0
let incc_cnt cnt =
  push_cnt := !push_cnt + cnt;
  pop_cnt := !pop_cnt + cnt;
  ()
let rec update_venv = fun d ->
  match d with
    [] -> 
      push_cnt := 0;
      []
  | (k, v)::d' -> 
      let v' =
        (match v with
          L_DREF (L_REG sp, cnt) -> L_DREF (L_REG sp, cnt - !push_cnt)
        | _ -> v)
      in
      (k, v')::(update_venv d')
let update_env = fun e ->
  let venv, cnt = e in
  (update_venv venv, cnt)
let update_rvalue = fun v ->
  match v with
    REFREG (sp, cnt) -> REFREG (sp, cnt - !push_cnt)
  | _ -> v

(* pat2code : Mach.label -> Mach.label - > loc -> Mono.pat -> Mach.code * venv *)
let rec pat2code saddr faddr l pat = 
  let code, v = loc2rvalue l in
  match pat with
    P_WILD -> code0, venv0
  | P_INT i -> code @@ [JMPNEQ (ADDR (CADDR faddr), v, INT i)], venv0
  | P_BOOL b -> code @@ [JMPNEQ (ADDR (CADDR faddr), v, BOOL b)], venv0
  | P_UNIT -> code @@ [JMPNEQ (ADDR (CADDR faddr), v, UNIT)], venv0
  | P_VID (avid, is) -> 
      (match is with
        VAR ->
          (match l with
            L_DREF (L_REG tr, 1) -> code, Dict.singleton (avid, L_DREF (L_ADDR (HADDR (!heap_cnt - 1)), 1))
          | _ -> 
              code, Dict.singleton (avid, l))
      | CON -> 
          code @@ [JMPNEQ (ADDR (CADDR faddr), STR (con_label avid), v)], venv0
      | _ -> raise NotMatched)
  | P_VIDP ((avid, is), patty) -> 
      let code', venv = patty2code (labelNew ()) faddr (L_DREF (L_REG tr, 1)) patty in
      code @@ [JMPNEQ (ADDR (CADDR faddr), STR (con_label avid), v)] @@ code', venv
  | P_PAIR (patty1, patty2) -> 
      let code, l =
        match v with
          REFADDR _ | REFREG _ -> 
            let _ = incc_cnt 1 in
            code @@ [PUSH v], L_DREF (L_REG sp, -1)
        | _ -> code, l in
      let code1, venv1 = patty2code saddr faddr (L_DREF (l, 0)) patty1 in
      let code2, venv2 = patty2code saddr faddr (L_DREF (l, 1)) patty2 in
      code @@ code1 @@ code2, Dict.merge venv1 venv2

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
and patty2code saddr faddr l patty = 
  let PATTY (pat, _) = patty in 
  pat2code saddr faddr l pat

(* exp2code : env -> Mach.label -> Mono.exp -> Mach.code * Mach.rvalue *)
let rec exp2code env saddr e = 
  let venv, _ = env in
  match e with
    E_INT i -> code0, INT i
  | E_BOOL b -> code0, BOOL b
  | E_UNIT -> code0, UNIT
  | E_VID (avid, is) ->
    (match is with
      VAR ->
        let l = 
          (match Dict.lookup avid venv with
            None -> raise NotDeclared
          | Some l' -> l')
        in
        let code', v = loc2rvalue l in
        code0 @@ code', v
    | CON -> 
        heap_cnt := !heap_cnt + 1;
        let con_lb = con_label avid in
        let _ = incc_cnt 1 in
        prepare_code := !prepare_code @@ [LABEL con_lb] @@ [RETURN];
        [MALLOC (LREG cp, INT 1)]
          @@ [MOVE (LREFREG (cp, 0), ADDR (CADDR con_lb))]
          @@ [PUSH (REG cp)], REFREG (sp, -1)
    | CONF -> 
        heap_cnt := !heap_cnt + 2;
        let con_lb = con_label avid in
        let _ = incc_cnt 1 in
        prepare_code := !prepare_code @@ [LABEL con_lb] @@ [RETURN];
        [MALLOC (LREG cp, INT 2)]
          @@ [MOVE (LREFREG (cp, 0), ADDR (CADDR con_lb))]
          @@ [MALLOC (LREFREG (cp, 1), INT 2)]
          @@ [PUSH (REG cp)], REFREG (sp, -1))
  | E_FUN mlist -> 
      heap_cnt := !heap_cnt + 1;
      let code = mlist2code env (labelNew ()) failure_label mlist in
      let fun_lb = fun_label () in
      prepare_code := !prepare_code @@ [LABEL fun_lb] @@ code;
      pop_cnt := !pop_cnt + 1;
      [MALLOC (LREG tr, INT 2)]
          @@ [MOVE (LREFREG (tr, 0), ADDR (CADDR fun_lb))]
          @@ [PUSH (REG tr)], REFREG (sp, -1)
  | E_APP (expty1, expty2) ->
      let check = 
        (match expty1 with 
          EXPTY (E_PLUS, _) | EXPTY (E_MINUS, _) | EXPTY (E_MULT, _) | EXPTY (E_EQ, _) | EXPTY (E_NEQ, _) -> true
        | _ -> false) in
      let f = fun x y ->
        (match expty1 with
          EXPTY (E_PLUS, _) -> [ADD (LREG r29, x, y)] @@ [PUSH (REG r29)]
        | EXPTY (E_MINUS, _) -> [SUB (LREG r29, x, y)] @@ [PUSH (REG r29)]
        | EXPTY (E_MULT, _) -> [MUL (LREG r29, x, y)] @@ [PUSH (REG r29)]
        | EXPTY (E_EQ, _) -> 
            let lb = temp_label () in
            [MOVE (LREG r29, BOOL false)] @@ [JMPNEQ (ADDR (CADDR lb), x, y)] @@ [NOT (LREG r29, REG r29)] @@ [LABEL lb] @@ [PUSH (REG r29)]
        | EXPTY (E_NEQ, _) -> 
            let lb = temp_label () in
            [MOVE (LREG r29, BOOL true)] @@ [JMPNEQ (ADDR (CADDR lb), x, y)] @@ [NOT (LREG r29, REG r29)] @@ [LABEL lb] @@ [PUSH (REG r29)]
        | _ -> 
          let _ = incc_cnt (-1) in
          code0) in
      (match expty2 with
        EXPTY (E_PAIR (expty1', expty2'), _) when check -> 
          let code1, v1 = expty2code env (labelNew ()) expty1' in
          let code2, v2 = expty2code (update_env env) (labelNew ()) expty2' in
          let v1 = update_rvalue v1 in
          let _ = incc_cnt 1 in
          code1 @@ code2 @@ f v1 v2, REFREG (sp, -1)
      | _ -> 
          let code1, v1 = expty2code env (labelNew ()) expty1 in
          let code2, v2 = expty2code (update_env env) (labelNew ()) expty2 in
          let v1 = update_rvalue v1 in
          let _ = incc_cnt 1 in
          code1 @@ code2
              @@ [MOVE (LREG tr, v1)]
              @@ [MOVE (LREFREG (tr, 1), v2)]
              @@ [CALL (REFREG (tr, 0))]
              @@ [PUSH (REG tr)], REFREG (sp, -1))
  | E_PAIR (expty1, expty2) -> 
      let code1, v1 = expty2code env saddr expty1 in
      let code2, v2 = expty2code (update_env env) saddr expty2 in
      let _ = incc_cnt 1 in
      let v1 = update_rvalue v1 in
      heap_cnt := !heap_cnt + 1;
      code1 @@ code2 @@ [MALLOC (LREG r29, INT 2)] 
          @@ [MOVE (LREFREG (r29, 0), v1)] 
          @@ [MOVE (LREFREG (r29, 1), v2)] 
          @@ [PUSH (REG r29)], REFREG (sp, -1) 
  | E_LET (dec, expty) -> 
      let code1, env1 = dec2code env (labelNew ()) dec in
      let code2, v2 = expty2code env1 (labelNew ()) expty in
      code1 @@ code2, v2
  | _ -> raise NotMatched

(* expty2code : env -> Mach.label -> Mono.expty -> Mach.code * Mach.rvalue *)
and expty2code env saddr et = 
  let EXPTY (e, _) = et in
  exp2code env saddr e

(* dec2code : env -> Mach.label -> Mono.dec -> Mach.code * env *)
and dec2code env saddr dec = 
  let venv, cnt = env in
  match dec with
    D_VAL (patty, et) ->
      let etCode, v = expty2code env saddr et in
      let pattyCode, pattyVenv = patty2code (labelNew ()) failure_label (L_DREF (L_REG sp, 0)) patty in 
      let _ = incc_cnt 1 in
      let newVenv = update_venv (Dict.merge venv pattyVenv) in
      etCode @@ [PUSH v] @@ pattyCode, (newVenv, cnt)
  | D_REC (patty, et) -> 
      (match patty, et with
        PATTY (P_VID (avid, VAR), _), EXPTY (E_FUN _, _) -> 
          let venv = Dict.insert (avid, L_DREF (L_REG sp, -1)) venv in
          let etCode, v = expty2code (venv, cnt) saddr et in
          let pattyCode, pattyVenv = patty2code (labelNew ()) failure_label (L_DREF (L_REG sp, 0)) patty in 
          push_cnt := !push_cnt - 1;
          let newEnv = update_venv (Dict.merge venv pattyVenv) in
          etCode @@ pattyCode, (newEnv, cnt)
      | _ -> raise NotMatched)
  | D_DTYPE -> code0, env

(* dlist2code : env -> Mono.dec list-> Mach.code * env *)
and dlist2code env l =
  let rec helper env l code =
    match l with
      [] -> code, env
    | h::t ->
        let code', env = dec2code env (labelNew ()) h in
        helper env t (code @@ code')
    in
  helper env l code0

(* mrule2code : env -> Mach.label -> Mach.label -> Mono.mrule -> Mach.code *)
and mrule2code env saddr faddr mrule = 
  let M_RULE (patty, et) = mrule in
  let temp = !pop_cnt in
  pop_cnt := 0;
  let pattyCode, venv' = patty2code saddr faddr (L_DREF (L_REG tr, 1)) patty in
  let venv, cnt = env in
  let newEnv = (Dict.merge venv venv', cnt + 1) in
  let etCode, v = expty2code newEnv saddr et in
  let pop_code = 
    let rec helper = fun i -> 
      if i = 0 then code0
      else [POP (LREG r29)] @@ helper (i - 1) in
    helper !pop_cnt in
  pop_cnt := temp;
  [LABEL saddr] @@ pattyCode @@ etCode @@ [MOVE (LREG tr, v)] @@ pop_code @@ [RETURN]

(* mrule2code : env -> Mach.label -> Mach.label -> Mono.mrule list -> Mach.code *)
and mlist2code env saddr faddr mlist = 
    match mlist with
      [] -> code0
    | h::t ->
        let lb = temp_label () in
        let code = mrule2code env saddr lb h in
        code @@ mlist2code env lb faddr t

(* program2code : Mono.program -> Mach.code *)
let program2code (dlist, et) = 
  let decCode, env = dlist2code env0 dlist in
  let etCode, v = expty2code env (labelNew ()) et in
  let pop_code = 
    let rec helper = fun i -> 
      if i = 0 then code0
      else [POP (LREG r29)] @@ helper (i - 1) in
    helper !pop_cnt in
  !prepare_code @@ [LABEL start_label] @@ decCode @@ etCode 
      @@ [MOVE (LREG ax, REFREG (sp, -1))] 
      @@ pop_code 
      @@ [HALT (REG ax)]
