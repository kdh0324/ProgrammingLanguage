open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1

  let (++) x y = x + y
  let ( ** ) x y = x * y
  let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true

  let (++) x y = x || y
  let ( ** ) x y = x && y
  let (==) x y = x = y
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list

  exception VectorIllegal

  let create v = 
    if v = [] then raise VectorIllegal
    else v
  let to_list v = v
  let dim v = List.length v
  let nth v = 
    fun n -> 
      if n >= dim v || n < 0 then raise VectorIllegal
      else List.nth v n
  let (++) x y = 
    if dim x <> dim y then raise VectorIllegal
    else
      let rec merge v1 v2 =
        match v1, v2 with
        | [], [] -> []
        | h1::t1, h2::t2 -> (Scal.(++) h1 h2)::(merge t1 t2)
      in merge x y
  let (==) x y = 
    if dim x <> dim y then raise VectorIllegal
    else
      let rec checkAll v1 v2 =
        match v1, v2 with
        | [], [] -> true
        | h1::t1, h2::t2 -> (Scal.(==) h1 h2) && (checkAll t1 t2)
      in checkAll x y
  let innerp x y = 
    if dim x <> dim y then raise VectorIllegal
    else
      let rec prod v1 v2 =
        match v1, v2 with
        | [], [] -> Scal.zero
        | h1::t1, h2::t2 -> Scal.(++) (Scal.( ** ) h1 h2) (prod t1 t2)
      in prod x y
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = (elem list) list

  exception MatrixIllegal

  let create m = 
    match m with
    | [] -> raise MatrixIllegal
    | h::t ->
      let len = List.length h in
      let check a = List.length a = len in
      if List.for_all check t then m
      else raise MatrixIllegal
  let identity d = 
    if d <= 0 then raise MatrixIllegal
    else 
      let rec makeMatrix n =
        if n = d then []
        else
          let rec makeRow n_ =
            if n_ = d then []
            else
              if n_ = n then Scal.one::makeRow (n_ + 1)
              else Scal.zero::makeRow (n_ + 1)
          in
          (makeRow 0)::makeMatrix (n + 1)
      in makeMatrix 0
  let dim m = List.length m
  let transpose m = 
    let d = dim m in
    let rec makeMatrix i =
      if i = d then []
      else
        let rec makeRow j =
          if j = d then []
          else (List.nth (List.nth m j) i)::makeRow (j + 1)
        in
        (makeRow 0)::makeMatrix (i + 1)
    in makeMatrix 0
  let to_list m = m
  let get m r c = 
    let d = dim m in
    if r >= d || c >= d then raise MatrixIllegal
    else List.nth (List.nth m r) c
  let (++) x y = 
    if dim x <> dim y then raise MatrixIllegal
    else
      let rec calRow r1 r2 =
        match r1, r2 with
        | [], [] -> []
        | h1::t1, h2::t2 -> (Scal.(++) h1 h2)::(calRow t1 t2)
      in
      let rec calMat m1 m2 =
        match m1, m2 with
        | [], [] -> []
        | h1::t1, h2::t2 -> (calRow h1 h2)::(calMat t1 t2)
      in calMat x y
  let ( ** ) x y = 
    if dim x <> dim y then raise MatrixIllegal
    else
      let rec calRow r1 r2 =
        match r1, r2 with
        | [], [] -> []
        | h1::t1, h2::t2 -> (Scal.( ** ) h1 h2)::(calRow t1 t2)
      in
      let rec calMat m1 m2 =
        match m1, m2 with
        | [], [] -> []
        | h1::t1, h2::t2 -> (calRow h1 h2)::(calMat t1 t2)
      in calMat x y
  let (==) x y =
    if dim x <> dim y then raise MatrixIllegal
    else
      let rec calRow r1 r2 =
        match r1, r2 with
        | [], [] -> true
        | h1::t1, h2::t2 -> (Scal.(==) h1 h2) && (calRow t1 t2)
      in
      let rec calMat m1 m2 =
        match m1, m2 with
        | [], [] -> true
        | h1::t1, h2::t2 -> (calRow h1 h2) && (calMat t1 t2)
      in calMat x y
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure _ = raise NotImplemented
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach _ = raise NotImplemented

let al = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  false; false];
   [false; true;  true;  false; true;  false];
   [false; true;  false; true;  true;  true];
   [false; false; true;  true;  true;  false];
   [false; false; false; true;  false; true]]

let solution_al' = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 999999              (* Dummy value : Rewrite it! *)
  let one = 999999               (* Dummy value : Rewrite it! *)

  let (++) _ _ = raise NotImplemented
  let ( ** ) _ _ = raise NotImplemented
  let (==) _ _ = raise NotImplemented
end

(* .. Write some code here .. *)

let distance _ = raise NotImplemented

let dl =
  [[  0;  -1;  -1;  -1;  -1;  -1 ];
   [ -1; 0  ; 35 ; 200; -1 ; -1  ];
   [ -1; 50 ; 0  ; -1 ; 150; -1  ];
   [ -1; 75;  -1 ; 0  ; 100; 25  ];
   [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
   [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
  [[0;  -1;  -1;  -1;  -1;  -1  ];
   [-1; 0;   35;  200; 185; 225 ];
   [-1; 50;  0;   215; 150; 240 ];
   [-1; 75;  110; 0;   100; 25  ];
   [-1; 100; 50;  65;  0;   90  ];
   [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 999999              (* Dummy value : Rewrite it! *)
  let one = 999999               (* Dummy value : Rewrite it! *)
 
  let (++) _ _ = raise NotImplemented
  let ( ** ) _ _ = raise NotImplemented
  let (==) _ _ = raise NotImplemented
end

(* .. Write some code here .. *)

let weight _ = raise NotImplemented

let ml =
  [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
   [0 ; -1 ; 10 ; 100; 0  ; 0   ];
   [0 ; 50 ; -1 ; 0  ; 150; 0   ];
   [0 ; 75 ; 0  ; -1 ; 125; 40 ];
   [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
   [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
  [[-1; 0;  0;   0;   0;   0  ];
   [0;  -1; 25;  100; 100; 40 ];
   [0;  75; -1;  150; 150; 40 ];
   [0;  75; 25;  -1;  125; 40 ];
   [0;  75; 25;  -1;  -1;  40 ];
   [0;  0;  0;   0;   0;   -1 ]]

let _ =
  try 
  if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
    print_endline "\nYour program seems fine (but no guarantee)!"
  else
    print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!" 

