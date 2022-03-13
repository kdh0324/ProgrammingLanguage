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
      try List.nth v n with
        _ -> raise VectorIllegal
  let (++) x y = 
    if dim x <> dim y then raise VectorIllegal
    else List.map2 (fun e1 e2 -> Scal.(++) e1 e2) x y
  let (==) x y = 
    if dim x <> dim y then raise VectorIllegal
    else List.for_all2 (fun e1 e2 -> Scal.(==) e1 e2) x y
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
  module Vec = VectorFn (Scal)

  type elem = Vec.elem
  type t = Vec.t list

  exception MatrixIllegal

  let create m = 
    match m with
    | [] -> raise MatrixIllegal
    | h::t ->
      let len = List.length h in
      let check a = List.length a = len in
      if List.for_all check t then List.map (fun r -> Vec.create r) m
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
          (Vec.create (makeRow 0))::makeMatrix (n + 1)
      in makeMatrix 0
  let dim m = List.length m
  let transpose m = 
    let d = dim m in
    let rec makeMatrix i =
      if i = d then []
      else
        let rec makeRow j =
          if j = d then []
          else (Vec.nth (List.nth m j) i)::makeRow (j + 1)
        in
        (Vec.create (makeRow 0))::makeMatrix (i + 1)
    in makeMatrix 0
  let to_list m = List.map (fun r -> Vec.to_list r) m
  let get m r c = 
    try Vec.nth (List.nth m r) c with
      _ -> raise MatrixIllegal
  let (++) x y = 
    if dim x <> dim y then raise MatrixIllegal
    else List.map2 (fun r1 r2 -> Vec.(++) r1 r2) x y
  let ( ** ) x y = 
    if dim x <> dim y then raise MatrixIllegal
    else 
      let transpose_y = transpose y in
      List.map (fun r -> 
        Vec.create (List.map (fun r_ -> Vec.innerp r r_) transpose_y)) x
  let (==) x y =
    if dim x <> dim y then raise MatrixIllegal
    else List.for_all2 (fun r1 r2 -> Vec.(==) r1 r2) x y
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure m = 
    let i = Mat.identity (Mat.dim m) in
    let rec get_closure curr =
      let next = Mat.(++) i (Mat.( ** ) m curr) in
      if Mat.(==) curr next then curr
      else get_closure next
    in get_closure i
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach g = BoolMat.to_list (BoolMatClosure.closure (BoolMat.create g))

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

  let zero = -1              (* Dummy value : Rewrite it! *)
  let one = 0               (* Dummy value : Rewrite it! *)

  let (++) x y = 
    if x = zero then y
    else if y = zero then x
    else if x < y then x
    else y
  let ( ** ) x y = 
    if x = zero || y = zero then zero
    else x + y
  let (==) x y = x = y
end

(* .. Write some code here .. *)

module DisMat = MatrixFn (Distance)
module DisMatClosure = ClosureFn (DisMat)

let distance g = DisMat.to_list (DisMatClosure.closure (DisMat.create g))

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
