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
  type t = int * (int -> elem)

  exception VectorIllegal

  let create l = 
    if l = [] then raise VectorIllegal
    else ((List.length l), fun x -> List.nth l x)
  let to_list v = 
    let d, f = v in
    let rec makeList n =
      if n = d then []
      else (f n)::makeList (n + 1)
    in makeList 0
  let dim v = let d, _ = v in d
  let nth v = 
    let _, f = v in 
    try fun n -> f n with 
    _ -> raise VectorIllegal
  let (++) v1 v2 = 
    let d1, f1 = v1 in
    let d2, f2 = v2 in
    if d1 <> d2 then raise VectorIllegal
    else (d1, fun n -> Scal.(++) (f1 n) (f2 n))
  let (==) v1 v2 = 
    let d1, f1 = v1 in
    let d2, f2 = v2 in
    if d1 <> d2 then raise VectorIllegal
    else
      let rec for_all n =
        if n = d1 then true
        else (Scal.(==) (f1 n) (f2 n)) && for_all (n + 1)
      in for_all 0
  let innerp v1 v2 = 
    let d1, f1 = v1 in
    let d2, f2 = v2 in
    if d1 <> d2 then raise VectorIllegal
    else
      let rec for_all n =
        if n = d1 then Scal.zero
        else Scal.(++) (Scal.( ** ) (f1 n) (f2 n)) (for_all (n + 1))
      in for_all 0
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  module Vec = VectorFn (Scal)

  type elem = Scal.t
  type t = int * (int -> Vec.t)

  exception MatrixIllegal

  let create m = 
    match m with
    | [] -> raise MatrixIllegal
    | _ ->
      let len = List.length m in
      let check a = List.length a = len in
      if List.for_all check m then 
        let l = List.map (fun r -> Vec.create r) m in
        (List.length l, fun c -> List.nth l c)
      else raise MatrixIllegal
  let identity d = 
    if d <= 0 then raise MatrixIllegal
    else 
      let rec makeRow n r =
        if n = d then []
        else
          if n = r then Scal.one::makeRow (n + 1) r
          else Scal.zero::makeRow (n + 1) r
      in
      (d, fun y -> Vec.create (makeRow 0 y))
  let dim m = let d, _ = m in d
  let transpose m = 
    let d, f = m in
    let vec_to_list v =
      let dim, func = v in
      let rec fun_to_list n =
        if n = dim then []
        else (func n)::fun_to_list (n + 1)
      in fun_to_list 0
    in
    (d, fun y -> 
          Vec.create (vec_to_list (d, fun x -> Vec.nth (f x) y)))
  let to_list m = 
    let d, f = m in
    let rec makeList n =
      if n = d then []
      else (Vec.to_list (f n))::makeList (n + 1)
    in makeList 0
  let get m r c = 
    let _, f = m in
    try Vec.nth (f r) c with
      _ -> raise MatrixIllegal
  let (++) x y =
    let d1, f1 = x in
    let d2, f2 = y in
    if d1 <> d2 then raise MatrixIllegal
    else (d1, fun n -> Vec.(++) (f1 n) (f2 n))
  let ( ** ) x y =
    let d1, f1 = x in
    let d2, f2 = transpose y in
    if d1 <> d2 then raise MatrixIllegal
    else 
      let vec_to_list v =
        let dim, func = v in
        let rec fun_to_list n =
          if n = dim then []
          else (func n)::fun_to_list (n + 1)
        in fun_to_list 0
      in
      (d1, fun r -> 
            Vec.create (vec_to_list (d1, fun c -> Vec.innerp (f1 r) (f2 c))))
  let (==) x y =
    let d1, f1 = x in
    let d2, f2 = transpose y in
    if d1 <> d2 then raise MatrixIllegal
    else 
      let rec for_all n =
        if n = d1 then true
        else (Vec.(==) (f1 n) (f2 n)) && for_all (n + 1)
      in for_all 0
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

let reach g = 
  try BoolMat.to_list (BoolMatClosure.closure (BoolMat.create g)) with
  _ -> raise IllegalFormat

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

let distance g = raise NotImplemented

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

  let zero = 0              (* Dummy value : Rewrite it! *)
  let one = -1               (* Dummy value : Rewrite it! *)

  let (++) x y = 
    if x = one || y = one then one
    else if x > y then x
    else y
  let ( ** ) x y = 
    if x = one then y
    else if y = one then x
    else if x > y then y
    else x
  let (==) x y = x = y
end

(* .. Write some code here .. *)

module WeightMat = MatrixFn (Weight)
module WeightMatClosure = ClosureFn (WeightMat)

let weight g = raise NotImplemented

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
