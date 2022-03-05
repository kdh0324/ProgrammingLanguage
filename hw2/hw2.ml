exception NotImplemented
exception Out_of_boundary
	    
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lrevrev l = 
  match l with
  | [] -> []
  | h::t -> 
    let rec rev list =
      match list with
      | [] -> []
      | h_::t_ -> rev t_ @ [h_]
    in lrevrev t @ [rev h];;

let rec lfoldl f e l = 
  match l with
  | [] -> e
  | h::t -> lfoldl f (f (h, e)) t;;

			 
(** Tail recursive functions  **)

let fact n = 
  if (n < 0) then
    raise Out_of_boundary
  else
    let rec helper i acc =
      match i with
      | 0 -> 1
      | 1 -> acc
      | _ -> acc * helper (i - 1) (acc + 1)
    in helper n 1;;

let fib n = 
  if (n < 0) then
    raise Out_of_boundary
  else
    let rec helper i acc1 acc2 =
      match i with
      | 0 -> acc1
      | 1 -> acc2
      | _ -> helper (i - 1) acc2 (acc1 + acc2)
    in helper n 1 1;;

let alterSum l = 
  let rec helper l_ acc flag =
    match l_, flag with
    | [], _ -> acc
    | h::t, 0 -> helper t (acc + h) 1
    | h::t, 1 -> helper t (acc - h) 0
  in helper l 0 0;;

let ltabulate n f = 
  if n < 0 then
    raise Out_of_boundary
  else
    let rec helper n_ acc =
      match n_ with
      | 0 -> acc
      | _ -> helper (n_ - 1) ([f (n_ - 1)] @ acc)
    in helper n [];;

let lfilter f l =
  let rec helper l_ acc =
    match l_ with
    | [] -> acc
    | h::t ->
      if f h then helper t (acc @ [h])
      else helper t acc
  in helper l [];;

let union l1 l2 = 
  let rec helper l acc =
    match l with
    | [] -> acc
    | h::t ->
      let rec find n l_ =
        match l_ with
        | [] -> false
        | h::t -> (n = h) || (find n t)
      in if find h acc then helper t acc
      else helper t (h::acc)
  in helper l1 l2;;

let inorder t = 
  let rec helper t_ acc =
    match t_ with
    | Leaf n -> acc @ [n]
    | Node (l, n, r) -> (helper l []) @ [n] @ (helper r [])
  in helper t [];;
	   
let postorder t = 
  let rec helper t_ acc =
    match t_ with
    | Leaf n -> acc @ [n]
    | Node (l, n, r) -> (helper l []) @ (helper r []) @ [n]
  in helper t [];;

let preorder t = 
  let rec helper t_ acc =
    match t_ with
    | Leaf n -> acc @ [n]
    | Node (l, n, r) -> [n] @ (helper l []) @ (helper r [])
  in helper t [];;
		       
(** Sorting in the ascending order **)

let rec quicksort l = 
  match l with
  | [] -> []
  | h::[] -> [h]
  | h::t ->
    let rec splitWithPivot n l_ acc1 acc2 =
      match l_ with
      | [] -> (acc1, acc2)
      | h_::t_ when h_ > n -> splitWithPivot n t_ acc1 (acc2 @ [h_])
      | h_::t_ when h_ <= n -> splitWithPivot n t_ (acc1 @ [h_]) acc2
    in
    let left, right = splitWithPivot h t [] []
    in (quicksort left) @ [h] @ (quicksort right)
  ;;

let rec mergesort l = 
  match l with
  | [] -> []
  | h::[] -> [h]
  | _ ->
    let rec split l_ acc1 acc2 =
      match l_ with
      | [] -> (acc1, acc2)
      | h::t -> split t acc2 (h::acc1)
    in
    let rec merge l1 l2 =
      match l1, l2 with
      | _, [] -> l1
      | [], _ -> l2
      | h1::t1, h2::t2 when h1 > h2 -> h2::(merge l1 t2)
      | h1::t1, h2::t2 when h1 <= h2 -> h1::(merge t1 l2)
    in
    let left, right = split l [] []
    in 
    merge (mergesort left) (mergesort right)
  ;;
			
(** Structures **)

module type HEAP = 
  sig
    exception InvalidLocation
    type loc
    type 'a heap
    val empty : unit -> 'a heap
    val allocate : 'a heap -> 'a -> 'a heap * loc
    val dereference : 'a heap -> loc -> 'a 
    val update : 'a heap -> loc -> 'a -> 'a heap
  end
    
module type DICT =
  sig
    type key
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict 
  end

module Heap : HEAP =
  struct
    exception InvalidLocation 
		
    type loc = int       (* dummy type, to be chosen by students *) 
    type 'a heap = (loc * 'a) list   (* dummy type, to be chosen by students *)

    let empty () = [];;
    let allocate h v = 
      let len = List.length h in
      (h @ [(len, v)], len)
      ;;
    let dereference h l =
      let len = List.length h in
      if len <= l then raise InvalidLocation
      else 
        let _, v = List.nth h l in
        v
      ;;
    let update h l v = 
      let len = List.length h in
      if len <= l then raise InvalidLocation
      else
        let rec splitWithLoc h_ l_ acc =
          if l_ = 0 then (acc, h_)
          else
            match h_ with
            | [] -> raise InvalidLocation
            | h__::t -> splitWithLoc t (l_ - 1) (acc @ [h__])
        in
        let left, right = splitWithLoc h l [] in
        left @ [(l, v)] @ right
      ;;
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty () = []
    let lookup d k = 
      let rec find =
        function
        | [] -> None
        | (k_, v)::t when k_ = k -> Some v
        | h::t -> find t
      in find d
      ;;
    let delete d k =
      let rec find =
        function
        | [] -> []
        | (k_, v)::t when k_ = k -> find t
        | h::t -> h::(find t)
      in find d
      ;;
    let insert d (k, v) = 
      let rec find =
        function
        | [] -> [(k, v)]
        | (k_, v_)::t when k_ = k -> (k, v)::t
        | h::t -> h::(find t)
      in find d
    ;;
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty () = function k -> None;;
    let lookup d k = d k;;
    let delete d k = 
      function k_ ->
        if k_ = k then None
        else d k_
      ;;
    let insert d (k, v) = 
      function k_ ->
        if k_ = k then Some v
        else d k
      ;;
  end
