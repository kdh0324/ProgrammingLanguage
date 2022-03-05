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
  if (n < 0) then
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
		
    type loc = unit       (* dummy type, to be chosen by students *) 
    type 'a heap = unit   (* dummy type, to be chosen by students *)

    let empty _ = raise NotImplemented
    let allocate _ _ = raise NotImplemented
    let dereference _ _ = raise NotImplemented
    let update _ _ _ = raise NotImplemented
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty _ = raise NotImplemented
    let lookup _ _ = raise NotImplemented
    let delete _ _ = raise NotImplemented 
    let insert _ _ = raise NotImplemented
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty _ = raise NotImplemented
    let lookup _ _ = raise NotImplemented
    let delete _ _ = raise NotImplemented
    let insert _ _ = raise NotImplemented
  end
