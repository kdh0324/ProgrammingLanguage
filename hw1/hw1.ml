exception Not_implemented
exception Out_of_boundary

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

let rec sum n = 
    if (n < 0) then raise Out_of_boundary
    else if (n == 1) then 1
    else sum (n - 1) + n
;;

let rec fib n = 
    (* if (n < 0) then raise Out_of_boundary
    else if (n >= 2) then
        fib (n - 1) + fib (n - 2)
    else
        1 *)
    match n with
    | 0 -> 1
    | 1 -> 1
    | _ -> fib (n - 1) + fib (n - 2)
;;

let rec gcd m n = 
    if (m < 0 || n < 0) then raise Out_of_boundary
    else if (m == 0) then n
    else if (n == 0) then m
    else if (m > n) then gcd n (m mod n)
    else if (n < m) then gcd m (n mod m)
    else m
;;

let rec combi n k = 
    if (n <= 0 || k < 0 || k > n) then raise Out_of_boundary
    else if (k == 1) then n
    else n * combi (n - 1) (k - 1) / k
;;

let rec sum_tree t = 
    match t with
    | Leaf n -> n
    | Node (l, n, r) ->
        n + (sum_tree l) + (sum_tree r)
;;

let rec depth t = 
    match t with
    | Leaf n -> 0
    | Node (l, n, r) ->
        if (depth l > depth r) then
            depth l + 1
        else
            depth r + 1
;;

let rec bin_search t n = 
    match t with
    | Leaf i ->
        if (i == n) then true
        else false
    | Node (l, i, r) ->
        if (i == n) then true
        else (bin_search l n) && (bin_search r n)
;;

let rec inorder t = 
    match t with
    | Leaf n -> [n]
    | Node (l, n, r) ->
        (inorder l) @ [n] @ (inorder r)
;;

let rec max l = 
    match l with
    | [] -> 0
    | head::[] -> head
    | head::list ->
        if (head > max list) then head
        else max list
;;

let rec list_add l1 l2 = 
    match l1, l2 with
    | [], list -> list
    | list, [] -> list
    | (h1::list1), (h2::list2) -> [h1 + h2] @ list_add list1 list2
;;

let rec insert n l = 
    match l with
    | [] -> [n]
    | head::tail ->
        if (head < n) then head::(insert n tail)
        else n::l
;;

let rec insort l = 
    match l with
    | [] -> []
    | head::tail -> insert head (insort tail)
;;

let rec compose f g =
    fun x -> g (f x)
;;

let rec merge f g = 
    fun (x, y) -> ((f x), (g y))
;;

let rec curry f x y = f (x, y);;

let rec uncurry f (x, y) = f x y;;

let rec multifun f n = 
    fun x ->
        if (n <= 0) then raise Out_of_boundary
        else if (n == 1) then f x
        else f (multifun f (n - 1) x)
;;

let rec ltake l n = 
    if (n < 0) then raise Out_of_boundary
    else
        match l, n with
        | [], _ -> []
        | _, 0 -> []
        | head::tail, _ -> [head] @ (ltake tail (n - 1))
;;

let rec lall f l = 
    (* List.for_all f l *)
    match l with
    | [] -> true
    | head::tail -> (f head) && (lall f tail)
;;

let rec lmap f l = 
    (* List.map f l *)
    match l with
    | [] -> []
    | head::tail -> [f head] @ (lmap f tail)
;;

let rec lrev l = 
    (* List.fold_left (fun x y -> y::x) [] l *)
    match l with
    | [] -> []
    | head::tail -> (lrev tail) @ [head]
;;

let rec lflat l = 
    (* List.flatten l *)
    match l with
    | [] -> []
    | head::tail -> head @ lflat tail
;;

let rec lzip l1 l2 = 
    match l1, l2 with
    | _, [] -> []
    | [], _ -> []
    | h1::t1, h2::t2 -> (h1, h2)::(lzip t1 t2)
;;

let rec split l = 
    let rec sp list fst snd =
        match list with
        | [] -> (fst, snd)
        | [n] -> (fst @ [n], snd)
        | head::second::remain -> sp remain (fst @ [head]) (snd @ [second])
    in sp l [] []
;;

let rec cartprod l1 l2 = 
    match l1, l2 with
    | [], _ -> []
    | _, [] -> []
    | head::tail, _ -> (lmap (fun x -> (head, x)) l2) @ (cartprod tail l2)
;;
