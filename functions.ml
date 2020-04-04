let sumList list =
  let rec smlst curr =
      match curr with
      | [] -> 0 (*base pattern*)
      | head :: rest -> head + smlst rest (*inductive pattern*)
in
  smlst list

(* Compute the Fibonacci number of n *)
let fibonacci n =
  let rec fib curr =
      match curr with
      | 0 -> 0 (*base pattern*)
      | 1 -> 1 (* base pattern*)
      | n -> fib (n-1) + fib(n-2) (*inductive pattern*)
in
  fib n

(* Duplicate the elements of a list *)
let duplicate list = 
  let rec dup curr = 
      match curr with
      | [] -> [] (*base pattern*)
      | head :: rest -> head :: head :: dup rest (*inductive pattern*)
in
  dup list

(* Reverse a list *)
let rev list =
  let rec visit i curr = 
      match curr with 
      | [] -> i
      | head :: rest -> visit (head :: i) rest
in 
  visit [] list

(* Converse a string to a list of characters. *)
let explode s =
let rec exp i l =
  if i < 0 then l else exp (i - 1) (s.[i] :: l) in
exp (String.length s - 1) []


(* Check whether a list is a palindrome *)
let is_palindrome str =
  let str = explode str in 
  let rec pal str = 
      str = rev str
in pal str


(* below functions using format 
type var = string
type exp =
    Var of var
  | Lam of var * exp
  | App of exp * exp
 *)
let newvar =
  let x = ref 0 in
  fun () -> 
    let c = !x in
    incr x;
    "v"^(string_of_int c)

let rec fvs e = 
  match e with
    |Var x -> x::[] (*FV(x)=x*)
    |Lam(x,e0) -> List.find_all(fun y -> x <> y)(fvs e0)(* find_all p l - returns all elements of list l that satisfy predicate p -  [varse(e) - x] *)
    |App(e0,e1) -> List.append(fvs e0)(fvs e1) (* FV(e1) + FV(e2) combining *)

let rec subst e y m =
  match e with 
    |Var x -> if (x <> y) then e else m  (*when y subsitute in variable m *)
    |Lam (x, e0) -> 
        if(List.exists(fun x -> y = x)(fvs m)) then (*alpha renaming needed (called fvs) - when m contains free variable already bounded in the 'e'*)
          let a = newvar() in Lam(a, subst(subst e0 x (Var a))(y)(m))
        else (*no alpha renaming needed*)
          if (y <> x) then let a = subst e0 y m in Lam(x,a)
          else Lam(y, e0)(*y must be equal to x - can't just place m in x here *)
    |App (e0,e1) -> 
        let a1 = (subst e0 y m) in let a2 = (subst e1 y m) in App(a1,a2)

let rec reduce e =
  match e with
    |Var x -> e
    |Lam(x,e0) -> let a1 = (reduce e0) in Lam(x, a1) (* recursively call reduce *)
    |App (Lam(x,e0), e1) -> subst e0 x e1 (*normal beta reduction -- like (λx.y) z   which looks for x in left side to replace with z*)
    |App (e0,e1) -> let a1 = (reduce e0) in let a2=(reduce e1) in App(a1, a2) (*recursively call reduce function to both sides of application*)


(* more practice functions *)
(* return a list that contains the integers i through j inclusive *)
let interval i j =
  let rec intr i j =
     if i>j then []
     else i::intr (i+1) (j) 
   in 
     intr i j
 ;;
 
 (* Use tail-recursion to compute the number of elements in the list *)
 let length list =
   let rec len i curr =
     match curr with
     | [] -> i
     | head::rest -> len (i+1) rest
   in
     len 0 list
 ;;
 
 (* Eliminate consecutive duplicates of list elements. *)
 let compress list =
   let rec comp list =
     match list with
       | [] -> [] (*base pattern*)
       | head::mid::rest -> 
           if head <> mid then head::(comp (mid::rest))
           else comp (mid::rest)
       | head::rest -> head::comp rest 
   in
     comp list
 ;;
 
 (* Check if n is a prime number *)
  let is_prime n =
     let n = abs n in
     let rec is_not_divisor d =
       d * d > n || (n mod d <> 0 && is_not_divisor (d+1)) in
     n <> 1 && is_not_divisor 2;;
 
 (* Goldbach's conjecture *)
 let goldbach n =
   let rec gold prime1 prime2  =
     if (is_prime(prime1) && is_prime(prime2)) then (prime1, prime2) (* both are prime numbers return!*)
     else
         gold (prime1+1) (n-(prime1+1)) 
   in 
     gold (2) (n-1)  (*2 is first prime number - 1 isn't prime *)
 ;;
 
 type 'a binary_tree =
     | Empty
     | Node of 'a * 'a binary_tree * 'a binary_tree;;
 
 (*Symmetric binary trees.*)
 let is_symmetric t = 
   let rec sym left right =
     match left,right with
     | Empty, Empty -> true
     | Node(root1, left1, right1), Node(root2, left2, right2) -> 
         if (left1=left2 && right1=right2) then (sym (left1) (right1) && sym (left2) (right2))
         else false
     | (Node (_, _, _), Empty) ->  false
     | (Empty, Node (_, _, _)) -> false 
   in  
     sym t t
 ;;

 let rec check queenSpot col row = 
  match queenSpot with
  | [] -> true 
  | (horizL,diagUpL,diagDownL)::tl -> if ( (horizL = row) || ( diagUpL =(col-row)) || (diagDownL = (col+row))) then false else check tl col row
;;

let rec makeArr tup= 
  match tup with
  | [] -> []
  | (horizL,non1,non2)::tl -> horizL:: makeArr tl ;;

let queens_positions n =
    let rec queen col row placedQueens  =
      if col <= n then (*completed last column so stop recursion   -  (makeArr (placedQueens))*)
        (if row>=1 then (List.rev_append (if (check (placedQueens) (col) (row)) then 
        queen (col + 1) n (((row), (col-row), (col+row))::(placedQueens)) else [])  (queen col (row-1) placedQueens)  ) 
        else [] )
      else [ makeArr (placedQueens) ]
    in queen 1 n [];;


(*more practice functions *)

type substitution = (id * typ) list
(* ~ check if a variable occurs in a term ~ *)
(*
id is string

typ is 
|TVar of id
|Arrow of typ * typ
*)

let rec occurs (x : id) (t : typ) : bool =
	match t with
	| TVar a -> 
			if a = x then true 
			else false 
	| Arrow (a, b) -> 
			if occurs x a then true
			else if occurs x b then true
      else false 
      
(* ~ substitute term s for all occurrences of var x in term t ~ *)
(*
id is string

typ is
|TVar of id
|Arrow of typ * typ
*)

let rec subst (s : typ) (x : id) (t : typ) : typ =
	match t with
	| TVar a -> if (a <> x) then t else s
	| Arrow (a, b) -> 
		let a1 = (subst s x a) in 
		let a2 = (subst s x b) in 
    Arrow (a1, a2) (*recurse through both sides*)
  
(* ~ apply a substitution to t right to left ~*)
(*
substitution is (id * typ) list
typ is 
|TVar of id
|Arrow of typ * typ
*)

let apply (s : substitution) (t : typ) : typ =
	let rec app s t =
		match s with
			| [] -> t
			| (a, b)::r -> app r (subst b a t) 
		in app s t

(* ~ unify one pair ~  *)
let rec unHelper (s : (typ * typ) list) : substitution =
	match s with
	| [] -> []
	| (TVar a, ((TVar b) as t))::r ->
		if a=b then [] @ unify r
		else [(a, t)] @ unify r
	| (Arrow (_,_) as t, TVar d)::r ->
		if not (occurs d t) then [(d, t)] @ unify r
		else failwith "not unifiable: circularity"
	| (TVar a,(Arrow (_,_) as t))::r  ->
		if not(occurs a t) then [(a, t)] @ unify r
		else failwith "not unifiable: circularity"
	| ((Arrow (a, b) as l), (Arrow (c, d) as m))::r -> 
		if l = m then [] 
		else unify [(a, c); (b, d)] @ unify r

and unify (s : (typ * typ) list) : substitution =
	(* print_endline "unify called"; *)
	let rec uni s =
  	match s with
  	| [] -> []
		| (a, b) :: r ->
			unHelper (((apply (unify r) a),(apply (unify r) b))::r)
  in uni s 
  
(* collect constraints and perform unification using separate infer file which the code was provided *)
let infer (e : expr) : typ =
    Infer.reset_type_vars();
    let annotate = Infer.annotate e in
      apply (unify (Infer.collect [annotate] [])) (Infer.type_of annotate)



  
