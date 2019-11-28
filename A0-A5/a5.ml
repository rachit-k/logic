exception Exception;;
exception NOT_UNIFIABLE;;
exception Noclauses;;
exception Notermination of string;;

type symbol = string ;; 
type variable = string ;;

type term = V of variable | Node of symbol * (term list)
;;

type signature = (symbol * int) list
;;

type substitution = (variable * term) list 
;;

let rec is_repeat x l = match l with
	[]-> false
	|(a,n)::xs -> if (x=a) then true else (is_repeat x xs) ;;
;;

let rec check_sig l = match l with 
		[] -> true 
		| ((x,n)::xs)->if n<0 then false else (if (is_repeat x xs) then false else (check_sig xs)) 
;;

let rec arity x l = match l with 
	[]-> -1
	| (a,n)::xs	-> if (x=a) then n else arity x xs
;;

let do_and a b= a && b
;;

let rec wfterm sign t = match t with
		V(x)-> true
		| Node(a,l) -> if (List.length l != arity a sign) then false else (List.fold_left do_and true (List.map (wfterm sign) l))
;;

let max a b=if a>b then a else b
;;

let rec ht t=match t with
		V(x)->0
		|Node(a,l) -> 1+ (List.fold_left max 0 (List.map ht l))
;;

let plus a b = a+b ;;

let rec size t = match t with
		V(x) -> 0
		| Node(a,l) -> 1 + (List.fold_left plus 0 (List.map size l)) 
;;		

let rec union l1 l2= match l1 with
	[]->l2
	| x::xs-> if (List.mem x l2) then union xs l2 else union xs (x::l2)
;;	

let rec vars t = match t with
		V(x)->[x]
		| Node(a,l) -> List.fold_left union [] (List.map vars l)
;;

let rec find l x = match l with
	[]->V(x)
	|(x1,t1)::xs-> if (x=x1) then t1 else find xs x
;;	

let rec sub s t = match t with
		V(x)-> find s x
		| Node(a,[])->t
		| Node(a,l)-> Node(a, (List.map (sub s) l))
;;

let rec comph s1 s2 l = match s2 with
	[] -> l
	| (x,t)::xs -> comph s1 xs ((x,sub s1 t)::l)
;;

let rec present x s=match s with
	[]->false
	| (x1,t)::xs -> if (x=x1) then true else present x xs

let rec comph1 s1 s2 l=match s1 with
	[] -> l
	| (x,t)::xs -> if (present x s2) then (comph1 xs s2 l) else (comph1 xs s2 ((x,t)::l))

let rec comp s1 s2 = (comph1 s1 s2 [])@(comph s1 s2 [])
;;

let rec mguh t1 t2 l = if (List.length (vars t1))=0 && (List.length (vars t2))=0 then (if (t1==t2) then l else raise NOT_UNIFIABLE ) else
		 		match (t1,t2) with 
					  (V(x), V(y)) -> if (x=y) then l else (x,t2)::l
					| (V(x), Node(a,l1)) -> if (List.mem x (vars t2)) then raise NOT_UNIFIABLE
												   			else (x,t2)::l
					| (Node(a,l1), V(x)) -> if (List.mem x (vars t1)) then raise NOT_UNIFIABLE
												   			else (x,t1)::l
					| (Node(a1,l1), Node(a2,l2)) -> if (String.equal a1 a2)==false then raise NOT_UNIFIABLE else if (List.length l1 != List.length l2) then raise NOT_UNIFIABLE 
														else let rec unify l11 l22 ll = match l11,l22 with
																					  ([],[]) -> ll
																					| (x,[]) -> ll
																					| ([],x) -> ll
																					| (x::xs,y::ys) -> let a = (mguh x y ll) in (unify (List.map (sub a) xs) (List.map (sub a) ys) a)
														in unify l1 l2 l
;;

let mgu t1 t2 = mguh t1 t2 [];;


(* module SL = Set.Make(String);;
module SC = Set.Make(SL);;

let s1=SC.empty;;
 *)
(* type prop = None | F of string * (prop list)
;;
type term = V of variable | Node of symbol * (term list)
;; *)
type literal = bool * term (* prop *)
;;
type clause = (literal list)
;;
type soc = (clause list)
;;

let can_unify a b= try (List.length (mgu a b)) with NOT_UNIFIABLE-> -1
;;

let rec get_clauses s1 = match s1 with
	[]->raise Noclauses
	|x::xs-> (match xs with []-> get_clauses xs
						|y::ys-> (match x with []-> get_clauses xs
											|x1::xs1-> (match y with []-> get_clauses ys
											|y1::ys1-> (match x1 with (a1,b1)-> (match y1 with (a2,b2) -> if (a1!=a2) && (b1=b2) && ((can_unify b1 b2) !=-1) then (x,y) else get_clauses ys )))))
;;	

let rec get_clause_literal s1 = match s1 with
	[]->raise Noclauses
	|x::xs-> (match xs with []-> get_clause_literal xs
						|y::ys-> (match x with []-> get_clause_literal xs
											|x1::xs1-> (match y with []-> get_clause_literal ys
											|y1::ys1-> (match x1 with (a1,b1)-> (match y1 with (a2,b2) -> if (a1!=a2) && (b1=b2) && ((can_unify b1 b2) != -1) then (x,y,x1,y1) else get_clause_literal ys )))))
;;

let rec osr_helper c1 l1 s l= match c1 with
	[]-> l
	|x::xs-> if (x=l1) then (osr_helper xs l1 s l) else match x with (a,b)-> let y=(sub s b) in osr_helper xs l1 s ((a,y)::l)
;;

let one_step_res c1 c2 l1 l2= match l1 with (a1,b1)-> (match l2 with (a2,b2)-> let s = try mgu b1 b2 with NOT_UNIFIABLE->raise NOT_UNIFIABLE in 
	(union (osr_helper c1 l1 s []) (osr_helper c2 l2 s [])) )
;;

let rec remove l a =
  match l with
  [] -> []
  | x::xs -> if a=x then xs else x::(remove xs a)
;;

let rec res s1 = if s1=[] then false else let temp = try get_clause_literal s1 with Noclauses->raise (Notermination "no clauses") in 
				match temp with (c1,c2,l1,l2) -> let temp1=(try (one_step_res c1 c2 l1 l2) with NOT_UNIFIABLE-> raise (Notermination "not unifiable")) in 
					(match temp1 with []->true 
									|_->(res (temp1::(remove (remove s1 c1) c2))) )
;;



