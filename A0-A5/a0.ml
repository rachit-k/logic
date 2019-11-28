
exception Notimplemented;;

exception DontCare;;

exception NotSubProp;;
type prop = T | F | L of string 
                  | Not of prop
                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
;;

let rec ht p= match p with 
			T ->0| F -> 0| L s-> 0
			| Not p1 -> 1+ (ht p1)
			| And(p1,p2) -> if (ht p1)>(ht p2) then 1+ (ht p1) else 1+(ht p2)
			| Or(p1,p2) -> if (ht p1)>(ht p2) then 1+ (ht p1) else 1+(ht p2)
			| Impl(p1,p2) -> if (ht p1)>(ht p2) then 1+ (ht p1) else 1+(ht p2)
			| Iff(p1,p2) -> if (ht p1)>(ht p2) then 1+ (ht p1) else 1+(ht p2)  
;;

let rec size p= match p with 	
			T ->1 | F -> 1 | L s->1
			| Not p1 -> 1+ (size p1)
			| And(p1,p2) -> 1+ (size p1) +(size p2)
			| Or(p1,p2) -> 1+ (size p1) +(size p2)
			| Impl(p1,p2) -> 1+ (size p1) +(size p2)
			| Iff(p1,p2) ->	1+ (size p1) +(size p2)
;;

let rec union l1 l2 =match l1 with
		[]-> l2
		|x::xs-> if (List.mem x l2) then union xs l2 else [x]@(union xs l2)
;;		 

let rec letters p=match p with 
			| T ->[] | F -> [] | L s->[s]
			| Not p1 -> letters p1
			| And(p1,p2) -> union (letters p1) (letters p2)
			| Or(p1,p2) -> union (letters p1) (letters p2)
			| Impl(p1,p2) -> union (letters p1) (letters p2)
			| Iff(p1,p2) ->	union (letters p1) (letters p2)
;;

let rec subprop_help p1 p2 l=match p2 with
			T-> (if p1=T then l else raise NotSubProp)
			| F-> (if p1=F then l else raise NotSubProp)
			| L s -> (if p1=(L s) then l else raise NotSubProp)
			| Not q-> if p1=q then l else (try (subprop_help p1 q l@[2]) with NotSubProp -> raise NotSubProp)
			| And(q1,q2)-> if p1=q1 then l@[0] else if p1=q2 then l@[1] else (try (subprop_help p1 q1 l@[0]) with NotSubProp-> (try (subprop_help p1 q2 l@[1]) with NotSubProp-> raise NotSubProp))
			| Or(q1,q2)-> if p1=q1 then l@[0] else if p1=q2 then l@[1] else (try (subprop_help p1 q1 l@[0]) with NotSubProp-> (try (subprop_help p1 q2 l@[1]) with NotSubProp-> raise NotSubProp))
			| Impl(q1,q2)-> if p1=q1 then l@[0] else if p1=q2 then l@[1] else (try (subprop_help p1 q1 l@[0]) with NotSubProp-> (try (subprop_help p1 q2 l@[1]) with NotSubProp-> raise NotSubProp))
			| Iff(q1,q2)-> if p1=q1 then l@[0] else if p1=q2 then l@[1] else (try (subprop_help p1 q1 l@[0]) with NotSubProp-> (try (subprop_help p1 q2 l@[1]) with NotSubProp-> raise NotSubProp))
;;			

let rec subprop_at p1 p2= (try List.rev(subprop_help p1 p2 []) with NotSubProp-> raise NotSubProp)
;;

let rec truth p rho = match p with 
		T-> true
		| F-> false
		| L s -> (try rho s with DontCare-> raise DontCare)
		| Not p1 -> not (truth p1 rho)
		| And(p1,p2) -> (truth p1 rho) && (truth p2 rho)
		| Or(p1,p2) -> (truth p1 rho) || (truth p2 rho)	  
		| Impl(p1,p2) -> (not (truth p1 rho)) || (truth p2 rho)	
		| Iff(p1,p2) -> ((not (truth p1 rho)) || (truth p2 rho)) && ((not (truth p2 rho)) || (truth p1 rho))
;;

let rec nnf_help p = match p with
		 T-> p | F-> p | L s -> p
		| Not T -> F
		| Not F -> T
		| Not L s -> p		
		| Not Not p1 -> nnf_help p1
		| Not And(p1, p2) -> Or(nnf_help (Not p1),nnf_help (Not p2))
	    | Not Or(p1, p2) -> And(nnf_help (Not p1),nnf_help (Not p2))
	    | And(p1,p2) -> And(nnf_help p1, nnf_help p2)
		| Or(p1,p2) -> Or(nnf_help p1, nnf_help p2)
;;

let rec rem p=match p with
		 T-> p | F-> p | L s -> p
		| Not T -> F
		| Not F -> T
		| Not p -> Not (rem p)
		| And(p1,p2) -> And(rem p1, rem p2)
		| Or(p1,p2) -> Or(rem p1, rem p2)
		| Impl(p1,p2) -> Or(rem (Not (p1)),rem p2)
		| Iff(p1,p2) -> And(Or(rem (Not (p1)),rem p2),Or(rem (Not (p2)),rem p1))
;;

let nnf p=nnf_help (rem p);;


let rec nnf_to_cnf p= match p with
		T-> p | F-> p | L s -> p 
		| Not T -> F
		| Not F -> T
		| Not (L s)-> p
		| And(p1,p2)-> And(nnf_to_cnf p1, nnf_to_cnf p2)
		| Or(And(p1,p2),And(p3,p4))-> And(And(nnf_to_cnf (Or(p1, p3)),nnf_to_cnf (Or(p1, p4))), And(nnf_to_cnf (Or(p2, p3)), nnf_to_cnf (Or(p2, p4))))		
  		| Or(And(p2, p3), p1) -> And(nnf_to_cnf (Or(p1, p2)),nnf_to_cnf (Or(p1, p3)))
  		| Or(p1, And(p2, p3)) -> And(nnf_to_cnf (Or(p1, p2)),nnf_to_cnf (Or(p1, p3)))
		| Or(p1,p2)-> Or(nnf_to_cnf p1, nnf_to_cnf p2)
;;

let rec nnf_to_dnf p= match p with 
		T-> p | F-> p | L s -> p 
		| Not T -> F
		| Not F -> T
		| Not p1-> Not (nnf_to_dnf p1)
		| Or(p1,p2)-> Or(nnf_to_dnf p1, nnf_to_dnf p2)
		| And(Or(p1,p2),Or(p3,p4))-> Or(Or(nnf_to_dnf (And(p1, p3)),nnf_to_dnf (And(p1, p4))), Or(nnf_to_dnf (And(p2, p3)),nnf_to_dnf (And(p2, p4))))
		| And(Or(p1,p2),p3)-> Or(nnf_to_dnf (And(p1, p2)),nnf_to_dnf (And(p1, p3)))
		| And(p1,Or(p2,p3))-> Or(nnf_to_dnf (And(p1, p2)),nnf_to_dnf (And(p1, p3)))
		| And(p1,p2)-> And(nnf_to_dnf p1, nnf_to_dnf p2)		
;;

let cnf1 p=nnf_to_cnf (nnf p)
;;
let dnf1 p=nnf_to_dnf (nnf p)
;; 

let rec cnf p= let x= (cnf1 p) in if x=(cnf1 x) then x else cnf x
;;
let rec dnf p= let x= (dnf1 p) in if x=(dnf1 x) then x else dnf x
;;


let rho s=match s with
	"p"-> true
	|"q"-> true
	|"r"-> false
	|"s"-> false
	|_-> raise DontCare
;;


let f1= And(Or(L("p"),T),Impl(L("p"),L("q")));;
let f2= Or(L("s"), Not(Or(T, And(L("s"),L("r")))));;
let f3= Iff((Or(Or(L("p"),L("q")),T)),(And(T,Impl(L("p"),L("q")))));;
let f4= Iff((Or(Or(L("p"),L("q")),Impl(L("q"),L("q")))),(And(Or(T,T),Impl(L("p"),L("q")))));;
let f13=And(Or(Not T, L("a")),T);;


let f5= And(Or(L("p"),F),Impl(L("r"),L("q")));;
let f6= Or(L("r"), Not(Or(L("q"), And(L("s"),L("r")))));;
let f7= Iff((Or(Or(F,L("q")),T)),(And(T,Impl(L("p"),T))));;
let f8= (Iff((Or(Or(L("p"),F),Impl(L("q"),L("q")))),(And(Or(L("q"),L("p")),Impl(L("p"),L("q"))))));;

let f9= And(Or(T,L("r")),Impl(L("s"),L("q")));;
let f10= Or(T, Not(Or(L("q"), And(L("s"),F))));;
let f11= Iff((Or(Or(L("p"),F),T)),(And(T,Impl(F,L("q")))));;
let f12= (Iff((Or(Or(L("p"),L("r")),Impl(L("r"),T))),(And(Or(L("q"),L("r")),Impl(T,L("q"))))));;

