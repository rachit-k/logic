exception NotFound;;
exception Illformed;;

type prop = T | F | L of string 
                  | Not of prop
                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
;;

type letter = TI | Hyp | ImpI | ImpE | AndI | AndEl | AndEr | OrIl | OrIr | OrE | NotI | NotClass
;;
type gamma = Nothingg | N of prop * gamma
;;
type ndprooftree = Nothing | Root of prop * ndprooftree * ndprooftree * ndprooftree * letter * gamma
;;

let rec findp gamma pp=match gamma with
	Nothingg->false
	|N(p,t)->if p=pp then true else findp t pp
;;	

let rec valid_ndprooftree tree= match tree with
		Nothing->true
		| Root(p,l,m,r,x,t)->match x with
				  TI-> if (p!=T)||(l!=Nothing)||(m!=Nothing)||(r!=Nothing) then false else true
				| Hyp-> if (findp t p)!=true||(l!=Nothing)||(m!=Nothing)||(r!=Nothing) then false else true (* change here *)
				| ImpI-> if (m!=Nothing)||(r!=Nothing) then false else (match l with Nothing->false
																					|Root(p1,l1,m1,r1,x1,t1)-> (match p with Impl(q1,q2)-> if (p1!=q2)||(t1!=N(q1,t)) then false else true
																															|_->false ) )
				| ImpE-> if (r!=Nothing) then false else (match l with Nothing->false
																	|Root(p1,l1,m1,r1,x1,t1)-> (match m with Nothing->false
																											|Root(p2,l2,m2,r2,x2,t2)-> (match p1 with Impl(q1,q2)-> if (q1!=p2)||(p!=q2)||(t!=t1)||(t!=t2) then false else true
																																					|_->false ) ) )
				| AndI-> if (r!=Nothing) then false else (match l with Nothing->false
																	|Root(p1,l1,m1,r1,x1,t1)-> (match m with Nothing->false
																											|Root(p2,l2,m2,r2,x2,t2)-> (match p with And(q1,q2)-> if (q1!=p1)||(p2!=q2)||(t!=t1)||(t!=t2) then false else true
																																					|_->false ) ) )
				| AndEl-> if (r!=Nothing)||(m!=Nothing) then false else (match l with Nothing->false
																					|Root(p1,l1,m1,r1,x1,t1)-> (match p1 with And(q1,q2)-> if (q1!=p)||(t1!=t) then false else true
																															|_->false ) )
				| AndEr-> if (r!=Nothing)||(m!=Nothing) then false else (match l with Nothing->false
																					|Root(p1,l1,m1,r1,x1,t1)-> (match p1 with And(q1,q2)-> if (q2!=p)||(t1!=t) then false else true
																															|_->false ) )
				| OrIl-> if (r!=Nothing)||(m!=Nothing) then false else (match l with Nothing->false
																					|Root(p1,l1,m1,r1,x1,t1)-> (match p with Or(q1,q2)-> if (q1!=p1)||(t1!=t) then false else true
																															|_->false ) )
				| OrIr-> if (r!=Nothing)||(m!=Nothing) then false else (match l with Nothing->false
																					|Root(p1,l1,m1,r1,x1,t1)-> (match p with Or(q1,q2)-> if (q2!=p1)||(t1!=t) then false else true
																															|_->false ) )
				| OrE-> (match l with Nothing->false
									|Root(p1,l1,m1,r1,x1,t1)-> (match m with Nothing->false
																			|Root(p2,l2,m2,r2,x2,t2)-> (match r with Nothing->false
																													|Root(p3,l3,m3,r3,x3,t3)-> (match p1 with Or(q1,q2)-> if(p2!=p)||(p3!=p)||(t1!=t)||(t2!=N(q1,t))||(t3!=N(q2,t)) then false else true
																																							|_-> false ) ) ) )
				| NotI-> if (r!=Nothing)||(m!=Nothing) then false else (match l with Nothing->false
																					|Root(p1,l1,m1,r1,x1,t1)-> if (p1!=F)||(t1!=t) then false else true )
				| NotClass-> if (r!=Nothing)||(m!=Nothing) then false else (match l with Nothing->false
																					|Root(p1,l1,m1,r1,x1,t1)-> if(p1!=F)||(t1!=N(Not p,t)) then false else true )
;;

let rec padh tree pp= match tree with
		Nothing-> tree
		|Root(p,l,m,r,x,t)-> let l1=padh l pp in let m1=padh m pp in let r1=padh r pp in let t1=N(pp,t) in Root(p,l1,m1,r1,x,t1)
;;

let rec pad tree del= match del with
		Nothingg-> tree
		|N(p,del1)-> pad (padh tree p) del1
;;

let rec delunion del1 del2= match del2 with
		Nothingg-> del1
		|N(p,del3)-> delunion (N(p,del1)) del3
;;
(* finds/constructs del *)
let rec pruneh tree del= match tree with
		Nothing->del
		| Root(p,l,m,r,x,t)-> match x with
						Hyp-> N(p, del)
						|_-> delunion (pruneh l del) (pruneh r del)
;;
(* makes every gamma =del *)
let rec prunehh tree del=match tree with	
		Nothing->tree
		| Root(p,l,m,r,x,t)->let l1=prunehh l del in let m1=prunehh l del in let r1=prunehh r del in Root(p,l1,m1,r1,x,del)
;;

let prune tree = let del=(pruneh tree Nothingg) in 
				(prunehh tree del)
;;

let rec graftfind li pp=match li with
		[]-> raise NotFound
		|x1::xs-> match x1 with 
				Nothing->graftfind xs pp
				| Root(p,l,m,r,x,t)-> if p=pp then x1 else graftfind xs pp

;;				

let rec getgamma li =match li with 
	[]->raise NotFound
	|x1::xs->match x1 with
			Nothing-> getgamma xs
			|Root(p,l,m,r,x,t)->t
;;

let rec graft tree li = let gammaa=getgamma li in match tree with
		Nothing->tree
		| Root(p,l,m,r,x,t)-> (match l with Nothing->(match x with Hyp-> (graftfind li p)
																|_->Root(p,l,m,r,x,gammaa) )
											|Root(p1,l1,m1,r1,x1,t1)-> (match x1 with Hyp-> let y=(graftfind li p1) in (match m with Nothing->Root(p,y,m,r,x,gammaa) 
																																	|Root(p2,l2,m2,r2,x2,t2)-> (match x2 with Hyp-> let z=(graftfind li p2) in (match r with Nothing->Root(p,y,z,r,x,gammaa)
																																																						|Root(p3,l3,m3,r3,x3,t3)-> (match x3 with Hyp-> let zz=(graftfind li p3) in Root(p,y,z,zz,x,gammaa)
																																																																|_-> let zz=(graft r li) in  Root(p,y,z,zz,x,gammaa) ) )
																																											|_->let z=(graft m li) in (match r with Nothing->Root(p,y,z,r,x,gammaa)
																																																				|Root(p3,l3,m3,r3,x3,t3)-> (match x3 with Hyp-> let zz=(graftfind li p3) in Root(p,y,z,zz,x,gammaa)
																																																														|_-> let zz=(graft r li) in  Root(p,y,z,zz,x,gammaa) ) ) ) )
																					|_-> let y=(graft l li) in  (match m with Nothing->Root(p,y,m,r,x,gammaa) 
																															|Root(p2,l2,m2,r2,x2,t2)-> (match x2 with Hyp-> let z=(graftfind li p2) in (match r with Nothing->Root(p,y,z,r,x,gammaa)
																																																				|Root(p3,l3,m3,r3,x3,t3)-> (match x3 with Hyp-> let zz=(graftfind li p3) in Root(p,y,z,zz,x,gammaa)
																																																														|_-> let zz=(graft r li) in  Root(p,y,z,zz,x,gammaa) ) )
																																									|_->let z=(graft m li) in (match r with Nothing->Root(p,y,z,r,x,gammaa)
																																																		|Root(p3,l3,m3,r3,x3,t3)-> (match x3 with Hyp-> let zz=(graftfind li p3) in Root(p,y,z,zz,x,gammaa)
																																																												|_-> let zz=(graft r li) in  Root(p,y,z,zz,x,gammaa) ) ) ) ) ) )
;;

