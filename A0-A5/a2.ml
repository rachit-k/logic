exception NotFound;;
exception Illformed;;

type prop = T | F | L of string 
                  | Not of prop
                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
;;

type letter = K | S | R | Ass | MP
;;
type gamma = Nothingg | N of prop * gamma
;;
type hprooftree = Nothing | Root of prop * hprooftree * hprooftree * letter * gamma
;;

let rec findp gamma pp=match gamma with
	Nothingg->false
	|N(p,t)->if p=pp then true else findp t pp
;;

let rec valid_hprooftree tree = match tree with
		Nothing-> true
		| Root(p,l,r,x,t)-> match x with
					MP-> ( match l with 
						Nothing-> false
						|Root(p1,l1,r1,x1,t1)-> if t1!=t then false else  (match r with Nothing->false
																						|Root(p2,l2,r2,x2,t2)-> if t2!=t then false else (match p1 with Impl(p3,p)-> if p2=p3 then (valid_hprooftree l)&&(valid_hprooftree r) else false
											 																											|_-> false (*match p2 with Impl(p1,p) -> (valid_hprooftree l)&&(valid_hprooftree r)
																																											|_->false*) ) ) )
					|Ass->( match l with 
						Nothing-> (match r with Nothing-> (findp t p)
												|_-> false)
						|_-> false )
					|K-> ( match l with 
						Nothing-> (match r with Nothing-> (match p with Impl(p1,Impl(p2,p3))->if p1=p3 then true else false
																		|_->false)
												|_-> false)
						|_-> false )
					|S-> ( match l with 
						Nothing-> (match r with Nothing-> (match p with Impl(Impl(p1,Impl(p2,p3)),Impl(Impl(p4,p5),Impl(p6,p7)))-> if (p1=p4)&&(p1=p6)&&(p2=p5)&&(p3=p7) then true else false
																		|_->false)
												|_-> false)
						|_-> false )
					|R-> ( match l with 
						Nothing-> (match r with Nothing-> (match p with Impl(Impl(Not p1,Not p2),Impl(Impl(Not p3,Not p4),p5))-> if (p1=p3)&&(p1=p5)&&(p2=p4) then true else false
																		|_->false)
												|_-> false)
						|_-> false )
;;

let rec padh tree pp= match tree with
		Nothing-> tree
		|Root(p,l,r,x,t)-> let l1=padh l pp in let r1=padh r pp in let t1=N(pp,t) in Root(p,l1,r1,x,t1)
;;

let rec pad tree del = match del with
		Nothingg-> tree
		|N(p,del1)-> pad (padh tree p) del1
;;

let rec delunion del1 del2= match del2 with
		Nothingg-> del1
		|N(p,del3)-> delunion (N(p,del1)) del3
;;

let rec pruneh tree del= match tree with
		Nothing->del
		| Root(p,l,r,x,t)-> match x with
						Ass-> N(p, del)
						|_-> delunion (pruneh l del) (pruneh r del)
;;

let rec prunehh tree del=match tree with
		Nothing->tree
		| Root(p,l,r,x,t)->let l1=prunehh l del in (let r1=prunehh r del in Root(p,l1,r1,x,del))
;;

let prune tree = let del=(pruneh tree Nothingg) in 
				(prunehh tree del)
;;

let rec graftfind li pp=match li with
		[]-> raise NotFound
		|x1::xs-> match x1 with 
				Nothing->graftfind xs pp
				| Root(p,l,r,x,t)-> if p=pp then x1 else graftfind xs pp

;;				

let rec getgamma li =match li with 
	[]->raise NotFound
	|x1::xs->match x1 with
			Nothing-> getgamma xs
			|Root(p,l,r,x,t)->t
;;				

let rec graft tree li = let gammaa=getgamma li in match tree with
		Nothing->tree
		| Root(p,l,r,x,t)-> (match l with Nothing-> (match r with Nothing-> (match x with Ass-> (graftfind li p)
																						|_->Root(p,l,r,x,gammaa) )
																|Root(p1,l1,r1,x1,t1)-> (match x1 with Ass-> let z=(graftfind li p1) in Root(p,l,z,x,gammaa)
																										|_-> let z=(graft r li) in Root(p,l,z,x,gammaa) ) )
										| Root(p1,l1,r1,x1,t1)-> (match x1 with Ass-> let y=(graftfind li p1) in (match r with Nothing->Root(p,y,r,x,gammaa) 
																															|Root(p2,l2,r2,x2,t2)-> (match x2 with Ass-> let z=(graftfind li p2) in Root(p,y,z,x,gammaa)
																																								|_->let z=(graft r li) in Root(p,y,z,x,gammaa) ) )
																				|_-> let y=(graft l li) in (match r with Nothing->Root(p,y,r,x,t) 
																														|Root(p2,l2,r2,x2,t2)-> (match x2 with Ass-> let z=(graftfind li p2) in Root(p,y,z,x,gammaa)
																																								|_->let z=(graft r li) in Root(p,y,z,x,gammaa) ) ) ) )
;;

let rec remproph del pp=match del with
	Nothingg-> Nothingg (* change here *)
	|N(p,t)->if p=pp then t else let tt=remproph t pp in N(p,tt)
;;	

let rec remprop tree pp=match tree with
		Nothing->tree
		|Root(p,l,r,x,t)-> (let y=remprop l pp in (let z=remprop r pp in (let t1=remproph t pp in Root(p,y,z,x,t1) )))
;;		

let rec dedthm tree pp= let tree1 = (remprop tree pp) in (match tree1 with
		Nothing->raise Illformed
		|Root(p,l,r,x,t)-> (if (p!=pp) then (match l with Nothing-> (match x with Ass-> (Root(Impl(p,pp),l,r,x,t))
																			|_-> raise Illformed )
													|Root(p1,l1,r1,x1,t1)-> (match r with Nothing->raise Illformed
																						|Root(p2,l2,r2,x2,t2)-> let r_dash= dedthm (Root(p2,l2,r2,x2,t2)) pp in let l_dash=dedthm (Root(p1,l1,r1,x1,t1)) pp in 
																												let temp=Root(Impl(Impl(pp,p1),Impl(Impl(pp,p2),Impl(pp,p))),Nothing,Nothing,S,t) in 
																												let l_ddash=Root(Impl(Impl(pp,p2),Impl(pp,p)),temp,l_dash,MP,t) in
																												Root(Impl(pp,p),l_ddash,r_dash,MP,t) )) 
							 else (let r_dash=Root(Impl(pp,Impl(T,pp)),Nothing,Nothing,K,t) in let l_ldash=Root(Impl(Impl(pp,Impl(Impl(T,pp),pp)),Impl(Impl(pp,Impl(T,pp)),Impl(pp,pp))),Nothing,Nothing,S,t) in
									let l_rdash= Root(Impl(pp,Impl(Impl(T,pp),pp)),Nothing,Nothing,K,t) in let l_dash=Root(Impl(Impl(pp,Impl(T,pp)),Impl(pp,pp)),l_ldash,l_rdash,MP,t) in
									Root(Impl(pp,pp),l_dash,r_dash,MP,t) )	)	)											
;;

(* taken left to be left part of MP only(not interchangable) *)

