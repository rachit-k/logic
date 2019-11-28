exception Exception;;
exception Normalised;;

type prop = T | F | L of string 
                  | Not of prop
                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop
;;

type letter = TI | Hyp | ImpI | ImpE | AndI | AndEl | AndEr | OrIl | OrIr | OrE | NotI | NotClass
;;
type gamma = Nothingg | N of prop * gamma
;;
type ndprooftree = Nothing | Root of prop * ndprooftree * ndprooftree * ndprooftree * letter * gamma
;;

let rec find_rpair tree = match tree with
	Nothing-> raise Normalised
	| Root(p,l,m,r,x,t)-> if x=ImpE then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=ImpI then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2||t2=N(p,t)) then tree else (try find_rpair l with Normalised-> (try find_rpair m with Normalised -> raise Normalised ) )
																												|_-> raise Normalised )
																				else (try find_rpair l with Normalised-> (try find_rpair m with Normalised -> (try find_rpair r with Normalised -> raise Normalised ) ) )
														|_-> raise Normalised )				
						else if x=AndEl then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=AndI then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then tree else (try find_rpair l with Normalised-> (try find_rpair m1 with Normalised -> raise Normalised ) )
																												|_-> raise Normalised )
																					else (try find_rpair l with Normalised-> (try find_rpair m with Normalised -> (try find_rpair r with Normalised -> raise Normalised ) ) )
														|_-> raise Normalised )	
						else if x=AndEr then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=AndI then (match m1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then tree else (try find_rpair l with Normalised-> (try find_rpair m1 with Normalised -> raise Normalised ) )
																												|_-> raise Normalised )
																					else (try find_rpair l with Normalised-> (try find_rpair m with Normalised -> (try find_rpair r with Normalised -> raise Normalised ) ) )
														|_-> raise Normalised ) 
						else if x=OrE then (match l with Root(p1,l1,m1,r1,x1,t1)-> if (x1=OrIl)||(x1=OrIr) then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then tree else (try find_rpair l with Normalised-> (try find_rpair m with Normalised -> (try find_rpair r with Normalised -> raise Normalised ) ) )
																												|_-> raise Normalised )
																					else (try find_rpair l with Normalised-> (try find_rpair m with Normalised -> (try find_rpair r with Normalised -> raise Normalised ) ) )
														|_-> raise Normalised )
						else (try find_rpair l with Normalised-> (try find_rpair m with Normalised -> (try find_rpair r with Normalised -> raise Normalised ) ) )
;;

let simplify1 tree = match tree with
	Nothing-> raise Exception
	| Root(p,l,m,r,x,t)-> if x=ImpE then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=ImpI then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2||t2=N(p,t)) then l1 else raise Exception
																												|_-> raise Exception )
																				else raise Exception
														|_-> raise Exception )				
						else if x=AndEl then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=AndI then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then l1 else raise Exception
																												|_-> raise Normalised )
																					else raise Exception
														|_-> raise Exception )	
						else if x=AndEr then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=AndI then (match m1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then m1 else raise Exception
																												|_-> raise Normalised )
																					else raise Exception
														|_-> raise Exception ) 
						else if x=OrE then (match l with Root(p1,l1,m1,r1,x1,t1)-> if (x1=OrIl)||(x1=OrIr) then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then l1 else raise Exception
																												|_-> raise Exception )
																					else raise Exception
														|_-> raise Exception )
						else raise Exception
;;

let rec normalise tree = match tree with
	Nothing-> tree
	| Root(p,l,m,r,x,t)-> if x=ImpE then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=ImpI then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2||t2=N(p,t)) then normalise l1 else (let ll= normalise l in (let mm= normalise m in Root(p,ll,mm,r,x,t) ) )
																												|_-> tree )
																				else (let ll= normalise l in (let mm= normalise m in (let rr=normalise r in Root(p,ll,mm,rr,x,t) ) ) )
														|_-> tree )				
						else if x=AndEl then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=AndI then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then normalise l1 else (let ll= normalise l in (let mm= normalise m in Root(p,ll,mm,r,x,t) ) )
																												|_-> tree )
																					else (let ll= normalise l in (let mm= normalise m in (let rr=normalise r in Root(p,ll,mm,rr,x,t) ) ) )
														|_-> tree )	
						else if x=AndEr then (match l with Root(p1,l1,m1,r1,x1,t1)-> if x1=AndI then (match m1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then normalise m1 else (let ll= normalise l in (let mm= normalise m in Root(p,ll,mm,r,x,t) ) )
																												|_-> tree )
																					else (let ll= normalise l in (let mm= normalise m in (let rr=normalise r in Root(p,ll,mm,rr,x,t) ) ) )
														|_-> tree ) 
						else if x=OrE then (match l with Root(p1,l1,m1,r1,x1,t1)-> if (x1=OrIl)||(x1=OrIr) then (match l1 with Root(p2,l2,m2,r2,x2,t2)-> if (p=p2)&&(t=t2) then normalise l1 else (let ll= normalise l in (let mm= normalise m in (let rr=normalise r in Root(p,ll,mm,rr,x,t) ) ) )
																												|_-> raise Normalised )
																					else (let ll= normalise l in (let mm= normalise m in (let rr=normalise r in Root(p,ll,mm,rr,x,t) ) ) )
														|_-> tree )
						else (let ll= normalise l in (let mm= normalise m in (let rr=normalise r in Root(p,ll,mm,rr,x,t) ) ) )
;;



