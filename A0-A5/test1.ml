(* A0 *)
let p1= And(Or(L("p"),T),Impl(L("p"),L("q")));;
let p2= Or(L("s"), Not(Or(T, And(L("s"),L("r")))));;
let p3= Iff((Or(Or(L("p"),L("q")),T)),(And(T,Impl(L("p"),L("q")))));;
let p4= Iff((Or(Or(L("p"),L("q")),Impl(L("q"),L("q")))),(And(Or(T,T),Impl(L("p"),L("q")))));;
let p13=And(Or(Not T, L("a")),T);;


let p5= And(Or(L("p"),F),Impl(L("r"),L("q")));;
let p6= Or(L("r"), Not(Or(L("q"), And(L("s"),L("r")))));;
let p7= Iff((Or(Or(F,L("q")),T)),(And(T,Impl(L("p"),T))));;
let p8= (Iff((Or(Or(L("p"),F),Impl(L("q"),L("q")))),(And(Or(L("q"),L("p")),Impl(L("p"),L("q"))))));;

let p9= And(Or(T,L("r")),Impl(L("s"),L("q")));;
let p10= Or(T, Not(Or(L("q"), And(L("s"),F))));;
let p11= Iff((Or(Or(L("p"),F),T)),(And(T,Impl(F,L("q")))));;
let p12= (Iff((Or(Or(L("p"),L("r")),Impl(L("r"),T))),(And(Or(L("q"),L("r")),Impl(T,L("q"))))));;

let rho s=match s with
	"p"-> true
	|"q"-> true
	|"r"-> false
	|"s"-> false
	|_-> raise DontCare
;;

ht p1;;
size p1;;
letters p1;;
subprop_at (Impl(L("p"),L("q"))) p1;;

(truth (cnf p1) rho)=(truth (dnf p1) rho);;
(truth (cnf p2) rho)=(truth (dnf p2) rho);;
(truth (cnf p3) rho)=(truth (dnf p3) rho);;
(truth (cnf p4) rho)=(truth (dnf p4) rho);;



(* A2 *)

let gamm=N((Impl (Impl (T, L "s"), And (T, Impl (T, L "s")))),N((Impl (T, L "s")),N((And (T, Impl (T, L "s"))),Nothingg)))
;;
(* let gamm=N((Impl (Impl (T, L "s"), And (T, Impl (T, L "s")))),N((Impl (T, L "s")),Nothingg))
;;
 *)
let htree1=Root((Impl (Impl (T, L "s"), And (T, Impl (T, L "s")))), Nothing , Nothing , Ass, gamm )
;;

let htree2=Root((Impl (T, L "s")) , Nothing , Nothing , Ass, gamm)
;;

let htree= Root((And (T, Impl (T, L "s"))) , htree1 , htree2 , MP, gamm ) 
;;

(* pad/prune *)
let del=N(T,N(And(L("x"), F),Nothingg))
;;
pad htree del ;;

prune (pad htree del);;

(* graft *)
(* no change *)
let treegraft1=Root(And (T, Impl (T, L "s")), Nothing , Nothing , Ass, N((And (T, Impl (T, L "s"))),Nothingg) )
;;

graft treegraft1 [htree] ;;

(* dedn *)

let p=(And (T, Impl (T, L "s")))
;;

dedthm htree p
;;

(* A3 *)

let gam1=N((L "x"),N(L "y",Nothingg))
let ntree1=Root(L "x", Nothing , Nothing , Nothing ,Hyp,gam1)
;;
valid_ndprooftree ntree1;;

let del =N((And(L("x"), L("y"))),N(And(T, F),Nothingg));;

pad ntree1 del;;
prune ntree1;;

let gam=N(L "p",N(Or (L "p", L "q"),N((L "x"),N(L "y",Nothingg))))
;;
let ntree2=Root( (Or (L "p", L "q")) , Nothing , Nothing , Nothing ,Hyp, gam)
;;
let ntree3=Root(L "p",  Nothing , Nothing , Nothing ,Hyp, gam);;
;;
let ntree=Root( (Or (L "p", L "q")) ,ntree3, Nothing , Nothing ,OrIl , gam)
;;
pad ntree del;;
prune (pad ntree del);;
prune ntree ;;
graft ntree2 [ntree] ;;

(* A4 *)

let gamm=N(L "p",N(L "q",Nothingg))
;;

let ntree11=Root(L "p",  Nothing , Nothing , Nothing ,Hyp, gamm)
;;
let ntree12=Root(L "q",  Nothing , Nothing , Nothing ,Hyp, gamm)
;;
let ntree1=Root(And (L "p", L "q"),ntree11,ntree12,Nothing ,AndI,gamm)
;;
let ntree=Root(L "p", ntree1, Nothing , Nothing ,AndEl,gamm)
;;

find_rpair ntree
;;
simplify1 ntree
;;

let ntree0=Root(Or (L "p", L "q"),ntree,Nothing , Nothing ,OrIl,gamm)
;;
find_rpair ntree0
;;
normalise ntree0
;;



let ntree111=Root(F,  Nothing , Nothing , Nothing ,Hyp, N(L "p",N(F,Nothingg)))
;;
let ntree11=Root(L "q",  ntree111 , Nothing , Nothing ,NotI, N(L "p",N(F,Nothingg)))
;;

let ntree1=Root(Impl (L "p", L "q"),ntree11,Nothing,Nothing ,ImpI,N(F,Nothingg))
;;

let ntree22=Root(F,  Nothing , Nothing , Nothing ,Hyp, N(F,Nothingg))
;;
let ntree2=Root(L "p",  ntree22 , Nothing , Nothing ,NotI, N(F,Nothingg))
;;

let ntree=Root(L "q",  ntree1 , ntree2 , Nothing ,ImpE, N(F,Nothingg))
;;




(* A5 *)

#use "a5.ml";;

let sig1 = [("X",0);("Y",0);("f",1);("g",2);("h",3);("*",2)];;
let sig2 = [("X",0);("Y",0);("Z",0);("f",1);("g",2);("f",3);("*",2)];;
let sig3 = [("f",1)];;
let sig4 = [("X",0);("Y",0);("Z",0)];;

let term1 = (Node ("f",[V "x"]));;
let term2=(V "x");;

let term3=(Node ("f",[V "x";Node("g",[V "y"])]));;
let term4=(Node ("f",[V "y";Node("g",[Node("h",[V "z"] )] )] ) );;


let term2 = (Node ("g",[V "X";Node("h",[Node("f",[V "X"]);V "Y"])]));;
let term3 = (Node ("g",[V "X";Node("*",[V "Y";Node ("*",[V "X";V "Y"])])]));;
let term4 = (Node ("g",[V "X";Node("*",[V "Y";V "X"])]));;
let term5 = (Node ("g",[V "Z";Node("*",[V "X";V "Z"])]));;
let term6 = (Node ("g",[V "Z";Node("g",[V "X";V "Z"])]));;
let term7 = (V "X");;
let term8 = (Node ("K",[]));;
let term9 = (Node ("X",[]));;
let term10 = (Node ("g",[V "X";Node("h",[Node("f",[V "X"]);V "Y";Node ("X",[])])]));;
let term11 = (Node ("g",[V "X";Node("h",[Node("f",[V "X"]);V "Y";Node ("f",[V "X"])])]));;
let term12 = (Node ("g",[V "Z";Node("*",[V "Z";Node ("*",[V "X";V "Y"])])]));;

(check_sig sig1);;
(check_sig sig2);;
(check_sig sig3);;
(check_sig sig4);;

(wfterm sig1 term1);;
(wfterm sig1 term2);;
(wfterm sig4 term7);;
(wfterm sig4 term8);;
(wfterm sig4 term9);;

(ht term9);;
(ht term7);;
(ht term4);;
(ht term10);;
(ht term11);;

(size term9);;
(size term7);;
(size term4);;
(size term10);;
(size term11);;

(vars term9);; 
(vars term7);; 
(vars term4);; 
(vars term10);; 
(vars term11);; 

(mgu term14 term13);; 
(mgu term3 term12);; 
(mgu term12 term3);; 

(sub (mgu term3 term12) term12);; 
(sub (mgu term12 term3) term3);; 
(sub (mgu term12 term3) term12);; 
(sub (mgu term12 term3) term3);; 


let literal1=(true,V "X");;
let literal2=(true,V "Y");;
let literal3=(false,V "X");;
let literal4=(true,V "Z");;
let literal5=(true,V "x");;
let literal6=(true,V "y");;
let literal7=(true,V "z");;
let literal8=(false,V "z");;

let literal9=(false,term1);;
let literal10=(true,term1);;
let literal11=(false,term3);;
let literal12=(true,term3);;


let clause1=[literal1;literal2];;
let clause2=[literal3;literal4;literal8];;
let clause3=[literal5;literal6;literal7];;
let clause4=[literal9;literal11];;
let clause5=[literal10;literal12;literal8];;
let clause6=[literal7];;

let clause7=[(false, Node ("f", [V "X"])); (false, V "z"); (true, Node ("f", [V "X"]))]

let soc1=[clause1;clause2;clause3];;
let soc2=[clause1;clause2];;
let soc3=[clause4;clause5;clause3];;
let soc4=[clause4;clause6];;

let soc5=[clause4;clause5;clause6];;
let soc6=[clause4;clause5;clause6;clause7];;

get_clauses soc1;;

get_clauses soc3;;

one_step_res clause1 clause2 literal1 literal3;;
one_step_res clause4 clause2 literal1 literal3;;

one_step_res clause4 clause5 literal9 literal10;;
one_step_res clause4 clause5 literal11 literal12;;

res soc2;;








