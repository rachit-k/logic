
exception Notimplemented;;
exception DontCare;;
exception NotSubProp;;

type prop = T | F | L of string 
                  | Not of prop
                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
;;

type node = N of prop*bool*string* tableau* tableau

and  

 tableau = Nothing | Root of node
;;

(* 
let rec step_develop t=match t with
	nothing->t
	|Node e-> match e with
			(Not p,true)-> branch(t, step_develop(Node(p,false)))
			|(Not p,false)-> branch(t, step_develop(Node(p,true)))
			|(And(p1,p2),true)->branch(t,branch(step_develop(Node(p1,true)),step_develop(Node(p2,true))))
;; *)



let rec contrad_path_h tab rho c_l=match tab with
	Nothing-> c_l
	| Root(n)-> match n with
		(N(x,y, z,l,r)) -> match (x,y) with
						(T,false)-> [z]@c_l
						|(F,false)-> (contrad_path_h l rho c_l)
						|(F,true)-> [z]@c_l
						|(T,true)-> (contrad_path_h l rho c_l)
						|(L x,b)-> (try(if (rho x)!=b then [z]@c_l else (contrad_path_h l rho c_l)) with DontCare-> (contrad_path_h l rho c_l) )(* change about rho and include new x in dont DontCare *)
						|(Not(p1),b)-> contrad_path_h (Root(N(p1,not b,z,l,r))) rho c_l
						|(And(p1,p2),false)-> (contrad_path_h l rho [])@(contrad_path_h r rho [])@c_l
						|(Or(p1,p2),true)-> (contrad_path_h l rho [])@(contrad_path_h r rho [])@c_l
						|(And(p1,p2),true)-> (contrad_path_h l rho c_l)
						|(Or(p1,p2),false)-> (contrad_path_h l rho c_l)
						|(Iff(p1,p2),false)-> (contrad_path_h l rho c_l)
						|(Iff(p1,p2),true)-> (contrad_path_h l rho [])@(contrad_path_h r rho [])@c_l
;;

let contrad_path tab rho=contrad_path_h tab rho []
;;

let rec valid_tableau tab rho= let l= (contrad_path tab rho) in true
(* check for prefix of tab's root node in l  *)
		;;

let rec select_node tab = tab
;;

let rec find_assignments tab rho= let l= (contrad_path tab rho) in []
;;

let rec check_tautology p= p
;;

let check_contradiction p=p
;;


