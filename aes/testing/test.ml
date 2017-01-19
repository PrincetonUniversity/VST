open Printf
(*
let zeroWord = (((Z0,Z0),Z0),Z0) ;;

let zeroState = (((zeroWord,zeroWord),zeroWord),zeroWord) ;;
*)

let zeroWord = Pair(Pair(Pair(Z0,Z0),Z0),Z0) ;;

let zeroState = Pair(Pair(Pair(zeroWord,zeroWord),zeroWord),zeroWord) ;;

let rec repeat n p = match n with
  | 0 -> Nil
  | m ->  Cons (p, (repeat (m-1) p)) ;;

let exp_key0 = repeat 15 zeroState ;;

let rec pos_to_int p = match p with
  | XH -> 1
  | XI q -> 1 + (pos_to_int(q)*2)
  | XO q -> (pos_to_int(q)*2) ;;

let z_to_int z = match z with
  | Z0 -> 0
  | Zpos p -> pos_to_int(p)
  | Zneg p -> - pos_to_int(p) ;;

(*
let map_quadruple f q = match q with
  | Pair(Pair(Pair(a,b),c),d) -> Pair(Pair(Pair(f(a),f(b)),f(c)),f(d))
*)

let res = cipher exp_key0 zeroState ;;

let print_state s = match s with
  | Pair(Pair(Pair(Pair(Pair(Pair(b0,b1),b2),b3),Pair(Pair(Pair(b4,b5),b6),b7)),Pair(Pair(Pair(b8,b9),b10),b11)),Pair(Pair(Pair(b12,b13),b14),b15)) -> printf "%4x %4x %4x %4x %4x %4x %4x %4x %4x %4x %4x %4x %4x %4x %4x %4x\n" (z_to_int b0) (z_to_int b1) (z_to_int b2) (z_to_int b3) (z_to_int b4) (z_to_int b5) (z_to_int b6) (z_to_int b7) (z_to_int b8) (z_to_int b9) (z_to_int b10) (z_to_int b11) (z_to_int b12) (z_to_int b13) (z_to_int b14) (z_to_int b15) ;;

print_state res ;;

