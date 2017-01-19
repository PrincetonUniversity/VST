(* this file is not extracted, but written manually, to print Z numbers as hex *)
(* open the ocaml repl with command "ocaml", then
   #use "ciphertext1.ml";;
   then
   #use "t.ml";;
*)

open Printf

let rec pos_to_int p = match p with
  | XH -> 1
  | XI q -> 1 + (pos_to_int(q)*2)
  | XO q -> (pos_to_int(q)*2) ;;

let z_to_int z = match z with
  | Z0 -> 0
  | Zpos p -> pos_to_int(p)
  | Zneg p -> - pos_to_int(p) ;;

let print_state s = match s with
  | Pair(Pair(Pair(Pair(Pair(Pair(b0,b1),b2),b3),Pair(Pair(Pair(b4,b5),b6),b7)),Pair(Pair(Pair(b8,b9),b10),b11)),Pair(Pair(Pair(b12,b13),b14),b15)) -> printf "%2x%2x%2x%2x%2x%2x%2x%2x%2x%2x%2x%2x%2x%2x%2x%2x\n" (z_to_int b0) (z_to_int b1) (z_to_int b2) (z_to_int b3) (z_to_int b4) (z_to_int b5) (z_to_int b6) (z_to_int b7) (z_to_int b8) (z_to_int b9) (z_to_int b10) (z_to_int b11) (z_to_int b12) (z_to_int b13) (z_to_int b14) (z_to_int b15) ;;

print_state ciphertext1 ;;

