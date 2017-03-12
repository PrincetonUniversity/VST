Load loadpath.
Require Import veristar.superpose veristar.veristar veristar.clauses
               veristar.variables.

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Constant andb => "(&&)".

(* extraction of orb appears to make things slower *)

Extract Constant negb => "(not)".

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive prod => "(*)" [ "" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive option => option [ Some None ].

(* EXPERIMENTAL *)

Import Superposition.

Extraction Inline
  rewrite_by demodulate simplify
  andb negb.

(* ident and ident operator extraction *)

Extract Constant Ident.t => "int".

Extract Constant Ident.compare =>
   "(fun (x:int) (y : int) -> if x < y then Lt else if x > y then Gt else Eq)".

Extract Constant Ident.eq_dec =>
   "(fun (x:int) (y : int) -> x=y)".

Extract Constant minid => "min_int".

(* id2pos only used in proofs *)

Extract Constant id2pos => "(fun _ -> failwith (String.make 0 'x'))".

Extract Constant Z2id =>
  "(fun z ->
      let rec pos2int = function
      | XH -> 1
      | XO(p) -> 2 * pos2int p
      | XI(p) -> 2 * pos2int p + 1 in
    match z with
      Z0 -> 0
    | Zpos p -> pos2int p
    | Zneg p -> -1 * (pos2int p))".

Extract Constant add_id => "(fun x y -> x + y)".

(*Extract Constant mul_id => "(fun x y -> x * y)".*)

(* monolithic extraction *)

Extraction "veristar.ml" VeriStar.
