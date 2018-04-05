From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(* given n <= m, returns the list [n-1,...,0] with proofs of < m *)
    Program Fixpoint enum_from n m (pr : le n m) : list (ordinal m) :=
      match n with
        O => nil
      | S n => (@Ordinal m n ltac:(rewrite <-Heq_n in *; apply (introT leP pr)))
                :: @enum_from n m ltac:(rewrite <-Heq_n in *; apply Le.le_Sn_le, pr)
      end.

    Definition enum n := Coq.Lists.List.rev (@enum_from n n (Le.le_refl n)).

Axiom ord_enum_enum:
  forall n : nat, @eq (list (ordinal n)) (ord_enum n) (enum n).
