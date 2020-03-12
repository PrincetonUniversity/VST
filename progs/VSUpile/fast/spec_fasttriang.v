Require Import VST.floyd.proofauto.
Require Import triang.
Require Import spec_stdlib.

(*Predicate bundle is empty, but the ASI still depend n the MemMGR bundle*)

(*decreasing is a model-level function - it is referred to not only
  in verif_triang.v but also in verif_main, so should be defined not
  in verif_triang but here (or a global model-level file).
  The auxiliary lemmas triangular_number and sumlist_decreasing_bound
  are also code-independent but can be left in verif_triang for now*)
Fixpoint decreasing (n: nat) :=
 match n with
 | O => nil
 | S n' => Z.of_nat n :: decreasing n'
 end.

Fixpoint triang (n: nat) :=
 match n with
 | O => 0
 | S n' => Z.of_nat n + triang n'
 end.

Section TriangASI.
Variable M: MemMGRPredicates.

Definition Triang_nth_spec :=
 DECLARE _Triang_nth
 WITH n:Z, gv: globals
 PRE [ tint ] 
    PROP( 0 <= n < 1000) 
    PARAMS (Vint (Int.repr n)) GLOBALS (gv) 
    SEP(mem_mgr M gv)
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (triang (Z.to_nat n)))))
    SEP(mem_mgr M gv).

Definition TriangASI:funspecs := [Triang_nth_spec].
End TriangASI.
