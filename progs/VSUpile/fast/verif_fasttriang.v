Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import triang.
Require Import spec_stdlib.
Require Import spec_fastpile.
Require Import spec_triang.
Require Import PileModel.

Instance TriangCompSpecs : compspecs. make_compspecs prog. Defined.

Section Triang_VSU.
Variable M: MallocFreeAPD.
Variable PILE: PileAPD.

  Definition triang_imported_specs:funspecs := PileASI M PILE.

  Definition triang_internal_specs: funspecs := TriangASI M.

  Definition TriangVprog: varspecs. mk_varspecs prog. Defined.
  Definition TriangGprog: funspecs := triang_imported_specs ++ triang_internal_specs.

Lemma body_Triang_nth: semax_body TriangVprog TriangGprog f_Triang_nth (Triang_nth_spec M).
Proof.
start_function.
forward_call gv.
Intros p.
forward_for_simple_bound n
  (EX i:Z,
   PROP() LOCAL(temp _p p; temp _n (Vint (Int.repr n)); gvars gv)
   SEP (pilerep PILE (decreasing (Z.to_nat i)) p; pile_freeable PILE p; mem_mgr M gv)).
-
 entailer!.
- forward_call (p, i+1, decreasing(Z.to_nat i), gv).
entailer!.
assert (Z.to_nat (i+1) = S (Z.to_nat i))
  by (rewrite <- Z2Nat.inj_succ by lia; f_equal).
rewrite H2.
unfold decreasing; fold decreasing.
rewrite inj_S.
rewrite Z2Nat.id by lia.
apply derives_refl.
-
forward_call (p, decreasing (Z.to_nat n)).
apply sumlist_decreasing_bound; auto.
forward_call (p, decreasing (Z.to_nat n), gv).
forward.
entailer!.
f_equal; f_equal.
clear.
induction (Z.to_nat n).
reflexivity.
simpl. congruence.
Qed.

  Definition TriangVSU: @VSU NullExtension.Espec
      nil triang_imported_specs ltac:(QPprog prog) (TriangASI M) emp.
  Proof. 
    mkVSU prog triang_internal_specs.
    + solve_SF_internal body_Triang_nth.
  Qed.

End Triang_VSU.
