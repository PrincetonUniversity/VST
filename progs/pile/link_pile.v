Require Import VST.floyd.proofauto.
Require Import linking.
Require main.
Require verif_stdlib.
Require verif_pile.
Require verif_onepile.
Require verif_apile.
Require verif_triang.
Require verif_main.

Definition allmodules := 
   verif_stdlib.module ++
   verif_pile.module ++
   verif_onepile.module ++
   verif_triang.module ++
   verif_apile.module ++
   verif_main.module ++ nil.

Definition Gprog := ltac:
  (let x := constr:(merge_Gprogs_of allmodules) in
   let x := eval hnf in x in
   let x := eval simpl in x in 
   exact x).

Lemma prog_correct:
  semax_prog spec_main.linked_prog spec_main.Vprog Gprog.
Proof.
  prove_semax_prog.
  do_semax_body_proofs (SortBodyProof.sort allmodules).
Qed.
