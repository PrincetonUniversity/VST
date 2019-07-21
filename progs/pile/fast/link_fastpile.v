Require Import VST.floyd.proofauto.
Require Import linking.
Require main.
Require verif_stdlib.
Require verif_fastpile.
Require verif_fastonepile.
Require verif_fastapile.
Require verif_fasttriang.
Require verif_fastmain.

Definition allmodules := 
   verif_stdlib.module ++
   verif_fastpile.module ++
   verif_fastonepile.module ++
   verif_fasttriang.module ++
   verif_fastapile.module ++
   verif_fastmain.module ++ nil.

Definition Gprog := ltac:
  (let x := constr:(merge_Gprogs_of allmodules) in
   let x := eval hnf in x in
   let x := eval simpl in x in 
   exact x).

Lemma prog_correct:
  semax_prog spec_fastmain.linked_prog spec_fastmain.Vprog Gprog.
Proof.
  prove_semax_prog.
  do_semax_body_proofs (SortBodyProof.sort allmodules).
Qed.
