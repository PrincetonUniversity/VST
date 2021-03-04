Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile.
Require Import spec_fastpile_concrete.
Require Import PileModel.

(*The FM paper contains direct subsumption proofs like the following

Lemma sub_Pile_count: 
  funspec_sub (snd spec_fastpile_concrete.Pile_count_spec)
                     (snd spec_fastpile.Pile_count_spec).
Proof. ... Qed.

A first idea might be to directly lift them to the specs embedded in
an the ASIs, as follows:*)

Section SubsumptionProofs_ASI.
(*Since the specs are parametric in predicate bundles,
  let's do the same here*)
Variable M: MallocFreeAPD.
Variable FPC:FastpileConcreteAPD.
Variable PILE:PileAPD.
Lemma sub_Pile_new: 
  funspec_sub (snd (spec_fastpile_concrete.Pile_new_spec M FPC))
              (snd (spec_fastpile.Pile_new_spec M PILE)).
Proof.
do_funspec_sub.
rename w into gv; clear H.
Exists gv emp. entailer!.
intros tau ? ?. Exists (eval_id ret_temp tau).
entailer!.
Abort.
(*But that can't work: the entailments left over as side conditions here
can never be proven abstractly but only given concrete predicate definitions.
One might think that imposing axioms countrep |-- pilerep and 
count_freeable |-- pile_freeable would help. But the following proof attempt shows 
(unsurprsingly given the structure of funspec sub and the occurrence of the abstract predicates in pre- AND post-conditions)
that one would additionally deen axioms in the opposite direction.*)

Lemma sub_Pile_add: 
  funspec_sub (snd (spec_fastpile_concrete.Pile_add_spec M FPC))
              (snd (spec_fastpile.Pile_add_spec M PILE)).
Proof.
do_funspec_sub. destruct w as [[[p n] sigma] gv]; clear H. simpl. normalize.
Exists (p,n, sumlist sigma,gv) emp. normalize.
entailer!.
Abort.
End SubsumptionProofs_ASI.
(*Thus, let's first do some proofs about concrete bundles, ie the constructions
from the deliverables verif_fastpile_concrete.v and verif_fastpile.v. 
Essentially, the replays the proofs from the FM paper. *)

Require Import verif_fastpile_concrete.
Require Import verif_fastpile.
(*Locate PILE. now gives Constant pile.fast.verif_fastpile.PILE.*)

Section SubsumptionProofs_FM.
Variable M: MallocFreeAPD.
Lemma sub_Pile_new:
  funspec_sub (snd (spec_fastpile_concrete.Pile_new_spec M (FASTPILECONC M)))
              (snd (spec_fastpile.Pile_new_spec M (PILE M))).
Proof.
do_funspec_sub.
rename w into gv; clear H.
Exists gv emp. entailer!.
intros tau ? ?. Exists (eval_id ret_temp tau).
entailer!.
unfold spec_fastpile_private.fastprep. unfold crep.
Intros s. Exists s. simpl in *. entailer.
Qed.

(*The other remaining side conditions are swapped compared to the FM code base,
  presumably because of a reformulation of sunpec_sub or becuase of the introduction of do_funspec_sub*)
Lemma sub_Pile_add: 
  funspec_sub (snd (spec_fastpile_concrete.Pile_add_spec M (FASTPILECONC M)))
              (snd (spec_fastpile.Pile_add_spec M (PILE M))).
Proof.
do_funspec_sub. destruct w as [[[p n] sigma] gv]; clear H. simpl. normalize.
Exists (p,n, sumlist sigma,gv) emp. normalize.
apply andp_right.
- unfold spec_fastpile_private.fastprep, crep.
  Intros s. apply prop_right. split; [ intros | intuition].
  Intros s'; Exists s'.
  entailer!.
  simpl in *. rewrite H8. simpl; trivial. lia.
- unfold spec_fastpile_private.fastprep, crep.
  Intros s; Exists s. apply sumlist_nonneg in H3. entailer!.
Qed.

Lemma sub_Pile_count: 
  funspec_sub (snd (spec_fastpile_concrete.Pile_count_spec (FASTPILECONC M)))
              (snd (spec_fastpile.Pile_count_spec (PILE M))).
Proof.
do_funspec_sub. destruct w as [p sigma]; clear H. simpl. normalize.
Exists (p, sumlist sigma) emp. normalize. entailer.
apply andp_right. 
- unfold spec_fastpile_private.fastprep, crep.
  Intros s. apply prop_right. intros.
  Intros s'; Exists s'.
  entailer!.
  + rewrite <- H5; auto.
  + Intros s''.
    change  spec_fastpile_concrete.tpile with  spec_fastpile.tpile.
    rewrite H5,H9 by lia.
    apply derives_refl.
- unfold spec_fastpile_private.fastprep, crep.
  Intros s; Exists s. entailer!.
Qed.

Lemma sub_Pile_free: 
  funspec_sub (snd (spec_fastpile_concrete.Pile_free_spec M (FASTPILECONC M)))
              (snd (spec_fastpile.Pile_free_spec M (PILE M))).
Proof.
do_funspec_sub. destruct w as [[p sigma] gv]. clear H; simpl; normalize.
Exists (p, sumlist sigma, gv) emp. normalize. 
apply andp_right.
- entailer!.
- unfold spec_fastpile_private.fastprep, crep.
  unfold pfreeable, cfreeable.
  Intros s; Exists s. entailer!.
  + apply sumlist_nonneg in H1. split; auto.
  + apply derives_refl.
Qed.

End SubsumptionProofs_FM.
(*
Definition ASI_sub (ASI1 ASI2: funspecs) :=
  map fst ASI1 = map fst ASI2 /\
  Forall2 funspec_sub (map snd ASI1) (map snd ASI2).
*)

(*Let's generalize a little, in stages. Stage 1: define a type that bundles
  subsumbption proofs for the four methods of pile, given
  FastpileConcretePredicates predicate bundle and a PilePredicates predicate bundle.*)
Record PileSub (M:MallocFreeAPD) 
               (ConcPreds: FastpileConcreteAPD)
               (Preds:PileAPD) := {
  sub_new: funspec_sub (snd (spec_fastpile_concrete.Pile_new_spec M ConcPreds))
                       (snd (spec_fastpile.Pile_new_spec M Preds));
  sub_add: funspec_sub (snd (spec_fastpile_concrete.Pile_add_spec M ConcPreds))
                       (snd (spec_fastpile.Pile_add_spec M Preds));
  sub_count: funspec_sub (snd (spec_fastpile_concrete.Pile_count_spec ConcPreds))
                         (snd (spec_fastpile.Pile_count_spec Preds));
  sub_free: funspec_sub (snd (spec_fastpile_concrete.Pile_free_spec M ConcPreds))
                        (snd (spec_fastpile.Pile_free_spec M Preds))
}.

(*Indeed, the lemmas we proved in Section SubsumptionProofs_FM can be bundled in this way.*)
Lemma PILE_SUB M: PileSub M (FASTPILECONC M) (PILE M).
Proof.
  constructor.
  apply sub_Pile_new.
  apply sub_Pile_add.
  apply sub_Pile_count.
  apply sub_Pile_free.
Qed. (*No need to keep the proof. Qed suffices.*)

(*Stage 2: let's abstract from the differences between FastpileConcreteASI
  and PileASI. Each one defines a predicate bundle (FastpileConcretePredicates
  in the first case, PilePredicates in the second), plus specs that depend on
  these bundles (by referring to the mpreds defined in the bundles in their
  pre- and postconditions).*) 
Record PileSpec :=
  { preds: Type;
    new_spec: preds -> funspec;
    add_spec: preds -> funspec;
    count_spec: preds -> funspec;
    free_spec: preds -> funspec
  }.

(*Indeed, here are the two instances, by "constructive proofs" ending in "Defined."*)
Definition Concspec (M: MallocFreeAPD): PileSpec.
eapply (Build_PileSpec FastpileConcreteAPD).
apply (spec_fastpile_concrete.Pile_new_spec M).
apply (spec_fastpile_concrete.Pile_add_spec M).
apply spec_fastpile_concrete.Pile_count_spec.
apply (spec_fastpile_concrete.Pile_free_spec M).
Defined.

Definition Fastspec (M: MallocFreeAPD): PileSpec.
eapply (Build_PileSpec PileAPD).
apply (spec_fastpile.Pile_new_spec M).
apply (spec_fastpile.Pile_add_spec M).
apply spec_fastpile.Pile_count_spec.
apply (spec_fastpile.Pile_free_spec M).
Defined. 
(*Interestingly, Coq accepts this, despite the fact that, for example,
Check spec_fastpile.Pile_new_spec.  yields PilePredicates -> ident * funspec)
rather than PilePredicates -> funspec.*)

(*Now lets say when one PileSpec is a subspec of another one. We require
  that the user gives two concrete predicate bundles (i.e. elements of the two "preds" fields),
  and provides the expected four funspec_sub proofs.*)
Record PileSpecsSub (PS1 PS2: PileSpec) (preds1:preds PS1) (preds2: preds PS2) := { 
  pile_sub_new: funspec_sub (new_spec _ preds1) (new_spec _ preds2);
  pile_sub_add: funspec_sub (add_spec _ preds1) (add_spec _ preds2);
  pile_sub_count: funspec_sub (count_spec _ preds1) (count_spec _ preds2);
  pile_sub_free: funspec_sub (free_spec _ preds1) (free_spec _ preds2)
}.

(*Here's a proof that the two bundles constructed in verif_fastpile_concrete and
  verif_fastpile satisfy this condition. Indeed, the four proofs we constructed in
  Lemma PILE_SUB can conveniently be reused here.*)
Lemma MyPileSpecsSub M: PileSpecsSub (Concspec M) (Fastspec M) (FASTPILECONC M) (PILE M).
Proof. constructor;  apply (PILE_SUB M). Qed.

(*Stage3: let's abstract from the four functions, and instead construct a type of specs
  for any list of (function) identifiers.*)
Record SPEC (l: list ident) :=
  { SPEC_preds: Type;
    SPEC_specs: SPEC_preds -> list funspec;
    SPEC_length: forall p, length l = length (SPEC_specs p);
    SPEC_LNR: compute_list_norepet l = true (*could be omitted or made a parameter of this RECORD definition*)
  }.

(*Here are the two instantiations - again as constructive proofs*)
Definition Pile_SPEC := SPEC [_Pile_new; _Pile_add; _Pile_count; _Pile_free].
Definition ConcSPEC (M: MallocFreeAPD): Pile_SPEC.
eapply (Build_SPEC _ FastpileConcreteAPD
           (fun p => map snd [ spec_fastpile_concrete.Pile_new_spec M p; 
                               spec_fastpile_concrete.Pile_add_spec M p;
                               spec_fastpile_concrete.Pile_count_spec p;
                               spec_fastpile_concrete.Pile_free_spec M p])).
reflexivity.
reflexivity.
Defined.

Definition FastSPEC (M: MallocFreeAPD): Pile_SPEC.
eapply (Build_SPEC _ PileAPD
           (fun p => map snd [ spec_fastpile.Pile_new_spec M p; 
                               spec_fastpile.Pile_add_spec M p;
                               spec_fastpile.Pile_count_spec p;
                               spec_fastpile.Pile_free_spec M p])).
reflexivity.
reflexivity.
Defined. 

(*Two specs for the same identifier list l are in SPECS_Sub relation if - 
  given appropriate predicate bundles - funspec_sub holds pointwise for all
  positions in l*)
Record SPECS_Sub l (SPEC1 SPEC2: SPEC l) (preds1:SPEC_preds _ SPEC1) (preds2: SPEC_preds _ SPEC2) := { 
  sub_proofs: Forall2 funspec_sub (SPEC_specs _ SPEC1 preds1) (SPEC_specs _ SPEC2 preds2)
}.

(*Here's a proof that the two bundles constructed in verif_fastpile_concrete and
  verif_fastpile satisfy this condition. Indeed, the four proofs we constructed in
  Lemma PILE_SUB can conveniently be reused here.*)
Lemma MyPile_SPECS_Sub M: SPECS_Sub _ (ConcSPEC M) (FastSPEC M) (FASTPILECONC M) (PILE M).
Proof. constructor. repeat constructor; apply PILE_SUB. Qed.

(*Relaxing the condition that SPECS1 and SPEC2 be over the same list (instead requiring one be a sublist
of the other one) should result in a notion of behavioral subtyping, so may be relevant for class-based
object systems*)