Require Import VST.floyd.proofauto.
Require Import fastpile.
Require spec_fastpile.
Require spec_fastpile_concrete.

Lemma sub_Pile_new: 
  funspec_sub (snd spec_fastpile_concrete.Pile_new_spec)
                     (snd spec_fastpile.Pile_new_spec).
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intro gv. simpl in gv.
Exists gv emp.
rewrite !insert_SEP.
apply andp_right.
entailer!.
apply prop_right.
Intros p. Exists p.
rewrite !insert_SEP.
unfold spec_fastpile_concrete.countrep, spec_fastpile.pilerep.
unfold spec_fastpile_concrete.count_freeable, spec_fastpile.pile_freeable.
Intros s'. Exists 0.
entailer!.
rewrite H0 by rep_omega.
apply derives_refl.
Qed.

Lemma sub_Pile_add: 
  funspec_sub (snd spec_fastpile_concrete.Pile_add_spec)
                     (snd spec_fastpile.Pile_add_spec).
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros [[[p n] sigma] gv].
Exists (p,n, spec_fastpile.sumlist sigma,gv) emp.
rewrite !insert_SEP.
apply andp_right.
-
entailer!.
unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
Intros s; Exists s. entailer!. simpl in H0.
assert (0 <= spec_fastpile.sumlist sigma). {
  clear - H1; induction sigma; simpl. omega.
  inv H1. specialize (IHsigma H3). omega.
}
split; auto.
-
unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
Intros s.
apply prop_right.
Intros s'; Exists s'.
entailer!.
split.
constructor; auto. omega.
intros.
apply H5.
simpl in H8.
omega.
Qed.

Lemma sub_Pile_count: 
  funspec_sub (snd spec_fastpile_concrete.Pile_count_spec)
                     (snd spec_fastpile.Pile_count_spec).
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros [p  sigma].
Exists (p, spec_fastpile.sumlist sigma) emp.
rewrite !insert_SEP.
apply andp_right.
-
unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
Intros s; Exists s. entailer!.
-
unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
Intros s.
apply prop_right.
Intros s'; Exists s'.
rewrite !insert_SEP.
entailer!.
rewrite <- H3; auto. omega.
Intros s''.
change  spec_fastpile_concrete.tpile with  spec_fastpile.tpile.
rewrite H3,H6 by omega.
apply derives_refl.
Qed.

Lemma sub_Pile_free: 
  funspec_sub (snd spec_fastpile_concrete.Pile_free_spec)
                     (snd spec_fastpile.Pile_free_spec).
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros [[p sigma] gv].
Exists (p, spec_fastpile.sumlist sigma, gv) emp.
rewrite !insert_SEP.
apply andp_right.
-
unfold spec_fastpile.pilerep, spec_fastpile_concrete.countrep.
unfold spec_fastpile_concrete.count_freeable, spec_fastpile.pile_freeable.
Intros s; Exists s. entailer!. simpl in H2.
assert (0 <= spec_fastpile.sumlist sigma). {
  clear - H0; induction sigma; simpl. omega.
  inv H0. specialize (IHsigma H3). omega.
}
split; auto.
apply derives_refl.
-
apply prop_right.
entailer!.
Qed.
