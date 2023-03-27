Require Export VST.veric.base.
Require Import VST.veric.res_predicates.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.mpred.
Require Import VST.veric.seplog.

Section mpred.

Context `{!heapGS Σ}.

Lemma mapsto_core_load: forall ch v sh loc,
  (address_mapsto ch v sh loc ∗ True) ⊢ core_load ch loc v.
Proof.
unfold address_mapsto, core_load.
intros; iIntros "[H $]".
iDestruct "H" as (bl ?) "H"; iExists bl; iFrame "%".
iSplit; auto.
iApply (big_sepL_mono with "H"); eauto.
Qed.

Lemma nth_error_in_bounds: forall {A} (l: list A) i, (O <= i < length l)%nat
  -> exists x, nth_error l i = value x.
Proof.
intros until i; intros H.
revert i l H.
induction i; destruct l; intros; simpl in *;
  try solve [eauto|lia].
apply IHi; lia.
Qed.

Lemma nth_eq_nth_error_eq: forall {A} (d: A) (l l': list A) i,
  (O <= i < length l)%nat
  -> length l = length l'
  -> nth i l d = nth i l' d
  -> nth_error l i = nth_error l' i.
Proof.
intros until i; intros H H0 H1.
revert i l l' H H0 H1.
induction i; destruct l; destruct l'; intros; simpl in *;
  try solve [auto|lia].
rewrite (IHi l l'); try solve [auto|lia].
Qed.

(*Lemma core_load_fun: forall ch m loc v1 v2,
   core_load ch loc v1 m -> core_load ch loc v2 m -> v1=v2.
Proof.
intros until v2; intros H H0.
unfold core_load in *.
unfold allp, jam in *.
destruct H as [bl [[H1 [H2 Halign]] H]].
destruct H0 as [bl' [[H3 [H4 Halign']] H0]].
cut (forall i, nth_error bl i = nth_error bl' i); [intro H5|].
cut (bl = bl'); [intro H6|].
rewrite H6 in H2.
rewrite H4 in H2.
auto.
clear - H5.
revert bl' H5.
induction bl; destruct bl'; intros; try solve [specialize (H5 O); inv H5|auto].
f_equal.
specialize (H5 O); inv H5; auto.
apply IHbl.
intro i.
specialize (H5 (S i)).
auto.
intro i.
destruct loc as (b, ofs).
specialize (H (b, ofs + Z_of_nat i)).
specialize (H0 (b, ofs + Z_of_nat i)).
hnf in H, H0. if_tac in H.
* (* adr_range *)
destruct H as [sh [rsh H]].
destruct H0 as [sh' [rsh' H0]].
rewrite H0 in H.
clear H0.
simpl in *.
inversion H.
replace (ofs + Z_of_nat i - ofs) with (Z_of_nat i) in * by lia.
rewrite nat_of_Z_eq in *.
rewrite <- H3 in H1.
apply nth_eq_nth_error_eq with (d := Undef); auto.
destruct H5 as [? [H5 H5']].
rewrite size_chunk_conv in H5'.
lia.
* (* ~adr_range *)
cut (i >= length bl)%nat. intro Hlen.
cut (i >= length bl')%nat. intro Hlen'.
generalize (nth_error_length i bl) as H6; intro.
generalize (nth_error_length i bl') as H7; intro.
rewrite <- H6 in Hlen.
rewrite <- H7 in Hlen'.
rewrite Hlen; rewrite Hlen'; auto.
rewrite <- H3 in H1; clear H3.
rewrite <- H1; auto.
unfold adr_range in H5.
rewrite size_chunk_conv in H5.
rewrite <- H1 in H5.
cut ( ~(O <= i < length bl))%nat.
lia.
intro HContra.
apply H5.
split; auto.
cut (0 <= Z_of_nat i < Z_of_nat (length bl)). intro H6.
2: lia.
lia.
Qed.*)

Lemma adr_range_split_lem1: forall n m r loc loc',
  r = n + m -> n >= 0 -> m >= 0 -> adr_range loc n loc' -> adr_range loc r loc'.
Proof.
unfold adr_range; intros.
destruct loc; destruct loc'; simpl in *.
destruct H2; split; auto.
lia.
Qed.

Lemma adr_range_split_lem2: forall n m r loc loc',
  r = n + m -> n >= 0 -> m >= 0 -> adr_range (fst loc, snd loc + n) m loc'
  -> adr_range loc r loc'.
Proof.
unfold adr_range; intros.
destruct loc; destruct loc'; simpl in *.
destruct H2; split; auto.
lia.
Qed.

Lemma adr_range_split_lem3: forall n m r loc loc',
  r = n + m -> n >= 0 -> m >= 0
  -> ~adr_range loc n loc'
  -> ~adr_range (fst loc, snd loc + n) m loc'
  -> ~adr_range loc r loc'.
Proof.
unfold adr_range; intros.
destruct loc; destruct loc'; simpl in *.
intros [c1 c2].
destruct (Z_lt_dec z0 (z+n)).
apply H2.
split; auto||lia.
apply H3.
split; auto||lia.
Qed.

End mpred.
