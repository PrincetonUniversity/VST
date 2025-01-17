(* Additional lemmas / proof rules about VST stack *)

Require Import VST.floyd.proofauto.
Require Export VST.floyd.compat. Export NoOracle.
Require Export sha.general_lemmas.

Definition data_block {cs: compspecs} (sh: share) (contents: list byte) :=
  data_at(cs := cs) sh (tarray tuchar (Zlength contents)) (map Vubyte contents).

Lemma data_block_local_facts:
 forall {cs: compspecs} sh f data,
  data_block sh f data |--
   !! (field_compatible (tarray tuchar (Zlength f)) [] data).
Proof.
intros. unfold data_block, array_at.
simpl.
entailer!.
Qed.
#[export] Hint Resolve data_block_local_facts : saturate_local.


Lemma data_block_valid_pointer {cs: compspecs} sh l p: sepalg.nonidentity sh -> Zlength l > 0 ->
      data_block sh l p |-- valid_pointer p.
Proof. unfold data_block. simpl; intros.
  apply data_at_valid_ptr; auto; simpl.
  rewrite Z.max_r, Z.mul_1_l; lia.
Qed.

Lemma split2_data_block:
  forall  {cs: compspecs}  n sh data d,
  (0 <= n <= Zlength data)%Z ->
  data_block sh data d ⊣⊢
  (data_block sh (sublist 0 n data) d *
   data_block sh (sublist n (Zlength data) data)
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc n] d)).
Proof.
  intros.
  unfold data_block. simpl. normalize.
  rewrite <- !sublist_map.
  unfold tarray.
  rewrite split2_data_at_Tarray_tuchar with (n1:=n) by (autorewrite with sublist; auto).
  autorewrite with sublist.
  reflexivity.
Qed.

Lemma split3_data_block:
  forall  {cs: compspecs} lo hi sh data d,
  0 <= lo <= hi ->
  hi <= Zlength data  ->
  data_block sh data d ⊣⊢
  (data_block sh (sublist 0 lo data) d *
   data_block sh (sublist lo hi data)
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc lo] d) *
   data_block sh (sublist hi (Zlength data) data)
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc hi] d)).
Proof.
  intros.
  unfold data_block. 
  rewrite <- !sublist_map.
  unfold tarray.
  rewrite split3_data_at_Tarray_tuchar with (n1:=lo)(n2:=hi) by (autorewrite with sublist; auto).
  autorewrite with sublist.
  rewrite assoc; auto; apply _.
Qed.

Lemma force_lengthn_long {A}: forall n (l:list A) d, (n <= length l)%nat -> force_lengthn n l d = firstn n l.
Proof. induction n; simpl; intros. trivial.
  destruct l; simpl in H. lia.
  rewrite IHn; trivial. lia.
Qed.

Lemma skipn_force_lengthn_app {A} n (l m:list A) a:
        skipn n (force_lengthn n l a ++ m) = m.
  intros. rewrite skipn_app1.
  specialize (skipn_exact_length (force_lengthn n l a)).
           rewrite force_lengthn_length_n. intros X; rewrite X; trivial.
  rewrite force_lengthn_length_n; lia.
Qed.

Lemma data_at_triv {cs} sh t v v' p: v=v' -> data_at(cs := cs) sh t v p |-- data_at sh t v' p.
Proof. intros; subst. auto. Qed.

Lemma sizeof_Tarray {cs: compspecs} k: Z.max 0 k = k -> sizeof (Tarray tuchar k noattr) = k.
Proof. intros K; simpl; rewrite K. destruct k; trivial. Qed.

Lemma nth_mapVint: forall i (l:list Z) (Hi: (0 <= i < length l)%nat),
  exists n, nth i (map Vint (map Int.repr l)) Vundef = Vint n.
Proof. intros i.
  induction i; simpl; intros.
    destruct l; simpl in *. lia. eexists; reflexivity.
    destruct l; simpl in *. lia.
      destruct (IHi l). lia. rewrite H. eexists; reflexivity.
Qed.

Lemma nth_mapVint' {z}: forall i (l:list Z)
  (Hi: (0 <= i < length l)%nat),
  nth i (map Vint (map Int.repr l)) Vundef =
  Vint (Int.repr (nth i l z)).
Proof. intros i.
  induction i; simpl; intros.
    destruct l; simpl in *. lia. trivial.
    destruct l; simpl in *. lia.
      rewrite (IHi l). trivial. lia.
Qed.

Lemma nth_mapVintZ: forall i (l:list Z) (Hi: 0 <= i < Zlength l),
  exists n, nth (Z.to_nat i) (map Vint (map Int.repr l)) Vundef = Vint n.
Proof. intros.
  eapply nth_mapVint. rewrite Zlength_correct in Hi.
  destruct Hi; split.   lia.
unfold Z.of_nat in H0. unfold Z.to_nat.
destruct l; simpl in *. lia.
destruct i; try lia.
Qed.

Lemma isptrD v: isptr v -> exists b ofs, v = Vptr b ofs.
Proof. intros. destruct v; try contradiction. exists b, i; trivial. Qed.

Ltac myframe_SEP'' L :=  (* this should be generalized to permit framing on LOCAL part too *)
 grab_indexes_SEP L;
 match goal with
 | |- semax _ _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  rewrite <- (firstn_skipn (length L) R);
  rewrite <- (firstn_skipn (length Q) Q);
    simpl length; unfold firstn, skipn;
    eapply (semax_frame_PQR nil);
      [ unfold closed_wrt_modvars;  auto 50 with closed
     | ]
 | |- (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
  rewrite <- (firstn_skipn (length L) R);
    simpl length; unfold firstn, skipn;
    apply derives_frame_PQR
end.
