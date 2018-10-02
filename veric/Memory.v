Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relations.
(*
Require Import compcert.exportclight.Clightdefs.
Require Import compcert.cfrontend.Ctypes. (*NEW*)*)
Require Import compcert.lib.Axioms.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memdata.
Require Import compcert.common.Memtype.
Require Import compcert.common.Memory.
Require Export VST.sepcomp.Address.

Lemma range_dec: forall a b c: Z, {a <= b < c}+{~(a <= b < c)}.
Proof. intros. destruct (zle a b). destruct (zlt b c). left; split; auto.
  right;  omega. right; omega.
Qed.

Require Export VST.msl.eq_dec.

Instance EqDec_ident: EqDec ident := ident_eq.

Instance EqDec_byte: EqDec byte := Byte.eq_dec.

(*Moved to base.v so that this file does not need to Import Clightdefs ad Ctypes
  Instance EqDec_type: EqDec type := type_eq.*)
Instance EqDec_int: EqDec int := Int.eq_dec.
Instance EqDec_int64: EqDec int64 := Int64.eq_dec.
Instance EqDec_float: EqDec float := Float.eq_dec.
Instance EqDec_float32: EqDec float32 := Float32.eq_dec.

Instance EqDex_ptr : EqDec ptrofs := Ptrofs.eq_dec. (*NEW*)

Instance EqDec_memval: EqDec memval.
Proof.
 hnf; repeat decide equality; apply eq_dec.
Defined.

Instance EqDec_val: EqDec val.
Proof.
hnf. decide equality; apply eq_dec.
Defined.

Instance EqDec_quantity: EqDec quantity.
Proof.
hnf. decide equality.
Defined.

Definition access_at (m: mem) (loc: address) (k: perm_kind): option permission :=
   PMap.get (fst loc) (Mem.mem_access m) (snd loc) k.

Lemma perm_access: forall m b ofs k p,
    Mem.perm m b ofs k p <-> (Mem.perm_order'' (access_at m (b,ofs) k) (Some p)).
Proof. reflexivity. Qed.

Lemma access_perm: forall m b ofs k p,
  access_at m (b, ofs) k = Some p ->
  Mem.perm m b ofs k p.
Proof.
intros.
unfold Mem.perm, Mem.perm_order'.
unfold access_at in H. simpl in H.
rewrite H; auto.
constructor.
Qed.

Lemma access_cur_max: forall m a,
           Mem.perm_order'' (access_at m a Max)  (access_at m a Cur).
Proof.
 destruct a as [b z].
 destruct (access_at m (b,z) Cur) eqn:Hc.
 rewrite <- perm_access.
 apply (Mem.perm_cur_max m b z).
 rewrite perm_access. rewrite Hc. constructor.
 destruct (access_at m (b, z) Max); constructor.
Qed.

Lemma invalid_noaccess: forall m b ofs k,
     ~Mem.valid_block m b -> access_at m (b, ofs) k = None.
Proof. intros; apply Mem.nextblock_noaccess. assumption. Qed.

Lemma access_empty: forall a k, access_at Mem.empty a k = None.
Proof.
  intros. unfold access_at, Mem.empty; simpl. rewrite PMap.gi. reflexivity.
Qed.

Transparent Mem.alloc.

Theorem alloc_access_other:
  forall m1 lo hi m2 b, Mem.alloc m1 lo hi = (m2, b) ->
  forall b' ofs k,
  b'<>b \/ (ofs < lo \/ ofs >= hi) ->
  access_at m1 (b', ofs) k = access_at m2 (b', ofs) k.
Proof.
 intros.
pose proof (Mem.nextblock_noaccess m1 b ofs k).
pose proof (Mem.alloc_result _ _ _ _ _ H).
unfold access_at; inversion H; clear H; subst; simpl.
destruct (eq_block b' (Mem.nextblock m1)).
destruct H0; try contradiction.
subst b'.
rewrite PMap.gss.
destruct (zle lo ofs), (zlt ofs hi); try omega; simpl; apply H1; apply Plt_strict.
rewrite PMap.gso by auto. auto.
Qed.

Theorem alloc_access_same:
  forall m1 lo hi m2 b, Mem.alloc m1 lo hi = (m2, b) ->
  forall ofs k,
  lo <= ofs < hi -> access_at m2 (b,ofs) k = Some Freeable.
Proof.
 intros.
 inversion H; clear H; subst. unfold access_at; simpl.
 rewrite PMap.gss.
destruct (zle lo ofs), (zlt ofs hi); try omega; simpl; auto.
Qed.

Opaque Mem.alloc.
Transparent Mem.free.

Lemma access_free:
  forall m1 b lo hi,
  (forall ofs, lo <= ofs < hi -> access_at m1 (b,ofs) Cur = Some Freeable) ->
  { m2: mem | Mem.free m1 b lo hi = Some m2 }.
Proof.
 intros.
 unfold Mem.free.
 destruct (Mem.range_perm_dec m1 b lo hi Cur Freeable).
 eauto.
 contradiction n; clear n.
 hnf; intros. unfold Mem.perm. unfold access_at in H.
 simpl in H; rewrite H by auto. constructor.
Qed.

Lemma free_access:
  forall m1 b lo hi m2, Mem.free m1 b lo hi = Some m2 ->
  (forall ofs, lo <= ofs < hi ->
      access_at m1 (b,ofs) Cur = Some Freeable /\ access_at m2 (b,ofs) Max = None).
Proof.
 intros.
 unfold Mem.free in H.
 destruct (Mem.range_perm_dec m1 b lo hi Cur Freeable); inversion H; clear H; subst.
 specialize (r _ H0).
 hnf in r.
 unfold access_at. simpl.
 destruct ((Mem.mem_access m1) !! b ofs Cur); try contradiction.
 assert (p=Freeable) by (destruct p; inversion r; auto). subst p.
 split; auto.
 simpl. rewrite PMap.gss.
 destruct (zle lo ofs), (zlt ofs hi); try omega. reflexivity.
Qed.

Lemma free_access_other:
  forall m1 bf lo hi m2, Mem.free m1 bf lo hi = Some m2 ->
  forall b ofs k,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  access_at m1 (b,ofs) k = access_at m2 (b,ofs) k.
Proof.
 intros.
 unfold Mem.free in H.
 destruct (Mem.range_perm_dec m1 bf lo hi Cur Freeable); inversion H; clear H; subst.
 unfold access_at; simpl.
 destruct (eq_block b bf).
 subst bf; rewrite PMap.gss.
 destruct H0. contradiction H; auto.
 destruct (zle lo ofs), (zlt ofs hi); try omega; simpl; auto.
 rewrite PMap.gso by auto. reflexivity.
Qed.

Opaque Mem.free.

Lemma access_drop_1:
  forall m b lo hi p m', Mem.drop_perm m b lo hi p = Some m' ->
  (forall ofs, lo <= ofs < hi ->
     forall k,
     access_at m (b, ofs) k = Some Freeable /\ access_at m' (b, ofs) k = Some p).
Proof.
 intros.
 unfold Mem.drop_perm in H.
 destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inversion H; clear H; subst.
 unfold access_at; simpl.
 rewrite PMap.gss.
 destruct (zle lo ofs), (zlt ofs hi); try omega; simpl; auto.
 split; auto.
 specialize (r _ H0). hnf in r. destruct ( (Mem.mem_access m) !! b ofs Cur) eqn:?; try contradiction.
 assert (p0=Freeable) by (destruct p0; inv r; auto). subst.
 pose proof (Mem.access_max m b ofs).
 rewrite Heqo in H.
 destruct k; auto.
 destruct ((Mem.mem_access m) !! b ofs Max); inv H; auto.
Qed.

Lemma access_drop_2:
  forall m b lo hi p,
  (forall ofs, lo <= ofs < hi -> access_at m (b,ofs) Cur = Some Freeable) ->
  { m' | Mem.drop_perm m b lo hi p = Some m' }.
Proof.
 intros.
 unfold Mem.drop_perm.
 destruct (Mem.range_perm_dec m b lo hi Cur Freeable).
 eauto.
 contradiction n; hnf; intros.
 specialize (H _ H0).
 unfold access_at in *.  hnf. simpl in *; rewrite H. constructor.
Qed.

Lemma access_drop_3:
  forall m b lo hi p m', Mem.drop_perm m b lo hi p = Some m' ->
  forall b' ofs k, b' <> b \/ ofs < lo \/ hi <= ofs ->
    access_at m (b', ofs) k = access_at m' (b',ofs) k.
Proof.
 intros.
 unfold Mem.drop_perm in H.
 destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inversion H; clear H; subst.
 unfold access_at; simpl.
 destruct (eq_block b' b).
 subst. rewrite PMap.gss.
 destruct H0.
 contradiction H; auto.
 destruct (zle lo ofs), (zlt ofs hi); try omega; simpl; auto.
 rewrite PMap.gso by auto.
 auto.
Qed.

Lemma storebytes_access:
 forall m1 b ofs bytes m2 (STORE: Mem.storebytes m1 b ofs bytes = Some m2),
  access_at m1 = access_at m2.
Proof.
intros.
apply extensionality ;intros [b' z].
apply extensionality ;intro k.
apply Mem.storebytes_access in STORE.
unfold access_at; f_equal; auto.
Qed.

Lemma store_access:
 forall chunk m1 b ofs v m2 (STORE: Mem.store chunk m1 b ofs v = Some m2),
  access_at m1 = access_at m2.
Proof.
intros.
apply extensionality; intros [b' z'].
apply extensionality ;intro k.
unfold access_at. apply Mem.store_access in STORE. rewrite STORE; auto.
Qed.

Lemma perm_order'_dec_fiddle:
  forall y x, y = Some x ->
     proj_sumbool (Mem.perm_order'_dec y Nonempty) = true.
Proof.
intros. subst. simpl.
unfold Mem.perm_order_dec. destruct x; reflexivity.
Qed.

Lemma access_at_valid_pointer:
  forall m b ofs p, access_at m (b,ofs) Cur = Some p ->
   Mem.valid_pointer m b ofs = true.
Proof.
intros.
unfold access_at, Mem.valid_pointer in *.
simpl in *.
apply perm_order'_dec_fiddle with p.
auto.
Qed.







