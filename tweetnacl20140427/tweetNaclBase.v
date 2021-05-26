Require Import Recdef.
Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.

(*Require Import tweetnacl20140427.split_array_lemmas.*)
Require Import ZArith.
Local Open Scope Z.

Lemma Zlength_repeat' {A} n (v:A): Zlength (repeat v n) = Z.of_nat n.
Proof. rewrite Zlength_correct, repeat_length; trivial. Qed.

Lemma Zlength_cons' {A} (a:A) l: Zlength (a::l) = 1 + Zlength l.
  do 2 rewrite Zlength_correct. simpl. rewrite Zpos_P_of_succ_nat,<- Z.add_1_l; trivial. Qed.

Lemma isptrD v: isptr v -> exists b ofs, v = Vptr b ofs.
Proof. intros. destruct v; try contradiction. exists b, i; trivial. Qed.

Lemma firstn_Zlength {A} (l:list A) n: (n <= length l)%nat -> Zlength (firstn n l) = Z.of_nat n.
Proof. intros. rewrite Zlength_correct, firstn_length, Min.min_l; trivial. Qed.

Lemma skipn_Zlength {A} (l:list A) n: (n <= length l)%nat -> Zlength (skipn n l) = Zlength l - (Z.of_nat n).
Proof. intros.
       rewrite Zlength_correct, skipn_length.
       rewrite Zlength_correct, Nat2Z.inj_sub; trivial.
Qed.

Lemma map_cons_inv {A B} (f:A -> B) a l fT:
 (f a:: fT) = map f l -> exists b T, l = b :: T /\ f a = f b /\ fT = map f T.
Proof. destruct l; simpl; intros; inv H.
  exists a0, l. auto. Qed.

Lemma inj_le':
  forall n m : nat, (Z.of_nat n <= Z.of_nat m <-> (n <= m)%nat).
Proof. intros. specialize (Z2Nat.inj_le (Z.of_nat n) (Z.of_nat m)). repeat rewrite Nat2Z.id.
  intros X; apply X; clear X. lia. lia.
Qed.
Lemma Byte_max_unsigned_Int_max_unsigned: Byte.max_unsigned < Int.max_unsigned.
  unfold Byte.max_unsigned, Int.max_unsigned. simpl. lia. Qed.

Lemma force_lengthn_map {A B} (f:A->B) n: forall l d fd,
      fd = f d ->
      force_lengthn n (map f l) fd =
      map f (force_lengthn n l d).
Proof.
  induction n; simpl; intros. trivial. subst.
  destruct l; simpl; f_equal. erewrite (IHn nil); reflexivity.
  apply IHn; trivial.
Qed.
Lemma force_lengthn_mapN {A B} (f:A->B) n: forall l d fd,
      (n < length l)%nat ->
      force_lengthn n (map f l) fd =
      map f (force_lengthn n l d).
Proof.
  induction n; simpl; intros. trivial.
  destruct l; simpl in *. lia.
  f_equal. apply IHn; trivial. lia.
Qed.

Lemma In_force_lengthn {A} d u: forall n l, @In A u (force_lengthn n l d) -> In u l \/ u=d.
  Proof. induction n; simpl; intros. contradiction.
    destruct l. destruct H. subst. right; trivial. apply IHn in H. trivial.
    destruct H. left; left; trivial. apply IHn in H. destruct H. left; right; trivial. right; trivial.
  Qed.
Lemma In_force_lengthn_n {A} d u: forall n l (L:(length l >=n)%nat), @In A u (force_lengthn n l d) -> In u l.
  Proof. induction n; simpl; intros. contradiction.
    destruct l; simpl in *. lia.
    destruct H. left; trivial. apply IHn in H. right; trivial. lia.
  Qed.
Lemma In_skipn {A} (u:A): forall n l, In u (skipn n l) -> In u l.
  Proof. Transparent skipn.
    induction n; simpl; intros. apply H.
    destruct l. trivial. apply IHn in H. right; trivial.
Qed.

Lemma nth_force_lengthn':
  forall (A : Type) (n i : nat) (xs : list A) (default d: A) (N: (n < length xs)%nat),
  (0 <= i < n)%nat ->
  @nth A i (@force_lengthn A n xs default) d = @nth A i xs d.
Proof. intros A.
  induction n; simpl; intros. lia.
  destruct xs; simpl in *. lia. destruct i. trivial.
  rewrite IHn. trivial. lia. lia.
Qed.

Lemma app_Znth1: forall (A : Type){d: Inhabitant A} (l l' : list A) (n :Z),
           (n < Zlength l) -> Znth n (l ++ l') = Znth n l.
Proof. intros. unfold Znth. destruct (Z_lt_dec n 0). trivial.
       apply app_nth1. apply Z2Nat.inj_lt in H.
         rewrite ZtoNat_Zlength in H. trivial.
         lia.
         apply Zlength_nonneg.
Qed.

Lemma app_Znth2: forall (A : Type) {d: Inhabitant A}(l l' : list A) (n : Z),
               (Zlength l <= n) -> Znth n (l ++ l') = Znth (n - Zlength l) l'.
Proof. intros. specialize (Zlength_nonneg l); intros. unfold Znth.
       destruct (Z_lt_dec n 0). lia.
       destruct (Z_lt_dec (n - Zlength l) 0).
         destruct (Z.sub_le_mono_r (Zlength l) n (Zlength l)) as [? _].
         specialize (H1 H). rewrite Z.sub_diag in H1. remember (n - Zlength l). clear - l0 H1. lia.
       rewrite app_nth2.
        rewrite Z2Nat.inj_sub, ZtoNat_Zlength; trivial.
        apply Z2Nat.inj_le in H; trivial. rewrite ZtoNat_Zlength in H; trivial. lia.
Qed.

Lemma nth_extensional {A}: forall l1 l2 (L:length l1 = length l2) (d:A)
         (N: forall i, (0<=i<length l1)%nat -> nth i l1 d = nth i l2 d), l1=l2.
induction l1; intros.
  destruct l2; simpl in L. trivial. lia.
  destruct l2; simpl in L. lia.
  rewrite (IHl1 l2) with (d:=d).
    specialize (N O). simpl in N. rewrite N; trivial. lia.
    lia.
    intros. apply (N (S i)). simpl; lia.
Qed.

Lemma Znth_extensional {A} {d: Inhabitant A}(l1 l2 : list A):
       Zlength l1 = Zlength l2 -> 
       (forall i,
        (0 <= i < Zlength l1) -> Znth i l1 = Znth i l2) -> l1 = l2.
Proof. intros.
  assert (HH: Z.to_nat (Zlength l1) = Z.to_nat (Zlength l2)).
    rewrite H; trivial.
  do 2 rewrite Zlength_correct, Nat2Z.id in HH.
  eapply nth_extensional with (d0:=d). trivial.
  intros.
  assert (I: 0 <= (Z.of_nat i) < Zlength l1).
    split. apply (Nat2Z.inj_le 0). apply H1. rewrite Zlength_correct. apply Nat2Z.inj_lt. apply H1.
  specialize (H0 _ I). unfold Znth in H0.
  destruct (Z_lt_dec (Z.of_nat i) 0). lia.
  rewrite Nat2Z.id in H0. trivial.
Qed.

Lemma force_lengthn_app1 {A}{d: Inhabitant A}: forall n l1 l2, length l1 =n -> force_lengthn n (l1 ++ l2) d = l1.
Proof.
  induction n; simpl; intros. destruct l1; simpl in *; trivial. lia.
  destruct l1; simpl in *. lia. rewrite IHn; trivial. lia.
Qed.

(*Lemma map_Znth {A B : Type}{d: Inhabitant A} (f : A -> B) l n:
      Znth n (map f l) = f (Znth n l).
Proof. unfold Znth. destruct (Z_lt_dec n 0); simpl. trivial. apply map_nth. Qed.

Lemma Znth_map' {A B : Type} (f : A -> B) d d' i al:
        (0<= i < Zlength al)%Z -> Znth i (map f al) d = f (Znth i al d').
Proof. unfold Znth; intros. destruct (Z_lt_dec i 0); simpl. lia. apply nth_map'.
  destruct H. rewrite Zlength_correct in H0. apply Z2Nat.inj_lt in H0.
   rewrite Nat2Z.id in H0. assumption. assumption. lia.
Qed.
*)

Lemma listD16 {A} (l:list A): Zlength l = 16 ->
  exists v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
  l = [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15].
Proof. intros.
destruct l. rewrite Zlength_nil in H; lia. exists a. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a0. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a1. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a2. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a3. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a4. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a5. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a6. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a7. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a8. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a9. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a10. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a11. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a12. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a13. rewrite Zlength_cons' in H.
destruct l. rewrite Zlength_nil in H; lia. exists a14. rewrite Zlength_cons' in H.
destruct l; trivial.
rewrite Zlength_cons' in H. specialize (Zlength_nonneg l); intros. lia.
Qed.

Lemma listGE16 {A} (l:list A): 16 <= Zlength l ->
  exists v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 t,
  l = [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] ++ t
  /\ Zlength t = Zlength l - 16.
Proof. intros.
destruct (listD16 (firstn 16 l)) as
  [v0 [v1 [v2 [v3 [v4 [v5 [v6 [v7 [v8 [v9 [v10 [v11 [v12 [v13 [v14 [v15 V]]]]]]]]]]]]]]]].
  rewrite (Zlength_firstn 16), Z.max_r, Z.min_l; lia.
  exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, (skipn 16 l).
  rewrite <- V, firstn_skipn, (Zlength_skipn 16), (Z.max_r 0 16), Z.max_r; try lia.
  split; trivial.
Qed.

Definition bind {A B} (aopt: option A) (f: A -> option B): option B :=
  match aopt with None => None | Some a => f a end.

Section CombineList.
Variable A: Type.
Variable f: A -> A -> A.

Fixpoint combinelist xs ys :=
  match xs, ys with
    nil, nil => Some nil
  | (u::us),(v::vs) => bind (combinelist us vs) (fun l => Some (f u v :: l))
  | _, _ => None
  end.

Lemma combinelist_Zlength: forall xs ys zs,
  combinelist xs ys = Some zs -> Zlength zs = Zlength xs /\ Zlength ys = Zlength xs.
Proof.
  induction xs; intros; destruct ys; simpl in H; inv H.
  split; trivial.
  unfold bind in *.
  remember (combinelist xs ys). symmetry in Heqo.
  destruct o; inv H1. destruct (IHxs _ _ Heqo). repeat rewrite Zlength_cons'.
  rewrite H, H0. split; trivial.
Qed.

Lemma combinelist_Some: forall xs ys, length xs = length ys ->
      exists l, combinelist xs ys = Some l.
Proof.
  induction xs; simpl; intros.
    destruct ys; simpl in *. exists nil; trivial. lia.
  destruct ys; simpl in *. lia.
   inversion H; clear H.
   destruct (IHxs _ H1). rewrite H. simpl. eexists; reflexivity.
Qed.

Lemma combinelist_SomeInv: forall xs ys l, combinelist xs ys = Some l ->
      Zlength xs = Zlength ys.
Proof.
  induction xs; simpl; intros.
    destruct ys; simpl in *. trivial. inversion H.
    destruct ys; simpl in *. inversion H.
    remember (combinelist xs ys). destruct o; symmetry in Heqo; simpl in H.
      inversion H; clear H. apply IHxs in Heqo. do 2 rewrite Zlength_cons'; rewrite Heqo. trivial.
    inversion H.
Qed.

Lemma combinelist_length:
  forall xs ys l, Some l = combinelist xs ys -> length l = length ys.
Proof. induction xs; intros; destruct ys; simpl in *.
  inv H; trivial. inv H. inv H.
  remember (combinelist xs ys) as q. destruct q; simpl in *. inv H. simpl. rewrite (IHxs _ _ Heqq). trivial.
  inv H.
Qed.

Lemma combinelist_symm (C: forall a b, f a b = f b a):
      forall xs ys, combinelist xs ys = combinelist ys xs.
Proof. induction xs; intros.
  destruct ys; simpl; trivial.
  destruct ys; simpl; trivial. rewrite C, IHxs. trivial.
Qed.

Lemma combinelist_char_nth: forall xs ys l, combinelist xs ys = Some l ->
  forall i d, (0 <= i < length l)%nat -> nth i l d = f (nth i xs d) (nth i ys d).
Proof.
  induction xs; simpl; intros.
  destruct ys; inv H; simpl in *. lia.
  destruct ys; inv H; simpl in *.
  remember (combinelist xs ys) as s. symmetry in Heqs.
  destruct s; inv H2. specialize (IHxs _ _ Heqs). simpl in *.
  destruct i; trivial.
  apply IHxs. lia.
Qed.

Lemma combinelist_char_Znth {d: Inhabitant A} xs ys l (C: combinelist xs ys = Some l)
      i (L:0 <= i < Zlength l): Znth i l = f (Znth i xs) (Znth i ys).
Proof.
  unfold Znth.
  destruct (Z_lt_dec i 0). lia.
  rewrite (combinelist_char_nth _ _ _ C); trivial.
  split. lia. destruct (Z2Nat.inj_lt i (Zlength l)). lia. lia.
  rewrite ZtoNat_Zlength in H; apply H. lia.
Qed.
End CombineList.

Lemma shift_two_8 z:
 match z with
 | 0 => 0
 | Z.pos y' => Z.pos y'~0~0~0~0~0~0~0~0
 | Z.neg y' => Z.neg y'~0~0~0~0~0~0~0~0
 end = (z * two_p 8)%Z.
 destruct z; simpl; trivial. f_equal.
  (*rewrite shift_pos_equiv.*) simpl; lia.
  (*rewrite shift_pos_equiv.*) simpl; lia.
Qed.
Lemma shift_two_8_2 z:
  match z with
  | 0 => 0
  | Z.pos y' => Z.pos y'~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  | Z.neg y' => Z.neg y'~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  end = (z * two_p 8 * two_p 8)%Z.
 destruct z; simpl; trivial. f_equal.
  (*rewrite shift_pos_equiv.*) simpl; lia.
  (*rewrite shift_pos_equiv.*) simpl; lia.
Qed.
Lemma shift_two_8_3 z:
  match z with
  | 0 => 0
  | Z.pos y' => Z.pos y'~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  | Z.neg y' => Z.neg y'~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  end = (z * two_p 8 * two_p 8 * two_p 8)%Z.
 destruct z; simpl; trivial. f_equal.
  (*rewrite shift_pos_equiv.*) simpl; lia.
  (*rewrite shift_pos_equiv.*) simpl; lia.
Qed.

Fixpoint iterShr8 u n :=
  match n with O => u
   | S n' => Int.shru (iterShr8 u n') (Int.repr 8)
  end.

Lemma Znth_mapVint: forall {d: Inhabitant _} l i, 0<=i< Zlength l -> exists x, Znth i (map Vint l) = Vint x.
Proof. unfold Znth.
  induction l; simpl; intros.
  rewrite Zlength_correct in H; simpl in *. lia.
  destruct (Z_lt_dec i 0); subst; simpl in *. lia. clear n.
  remember (Z.to_nat i). destruct n. exists a; trivial.
  rewrite Zlength_cons in H.
  destruct (zeq i 0); subst.  simpl in Heqn. lia.
  destruct (IHl (i-1)). lia.
  destruct (Z_lt_dec (i - 1) 0). subst;  lia.
  rewrite Z2Nat.inj_sub in H0. rewrite <- Heqn in H0. simpl in H0. rewrite <- minus_n_O in H0.
     rewrite H0. exists x; trivial. lia.
Qed.

Lemma app_inj {A}: forall l l'
  (L:Zlength l = Zlength l') (m m':list A) (M: Zlength m = Zlength m'),
  l ++ m = l'++m' -> l=l' /\ m = m'.
Proof. induction l; simpl; intros.
+ destruct l'; simpl in *. subst; split; trivial. 
  rewrite Zlength_nil, Zlength_cons in L. specialize (Zlength_nonneg l'); lia.
+ destruct l'; simpl. rewrite Zlength_nil, Zlength_cons in L. specialize (Zlength_nonneg l); lia.
  simpl in *. inv H. 
  assert (LL': Zlength l = Zlength l') by (rewrite 2 Zlength_cons in L; lia).
  destruct (IHl _ LL' _ _ M H2); subst. split; trivial.
Qed.

Lemma list_eq_dec_app {A} (eq_dec: forall x y : A, {x = y} + {x <> y}):
  forall l m l' m'
  (L:Zlength l = Zlength l') (M: Zlength m = Zlength m'),
  ((if list_eq_dec eq_dec (l++m) (l'++m') then true else false) =
  ((if list_eq_dec eq_dec l l' then true else false) &&
   (if list_eq_dec eq_dec m m' then true else false)))%bool.
Proof. 
induction l; intros.
+ destruct l'; simpl; trivial. 
  rewrite Zlength_nil, Zlength_cons in L. specialize (Zlength_nonneg l'); lia.
+ destruct l'. rewrite Zlength_nil, Zlength_cons in L. specialize (Zlength_nonneg l); lia.
  assert (LL': Zlength l = Zlength l') by (rewrite 2 Zlength_cons in L; lia).
  specialize (IHl _ _ _ LL' M).
  destruct (eq_dec a a0); subst.
  - destruct (list_eq_dec eq_dec (l ++ m) (l' ++ m')); subst.
    * destruct (app_inj _ _ LL' _ _ M e); subst l' m'.
      rewrite 3 if_true; trivial.
    * if_tac; simpl in H. 
      ++ inv H. contradiction.
      ++ if_tac in IHl; simpl in IHl.
         -- subst l'. rewrite if_true; trivial.
         -- if_tac; trivial. inv H1; congruence.
  - destruct (list_eq_dec eq_dec (l ++ m) (l' ++ m')); subst.
    * destruct (app_inj _ _ LL' _ _ M e); subst l' m'.
      rewrite if_false. rewrite if_false; trivial. congruence.
      simpl; congruence.
    * rewrite if_false. 2: simpl; congruence.
      rewrite if_false; trivial. simpl; congruence.
Qed. 

Lemma combine_app {A B}: forall (l1:list A) (m1:list B) l2 m2 
  (L:Zlength l1 = Zlength m1) (M: Zlength l2 = Zlength m2),
  combine (l1 ++ l2) (m1 ++ m2) = combine l1 m1 ++ combine l2 m2.
Proof.
induction l1; intros.
+ destruct m1; simpl; trivial. 
  rewrite Zlength_nil, Zlength_cons in L. specialize (Zlength_nonneg m1); lia.
+ destruct m1. rewrite Zlength_nil, Zlength_cons in L. specialize (Zlength_nonneg l1); lia.
  assert (LL': Zlength l1 = Zlength m1) by (rewrite 2 Zlength_cons in L; lia).
  specialize (IHl1 _ _ _ LL' M). simpl. f_equal; trivial.
Qed.

Lemma Byte_zero_ext_8 b: Byte.zero_ext 8 b = b.
 apply Byte.same_bits_eq; intros.
 rewrite Byte.bits_zero_ext by lia. if_tac; trivial.
 replace Byte.zwordsize with 8 in H by reflexivity. lia.
Qed.

Lemma Byte_Int_max_unsigned: Byte.max_unsigned < Int.max_unsigned.
Proof. cbv; trivial. Qed.

Lemma byte_unsigned_range_int_unsigned_max x: 0 <= Byte.unsigned x <= Int.max_unsigned.
Proof. destruct (Byte.unsigned_range_2 x). specialize Byte_Int_max_unsigned; lia. Qed.

Lemma Zlxor_of_byte_range x y: 0 <= Z.lxor (Byte.unsigned x) (Byte.unsigned y) <= Byte.max_unsigned.
Proof.
 destruct (Byte.unsigned_range x).
 destruct (Byte.unsigned_range y).
 split; apply Zbits.Ztestbit_le.
 + apply Z.lxor_nonneg. lia.
 + intros. destruct i; discriminate.
 + unfold Byte.max_unsigned. simpl; lia.
 + intros. unfold Byte.max_unsigned. simpl. rewrite Z.lxor_spec in H4.
   unfold xorb in H4.
   specialize (Zbits.Ztestbit_two_p_m1 8 i); simpl. intros X; rewrite X; clear X; try lia.
   destruct (zlt i 8); trivial.
   rewrite 2 (Zbits.Ztestbit_above 8) in H4. discriminate.
   apply Byte.unsigned_range. simpl; lia.
   apply Byte.unsigned_range. simpl; lia.
Qed.

Lemma unsigned_xor_Byte_Int xi yi: Byte.unsigned (Byte.xor xi yi) =
      Int.unsigned (Int.xor (Int.repr (Byte.unsigned xi)) (Int.repr (Byte.unsigned yi))).
Proof.
  unfold Int.xor, Byte.xor.
  rewrite (Int.unsigned_repr (Byte.unsigned xi)) by apply byte_unsigned_range_int_unsigned_max.
  rewrite (Int.unsigned_repr (Byte.unsigned yi)) by apply byte_unsigned_range_int_unsigned_max.
  rewrite Int.unsigned_repr, Byte.unsigned_repr; trivial. apply Zlxor_of_byte_range.
  destruct (Zlxor_of_byte_range xi yi). specialize Byte_Int_max_unsigned; lia.
Qed.

Lemma Z_lxor_byte_neq b1 b2 (B:b1 <> b2): exists b, 
      Z.lxor (Byte.unsigned b1) (Byte.unsigned b2) = Byte.unsigned b /\ b <> Byte.zero.
Proof.
  exists (Byte.xor b1 b2); split. 2: intros N; apply Byte.xor_zero_equal in N; contradiction.
  apply Zbits.equal_same_bits; intros.
  destruct (zlt i 8).
  + unfold Byte.xor. rewrite Byte.unsigned_repr; trivial. apply Zlxor_of_byte_range. 
  + rewrite ! (Zbits.Ztestbit_above 8); simpl; trivial; try lia. apply Byte.unsigned_range.
    specialize (Zlxor_of_byte_range b1 b2). 
    replace (two_power_nat 8) with 256 by reflexivity.
    replace Byte.max_unsigned with 255 by reflexivity. lia.
Qed.

Lemma Zlor_of_byte_range x y: 0 <= Z.lor (Byte.unsigned x) (Byte.unsigned y) <= Byte.max_unsigned.
Proof. 
 destruct (Byte.unsigned_range x).
 destruct (Byte.unsigned_range y).
 split.
+ apply Zbits.Ztestbit_le.
  - apply Z.lor_nonneg. lia.
  - destruct i; discriminate.
+ unfold Byte.max_unsigned. simpl.
  apply Zbits.Ztestbit_le. lia. intros.
  rewrite Z.lor_spec in H4. 
  destruct (zlt i 8 ).
  - destruct (zeq i 0). subst; reflexivity. 
    destruct (zeq i 1). subst; reflexivity. 
    destruct (zeq i 2). subst; reflexivity. 
    destruct (zeq i 3). subst; reflexivity. 
    destruct (zeq i 4). subst; reflexivity. 
    destruct (zeq i 5). subst; reflexivity. 
    destruct (zeq i 6). subst; reflexivity. 
    destruct (zeq i 7). subst; reflexivity. lia.  
  - rewrite 2 (Zbits.Ztestbit_above 8) in H4; try discriminate; simpl; try lia; apply Byte.unsigned_range.
Qed. 

Lemma Zlor_Byteor b1 b2: Z.lor (Byte.unsigned b1) (Byte.unsigned b2) = Byte.unsigned (Byte.or b1 b2).
Proof. unfold Byte.or. rewrite Byte.unsigned_repr; trivial. apply Zlor_of_byte_range. Qed.

Lemma ByteOr_zero b1 b2 (B: Byte.or b1 b2 = Byte.zero): b1=Byte.zero /\ b2=Byte.zero.
Proof.
  specialize (Byte.bits_or b1 b2); intros. rewrite B in H; clear B.
  assert (forall i, 0 <= i < Byte.zwordsize -> (Byte.testbit b1 i = false /\ Byte.testbit b2 i = false)).
  + intros. specialize (H _ H0). rewrite Byte.bits_zero in H. symmetry in H. 
    apply orb_false_iff in H; trivial.
  + clear H. split; apply Byte.same_bits_eq; intros; rewrite Byte.bits_zero; apply (H0 _ H).
Qed.
