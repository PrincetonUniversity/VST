Require Import floyd.proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha.
Require Export sha.common_lemmas.
Require Psatz.

Global Opaque K256 CBLOCKz LBLOCKz.

Transparent peq.

Definition field_offset' (i: ident) (t: type) : Z :=
match t with
| Tstruct _ f _ => 
    match field_offset i f with Errors.OK n => n | _ => -1 end
| _ => -1
end.

Definition data_offset : Z.  (* offset, in bytes, of _data field in struct SHA256_state *)
pose (n := field_offset' _data t_struct_SHA256state_st); subst; compute in n.
match goal with n := ?N |- _ => apply N end.
Defined.

(* Definition data_offset := 40%Z. (* offset  of _data field in the struct *) *)
(*Global Opaque data_offset. *)

Lemma elim_globals_only'':
  forall i t rho,  
   (exists Delta, tc_environ Delta rho /\
       (var_types Delta) ! i = None /\ isSome ((glob_types Delta) ! i)) ->
       (eval_var i t (globals_only rho)) = eval_var i t rho.
Proof. 
  intros.
  unfold_lift.
 destruct H as [Delta [?[? ?]]].
  destruct ((glob_types Delta) ! i) eqn:?; try contradiction.
  erewrite elim_globals_only; eauto.
Qed.

Hint Rewrite elim_globals_only'' using (eexists; split3; [eassumption | reflexivity | apply I]) : norm.

Lemma elim_make_args:
  forall i t il vl rho,  
   (exists Delta, tc_environ Delta rho /\
       (var_types Delta) ! i = None /\ isSome ((glob_types Delta) ! i)) ->
       (eval_var i t (make_args il vl rho)) = eval_var i t rho.
Proof. 
  intros.
 revert vl; induction il; destruct vl; simpl; auto.
 apply elim_globals_only''; auto. 
 rewrite <- (IHil vl).
 clear.
 reflexivity.
Qed.

Hint Rewrite elim_make_args using (eexists; split3; [eassumption | reflexivity | apply I]) : norm.

Fixpoint loops (s: statement) : list statement :=
 match s with 
  | Ssequence a b => loops a ++ loops b
  | Sloop _ _ => [s]
  | Sifthenelse _ a b => loops a ++ loops b
  | _ => nil
  end.

Lemma Zlength_length:
  forall A (al: list A) (n: Z),
    0 <= n ->
    (Zlength al = n <-> length al = Z.to_nat n).
Proof.
intros. rewrite Zlength_correct.
split; intro.
rewrite <- (Z2Nat.id n) in H0 by omega.
apply Nat2Z.inj in H0; auto.
rewrite H0.
apply Z2Nat.inj; try omega.
rewrite Nat2Z.id; auto.
Qed.

Hint Rewrite Int.bits_or using omega : testbit.
Hint Rewrite Int.bits_shl using omega : testbit.
Hint Rewrite Int.bits_and using omega : testbit.
Hint Rewrite Int.bits_shru using omega : testbit.
Hint Rewrite Int.unsigned_repr using omega : testbit.
Hint Rewrite Int.testbit_repr using omega : testbit.
Hint Rewrite if_false using omega : testbit.
Hint Rewrite if_true using omega : testbit.
Hint Rewrite Z.ones_spec_low using omega : testbit.
Hint Rewrite Z.ones_spec_high using omega : testbit.
Hint Rewrite orb_false_r orb_true_r andb_false_r andb_true_r : testbit.
Hint Rewrite orb_false_l orb_true_l andb_false_l andb_true_l : testbit.
Hint Rewrite Z.add_simpl_r : testbit.
Hint Rewrite Int.unsigned_repr using repable_signed : testbit.

Lemma Ztest_Inttest:
 forall a, Z.testbit (Int.unsigned a) = Int.testbit a.
Proof. reflexivity. Qed.
Hint Rewrite Ztest_Inttest : testbit.

Definition swap (i: int) : int :=
 Int.or (Int.shl (Int.and i (Int.repr 255)) (Int.repr 24))
   (Int.or (Int.shl (Int.and (Shr 8 i) (Int.repr 255)) (Int.repr 16))
      (Int.or (Int.shl (Int.and (Shr 16 i) (Int.repr 255)) (Int.repr 8))
         (Shr 24 i))).

Lemma swap_swap: forall w, swap (swap w) = w.
Proof.
unfold swap, Shr; intros.
apply Int.same_bits_eq; intros.
assert (Int.zwordsize=32) by reflexivity.
change 255 with (Z.ones 8).
assert (32 < Int.max_unsigned) by (compute; auto).
autorewrite with testbit.
if_tac; [if_tac; [if_tac | ] | ]; autorewrite with testbit; f_equal; omega.
Qed.

Lemma map_swap_involutive:
 forall l, map swap (map swap l)  = l.
Proof. intros.
 rewrite map_map. 
 replace (fun x => swap (swap x)) with (@Datatypes.id int).
 apply map_id. extensionality x. symmetry; apply swap_swap.
Qed.

Lemma isbyteZ_testbit:
  forall i j, 0 <= i < 256 -> j >= 8 -> Z.testbit i j = false.
Proof.
intros; erewrite Byte.Ztestbit_above with (n:=8%nat); auto.
Qed.

Lemma length_intlist_to_Zlist:
  forall l, length (intlist_to_Zlist l) = (4 * length l)%nat.
Proof.
induction l.
simpl. reflexivity. simpl. omega.
Qed.

Lemma Zlength_intlist_to_Zlist: forall l,
  Zlength (intlist_to_Zlist l) = WORD*Zlength l.
Proof.
intros. repeat rewrite Zlength_correct. rewrite length_intlist_to_Zlist.
rewrite Nat2Z.inj_mul. reflexivity.
Qed.

Lemma intlist_to_Zlist_Z_to_int_cons:
  forall a b c d l, 
      isbyteZ a -> isbyteZ b -> isbyteZ c -> isbyteZ d ->
     intlist_to_Zlist (Z_to_Int a b c d :: l) = 
     a::b::c::d:: intlist_to_Zlist l.
Proof.
intros. simpl.
unfold isbyteZ in *.
assert (Int.zwordsize=32)%Z by reflexivity.
unfold Z_to_Int, Shr; simpl.
change 255%Z with (Z.ones 8).
repeat f_equal; auto;
match goal with |- _ = ?A => transitivity (Int.unsigned (Int.repr A));
   [f_equal | apply Int.unsigned_repr; repable_signed]
end;
apply Int.same_bits_eq; intros;
autorewrite with testbit.
*
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
rewrite (isbyteZ_testbit b) by omega.
rewrite (isbyteZ_testbit c) by omega.
rewrite (isbyteZ_testbit d) by omega.
autorewrite with testbit; auto.
*
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
rewrite (isbyteZ_testbit c) by omega.
rewrite (isbyteZ_testbit d) by omega.
autorewrite with testbit; auto.
*
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
rewrite (isbyteZ_testbit d) by omega.
autorewrite with testbit; auto.
*
destruct (zlt i 8); autorewrite with testbit;  [ | symmetry; apply isbyteZ_testbit; omega].
auto.
Qed.

Lemma Zlist_to_intlist_to_Zlist:
  forall nl: list Z, 
  NPeano.divide (Z.to_nat WORD) (length nl) ->
  Forall isbyteZ nl ->
  intlist_to_Zlist (Zlist_to_intlist nl) = nl.
Proof.
intros nl [k H].
revert nl H; induction k; intros.
destruct nl; inv H; reflexivity.
simpl in H.
destruct nl as [ | a [ | b [ | c [ | d ?]]]]; inv H.
inv H0. inv H4. inv H5. inv H6.
unfold Zlist_to_intlist; fold Zlist_to_intlist.
rewrite intlist_to_Zlist_Z_to_int_cons by auto.
repeat f_equal; auto.
Qed.

Lemma intlist_to_Zlist_to_intlist:
  forall il: list int,
   Zlist_to_intlist (intlist_to_Zlist il) = il.
Proof.
induction il.
reflexivity.
simpl.
f_equal; auto. clear.
assert (Int.zwordsize=32)%Z by reflexivity.
unfold Z_to_Int, Shr; simpl.
change 255%Z with (Z.ones 8).
apply Int.same_bits_eq; intros.
rewrite Int.repr_unsigned.
autorewrite with testbit.
if_tac; autorewrite with testbit; [ | f_equal; omega].
if_tac; autorewrite with testbit; [ | f_equal; omega].
if_tac; autorewrite with testbit; [ | f_equal; omega].
auto.
Qed.

Lemma length_Zlist_to_intlist: forall n l, 
       length l = (Z.to_nat WORD * n)%nat -> 
       length (Zlist_to_intlist l) = n.
Proof.
induction n; intros.
destruct l; inv H; reflexivity.
replace (S n) with (1 + n)%nat in H by omega.
rewrite mult_plus_distr_l in H.
destruct l as [|i0 l]; [ inv H |].
destruct l as [|i1 l]; [ inv H |].
destruct l as [|i2 l]; [ inv H |].
destruct l as [|i3 l]; [ inv H |].
simpl. f_equal. apply IHn. forget (Z.to_nat WORD * n)%nat as A. inv H; auto.
Qed.

Lemma big_endian_integer_ext:
 forall f f', (forall z, (0 <= z < WORD)%Z -> f z = f' z) ->
    big_endian_integer f = big_endian_integer f'.
Proof.
unfold big_endian_integer;
intros.
repeat f_equal; intros; apply H; repeat split; computable.
Qed.

Lemma nth_big_endian_integer:
  forall i bl w, 
   nth_error bl i = Some w ->
    w = big_endian_integer
                 (fun z : Z =>
                  force_int
                    (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist bl)))
                       (z + Z.of_nat i * WORD))).
Proof.
induction i; destruct bl; intros; inv H.
*
 simpl.
 unfold big_endian_integer; simpl.
 repeat rewrite Int.repr_unsigned.
 assert (Int.zwordsize=32)%Z by reflexivity.
 unfold Z_to_Int, Shr; simpl.
 change 255%Z with (Z.ones 8).
 apply Int.same_bits_eq; intros;
 autorewrite with testbit.
 if_tac; simpl.
 if_tac; simpl.
 if_tac; simpl; autorewrite with testbit. auto. f_equal; omega.
 rewrite if_false by omega. autorewrite with testbit. f_equal; omega.
 rewrite if_false by omega. rewrite if_false by omega.
 autorewrite with testbit. f_equal; omega.
*
specialize (IHi _ _ H1).
rewrite IHi; clear IHi.
apply big_endian_integer_ext; intros j ?.
f_equal.
rewrite inj_S.
unfold Z.succ.
unfold ZnthV.
assert (i < length bl)%nat.
revert w bl H1; induction i; destruct bl; intros; inv H1; simpl; try omega.
apply IHi in H2. omega.
clear w H1.
if_tac; [rewrite if_true by (unfold WORD in *; omega) | rewrite if_false by (unfold WORD in *; omega)]; auto.
simpl default_val.
rewrite Z.mul_add_distr_r.
rewrite Z.mul_1_l.
simpl.
assert (Z.to_nat (j + (Z.of_nat i * WORD + WORD)) = (Z.to_nat WORD) + Z.to_nat (j + Z.of_nat i * WORD))%nat.
repeat rewrite Z2Nat.inj_add by (unfold WORD in *; omega).
simpl Z.to_nat; unfold WORD in *. omega.
rewrite H2. simpl.
auto.
Qed.

Local Open Scope nat.

Definition LBLOCK : nat := Z.to_nat LBLOCKz.   
Definition CBLOCK : nat := Z.to_nat CBLOCKz.
Opaque LBLOCK CBLOCK.

Lemma LBLOCK_zeq: Z.of_nat LBLOCK = 16%Z.
Proof. reflexivity. Qed.

Lemma CBLOCK_zeq: (Z.of_nat CBLOCK = 64%Z).
Proof. reflexivity. Qed.

Lemma LBLOCKz_nonneg: (0 <= LBLOCKz)%Z.
Proof. change LBLOCKz with 16%Z; omega. Qed.
Hint Resolve LBLOCKz_nonneg.

Lemma LBLOCKz_pos: (0 < LBLOCKz)%Z.
Proof. change LBLOCKz with 16%Z; omega. Qed.
Hint Resolve LBLOCKz_pos.

Lemma CBLOCKz_nonneg: (0 <= CBLOCKz)%Z.
Proof. change CBLOCKz with 64%Z; omega. Qed.
Hint Resolve CBLOCKz_nonneg.

Lemma CBLOCKz_pos: (0 < CBLOCKz)%Z.
Proof. change CBLOCKz with 64%Z; omega. Qed.
Hint Resolve CBLOCKz_pos.

Fixpoint sequence (cs: list statement) s :=
 match cs with
 | nil => s
 | c::cs' => Ssequence c (sequence cs' s)
 end.

Fixpoint rsequence (cs: list statement) s :=
 match cs with
 | nil => s
 | c::cs' => Ssequence (rsequence cs' s) c
 end.

Lemma sequence_rsequence:
 forall Espec Delta P cs s0 s R, 
    @semax Espec Delta P (Ssequence s0 (sequence cs s)) R  <->
  @semax Espec Delta P (Ssequence (rsequence (rev cs) s0) s) R.
Proof.
intros.
revert Delta P R s0 s; induction cs; intros.
simpl. apply iff_refl.
simpl.
rewrite seq_assoc.
rewrite IHcs; clear IHcs.
replace (rsequence (rev cs ++ [a]) s0) with
    (rsequence (rev cs) (Ssequence s0 a)); [apply iff_refl | ].
revert s0 a; induction (rev cs); simpl; intros; auto.
rewrite IHl. auto.
Qed.

Lemma seq_assocN:  
  forall {Espec: OracleKind},
   forall Q Delta P cs s R,
        @semax Espec Delta P (sequence cs Sskip) (normal_ret_assert Q) ->
         @semax Espec 
       (update_tycon Delta (sequence cs Sskip)) Q s R ->
        @semax Espec Delta P (sequence cs s) R.
Proof.
intros.
rewrite semax_skip_seq.
rewrite sequence_rsequence.
rewrite semax_skip_seq in H.
rewrite sequence_rsequence in H.
rewrite <- semax_seq_skip in H.
eapply semax_seq'; [apply H | ].
eapply semax_extensionality_Delta; try apply H0.
clear.
revert Delta; induction cs; simpl; intros.
apply expr_lemmas.tycontext_sub_refl.
eapply semax_lemmas.tycontext_sub_trans; [apply IHcs | ].
clear.
revert Delta; induction (rev cs); simpl; intros.
apply expr_lemmas.tycontext_sub_refl.
apply expr_lemmas.update_tycon_sub.
apply IHl.
Qed.

Fixpoint sequenceN (n: nat) (s: statement) : list statement :=
 match n, s with 
 | S n', Ssequence a s' => a::sequenceN n' s'
 | _, _ => nil
 end.

Lemma intlist_to_Zlist_app:
 forall al bl, intlist_to_Zlist (al++bl) = intlist_to_Zlist al ++ intlist_to_Zlist bl.
Proof. intros; induction al; simpl; auto. repeat f_equal; auto. Qed.

Lemma firstn_app:
 forall {A} n m (al: list A), firstn n al ++ firstn m (skipn n al) =
  firstn (n+m) al.
Proof. induction n; destruct al; intros; simpl; auto.
destruct m; reflexivity.
f_equal; auto.
Qed.

Lemma datablock_local_facts:
 forall sh f data,
  data_block sh f data |-- prop (isptr data /\ Forall isbyteZ f).
Proof.
intros. unfold data_block.
simpl.
entailer.
Qed.
Hint Resolve datablock_local_facts : saturate_local.

Lemma nth_skipn:
  forall A i n data (d:A),
       nth i (skipn n data) d = nth (i+n) data d.
Proof.
intros.
revert i data; induction n; simpl; intros.
f_equal; omega.
destruct data; auto.
destruct i; simpl; auto.
rewrite IHn.
replace (i + S n) with (S (i + n)) by omega; auto.
Qed.

Lemma array_at_ext':
  forall t sh (f f': Z -> reptype t) lo lo' hi hi',
    (forall i : Z, (lo <= i < hi)%Z -> f i = f' i) ->
   lo=lo' -> hi=hi' ->
   array_at t sh f lo hi = array_at t sh f' lo' hi'.
Proof.
intros.
rewrite (array_at_ext t sh f f' lo hi); auto.
f_equal; auto.
Qed.


Lemma Forall_app :
forall {A} P (l1 l2 :list A),
Forall P (l1 ++ l2) <->
Forall P l1 /\ Forall P l2.
intros.
split; induction l1; intros.
inv H. destruct l2; inv H0. auto.
split. auto. simpl in H2. inv H2.
constructor; auto.
split. inv H. constructor; auto. apply IHl1 in H3.
intuition.
inv H. apply IHl1 in H3. intuition.
simpl. intuition.
simpl. constructor.
destruct H. inv H. auto.
apply IHl1. intuition.
inv H0; auto.
Qed.

Lemma split2_data_block:
  forall n sh data d,
  n <= length data ->
  data_block sh data d = 
  (!! offset_in_range (sizeof tuchar * Zlength data) d &&
  data_block sh (firstn n data) d *
  data_block sh (skipn n data) (offset_val (Int.repr (Z.of_nat n)) d))%logic.
Proof.
  intros.
  assert (isptr d \/ ~isptr d) by (clear; destruct d; simpl; intuition).
  destruct H0; [ | apply pred_ext; entailer].
  unfold data_block.
  remember (sizeof tuchar) as TU.
  simpl.
  normalize.
  subst TU.
  rewrite prop_and.
  rewrite (andp_comm (prop (offset_in_range (sizeof tuchar * Zlength data) d))).
  rewrite andp_assoc.
  f_equal.
  Focus 1. {
    f_equal.
    apply prop_ext.
    repeat rewrite <- Forall_app.
    rewrite firstn_skipn.
    intuition.
  } Unfocus.
  match goal with
  | |- ?A = _ => rewrite (add_andp A (!!offset_in_range (sizeof tuchar * Zlength data) d)%logic)
  end;
    [| unfold array_at; simpl (sizeof tuchar); rewrite !Zmult_1_l; normalize].
  rewrite andp_comm.

  rewrite split_offset_array_at with (lo :=Z.of_nat n);
    [| rewrite Zlength_correct; omega| simpl; omega | reflexivity].
  rewrite andp_comm.
  erewrite <- add_andp by entailer!.
  assert (offset_in_range (sizeof tuchar * 0) d) by
    (destruct d; simpl; auto; unfold offset_in_range; pose proof Int.unsigned_range i; omega).
  normalize.
  clear H1.
  f_equal.
  f_equal.

  + apply equal_f; apply array_at_ext'; intros; auto.
    unfold tuchars, ZnthV.
    repeat rewrite if_false by omega.
    repeat rewrite map_map.
    repeat rewrite @nth_map' with (d':=0%Z).
    rewrite nth_firstn_low; auto.
    rewrite <- (Z2Nat.id i) in H1 by omega.
    destruct H1 as [_ ?].
    apply Nat2Z.inj_lt in H1.
    omega.
    rewrite firstn_length.
    rewrite min_l by omega.
    rewrite <- (Z2Nat.id i) in H1 by omega.
    destruct H1 as [_ ?].
    apply Nat2Z.inj_lt in H1.
    omega.
    rewrite <- (Z2Nat.id i) in H1 by omega.
    destruct H1 as [_ ?].
    apply Nat2Z.inj_lt in H1.
    omega.
    rewrite Zlength_correct.
    rewrite firstn_length.
    f_equal.
    rewrite min_l by omega.
    auto.
  + replace (Int.repr (Z.of_nat n)) with (Int.repr (sizeof tuchar * Z.of_nat n))
      by (rewrite sizeof_tuchar; rewrite Z.mul_1_l; auto).
    apply equal_f; apply array_at_ext'; intros; auto.
    unfold tuchars, ZnthV.
    repeat rewrite if_false by omega.
    repeat rewrite map_map.
    repeat rewrite @nth_map' with (d':=0%Z).
    f_equal. f_equal.
    rewrite nth_skipn; auto.
    f_equal.
    rewrite Z2Nat.inj_add by omega.
    rewrite Nat2Z.id.
    reflexivity.
    rewrite skipn_length.
    destruct H1.
    rewrite Zlength_correct in H2.
    rewrite <- Nat2Z.inj_sub in H2 by omega.
    rewrite <- (Z2Nat.id i) in H2 by omega.
    apply Nat2Z.inj_lt in H2; auto.
    rewrite <- (Z2Nat.id i) in H1 by omega.
    destruct H1.
    rewrite Zlength_correct in H2.
    rewrite <- Nat2Z.inj_sub in H2 by omega.
    apply Nat2Z.inj_lt in H2.
    omega.
    assert (i + Z.of_nat n < Zlength data)%Z by omega.
    rewrite <- (Z2Nat.id (i + Z.of_nat n)) in H2 by omega.
    rewrite Zlength_correct in H2.
    apply Nat2Z.inj_lt in H2; auto.
    rewrite !Zlength_correct.
    rewrite skipn_length by omega.
    rewrite <- Nat2Z.inj_sub by omega.
    f_equal.
Qed.

Lemma firstn_firstn: forall {A} lo n (data: list A), firstn lo (firstn (lo + n) data) = firstn lo data.
Proof.
  intros.
  revert data; induction lo; intros.
  + reflexivity.
  + destruct data; simpl; [reflexivity |].
    rewrite IHlo.
    reflexivity.
Qed.

Lemma skipn_firstn: forall {A} lo n (data: list A), skipn lo (firstn (lo + n) data) = firstn n (skipn lo data).
Proof.
  intros.
  revert data; induction lo; intros.
  + reflexivity.
  + destruct data; simpl.
    - destruct n; reflexivity.
    - apply IHlo.
Qed.

Lemma split3_data_block:
  forall lo n sh data d,
  lo+n <= length data ->
  data_block sh data d = 
  (!! offset_in_range (sizeof tuchar * Zlength data) d &&
  (data_block sh (firstn lo data) d *
  data_block sh (firstn n (skipn lo data)) (offset_val (Int.repr (Z.of_nat lo)) d) *
  data_block sh (skipn (lo+n) data)  (offset_val (Int.repr (Z.of_nat (lo+n))) d)))%logic.
Proof.
  intros.
  rewrite split2_data_block with (n := lo + n) by omega.
  rewrite split2_data_block with (n := lo) (data := firstn (lo + n) data) by
    (rewrite firstn_length; rewrite Min.min_l by omega; omega).
  assert (!!offset_in_range (sizeof tuchar * Zlength data) d |-- 
    !! offset_in_range (sizeof tuchar * Zlength (firstn (lo + n) data)) d)%logic.
    remember (sizeof tuchar) as ST; normalize; subst ST.
    apply offset_in_range_mid with (lo := 0%Z) (hi := Zlength data); try assumption.
    rewrite !Zlength_correct.
    rewrite firstn_length; rewrite Min.min_l by omega. split; try omega.
    apply inj_le, H.
    rewrite Zmult_0_r.
    unfold offset_in_range; destruct d; auto.
    pose proof Int.unsigned_range i; omega.
  rewrite (add_andp _ _ H0) at 2.
  normalize.
  f_equal.
  f_equal.
  f_equal; f_equal.
  apply firstn_firstn.
  apply skipn_firstn.
Qed.

Lemma divide_length_app:
 forall {A} n (al bl: list A), 
      (n | Zlength al) -> 
      (n | Zlength bl) ->
      (n | Zlength (al++bl)).
Proof.
 intros. destruct H,H0. exists (x+x0)%Z.
 rewrite initial_world.Zlength_app,H,H0;  
 rewrite Z.mul_add_distr_r; omega.
Qed.

(*** Application of Omega stuff ***)

Lemma CBLOCK_eq: CBLOCK=64%nat.
Proof. reflexivity. Qed.
Lemma LBLOCK_eq: LBLOCK=16%nat.
Proof. reflexivity. Qed.

Ltac helper2 := 
 match goal with
   | |- context [CBLOCK] => add_nonredundant (CBLOCK_eq)
   | |- context [LBLOCK] => add_nonredundant (LBLOCK_eq)
  end.

(*** End Omega stuff ***)

Ltac Omega1 := Omega (helper1 || helper2).

Local Open Scope Z.

Local Open Scope logic.

Lemma mapsto_tuchar_isbyteZ:
  forall sh v i, mapsto sh tuchar v (Vint i) =
    !! (0 <= Int.unsigned i < 256)%Z && mapsto sh tuchar v (Vint i).
Proof.
intros. apply mapsto_value_range.
Qed.

Lemma array_at_tuchar_isbyteZ:
 forall sh dd n v,
 array_at tuchar sh (ZnthV tuchar (map Vint dd)) 0 (Z.of_nat n) v =
  !! Forall isbyteZ (firstn n (map Int.unsigned dd)) &&
 array_at tuchar sh (ZnthV tuchar (map Vint dd)) 0 (Z.of_nat n) v.
Proof.
intros.
apply pred_ext; [ | normalize].
apply andp_right; auto.
saturate_local.
revert v Pv dd; induction n; intros.
simpl. apply prop_right; constructor.
rewrite inj_S. unfold Z.succ.
destruct dd; simpl.
apply prop_right; constructor.
apply derives_trans with (!! isbyteZ (Int.unsigned i) && !! Forall isbyteZ (firstn n (map Int.unsigned dd)));
  [ | normalize].
apply andp_right.
* (* first byte *)
clear IHn.
unfold ZnthV at 1. 
unfold array_at; normalize. unfold rangespec, rangespec'.
rewrite Z.sub_0_r.
unfold nat_of_Z.
rewrite Z2Nat.inj_add by omega.
simpl Z.to_nat.
rewrite Nat2Z.id. replace (n+1)%nat with (S n) by omega.
rewrite if_false by omega.
simpl nth.
apply derives_trans with (data_at sh tuchar (Vint i) (add_ptr_int tuchar v 0) * TT).
cancel.
unfold data_at. simpl. unfold eq_rect_r; simpl.
destruct v; inv Pv. unfold add_ptr_int;  simpl.
forget  (Int.add i0 (Int.mul (Int.repr (align 1 1)) (Int.repr 0))) as z.
unfold spacer; simpl. normalize.
clear.
fold tuchar.
rewrite mapsto_tuchar_isbyteZ.
normalize. apply prop_right; split; auto.
* (* rest of bytes, using induction hyp *)
rewrite split_offset_array_at with (lo := 1); [| omega | simpl; omega | reflexivity].
normalize.
apply derives_trans with (TT *  !!Forall isbyteZ (firstn n (map Int.unsigned dd))); auto.
apply sepcon_derives; auto.
replace v with (offset_val (Int.repr (sizeof tuchar * -1)) (offset_val (Int.repr 1%Z) v))
 by (destruct v; inv Pv; simpl; f_equal; normalize).
eapply derives_trans; [ | apply (IHn (offset_val (Int.repr 1) v)); normalize].
apply derives_refl'. 
replace (offset_val (Int.repr 1)
        (offset_val (Int.repr (sizeof tuchar * -1))
           (offset_val (Int.repr 1) v))) with (offset_val (Int.repr 1) v).
apply equal_f. apply array_at_ext'; intros; try omega.
unfold ZnthV. if_tac. omega. if_tac; try omega.
replace (Z.to_nat (i0 + 1)) with (S (Z.to_nat i0)).
simpl. auto.
replace (i0 + 1)%Z with (1+i0)%Z by omega.
rewrite Z2Nat.inj_add by omega. simpl.  auto.

 destruct v; auto.
 unfold offset_val, Int.add.
 f_equal.
 rewrite !Int.unsigned_repr_eq.
 rewrite Zplus_mod_idemp_r.
 rewrite Zplus_mod_idemp_l.
 change (1 mod Int.modulus) with 1.
 simpl.
 replace (Int.unsigned i0 + 1 + -1) with (Int.unsigned i0) by omega.
 rewrite <- Int.unsigned_repr_eq.
 rewrite Int.repr_unsigned.
 reflexivity.

clear.
rewrite <- (andp_TT (!! _)).
normalize.
Qed.

Lemma isbyte_intlist_to_Zlist : forall l, Forall isbyteZ (intlist_to_Zlist l).
Proof.
induction l; simpl; intros.
constructor.
assert (forall i, Int.unsigned (Int.and i (Int.repr 255)) < 256).
clear; intro.
eapply Z.lt_le_trans.
apply (Int.and_interval i (Int.repr (Z.ones 8))).
change (Int.size  (Int.repr (Z.ones 8))) with 8.
rewrite Zmin_spec.
if_tac.
eapply Z.le_trans with (two_p 8).
apply two_p_monotone. 
split; [ | omega].
apply Int.size_range.
compute; congruence.
compute; congruence.
unfold Shr, isbyteZ; repeat constructor; try apply Int.unsigned_range; auto; clear IHl.
rewrite <- (Int.divu_pow2 a (Int.repr (2 ^ 24)) (Int.repr 24) (eq_refl _)).
unfold Int.divu.
rewrite Int.unsigned_repr.
rewrite Int.unsigned_repr by (compute; split; congruence).
apply Z.div_lt_upper_bound.
compute; congruence.
change (2 ^ 24 * 256)%Z with (Int.modulus).
apply Int.unsigned_range.
split.
apply Z.div_pos.
apply Int.unsigned_range.
rewrite Int.unsigned_repr.
compute; congruence.
compute; split; congruence.
apply Z.div_le_upper_bound.
compute; congruence.
apply Z.le_trans with (Int.modulus+1).
destruct (Int.unsigned_range a).
omega.
compute; congruence.
Qed.

Lemma isbyte_intlist_to_Zlist' : forall l,
   Forall isbyteZ (map Int.unsigned (map Int.repr (intlist_to_Zlist l))).
Proof.
intro.
replace (map Int.unsigned (map Int.repr (intlist_to_Zlist l))) with (intlist_to_Zlist l).
apply isbyte_intlist_to_Zlist.
induction l; simpl; auto.
repeat f_equal; auto; symmetry; apply Int.repr_unsigned.
Qed.

Lemma Forall_isbyte_repr_unsigned:
 forall l: list int, map Int.repr (map Int.unsigned l) = l.
Proof.
induction l; intros.
reflexivity.
simpl.
f_equal; auto.
apply Int.repr_unsigned.
Qed.

Lemma map_unsigned_repr_isbyte:
  forall l : list Z , Forall isbyteZ l -> map Int.unsigned (map Int.repr l) = l.
Proof. induction l; simpl; intros; auto.
  inv H. f_equal; auto. unfold isbyteZ in H2; apply Int.unsigned_repr. 
 assert (Int.max_unsigned > 256)%Z by computable.
 omega.
Qed.

Lemma int_unsigned_inj: forall a b, Int.unsigned a = Int.unsigned b -> a=b.
Proof.
intros.
rewrite <- (Int.repr_unsigned a); rewrite <- (Int.repr_unsigned b).
congruence.
Qed.

Lemma intlist_to_Zlist_inj: forall al bl, intlist_to_Zlist al = intlist_to_Zlist bl -> al=bl.
Proof.
induction al; destruct bl; intros; auto.
inv H.
inv H.
simpl in H.
injection H; intros.
f_equal; auto.
clear - H1 H2 H3 H4.
rename i into b.
apply int_unsigned_inj in H1.
apply int_unsigned_inj in H2.
apply int_unsigned_inj in H3.
apply int_unsigned_inj in H4.
unfold Shr in *.
apply Int.same_bits_eq; intros.
assert (Int.zwordsize=32)%Z by reflexivity.
change 255%Z with (Z.ones 8) in *.
destruct (zlt i 8).
transitivity (Int.testbit (Int.and a (Int.repr (Z.ones 8))) i).
autorewrite with testbit; auto.
rewrite H1. autorewrite with testbit; auto.
destruct (zlt i 16).
transitivity (Int.testbit (Int.and (Int.shru a (Int.repr 8)) (Int.repr (Z.ones 8))) (i-8)).
autorewrite with testbit.
change (Int.unsigned (Int.repr 8)) with 8%Z.
rewrite Z.sub_add; auto.
rewrite H2.
autorewrite with testbit.
rewrite Z.sub_add. auto.
destruct (zlt i 24).
transitivity (Int.testbit (Int.and (Int.shru a (Int.repr 16)) (Int.repr (Z.ones 8))) (i-16)).
autorewrite with testbit.
change (Int.unsigned (Int.repr 16)) with 16%Z.
rewrite Z.sub_add. auto.
rewrite H3.
autorewrite with testbit.
change (Int.unsigned (Int.repr 16)) with 16%Z.
rewrite Z.sub_add. auto.
transitivity (Int.testbit (Int.shru a (Int.repr 24)) (i-24)).
autorewrite with testbit.
change (Int.unsigned (Int.repr 24)) with 24%Z.
rewrite Z.sub_add. auto.
rewrite H4.
autorewrite with testbit.
change (Int.unsigned (Int.repr 24)) with 24%Z.
rewrite Z.sub_add. auto.
Qed.

Lemma Zlength_intlist_to_Zlist_app:
 forall al bl,  Zlength (intlist_to_Zlist (al++bl)) =
    (Zlength (intlist_to_Zlist al) + Zlength (intlist_to_Zlist bl))%Z.
Proof.
induction al; simpl; intros; auto.
repeat rewrite Zlength_cons.
rewrite IHal.
omega.
Qed.

Lemma data_block_isbyteZ:
 forall sh data v, data_block sh data v = !! Forall isbyteZ data && data_block sh data v.
Proof.
unfold data_block; intros.
simpl.
normalize.
f_equal. f_equal. apply prop_ext. intuition.
Qed.

Lemma Forall_firstn:
  forall A (f: A -> Prop) n l, Forall f l -> Forall f (firstn n l).
Proof.
induction n; destruct l; intros.
constructor. constructor. constructor.
inv H. simpl. constructor; auto.
Qed.

Lemma Forall_skipn:
  forall A (f: A -> Prop) n l, Forall f l -> Forall f (skipn n l).
Proof.
induction n; destruct l; intros.
constructor. inv H; constructor; auto. constructor.
inv H. simpl.  auto.
Qed.

Local Open Scope Z.

Lemma hilo_lemma:
  forall hi lo, [Int.repr (hilo hi lo / Int.modulus), Int.repr (hilo hi lo)] = [hi, lo].
Proof.
unfold hilo; intros.
rewrite Z.div_add_l by computable.
rewrite Zdiv_small by apply Int.unsigned_range.
rewrite Z.add_0_r.
rewrite Int.repr_unsigned.
f_equal.
f_equal.
rewrite <- add_repr.
rewrite <- mul_repr.
replace (Int.repr Int.modulus) with (Int.repr 0).
rewrite Int.mul_zero. rewrite Int.add_zero_l. apply Int.repr_unsigned.
apply Int.eqm_samerepr.
unfold Int.eqm.
change 0 with (Int.modulus mod Int.modulus).
apply Int.eqmod_sym.
apply Int.eqmod_mod.
computable.
Qed.

Lemma Forall_isbyteZ_unsigned_repr:
 forall l, Forall isbyteZ l -> Forall isbyteZ (map Int.unsigned (map Int.repr l)).
Proof. induction 1. constructor.
constructor. rewrite Int.unsigned_repr; auto.
unfold isbyteZ in H; repable_signed.
apply IHForall.
Qed.

Lemma cVint_force_int_ZnthV:
 forall sh contents hi, 
  (hi <= Zlength contents)%Z ->
  array_at tuchar sh (cVint (force_int oo ZnthV tuchar (map Vint contents))) 0 hi = 
  array_at tuchar sh (ZnthV tuchar (map Vint contents)) 0 hi.
Proof.
unfold ZnthV; simpl.
intros.
apply array_at_ext; intros.
unfold cVint,Basics.compose.
if_tac. omega.
assert (Z.to_nat i < length contents)%nat.
apply Nat2Z.inj_lt.
rewrite <- Zlength_correct; rewrite Z2Nat.id by omega.
omega.
clear - H2; revert contents H2; induction (Z.to_nat i); intros; destruct contents; 
simpl in *; try omega; auto.
apply IHn. omega.
Qed.

Definition f_upto {t} (f: Z -> reptype t) (bound: Z) (i: Z) : reptype t :=
 if zlt i bound then f i else default_val t.

Lemma array_at_f_upto_lo:
  forall t sh contents lo hi, 
  array_at t sh (f_upto contents lo) lo hi = array_at_ t sh lo hi.
Proof.
intros; apply array_at_ext; intros.
unfold f_upto; if_tac; auto. omega.
Qed.

Lemma divide_hashed:
 forall (bb: list int), 
    NPeano.divide LBLOCK (length bb) <->
    (LBLOCKz | Zlength bb).
Proof.
intros; split; intros [n ?].
exists (Z.of_nat n). rewrite Zlength_correct, H.
rewrite Nat2Z.inj_mul; auto.
exists (Z.to_nat n).
rewrite Zlength_correct in H.
assert (0 <= n).
assert (0 <= n * LBLOCKz) by omega.
apply Z.mul_nonneg_cancel_r in H0; auto.
rewrite <- (Z2Nat.id (n*LBLOCKz)%Z) in H by omega.
apply Nat2Z.inj in H. rewrite H.
change LBLOCK with (Z.to_nat LBLOCKz).
rewrite Z2Nat.inj_mul; auto.
Qed.

Lemma hash_blocks_equation' : forall (r : registers) (msg : list int),
       hash_blocks r msg =
       match msg with
       | [] => r
       | _ :: _ => hash_blocks (hash_block r (firstn LBLOCK msg)) (skipn LBLOCK msg)
       end.
Proof. exact hash_blocks_equation. Qed.

Lemma hash_blocks_last:
 forall a bl c, 
              Zlength a = 8 ->
              (LBLOCKz | Zlength bl) -> 
              Zlength c = LBLOCKz ->
   hash_block (hash_blocks a bl) c = hash_blocks a (bl++ c).
Proof.
intros.
assert (POS: (0 < LBLOCK)%nat) by (rewrite LBLOCK_eq; omega).
apply divide_hashed in H0.
destruct H0 as [n ?].
rewrite Zlength_correct in H,H1.
change 8 with (Z.of_nat 8) in H.
(*change LBLOCK with 16%nat in H0.*)
change LBLOCKz with (Z.of_nat LBLOCK) in H1.
apply Nat2Z.inj in H. 
apply Nat2Z.inj in H1.
revert a bl H H0; induction n; intros.
destruct bl; inv H0.
rewrite hash_blocks_equation'. 
simpl. rewrite hash_blocks_equation'.
destruct c eqn:?. inv H1.
rewrite <- Heql in *; clear i l Heql.
rewrite firstn_same by omega.
replace (skipn LBLOCK c) with (@nil int).
rewrite hash_blocks_equation'; reflexivity.
pose proof (skipn_length LBLOCK c).
spec H0; [omega |]. rewrite H1 in H0.
destruct (skipn LBLOCK c); try reflexivity; inv H0.
replace (S n * LBLOCK)%nat with (n * LBLOCK + LBLOCK)%nat  in H0 by
  (simpl; omega).
rewrite hash_blocks_equation'.
destruct bl.
simpl in H0.
Psatz.lia.
forget (i::bl) as bl'; clear i bl. rename bl' into bl.
rewrite IHn.
symmetry.
rewrite hash_blocks_equation.
destruct bl.
simpl in H0; Psatz.lia.
unfold app at 1; fold app.
forget (i::bl) as bl'; clear i bl. rename bl' into bl.
f_equal.
f_equal.
apply firstn_app1.
Psatz.nia.
apply skipn_app1.
Psatz.nia.
apply length_hash_block; auto. (* fixme *) change 16%nat with LBLOCK.
rewrite firstn_length. apply min_l.
Psatz.nia.
rewrite skipn_length.
apply plus_reg_l with LBLOCK.
rewrite plus_comm. 
rewrite NPeano.Nat.sub_add by Psatz.lia.
omega.
(*Psatz.lia.*)
rewrite H0. assert (Hn: (n*LBLOCK >= 0)%nat).
  remember ((n * LBLOCK)%nat). clear. omega.
  omega. 
Qed.

Lemma length_hash_blocks: forall regs blocks,
  length regs = 8%nat ->
  (LBLOCKz | Zlength blocks) ->
  length (hash_blocks regs blocks) = 8%nat.
Proof.
intros.
destruct H0 as [n ?].
rewrite Zlength_correct in H0.
assert (POS := LBLOCKz_pos).
change LBLOCKz with (Z.of_nat LBLOCK) in *.
rewrite <- (Z2Nat.id n) in H0 
 by (apply -> Z.mul_nonneg_cancel_r ; [ | apply POS]; omega).
rewrite <- Nat2Z.inj_mul in H0.
apply Nat2Z.inj in H0.
revert regs blocks H H0; induction (Z.to_nat n); intros.
  destruct blocks; inv H0.
rewrite hash_blocks_equation'; auto.
destruct blocks.
destruct LBLOCK; inv POS; inv H0.
rewrite hash_blocks_equation'; auto.
forget (i::blocks) as bb.
apply IHn0; auto.
apply length_hash_block; auto. (* fixme *) change 16%nat with LBLOCK.
rewrite firstn_length. apply min_l. simpl in H0. Psatz.nia.
rewrite skipn_length. rewrite H0; clear - POS.  simpl.
rewrite plus_comm. rewrite NPeano.Nat.add_sub. auto.
simpl in H0. rewrite H0; clear - POS. Psatz.lia.
Qed.

Lemma nth_list_repeat: forall A i n (x :A),
    nth i (list_repeat n x) x = x.
Proof.
 induction i; destruct n; simpl; auto.
Qed.

Lemma map_list_repeat:
  forall A B (f: A -> B) n x,
     map f (list_repeat n x) = list_repeat n (f x).
Proof. induction n; simpl; intros; f_equal; auto.
Qed.

Lemma Forall_list_repeat:
  forall A (f: A -> Prop) n (x: A),
     f x -> Forall f (list_repeat n x).
Proof.
 intros; induction n; simpl; auto.
Qed.

Lemma ZtoNat_Zlength: 
 forall {A} (l: list A), Z.to_nat (Zlength l) = length l.
Proof.
intros. rewrite Zlength_correct. apply Nat2Z.id.
Qed.
Hint Rewrite @ZtoNat_Zlength : norm.

Lemma Zlength_nonneg:
 forall {A} (l: list A), 0 <= Zlength l.
Proof.
intros. rewrite Zlength_correct. omega.
Qed.


