Require Import floyd.proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha.
Require Export sha.pure_lemmas.

Global Opaque K256.

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

Lemma datablock_local_facts:
 forall sh f data,
  data_block sh f data |-- prop (isptr data /\ Forall isbyteZ f).
Proof.
intros. unfold data_block.
simpl.
entailer.
Qed.
Hint Resolve datablock_local_facts : saturate_local.

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

Local Open Scope nat.

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

(*** Application of Omega stuff ***)

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

Lemma data_block_isbyteZ:
 forall sh data v, data_block sh data v = !! Forall isbyteZ data && data_block sh data v.
Proof.
unfold data_block; intros.
simpl.
normalize.
f_equal. f_equal. apply prop_ext. intuition.
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

