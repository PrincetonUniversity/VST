Require Import floyd.proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha.
Require Export sha.pure_lemmas.
Export ListNotations.

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
               (firstn (Z.to_nat WORD) 
                 (skipn (i * Z.to_nat WORD) 
                   (map Int.repr (intlist_to_Zlist bl)))).
Proof.
induction i; destruct bl; intros; inv H.
*
 simpl.
 rewrite big_endian_integer4.
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
specialize (IHi _ _ H1); clear H1.
apply IHi.
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
intros. unfold data_block, array_at.
simpl.
entailer.
Qed.
Hint Resolve datablock_local_facts : saturate_local.

(*
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
*)

Require Import JMeq.

Lemma array_at_isptr:
  forall t sh f lo hi v p, array_at sh t f lo hi v p = (array_at sh t f lo hi v p && !! isptr p)%logic.
Proof.
intros.
apply pred_ext; intros.
apply andp_right; auto.
admit. (*  apply array_at_local_facts. *)
normalize.
Qed.

Lemma data_at_array_at0: forall sh t gfs t0 n a hi v v' p,
  (0 <= hi <= n)%Z ->
  legal_alignas_type t = true ->
  legal_nested_field t gfs ->
  nested_field_type2 t gfs = Tarray t0 n a ->
  nested_field_offset2 t (ArraySubsc 0 :: gfs) = 0 ->
  size_compatible t p ->
  align_compatible t p ->
  JMeq v v' ->
  data_at sh (Tarray t0 hi a) v' (offset_val (Int.repr (nested_field_offset2 t gfs)) p) =
    array_at sh t gfs 0 hi v p.
Proof.
  intros.
  revert v' H6.
  pattern hi at 1 2 3.
  replace hi with (hi - 0) by omega.
  intros.
  erewrite array_at_data_at; [| omega | | | eauto..]; [| omega ..].
  normalize.
  erewrite nested_field_offset2_Tarray by eauto.
  rewrite Z.mul_0_r, Z.add_0_r.
  reflexivity.
Qed.

Local Open Scope nat.
Lemma split_offset_array_at:
  forall n sh t len (contents: list (reptype t)) v,
  legal_alignas_type t = true ->
  (Z.of_nat n <= Zlength contents)%Z ->
  (Z.of_nat n <= len)%Z ->
  data_at sh (tarray t len) contents v =
  (!! (offset_in_range (sizeof t * 0) v) &&
   !! (offset_in_range (sizeof t * len) v) && 
  (data_at sh (tarray t (Z.of_nat n)) (firstn n contents) v * 
    data_at sh (tarray t (len- Z.of_nat n)) (skipn n contents) (offset_val (Int.repr (sizeof t * Z.of_nat n)) v)))%logic.
Proof.
  intros.
  apply extract_prop_from_equal' with (isptr v);
    [| rewrite data_at_isptr; normalize | rewrite data_at_isptr; normalize].
  intros.
  unfold data_at.
  simpl.
  match goal with
  | |- _ = ?A && _ => replace A with 
    (!!(size_compatible (tarray t len) v))%logic
  end.
  Focus 2. {
    unfold size_compatible, offset_in_range.
    destruct v; try solve [apply pred_ext; normalize].
    simpl.
    rewrite Z.max_r by omega.
    rewrite Z.mul_0_r, Z.add_0_r.
    pose proof Int.unsigned_range i.
    pose proof (sizeof_pos t).
    pose proof (Z.mul_nonneg_nonneg (sizeof t) len).
    spec H5; [omega |].
    spec H5; [omega |].
    apply pred_ext; normalize; omega.
  } Unfocus.
  destruct v; try inversion H2.
  unfold align_compatible, offset_val.
  unfold tarray.
  rewrite !legal_alignas_type_Tarray by (unfold legal_alignas_type; simpl; auto).
  normalize.
  rewrite !prop_and, !andp_assoc.
  apply extract_prop_from_equal. intros.
  rewrite (andp_comm ( !!size_compatible (Tarray t (Z.of_nat n) noattr) (Vptr b i))).
  rewrite !andp_assoc.
  apply extract_prop_from_equal. intros.
  assert (size_compatible (Tarray t (len - Z.of_nat n) noattr)
       (Vptr b (Int.add i (Int.repr (sizeof t * Z.of_nat n))))).
  Focus 1. {
    unfold size_compatible in *.
    simpl in H3 |- *.
    rewrite !Z.max_r in H3 |- * by omega.
    rewrite !Int.Z_mod_modulus_eq.
    pose proof (sizeof_pos t).
    pose proof (Z.mul_nonneg_nonneg (sizeof t) (Z.of_nat n)).
    spec H6; [omega | ].
    spec H6; [omega | ].
    pose proof Zmod_le (sizeof t * Z.of_nat n) Int.modulus.
    spec H7; [cbv; reflexivity |].
    spec H7; [omega |].
    pose proof Z_mod_lt (sizeof t * Z.of_nat n) Int.modulus.
    spec H8; [cbv; reflexivity |].
    pose proof Int.unsigned_range i.
    pose proof Zmod_le (Int.unsigned i + (sizeof t * Z.of_nat n) mod Int.modulus) Int.modulus.
    spec H10; [cbv; reflexivity |].
    spec H10; [omega |].
    assert (sizeof t * Z.of_nat n + sizeof t * (len - Z.of_nat n) = sizeof t * len)%Z
      by (rewrite <- Z.mul_add_distr_l; f_equal; omega).
    omega.
  } Unfocus.
  assert (alignof t | Int.unsigned (Int.add i (Int.repr (sizeof t * Z.of_nat n)))).
  Focus 1. {
    unfold align_compatible in *.
    simpl in H4 |- *.
    rewrite !Int.Z_mod_modulus_eq.
    admit. (* omega issure *)
  } Unfocus.
  assert (size_compatible (Tarray t (Z.of_nat n) noattr) (Vptr b i)).
  Focus 1. {
    simpl in H3 |- *.
    rewrite !Z.max_r in H3 |- * by omega.
    pose proof (sizeof_pos t).
    assert (sizeof t * Z.of_nat n <= sizeof t * len)%Z by (apply Zmult_le_compat_l; omega).
    omega.
  } Unfocus.
  normalize.
  rewrite split2_array_at' with (mid := Z.of_nat n) by omega.
  simpl.
  f_equal.
  + unfold array_at'; f_equal.
    apply rangespec_ext; intros.
    f_equal.
    unfold Znth; if_tac; [omega |].
    rewrite nth_firstn; [reflexivity |].
    destruct H8.
    rewrite Z.sub_0_r.
    apply Z2Nat.inj_lt in H10; try omega.
    rewrite Nat2Z.id in H10.
    exact H10.
  + unfold array_at', rangespec.
    simpl; f_equal.
    rewrite !Z.sub_0_r.
    apply rangespec'_shift; intros.
    admit.
Qed.

Lemma firstn_map {A B} (f:A -> B): forall n l, 
      firstn n (map f l) = map f (firstn n l).
Proof. intros n.
induction n; simpl; intros. trivial.
  destruct l; simpl. trivial.
  rewrite IHn. trivial.
Qed.

Lemma skipn_map {A B} (f:A -> B): forall n l, 
      skipn n (map f l) = map f (skipn n l).
Proof. intros n.
induction n; simpl; intros. trivial.
  destruct l; simpl. trivial.
  rewrite IHn. trivial.
Qed.

Lemma split2_data_block:
  forall n sh data d,
  n <= length data ->
  data_block sh data d = 
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof tuchar * Zlength data) d &&
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
  do 2 rewrite prop_and. rewrite <- andp_assoc.  rewrite <- (prop_and (Forall _ _)).
  replace (Forall isbyteZ (skipn n data) /\ Forall isbyteZ (firstn n data)) with (Forall isbyteZ data)
  by (apply prop_ext; rewrite and_comm; rewrite <- Forall_app; rewrite firstn_skipn; intuition).
 rewrite andp_assoc.
  f_equal.
  rewrite (split_offset_array_at n); auto;
  [ 
  | rewrite Zlength_correct, map_length, map_length; apply Nat2Z.inj_le; auto
  |  repeat rewrite Zlength_map; rewrite Zlength_correct; omega].
  f_equal.
 normalize.
simpl sizeof. rewrite Z.mul_1_l.
repeat rewrite Zlength_correct.
rewrite firstn_length. rewrite min_l by auto.
repeat rewrite firstn_map.
repeat rewrite skipn_map.
rewrite skipn_length by auto.
rewrite Nat2Z.inj_sub by omega.
auto.
Qed.

Lemma split3_data_block:
  forall lo n sh data d,
  lo+n <= length data ->
  data_block sh data d = 
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof tuchar * Zlength data) d &&
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
  f_equal. apply prop_ext; intuition.
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
 data_at sh (tarray tuchar (Z.of_nat n)) (map Vint dd) v =
  !! Forall isbyteZ (firstn n (map Int.unsigned dd)) &&
 data_at sh (tarray tuchar (Z.of_nat n)) (map Vint dd) v.
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
unfold data_at. simpl. normalize.
unfold array_at'. normalize. unfold rangespec, rangespec'.
rewrite Z.sub_0_r.
unfold nat_of_Z.
rewrite Z2Nat.inj_add by omega.
simpl Z.to_nat.
rewrite Nat2Z.id. replace (n+1)%nat with (S n) by omega.
unfold Znth.
rewrite if_false by omega.
simpl nth.
normalize.
apply derives_trans with (at_offset2 (mapsto sh (Tint I8 Unsigned noattr)) (0 + 1 * 0) (Vint i) v * TT); [cancel | ].
unfold at_offset2, at_offset'.
simpl.
rewrite mapsto_tuchar_isbyteZ.
entailer!. split; auto.
* (* rest of bytes, using induction hyp *)
rewrite split_offset_array_at with (n := 1%nat);
 [ |reflexivity | rewrite Zlength_cons, Zlength_correct; simpl; omega | simpl; omega].
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
apply equal_f. simpl Z.of_nat. rewrite Z.add_simpl_r.
simpl skipn. auto.
 destruct v; try contradiction.
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

(*
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
*)

Definition f_upto {t} (f: Z -> reptype t) (bound: Z) (i: Z) : reptype t :=
 if zlt i bound then f i else default_val t.

(*
Lemma array_at_f_upto_lo:
  forall t sh contents lo hi, 
  array_at t sh (f_upto contents lo) lo hi = array_at_ t sh lo hi.
Proof.
intros; apply array_at_ext; intros.
unfold f_upto; if_tac; auto. omega.
Qed.
*)

