Require Import floyd.proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha.
Require Export sha.pure_lemmas.
Require Export general_lemmas.
Export ListNotations.

Local Open Scope logic.

Global Opaque K256.

Transparent peq.

Lemma mapsto_tc_val:
  forall sh t p v,
  readable_share sh ->
  v <> Vundef ->
  mapsto sh t p v = !! tc_val t v && mapsto sh t p v .
Proof.
intros.
apply pred_ext.
apply andp_right; auto.
unfold mapsto; simpl.
destruct (access_mode t); try apply FF_left.
destruct (type_is_volatile t); try apply FF_left.
destruct p; try apply FF_left.
if_tac; try contradiction. apply orp_left.
normalize.
normalize.
congruence.
normalize.
Qed.

Definition data_offset : Z :=  (* offset, in bytes, of _data field in struct SHA256_state *)
  nested_field_offset2 t_struct_SHA256state_st [StructField _data].

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
                   (sublist (Z.of_nat i * WORD)
                        (Z.succ (Z.of_nat i) * WORD)
                   (map Int.repr (intlist_to_Zlist bl))).
Proof.
induction i; destruct bl; intros; inv H.
*
 unfold sublist; simpl.
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
simpl map.
rewrite IHi.
unfold sublist.
replace (Z.to_nat (Z.of_nat (S i) * WORD)) with (4 + Z.to_nat (Z.of_nat i * WORD))%nat
  by (rewrite plus_comm, inj_S; unfold Z.succ; rewrite Z.mul_add_distr_r;
        rewrite Z2Nat.inj_add by (change WORD with 4; omega); reflexivity).
rewrite <- skipn_skipn.
simpl skipn.
f_equal. f_equal. f_equal. rewrite inj_S.  unfold Z.succ. 
rewrite !Z.mul_add_distr_r; omega.
Qed.

Lemma Znth_big_endian_integer:
  forall i bl, 
   0 <= i < Zlength bl ->
   Znth i bl Int.zero =
     big_endian_integer 
                   (sublist (i * WORD) (Z.succ i * WORD)
                   (map Int.repr (intlist_to_Zlist bl))).
Proof.
intros.
unfold Znth.
 rewrite if_false by omega.
pose proof (nth_error_nth _ Int.zero (Z.to_nat i) bl).
rewrite <- (Z2Nat.id i) at 2 3 by omega.
apply nth_big_endian_integer.
apply H0.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by omega.
rewrite <- Zlength_correct; omega.
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
 forall Espec CS Delta P cs s0 s R, 
    @semax CS Espec Delta P (Ssequence s0 (sequence cs s)) R  <->
  @semax CS Espec Delta P (Ssequence (rsequence (rev cs) s0) s) R.
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
  forall {Espec: OracleKind} CS, 
   forall Q Delta P cs s R,
        @semax CS Espec Delta P (sequence cs Sskip) (normal_ret_assert Q) ->
         @semax CS Espec 
       (update_tycon Delta (sequence cs Sskip)) Q s R ->
        @semax CS Espec Delta P (sequence cs s) R.
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
apply tycontext_sub_refl.
eapply tycontext_sub_trans; [apply IHcs | ].
clear.
revert Delta; induction (rev cs); simpl; intros.
apply tycontext_sub_refl.
apply update_tycon_sub.
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

Require Import JMeq.

Lemma reptype_tarray {cs: compspecs}:
   forall t len, reptype (tarray t len) = list (reptype t).
Proof.
intros.
rewrite reptype_ind. simpl. reflexivity.
Qed.

(*
Lemma split_offset_array_at:
  forall n sh t len 
    (contents': (@zlist _ _ (list_zlist _ (default_val t)) 0 len))
    (contents: reptype (tarray t len))
    (contents1: reptype (tarray t n))
    (contents2: reptype (tarray t (len-n)))
    v,
    JMeq contents contents' ->
    JMeq contents1 (zl_sublist 0 n contents') ->
    JMeq contents2 (zl_shift 0 (len-n) (zl_sublist n len contents')) ->
   legal_alignas_type t = true ->
   (0 <= n <= len) ->
  data_at sh (tarray t len) contents v =
  (!! (offset_in_range (sizeof cenv_cs t * 0) v) &&
   !! (offset_in_range (sizeof cenv_cs t * len) v) && 
  (data_at sh (tarray t n) contents1 v * 
    data_at sh (tarray t (len- n)) contents2 (offset_val (Int.repr (sizeof cenv_cs t * n)) v)))%logic.
Admitted. 
Proof.
  intros.
 SearchAbout data_at array_at.
  apply extract_prop_from_equal' with (isptr v);
    [| rewrite data_at_isptr; normalize | rewrite data_at_isptr; normalize].
  intros.
  unfold data_at.
  simpl.
  normalize.
  apply prop_andp_ext'.
*
  unfold size_compatible, offset_in_range.
  destruct v; try contradiction H2.
  simpl.
  clear b H2.
  rewrite Z.max_r by omega.
  rewrite Z.max_r by omega.
  rewrite Z.max_r by omega.
  replace (Int.add i) with (Int.add (Int.repr (Int.unsigned i))) by (rewrite Int.repr_unsigned; auto).
  rewrite add_repr.
  pose proof (Int.unsigned_range i).
  forget (Int.unsigned i) as z; clear i.
  assert (0 <= Z.of_nat n)%Z by omega.
  forget (Z.of_nat n) as N. clear n.
  pose proof (sizeof_pos t).
  pose proof (Z.mul_nonneg_nonneg (sizeof t) N).
  spec H5; [omega |].
  spec H5; [omega |].
  assert (Int.max_unsigned + 1 = Int.modulus) by computable.
  assert (N = len \/ N < len) by omega.
  destruct H7.
+
   subst N. clear H1.
  intuition.
  rewrite Z.sub_diag.
  rewrite Z.mul_0_r. rewrite Z.add_0_r.
  pose proof (Int.unsigned_range (Int.repr (z + sizeof t * len))); omega.
  assert (z + sizeof t * len < Int.modulus \/ z + sizeof t * len = Int.modulus) by omega.
  destruct H10.
  - rewrite Int.unsigned_repr; try (unfold Int.max_unsigned; omega).
    apply Z.divide_add_r; auto.
    rewrite Z.mul_comm.
    apply Z.divide_mul_r; auto.
    apply legal_alignas_sizeof_alignof_compat; auto. (* legal_alignas_sizeof_alignof_compat's specificaltion is modified. *)
  - rewrite H10.
    apply Z.divide_0_r.
+
  assert (sizeof t = 0 \/ 0 < sizeof t) by omega.
  destruct H8.
  - rewrite H8 in *.
     repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r.
     intuition.
     pose proof (Int.unsigned_range (Int.repr z)); omega.
     rewrite Int.unsigned_repr; auto; omega.
 -
   assert (sizeof t * N < sizeof t * len)%Z
    by (   apply Zmult_lt_compat_l; omega).
  rewrite Z.mul_sub_distr_l.
  intuition.
  rewrite Int.unsigned_repr; try omega.
  rewrite Int.unsigned_repr; try omega.
  apply Z.divide_add_r; auto.
  rewrite Z.mul_comm.
  apply Z.divide_mul_r; auto.
  apply legal_alignas_sizeof_alignof_compat; auto.
*
  intros [? ?].
  rewrite split2_array_at' with (mid := Z.of_nat n) by omega.
  simpl.
  f_equal.
  + unfold array_at'; f_equal.
    apply rangespec_ext; intros.
    f_equal.
    unfold Znth; if_tac; [omega |].
    rewrite nth_firstn; [reflexivity |].
    rewrite Z.sub_0_r.
    destruct H5.
    apply Z2Nat.inj_lt in H7; try omega.
    rewrite Nat2Z.id in H7.
    exact H7.
  + unfold array_at', rangespec.
      normalize.
    rewrite !Z.sub_0_r.
    apply rangespec'_shift; intros.
    rewrite Z.sub_0_r in H6. subst i'.
    change nat_of_Z with Z.to_nat in H5.
    rewrite Z2Nat.id in H5 by omega.
    rewrite Z.sub_0_r.
    repeat rewrite Z.add_0_l.
    rewrite Nat2Z.id.
    forget (Znth (i - Z.of_nat n) (skipn n contents) (default_val t)) as c.
    rewrite data_at'_at_offset'; auto.
    symmetry.
    rewrite data_at'_at_offset'; auto.
    repeat rewrite at_offset'_eq.
    f_equal. rewrite offset_offset_val.
    f_equal.
    rewrite add_repr.
    f_equal.
    rewrite <- Z.mul_add_distr_l.
    f_equal. omega.
    normalize.
    normalize.
  rewrite Z.mul_comm.
  apply Z.divide_mul_r; auto.
  apply legal_alignas_sizeof_alignof_compat; auto.
  rewrite Z.mul_comm.
  apply Z.divide_mul_r; auto.
  apply legal_alignas_sizeof_alignof_compat; auto.
Qed.
*)

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

Local Open Scope nat.

Lemma data_at_type_changable: forall (sh: Share.t) (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  data_at sh t1 v1 = data_at sh t2 v2.
Proof.
  intros.
  subst. apply JMeq_eq in H0. subst v2. reflexivity.
Qed.

(*
Lemma split2_data_block:
  forall n sh data d,
  n <= length data ->
  data_block sh data d = 
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof cenv_cs tuchar * Zlength data) d &&
  data_block sh (firstn n data) d *
  data_block sh (skipn n data) (offset_val (Int.repr (Z.of_nat n)) d))%logic.
Proof.
  intros.
  assert (isptr d \/ ~isptr d) by (clear; destruct d; simpl; intuition).
  destruct H0; [ | apply pred_ext; entailer].
  unfold data_block.
  remember (sizeof cenv_cs tuchar) as TU.
  simpl.
  normalize.
  subst TU.
  do 2 rewrite prop_and. rewrite <- andp_assoc.  rewrite <- (prop_and (Forall _ _)).
  replace (Forall isbyteZ (skipn n data) /\ Forall isbyteZ (firstn n data)) with (Forall isbyteZ data)
  by (apply prop_ext; rewrite and_comm; rewrite <- Forall_app; rewrite firstn_skipn; intuition).
 rewrite andp_assoc.
  f_equal.
  simpl sizeof. rewrite Z.mul_1_l.
  erewrite (split_offset_array_at (Z.of_nat n)); auto;
   [ | split; [omega | rewrite Zlength_correct; apply Nat2Z.inj_le; auto]].
  f_equal.
 normalize.
f_equal.
repeat rewrite Zlength_correct.
rewrite firstn_length. rewrite min_l by auto.
f_equal.
admit.  (* certainly true, but what a mess *)
apply equal_f.
apply data_at_type_changable.
f_equal.
rewrite !Zlength_correct.
rewrite skipn_length. rewrite Nat2Z.inj_sub by omega. auto.
rewrite <- !skipn_map.
apply eq_JMeq.
admit.  (* certainly true, but what a mess *)
Qed.
*)

(*** Application of Omega stuff ***)

Lemma CBLOCKz_eq : CBLOCKz = 64%Z.
Proof. reflexivity. Qed.
Lemma LBLOCKz_eq : LBLOCKz = 16%Z.
Proof. reflexivity. Qed.

Ltac helper2 := 
 match goal with
   | |- context [CBLOCK] => add_nonredundant (CBLOCK_eq)
   | |- context [LBLOCK] => add_nonredundant (LBLOCK_eq)
   | |- context [CBLOCKz] => add_nonredundant (CBLOCKz_eq)
   | |- context [LBLOCKz] => add_nonredundant (LBLOCKz_eq)
   | H: context [CBLOCK] |- _ => add_nonredundant (CBLOCK_eq)
   | H: context [LBLOCK] |- _ => add_nonredundant (LBLOCK_eq)
   | H: context [CBLOCKz] |- _ => add_nonredundant (CBLOCKz_eq)
   | H: context [LBLOCKz] |- _ => add_nonredundant (LBLOCKz_eq)
  end.

(*** End Omega stuff ***)

Ltac Omega1 := Omega (helper1 || helper2).

Ltac MyOmega :=
  rewrite ?length_list_repeat, ?skipn_length, ?map_length, 
   ?Zlength_map, ?Zlength_nil;
  pose proof CBLOCK_eq;
  pose proof CBLOCKz_eq;
  pose proof LBLOCK_eq;
  pose proof LBLOCKz_eq;
  Omega1.
(*  Omega OmegaHelper1.*)

Local Open Scope Z.

Local Open Scope logic.

Lemma mapsto_tuchar_isbyteZ:
  forall sh v i, readable_share sh-> mapsto sh tuchar v (Vint i) =
    !! (0 <= Int.unsigned i < 256)%Z && mapsto sh tuchar v (Vint i).
Proof.
intros. apply mapsto_value_range. trivial.
Qed.

Lemma data_block_isbyteZ:
 forall sh data v, data_block sh data v = !! Forall isbyteZ data && data_block sh data v.
Proof.
unfold data_block; intros.
simpl.
normalize.
f_equal. f_equal. apply prop_ext. intuition.
Qed.

Lemma sizeof_tarray_tuchar:
 forall (n:Z), (n>=0)%Z -> (sizeof cenv_cs (tarray tuchar n) =  n)%Z.
Proof. intros.
 unfold sizeof,tarray; cbv beta iota.
  rewrite Z.max_r by omega.
  unfold alignof, tuchar; cbv beta iota.
  rewrite Z.mul_1_l. auto.
Qed.

Lemma isbyte_value_fits_tuchar:
  forall x, isbyteZ x -> value_fits true tuchar (Vint (Int.repr x)).
Proof.
intros. hnf in H|-*; intros.
simpl. rewrite Int.unsigned_repr by repable_signed. 
  change Byte.max_unsigned with 255%Z. omega.
Qed.

Lemma Forall_map:
  forall {A B} (f: B -> Prop) (g: A -> B) al,
   Forall f (map g al) <-> Forall (f oo g) al.
Proof.
intros.
induction al; simpl; intuition; inv H1; constructor; intuition.
Qed.

Lemma Forall_sublist:
  forall {A} (f: A -> Prop) lo hi al,
   Forall f al -> Forall f (sublist lo hi al).
Proof.
intros. unfold sublist.
apply Forall_firstn. apply Forall_skipn. auto.
Qed.

Lemma Zlength_Zlist_to_intlist: 
  forall (n:Z) (l: list Z),
   (Zlength l = WORD*n)%Z -> Zlength (Zlist_to_intlist l) = n.
Proof.
intros.
rewrite Zlength_correct in *.
assert (0 <= n)%Z by ( change WORD with 4%Z in H; omega).
rewrite (length_Zlist_to_intlist (Z.to_nat n)).
apply Z2Nat.id; auto.
apply Nat2Z.inj. rewrite H.
rewrite Nat2Z.inj_mul.
f_equal. rewrite Z2Nat.id; omega.
Qed.

Lemma nth_intlist_to_Zlist_eq:
 forall d (n i j k: nat) al, (i < n)%nat -> (i < j*4)%nat -> (i < k*4)%nat -> 
    nth i (intlist_to_Zlist (firstn j al)) d = nth i (intlist_to_Zlist (firstn k al)) d.
Proof.
 induction n; destruct i,al,j,k; simpl; intros; auto; try omega.
 destruct i; auto. destruct i; auto. destruct i; auto.
 apply IHn; omega.
Qed.


