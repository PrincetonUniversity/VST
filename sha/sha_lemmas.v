Require Import VST.floyd.proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha.
Require Export sha.pure_lemmas.
Require Export sha.general_lemmas.
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
apply pred_ext; [ | normalize].
apply andp_right; auto.
unfold mapsto; simpl.
destruct (access_mode t); try apply FF_left.
destruct (attr_volatile (attr_of_type t)); try apply FF_left.
destruct p; try apply FF_left.
if_tac; try contradiction. apply orp_left.
normalize.
normalize.
Qed.

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

Lemma data_block_local_facts:
 forall {cs: compspecs} sh f data,
  data_block sh f data |--
   prop (field_compatible (tarray tuchar (Zlength f)) [] data
           /\ Forall isbyteZ f).
Proof.
intros. unfold data_block, array_at.
simpl.
entailer.
Qed.
Hint Resolve @data_block_local_facts : saturate_local.

Require Import JMeq.

Lemma reptype_tarray {cs: compspecs}:
   forall t len, reptype (tarray t len) = list (reptype t).
Proof.
intros.
rewrite reptype_eq. simpl. reflexivity.
Qed.

Local Open Scope nat.

(*** Application of Omega stuff ***)

Lemma CBLOCKz_eq : CBLOCKz = 64%Z.
Proof. reflexivity. Qed.
Lemma LBLOCKz_eq : LBLOCKz = 16%Z.
Proof. reflexivity. Qed.
Lemma WORD_eq: WORD = 4%Z.
Proof. reflexivity. Qed.

Hint Rewrite CBLOCKz_eq LBLOCKz_eq WORD_eq : rep_omega.

(*
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

Ltac Omega1 := Omega (helper1 || helper2).
*)
Ltac Omega1 := rep_omega.

Ltac MyOmega :=
  rewrite ?length_list_repeat, ?skipn_length, ?map_length,
   ?Zlength_map, ?Zlength_nil;
  pose proof CBLOCK_eq;
(*  pose proof CBLOCKz_eq;*)
  pose proof LBLOCK_eq;
(*  pose proof LBLOCKz_eq; *)
  Omega1.
(*** End Omega stuff ***)

Local Open Scope Z.

Local Open Scope logic.

Lemma data_block_valid_pointer {cs: compspecs} sh l p: sepalg.nonidentity sh -> Zlength l > 0 ->
      data_block sh l p |-- valid_pointer p.
Proof. unfold data_block. simpl; intros.
  apply andp_valid_pointer2. apply data_at_valid_ptr; auto; simpl.
  rewrite Z.max_r, Z.mul_1_l; omega.
Qed.

Lemma data_block_isbyteZ {cs: compspecs}:
 forall sh data v, data_block sh data v = !! Forall isbyteZ data && data_block sh data v.
Proof.
unfold data_block; intros.
simpl.
normalize.
f_equal. f_equal. apply prop_ext. intuition.
Qed.

Lemma sizeof_tarray_tuchar:
 forall (n:Z), (n>=0)%Z -> (sizeof (tarray tuchar n) =  n)%Z.
Proof. intros.
 unfold sizeof,tarray; cbv beta iota.
  rewrite Z.max_r by omega.
  unfold alignof, tuchar; cbv beta iota.
  rewrite Z.mul_1_l. auto.
Qed.

Lemma isbyte_value_fits_tuchar:
  forall x, isbyteZ x -> value_fits tuchar (Vint (Int.repr x)).
Proof.
intros. hnf in H|-*; intros.
simpl. rewrite Int.unsigned_repr by rep_omega.
  change Byte.max_unsigned with 255%Z. omega.
Qed.

Lemma Zlength_Zlist_to_intlist:
  forall (n:Z) (l: list Z),
   (Zlength l = WORD*n)%Z -> Zlength (Zlist_to_intlist l) = n.
Proof.
intros.
rewrite Zlength_correct in *.
rewrite (length_Zlist_to_intlist (Z.to_nat n)); rep_omega.
Qed.

Lemma nth_intlist_to_Zlist_eq:
 forall d (n i j k: nat) al, (i < n)%nat -> (i < j*4)%nat -> (i < k*4)%nat ->
    nth i (intlist_to_Zlist (firstn j al)) d = nth i (intlist_to_Zlist (firstn k al)) d.
Proof.
 induction n; destruct i,al,j,k; simpl; intros; auto; try omega.
 destruct i; auto. destruct i; auto. destruct i; auto.
 apply IHn; omega.
Qed.

Hint Resolve isbyteZ_sublist.

Lemma split2_data_block:
  forall  {cs: compspecs}  n sh data d,
  (0 <= n <= Zlength data)%Z ->
  data_block sh data d =
  (data_block sh (sublist 0 n data) d *
   data_block sh (sublist n (Zlength data) data)
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc n] d))%logic.
Proof.
  intros.
  unfold data_block. simpl. normalize.
  f_equal. f_equal.
  apply prop_ext.
  split; intro. split; apply Forall_sublist; auto.
  erewrite <- (sublist_same 0 (Zlength data)); auto.
  rewrite (sublist_split 0 n) by omega.
  apply Forall_app; auto.
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
  data_block sh data d =
  (data_block sh (sublist 0 lo data) d *
   data_block sh (sublist lo hi data)
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc lo] d) *
   data_block sh (sublist hi (Zlength data) data)
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc hi] d))%logic.
Proof.
  intros.
  unfold data_block. simpl. normalize.
  f_equal. f_equal.
  apply prop_ext.
  split; intro. split3; apply Forall_sublist; auto.
  erewrite <- (sublist_same 0 (Zlength data)); auto.
  rewrite (sublist_split 0 lo (Zlength data)) by omega.
  rewrite (sublist_split lo hi (Zlength data)) by omega.
  destruct H1 as [? [? ?]].
  repeat (apply Forall_app; split);  auto.
  rewrite <- !sublist_map.
  unfold tarray.
  rewrite split3_data_at_Tarray_tuchar with (n1:=lo)(n2:=hi) by (autorewrite with sublist; auto).
  autorewrite with sublist.
  reflexivity.
Qed.

Global Opaque WORD.

Lemma S256abs_data:
  forall hashed data,
   (LBLOCKz | Zlength hashed) ->
   Zlength data < CBLOCKz ->
   s256a_data (S256abs hashed data) = data.
Proof.
intros. unfold S256abs, s256a_data.
rewrite Zlength_app.
rewrite Zlength_intlist_to_Zlist.
destruct H as [n ?].
rewrite H.
assert (CBLOCKz > 0) by rep_omega. 
pose proof (Zmod_eq (n * CBLOCKz + Zlength data) CBLOCKz H1).
pose proof (Zmod_eq (Zlength data) CBLOCKz H1).
rewrite sublist_app2; rewrite Zlength_intlist_to_Zlist; rewrite H;
 rewrite <- Z.mul_assoc; change (LBLOCKz * 4)%Z with CBLOCKz.
apply sublist_same.
rewrite Z.div_add_l by omega.
rewrite Z.mul_add_distr_r.
rewrite Z.div_small by rep_omega. omega.
omega.
rewrite Z.div_add_l by  omega.
rewrite Z.mul_add_distr_r.
rewrite Z.div_small by rep_omega.
split; [ | omega].
apply Z.mul_nonneg_nonneg.
clear - H.
assert (n < 0 \/ 0 <= n) by omega.
destruct H0; auto.
assert (n * LBLOCKz < 0).
apply Z.mul_neg_pos; auto.
rep_omega.
omega.
Qed.

Lemma S256abs_hashed:
  forall hashed data,
   (LBLOCKz | Zlength hashed) ->
   Zlength data < CBLOCKz ->
   s256a_hashed (S256abs hashed data) = hashed.
Proof.
intros;  unfold S256abs, s256a_hashed.
rewrite Zlength_app.
rewrite Zlength_intlist_to_Zlist.
destruct H as [n ?].
assert (CBLOCKz > 0) by (rewrite CBLOCKz_eq; omega).
pose proof (Zmod_eq (n * CBLOCKz + Zlength data) CBLOCKz H1).
pose proof (Zmod_eq (Zlength data) CBLOCKz H1).
pose proof (Zlength_nonneg data).
rewrite sublist_app1; rewrite ?Zlength_intlist_to_Zlist;
  rewrite H.
rewrite sublist_same; try omega.
apply intlist_to_Zlist_to_intlist.
rewrite Zlength_intlist_to_Zlist.
  rewrite H.
rewrite <- Z.mul_assoc; change (LBLOCKz*4)%Z with CBLOCKz.
rewrite Z.div_add_l by omega.
rewrite Z.mul_add_distr_r.
rewrite Z.div_small by omega.  omega.
split; [omega | ].
rewrite <- Z.mul_assoc; change (LBLOCKz*4)%Z with CBLOCKz.
rewrite Z.div_add_l by omega.
rewrite Z.mul_add_distr_r.
rewrite Z.div_small by omega.
clear - H.
assert (n < 0 \/ 0 <= n) by omega.
simpl.
destruct H0.
pose proof (Zlength_nonneg hashed).
assert (n * LBLOCKz < 0).
apply Z.mul_neg_pos; auto.
omega.
rewrite Z.add_0_r.
apply Z.mul_nonneg_nonneg; auto.
rewrite <- Z.mul_assoc; change (LBLOCKz*4)%Z with CBLOCKz.
rewrite Z.div_add_l by omega.
rewrite Z.mul_add_distr_r.
rewrite Z.div_small by omega.  omega.
Qed.

Lemma s256a_hashed_divides:
  forall a, (LBLOCKz | Zlength (s256a_hashed a)).
Proof.
intros. unfold s256a_hashed.
exists (Zlength a / CBLOCKz)%Z.
erewrite Zlength_Zlist_to_intlist; [reflexivity |].
rewrite Zlength_sublist.
rewrite (Z.mul_comm WORD).
rewrite <- Z.mul_assoc.
change (LBLOCKz * WORD)%Z with CBLOCKz.
omega.
split; [ omega  |] .
apply Z.mul_nonneg_nonneg; auto.
apply Z.div_pos.
apply Zlength_nonneg.
rewrite CBLOCKz_eq; omega.
assert (CBLOCKz > 0) by (rewrite CBLOCKz_eq; omega).
pose proof (Zmod_eq (Zlength a) CBLOCKz H).
pose proof (Z_mod_lt (Zlength a) CBLOCKz H).
omega.
Qed.

Lemma s256a_data_len:
  forall a: s256abs,
  Zlength (s256a_data a) = Zlength a mod CBLOCKz.
Proof.
intros.
unfold s256a_data.
assert (CBLOCKz > 0) by (rewrite CBLOCKz_eq; omega).
pose proof (Zmod_eq (Zlength a) CBLOCKz H).
pose proof (Z_mod_lt (Zlength a) CBLOCKz H).
rewrite H0.
rewrite Zlength_sublist; try omega.
split; try omega.
apply Z.mul_nonneg_nonneg.
apply Z.div_pos.
apply Zlength_nonneg.
omega. omega.
Qed.

Lemma s256a_data_Zlength_less:
  forall a, Zlength (s256a_data a) < CBLOCKz.
Proof.
intros.
rewrite s256a_data_len.
apply Z_mod_lt.
rewrite CBLOCKz_eq; omega.
Qed.

Lemma hashed_data_recombine:
  forall a,
     Forall isbyteZ a ->
    intlist_to_Zlist (s256a_hashed a) ++ s256a_data a = a.
Proof.
intros. rename H into BYTES.
unfold s256a_hashed, s256a_data.
assert (CBLOCKz > 0) by (rewrite CBLOCKz_eq; omega).
rewrite Zlist_to_intlist_to_Zlist.
rewrite sublist_rejoin.
autorewrite with sublist. auto.
split; [ omega  |] .
apply Z.mul_nonneg_nonneg; auto.
apply Z.div_pos.
apply Zlength_nonneg.
rewrite CBLOCKz_eq; omega.
assert (CBLOCKz > 0) by (rewrite CBLOCKz_eq; omega).
pose proof (Zmod_eq (Zlength a) CBLOCKz H).
pose proof (Z_mod_lt (Zlength a) CBLOCKz H).
omega.
rewrite Zlength_sublist.
rewrite Z.sub_0_r.
apply Z.divide_mul_r.
exists LBLOCKz. reflexivity.
split; [ omega  |] .
apply Z.mul_nonneg_nonneg; auto.
apply Z.div_pos.
apply Zlength_nonneg.
omega.
pose proof (Zmod_eq (Zlength a) CBLOCKz H).
pose proof (Z_mod_lt (Zlength a) CBLOCKz H).
omega.
apply Forall_sublist.
auto.
Qed.

Definition bitlength (hashed: list int) (data: list Z) : Z :=
   ((Zlength hashed * WORD + Zlength data) * 8)%Z.

Lemma bitlength_eq:
  forall hashed data,
  bitlength hashed data = s256a_len (S256abs hashed data).
Proof.
intros.
unfold bitlength, s256a_len, S256abs.
rewrite Zlength_app.
rewrite Zlength_intlist_to_Zlist.
reflexivity.
Qed.

Lemma S256abs_recombine:
 forall a, Forall isbyteZ a ->
    S256abs (s256a_hashed a) (s256a_data a) = a.
Proof.
intros.
apply hashed_data_recombine; auto.
Qed.

Lemma Zlist_to_intlist_app:
  forall a b,
  (WORD | Zlength a) ->
   Zlist_to_intlist (a++b) = Zlist_to_intlist a ++ Zlist_to_intlist b.
Proof.
intros.
destruct H as [na H].
rewrite <- (Z2Nat.id na) in H.
Focus 2.
destruct (zlt na 0); try omega.
assert (na * WORD < 0); [apply Z.mul_neg_pos; auto | ].
pose proof (Zlength_nonneg a); omega.
revert a H; induction (Z.to_nat na); intros.
simpl in H. destruct a. simpl. auto. rewrite Zlength_cons in H.
pose proof (Zlength_nonneg a); omega.
rewrite inj_S in H.
unfold Z.succ in H. rewrite Z.mul_add_distr_r in H.
change (1*WORD)%Z with 4 in H.
assert (Zlength a >= 4).
assert (0 <= Z.of_nat n * WORD); [ | omega].
apply Z.mul_nonneg_nonneg; try omega.
change WORD with 4%Z; omega.
do 4 (destruct a; [rewrite Zlength_nil in H0; omega | rewrite Zlength_cons in H,H0  ]).
simpl.
do 4 f_equal. apply IHn.
omega.
Qed.

Lemma round_range:
 forall {A} (a: list A) (N:Z),
  N > 0 ->
   0 <= Zlength a / N * N <= Zlength a.
Proof.
intros.
split.
apply Z.mul_nonneg_nonneg; auto; try omega.
apply Z.div_pos; try omega.
apply Zlength_nonneg.
pose proof (Zmod_eq (Zlength a) N H).
pose proof (Z_mod_lt (Zlength a) N H).
omega.
Qed.

Lemma CBLOCKz_gt: CBLOCKz > 0.
Proof. rewrite CBLOCKz_eq; omega.
Qed.

Lemma Zlist_to_intlist_inj:
  forall a b,
   (WORD | Zlength a) ->
   (WORD | Zlength b) ->
   Forall isbyteZ a ->
   Forall isbyteZ b ->
   Zlist_to_intlist a = Zlist_to_intlist b ->
   a=b.
Proof.
intros.
rewrite <- (Zlist_to_intlist_to_Zlist a) by auto.
rewrite H3.
apply Zlist_to_intlist_to_Zlist; auto.
Qed.

Definition update_abs (incr: list Z) (a: list Z) (a': list Z) :=
    a' = a ++ incr.

Lemma update_abs_eq:
  forall msg a a',
 Forall isbyteZ (a++msg) ->
 Forall isbyteZ a' ->
 (update_abs msg a a' <->
  exists blocks,
    s256a_hashed a' = s256a_hashed a ++ blocks /\
    s256a_data a ++ msg = intlist_to_Zlist blocks ++ s256a_data a').
Proof.
intros. rename H0 into H'.
unfold update_abs.
assert (0 <= 0 <= Zlength a / CBLOCKz * CBLOCKz). {
 split; [omega | ].
 apply Z.mul_nonneg_nonneg.
 apply Z.div_pos.
 apply Zlength_nonneg.
 rewrite CBLOCKz_eq; omega.
 rewrite CBLOCKz_eq; omega.
}
pose proof (round_range a _ CBLOCKz_gt).
pose proof (round_range (a++msg) _ CBLOCKz_gt).
split; intro.
*
subst a'.
unfold s256a_hashed.
exists (Zlist_to_intlist
            (sublist (Zlength a / CBLOCKz * CBLOCKz) (Zlength (a++msg) / CBLOCKz * CBLOCKz)
                  (a++msg))).
split.
 +
 rewrite (sublist_split 0 (Zlength a / CBLOCKz * CBLOCKz)); auto.
 rewrite Zlist_to_intlist_app.
 f_equal.
 rewrite sublist_app1; auto. omega.
 rewrite Zlength_sublist; auto.
 rewrite Z.sub_0_r.
 apply Z.divide_mul_r.
 exists LBLOCKz; reflexivity.
 rewrite Zlength_app.
 pose proof (Zlength_nonneg msg); omega.
 split; [ | apply round_range; apply CBLOCKz_gt].
 apply Zmult_le_compat_r; [ | rewrite CBLOCKz_eq; omega].
 apply Z.div_le_mono; [rewrite CBLOCKz_eq; omega| ].
 rewrite Zlength_app; Omega1.
 +
 rewrite Zlist_to_intlist_to_Zlist.
 Focus 2. rewrite Zlength_sublist. rewrite <- Z.mul_sub_distr_r.
 apply Z.divide_mul_r.
 exists LBLOCKz; reflexivity.
 split; [Omega1 | ].
 apply Zmult_le_compat_r; [ | rewrite CBLOCKz_eq; omega].
 apply Z.div_le_mono; [rewrite CBLOCKz_eq; omega| ].
 rewrite Zlength_app; Omega1.
 apply round_range. apply CBLOCKz_gt.
 2: apply Forall_sublist; auto.
 unfold s256a_data.
 destruct (zlt   (Zlength (a ++ msg) / CBLOCKz * CBLOCKz) (Zlength a) ).
  -
   rewrite sublist_app1; try omega.
   rewrite (sublist_split (Zlength (a ++ msg) / CBLOCKz * CBLOCKz)
               (Zlength a) (Zlength (a ++ msg))); try omega.
   rewrite sublist_app1; try omega.
   rewrite sublist_app2 by omega.
   autorewrite with sublist.
   rewrite (sublist_same 0) by omega.
   rewrite <- app_ass. f_equal.
   rewrite sublist_rejoin; try omega. auto.
   split. apply round_range; apply CBLOCKz_gt.
 apply Zmult_le_compat_r; [ | rewrite CBLOCKz_eq; omega].
 apply Z.div_le_mono; [rewrite CBLOCKz_eq; omega| ].
  Omega1.
  rewrite Zlength_app in l; omega.
  rewrite Zlength_app; Omega1.
   split. apply round_range; apply CBLOCKz_gt.
 apply Zmult_le_compat_r; [ | rewrite CBLOCKz_eq; omega].
 apply Z.div_le_mono; [rewrite CBLOCKz_eq; omega| ].
  rewrite Zlength_app; Omega1.
 -
   rewrite (sublist_split (Zlength a / CBLOCKz * CBLOCKz) (Zlength a)
                  (Zlength (a ++ msg) / CBLOCKz * CBLOCKz) ); auto.
   rewrite app_ass.
   rewrite sublist_app1; try omega.
   rewrite sublist_app2; try omega.
   rewrite Z.sub_diag.
   f_equal.
   rewrite sublist_app2; try omega.
   rewrite sublist_rejoin.
   autorewrite with sublist. auto.
   omega.
  split; try omega. rewrite Zlength_app; Omega1.
   omega.
*
destruct H3 as [blocks [? ?]].
match type of H3 with ?A = ?B =>
  assert (Zlength A * WORD = Zlength B * WORD)%Z by congruence
end.
match type of H4 with ?A = ?B =>
  assert (sublist 0 (Zlength a / CBLOCKz * CBLOCKz) a ++ A =
              sublist 0 (Zlength a / CBLOCKz * CBLOCKz) a ++ B) by congruence
end.
unfold s256a_hashed, s256a_data in *.
rewrite <- app_ass in H6.
rewrite sublist_rejoin in H6 by omega.
rewrite sublist_same in H6 by omega.
rewrite H6.
clear H6 H4.
rewrite <- (sublist_same 0 (Zlength a') a') at 1; auto.
rewrite <- app_ass.
rewrite (sublist_split 0 (Zlength a' / CBLOCKz * CBLOCKz) (Zlength a')); try omega.
f_equal.
apply Zlist_to_intlist_inj.
rewrite Zlength_sublist.
 rewrite Z.sub_0_r.
 apply Z.divide_mul_r.
 exists LBLOCKz; reflexivity.
 split; [clear; omega | ].
 apply Z.mul_nonneg_nonneg; [ | rewrite CBLOCKz_eq; omega].
 apply Z.div_pos; [ | rewrite CBLOCKz_eq; omega].
 apply Zlength_nonneg.
 apply round_range; apply CBLOCKz_gt.
 rewrite Zlength_app.
 apply Z.divide_add_r.
rewrite Zlength_sublist.
 rewrite Z.sub_0_r.
 apply Z.divide_mul_r.
 exists LBLOCKz; reflexivity.
 split; [clear; omega | ].
 apply Z.mul_nonneg_nonneg; [ | rewrite CBLOCKz_eq; omega].
 apply Z.div_pos; [ | rewrite CBLOCKz_eq; omega].
 apply Zlength_nonneg.
 apply round_range; apply CBLOCKz_gt.
 exists (Zlength blocks).
 apply Zlength_intlist_to_Zlist.
 apply Forall_sublist; auto.
 apply Forall_app; split.
 apply Forall_app in H; destruct H;
 apply Forall_sublist; auto.
 apply isbyte_intlist_to_Zlist.
 rewrite H3.
 rewrite Zlist_to_intlist_app. f_equal.
 symmetry; apply intlist_to_Zlist_to_intlist.
rewrite Zlength_sublist.
 rewrite Z.sub_0_r.
 apply Z.divide_mul_r.
 exists LBLOCKz; reflexivity.
 auto.
 omega.
 split; [clear; omega |].
 apply round_range; apply CBLOCKz_gt.
 split; [ | clear; omega].
 apply round_range; apply CBLOCKz_gt.
Qed.

Lemma array_at_memory_block:
 forall {cs: compspecs} sh t gfs lo hi v p n,
  sizeof (nested_field_array_type t gfs lo hi) = n ->
  lo <= hi ->
  array_at sh t gfs lo hi v p |--
  memory_block sh n (field_address0 t (ArraySubsc lo :: gfs) p).
Proof.
intros.
rewrite  array_at_data_at by auto.
normalize.
unfold at_offset.
rewrite field_address0_offset by auto.
subst n.
apply data_at_memory_block.
Qed.

Hint Extern 2 (array_at _ _ _ _ _ _ _ |-- memory_block _ _ _) =>
   (apply array_at_memory_block; try reflexivity; try omega) : cancel.

