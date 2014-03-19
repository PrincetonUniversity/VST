Require Import proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.

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
  Zlength (intlist_to_Zlist l) = 4*Zlength l.
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
  NPeano.divide 4 (length nl) ->
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

Lemma length_Zlist_to_intlist: forall n l, length l = (4*n)%nat -> length (Zlist_to_intlist l) = n.
Proof.
induction n; intros.
destruct l; inv H; reflexivity.
replace (S n) with (1 + n)%nat in H by omega.
rewrite mult_plus_distr_l in H.
destruct l as [|i0 l]; [ inv H |].
destruct l as [|i1 l]; [ inv H |].
destruct l as [|i2 l]; [ inv H |].
destruct l as [|i3 l]; [ inv H |].
simpl. f_equal. apply IHn. forget (4*n)%nat as A. inv H; auto.
Qed.

Lemma big_endian_integer_ext:
 forall f f', (forall z, (0 <= z < 4)%Z -> f z = f' z) ->
    big_endian_integer f = big_endian_integer f'.
Proof.
unfold big_endian_integer;
intros.
repeat f_equal; intros; apply H; omega.
Qed.

Lemma nth_big_endian_integer:
  forall i bl w, 
   nth_error bl i = Some w ->
    w = big_endian_integer
                 (fun z : Z =>
                  force_int
                    (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist bl)))
                       (z + Z.of_nat i * 4))).
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
if_tac; [rewrite if_true by omega | rewrite if_false by omega]; auto.
simpl default_val.
rewrite Z.mul_add_distr_r.
change (1*4)%Z with 4%Z.
simpl.
assert (Z.to_nat (j + (Z.of_nat i * 4 + 4)) = 4 + Z.to_nat (j + Z.of_nat i * 4))%nat.
repeat rewrite (Z2Nat.inj_add j) by omega.
rewrite Z2Nat.inj_add by omega.
change (Z.to_nat 4) with 4%nat.
omega.
rewrite H2. simpl.
auto.
Qed.

Local Open Scope nat.

Lemma firstn_same:
  forall A n (b: list A), n >= length b -> firstn n b = b.
Proof.
induction n; destruct b; simpl; intros; auto.
inv H.
f_equal; auto.
apply IHn.
omega.
Qed.

Definition LBLOCK : nat := Z.to_nat LBLOCKz.   
Definition CBLOCK : nat := Z.to_nat CBLOCKz.
Opaque LBLOCK CBLOCK.

Lemma LBLOCK_zeq: Z.of_nat LBLOCK = 16%Z.
Proof. reflexivity. Qed.

Lemma CBLOCK_zeq: (Z.of_nat CBLOCK = 64%Z).
Proof. reflexivity. Qed.

Lemma LBLOCKz_pos: (0 <= LBLOCKz)%Z.
Proof. change LBLOCKz with 16%Z; omega. Qed.
Hint Resolve LBLOCKz_pos.

Lemma CBLOCKz_pos: (0 <= CBLOCKz)%Z.
Proof. change CBLOCKz with 64%Z; omega. Qed.
Hint Resolve CBLOCKz_pos.

Lemma length_map2:
 forall A B C (f: A -> B -> C) al bl n,
  length al = n -> length bl = n -> 
  length (map2 f al bl) = n.
Proof.
induction al; destruct bl,n; simpl; intros; auto.
inv H.
Qed.

Lemma length_rnd_64:
  forall r k w, length r = 8 -> length (rnd_64 r k w) = 8.
Proof.
intros.
revert r H w; induction k; simpl; intros; auto.
unfold rnd_64; fold rnd_64.
destruct w; auto.
rename H into H0.
repeat  (destruct r as [ | ? r]; rename H0 into H2; inv H2).
apply IHk.
reflexivity.
Qed.

Lemma length_rnd_64_inv:
  forall r k w, length (rnd_64 r k w) = 8 -> length r = 8.
Proof.
intros.
revert w r H; induction k; simpl; intros.
unfold rnd_64 in H; auto.
unfold rnd_64 in H; fold rnd_64 in H.
destruct w; inv H; auto.
rewrite H1.
apply IHk in H1.
clear - H1.
unfold rnd_function in H1.
rename H1 into H0.
destruct r; inv H0. destruct r; inv H1.
destruct r; inv H0. destruct r; inv H1.
destruct r; inv H0. destruct r; inv H1.
destruct r; inv H0. destruct r; inv H1.
destruct r; inv H0.
simpl.
auto.
Qed.

Lemma length_process_block:
  forall r b, length r = 8 -> length (process_block r b) = 8.
Proof.
 intros. unfold process_block.
 apply length_map2; auto.
 apply length_rnd_64; auto.
Qed.


Lemma length_map2_add_rnd_64:
 forall regs w,
  length regs = 8 ->
  length (map2 Int.add regs (rnd_64 regs K w)) = 8.
Proof.
 intros.
 apply length_map2; auto.
 apply length_rnd_64; auto.
Qed.

Lemma grab_and_process_block_length:
 forall n r firstr msg r' m',
    length r = 8 ->
    length msg >= n ->
    grab_and_process_block n r firstr msg  = (r',m') ->
    length r' = 8.
Proof.
 induction n; intros.
 inv H1.
 apply length_process_block; auto.
 destruct msg.
 inv H0.
 simpl in H0.
 apply IHn in H1; auto.
 omega.
Qed.

Lemma length_process_msg:
  forall b, length (process_msg init_registers b) = 8.
Proof.
 intros.
 assert (length init_registers = 8%nat) by reflexivity.
 forget init_registers as regs.
 assert (exists n, n >= length b)%nat by eauto.
 destruct H0 as [n H0].
 revert regs b H H0; induction n; intros; rewrite process_msg_equation.
 destruct b; auto.
 inv H0.
 unfold grab_and_process_block.
 repeat (destruct b; [apply H | ]).
 apply IHn.
 apply length_process_block; auto.
 simpl in H0.
 omega.
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

Lemma process_msg_eq2:
 forall regs hashed b,
  length b = 16 ->
 process_msg regs (b++hashed) =
  process_msg (process_block regs (rev b)) hashed.
Proof.
intros.
rewrite process_msg_equation.
destruct (b++hashed) eqn:?.
destruct b; inv H. inv Heql.
rewrite <- Heql; clear i l Heql.
unfold grab_and_process_block.
rename H into H0.
repeat (destruct b as [ | ?x b]; inv H0; rename H1 into H0).
destruct b; inv H0.
simpl. auto.
Qed.

Lemma process_msg_block:
 forall (hashed b: list int), 
   length b = LBLOCK ->
   NPeano.divide LBLOCK (length hashed) ->
   map2 Int.add (process_msg init_registers hashed)
            (rnd_64 (process_msg init_registers hashed) K
               (rev (generate_word (rev b) 48)))
   = process_msg init_registers (hashed ++ b).
Proof.
intros.
symmetry.
destruct H0 as [n ?].
change LBLOCK with 16 in H,H0.
rewrite mult_comm in H0.
transitivity (process_block (process_msg init_registers hashed) (rev b)) ; [ | reflexivity].
forget init_registers as regs.
revert hashed H0 b H regs; induction n; intros.
*
destruct hashed; inv H0.
simpl app. 
set (j :=  (rev (generate_word (rev b) 48))).
rename H into H0.
repeat (rename H0 into H2; destruct b as [ | ?x b]; inv H2).
do 2 rewrite process_msg_equation.
unfold grab_and_process_block.
rewrite process_msg_equation.
unfold j,process_block. simpl rev.
reflexivity.
*
rewrite mult_succ_r in H0. rewrite plus_comm in H0.
rename H0 into H1.
assert (exists hh, exists hashed', length hh = 16 /\ hashed=hh++hashed').
do 16 (destruct hashed as [ | ?h hashed]; inv H1; rename H2 into H1).
exists ([h,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14]), hashed.
split; auto.
destruct H0 as [hh [hashed' [? ?]]].
subst.
rewrite app_length in H1.
assert (length hashed' = 16*n) by omega.
clear H1.
rewrite app_ass.
rewrite process_msg_eq2 by auto.
symmetry.
rewrite process_msg_eq2 by auto.
symmetry.
apply IHn; auto.
Qed.
 
Lemma eval_var_env_set:
  forall i t j v (rho: environ), eval_var i t (env_set rho j v) = eval_var i t rho.
Proof. reflexivity. Qed.

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (var_types Delta) ! i = None /\ (glob_types Delta) ! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Proof.
intros. 
destruct H as [H [H8 H0]].
unfold eval_var, globals_only.
simpl. 
destruct H as [_ [? [? ?]]].
destruct (H2 i g H0).
unfold Map.get; rewrite H3; auto.
destruct H3.
congruence.
Qed.

Lemma rnd_64_S:
  forall regs i b k w, 
    nth_error K i = Some k ->
    nth_error b i = Some w ->
    rnd_64 regs K (firstn (S i) b) =
    rnd_function (rnd_64 regs K (firstn i b)) k w.
Proof.
intros.
forget K as K'.
assert (firstn (S i) b = firstn i b++[w]).
clear - H0.
revert b w H0; induction i; destruct b; simpl; intros; inv H0; auto.
rewrite <- (IHi _ _ H1).
reflexivity.
rewrite H1.
clear H1.
pose proof (firstn_length i b).
rewrite min_l in H1.
Focus 2.
clear - H0; revert b H0; induction i; destruct b; simpl; intros; inv H0; try omega.
specialize (IHi _ H1). omega.
rewrite <- H1 in H.
clear H0 H1.
revert K' k H regs; induction (firstn i b); destruct K'; simpl; intros; inv H.
unfold rnd_64; simpl; fold rnd_64.
destruct K'; reflexivity.
specialize (IHl _ _ H1).
unfold rnd_64; simpl; fold rnd_64.
apply IHl.
Qed.

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

(* moved to SHA256.v 
Lemma skipn_length:
  forall {A} n (al: list A), length al >= n -> length (skipn n al) = length al -n.
Proof.
 induction n; destruct al; simpl; intros; auto.
 apply IHn. omega.
Qed.
*)

Lemma datablock_local_facts:
 forall sh f data,
  data_block sh f data |-- prop (isptr data /\ Forall isbyteZ f).
Proof.
intros. unfold data_block.
simpl.
entailer.
Qed.
Hint Resolve datablock_local_facts : saturate_local.

Lemma nth_firstn_low:
 forall A i n al (d: A),
  i < n <= length al -> nth i (firstn n al) d = nth i al d.
Proof.
intros.
revert n al H; induction i; destruct n,al; simpl; intros; auto; try omega.
apply IHi; omega.
Qed.

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
Lemma list_repeat_app: forall A a b (x:A),
  list_repeat a x ++ list_repeat b x = list_repeat (a+b) x.
Proof.
intros; induction a; simpl; f_equal.
auto.
Qed.

Lemma skipn_nil: forall A n, skipn n (@nil A) = nil.
Proof. induction n; simpl; auto.
Qed.

Lemma skipn_drop:
 forall A n m (al: list A), skipn n (skipn m al) = skipn (n+m) al.
Proof.
induction m; intros.
* simpl; auto. f_equal; omega.
* replace (n + S m)%nat with (S (n + m))%nat by omega.
  destruct al; [ rewrite skipn_nil; auto | ].
  unfold skipn at 3; fold skipn.
 rewrite <- IHm.
 f_equal.
Qed.

Lemma skipn_app1:
 forall A n (al bl: list A),
  (n <= length al)%nat ->
  skipn n (al++bl) = skipn n al ++ bl.
Proof.
intros. revert al H;
induction n; destruct al; intros; simpl in *; try omega; auto.
apply IHn; omega.
Qed.


Lemma split3_data_block:
  forall lo n sh data d,
  lo+n <= length data ->
  data_block sh data d = 
  (data_block sh (firstn lo data) d *
  data_block sh (firstn n (skipn lo data)) (offset_val (Int.repr (Z.of_nat lo)) d) *
  data_block sh (skipn (lo+n) data)  (offset_val (Int.repr (Z.of_nat (lo+n))) d))%logic.
Proof.
intros.
assert (isptr d \/ ~isptr d) by (clear; destruct d; simpl; intuition).
destruct H0; [ | apply pred_ext; entailer].
unfold data_block.
simpl.
normalize.
f_equal. f_equal.
apply prop_ext.
rewrite plus_comm.
rewrite <- skipn_drop.
rewrite (and_comm (Forall _ (skipn _ _))).
repeat rewrite <- Forall_app.
rewrite firstn_skipn.
rewrite firstn_skipn.
intuition.
rewrite (split_array_at (Z.of_nat (lo+n))).
rewrite (split_array_at (Z.of_nat lo)).
f_equal; [f_equal | ].
*
 apply equal_f; apply array_at_ext'; intros; auto.
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
* 
replace (Int.repr (Z.of_nat lo)) with (Int.repr (sizeof tuchar * Z.of_nat lo))
 by (rewrite sizeof_tuchar; rewrite Z.mul_1_l; auto).
rewrite <- offset_val_array_at.
 apply equal_f; apply array_at_ext'; intros; auto.
 unfold tuchars, ZnthV.
 repeat rewrite if_false by omega.
 repeat rewrite map_map.
 repeat rewrite @nth_map' with (d':=0%Z).
 f_equal. f_equal.
 rewrite nth_firstn_low; auto.
 rewrite nth_skipn; auto.
 f_equal.
 rewrite Z2Nat.inj_sub by omega.
 rewrite Nat2Z.id.
 destruct H1.
 rewrite <- (Z2Nat.id i) in H1 by omega.
 apply Nat2Z.inj_le in H1.
 omega.
 rewrite skipn_length.
 rewrite Z2Nat.inj_sub by omega.
 rewrite <- (Z2Nat.id i) in H1 by omega.
 destruct H1.
 apply Nat2Z.inj_le in H1.
 apply Nat2Z.inj_lt in H2.
 rewrite Nat2Z.id.
 omega.
 omega.
 rewrite <- (Z2Nat.id i) in H1 by omega.
 destruct H1.
 apply Nat2Z.inj_le in H1.
 apply Nat2Z.inj_lt in H2.
 rewrite Z2Nat.inj_sub by omega.
 rewrite Nat2Z.id.
 rewrite firstn_length.
 rewrite skipn_length.
 rewrite min_l by omega.
 omega.
 omega.
 rewrite <- (Z2Nat.id i) in H1 by omega.
 destruct H1.
 apply Nat2Z.inj_le in H1.
 apply Nat2Z.inj_lt in H2. 
 omega.
 omega.
 rewrite Zlength_correct.
 rewrite firstn_length.
 rewrite skipn_length by omega.
 rewrite min_l by omega.
 rewrite Nat2Z.inj_add.
 omega.
*
 replace (Int.repr (Z.of_nat (lo+n))) with (Int.repr (sizeof tuchar * Z.of_nat (lo+n)))
 by (rewrite sizeof_tuchar; rewrite Z.mul_1_l; auto).
rewrite <- offset_val_array_at.
 apply equal_f; apply array_at_ext'; intros; auto.
 rewrite Zlength_correct in H1.
 unfold tuchars, ZnthV.
 repeat rewrite if_false by omega.
 repeat rewrite map_map.
 repeat rewrite @nth_map' with (d':=0%Z).
 f_equal. f_equal.
 rewrite nth_skipn; auto.
 f_equal.
 rewrite Z2Nat.inj_sub by omega.
 rewrite <- (Z2Nat.id i) in H1 by omega.
 destruct H1.
 apply Nat2Z.inj_le in H1.
 apply Nat2Z.inj_lt in H2.
 rewrite Nat2Z.id.
 omega.
 rewrite <- (Z2Nat.id i) in H1 by omega.
 destruct H1.
 apply Nat2Z.inj_le in H1.
 apply Nat2Z.inj_lt in H2.
 rewrite skipn_length.
 rewrite Z2Nat.inj_sub by omega.
 rewrite Nat2Z.id.
 omega.
 omega.
 rewrite <- (Z2Nat.id i) in H1 by omega.
 destruct H1.
 apply Nat2Z.inj_le in H1.
 apply Nat2Z.inj_lt in H2.
 omega.
 omega.
 repeat rewrite Zlength_correct.
 rewrite skipn_length by omega.
 rewrite Nat2Z.inj_sub.
 omega.
 auto.
*
 split. omega.
 apply Nat2Z.inj_le. omega.
* 
 split. omega.
 rewrite Zlength_correct.
 apply Nat2Z.inj_le. omega.
Qed.

 Lemma divide_length_app:
 forall {A} n (al bl: list A), 
      NPeano.divide n (length al) -> 
      NPeano.divide n (length bl) ->
      NPeano.divide n (length (al++bl)).
Proof.
 intros. destruct H,H0. exists (x+x0).
 rewrite app_length,H,H0;  rewrite  mult_plus_distr_r; omega.
Qed.

Lemma Zlength_zeros: 
    forall n, (n>=0)%Z -> Zlength (zeros n) = n.
Proof.
intros.
rewrite <- (Z2Nat.id n) in * by omega.
clear H.
induction (Z.to_nat n).
reflexivity.
rewrite inj_S.
rewrite zeros_equation.
pose proof (Zgt_cases (Z.succ (Z.of_nat n0)) 0).
destruct (Z.succ (Z.of_nat n0) >? 0); try omega.
rewrite Zlength_cons.
f_equal.  rewrite <- IHn0.
f_equal. f_equal. omega.
Qed.

Lemma nth_map_zeros:
 forall i j v, (Z.of_nat i < j)%Z -> nth i (map Vint (zeros j)) v = Vint Int.zero.
Proof.
intros.
rewrite <- (Z2Nat.id j) in * by omega.
apply Nat2Z.inj_lt in H.
replace (Z.to_nat j) with (Z.to_nat j - S i + S i) by omega.
forget (Z.to_nat j - S i) as k.
clear j H.
rewrite Nat2Z.inj_add.
rewrite inj_S.
induction i.
rewrite zeros_equation.
pose proof (Zgt_cases (Z.of_nat k + Z.succ (Z.of_nat 0)) 0).
destruct (Z.of_nat k + Z.succ (Z.of_nat 0) >? 0); try omega.
simpl. reflexivity.
rewrite zeros_equation.
pose proof (Zgt_cases (Z.of_nat k + Z.succ (Z.of_nat (S i))) 0).
destruct (Z.of_nat k + Z.succ (Z.of_nat (S i)) >? 0); try omega.
rewrite map_cons.
unfold nth.
rewrite <- IHi.
unfold nth.
f_equal.
f_equal.
f_equal.
rewrite inj_S.
omega.
Qed.


Lemma length_zeros: forall n:Z, length (zeros n) = Z.to_nat n.
Proof.
intros. destruct (zlt n 0).
rewrite zeros_equation. 
pose proof (Zgt_cases n 0).
destruct (n>?0). omega.
destruct n. inv l. inv l. simpl. reflexivity.
rename g into H.
pose proof (Zlength_zeros n H). 
rewrite Zlength_correct in H0.
rewrite <- H0 at 2.
rewrite Nat2Z.id. auto.
Qed.

Hint Rewrite length_zeros : norm.

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

(*
Lemma length_padlen:
 forall n,
  length (padlen n) = Z.to_nat (16 - (Zmod ((n+4)/4 + 2) 16)) + 2.
Proof.
intros.
unfold padlen.
rewrite app_length.
rewrite length_zeros.
simpl length.
auto.
Qed.
*)

Local Open Scope Z.

Definition roundup (a b : Z) := (a + (b-1))/b*b.

Lemma Zlength_padlen:
 forall n,
  n>=0 -> 
  Zlength (padlen n) = roundup (n/4+3) 16 - n/4 - 1.
Proof.
intros.
unfold padlen.
rewrite initial_world.Zlength_app.
rewrite Zlength_zeros.
repeat rewrite Zlength_cons; rewrite Zlength_nil.
change (Z.succ (Z.succ 0)) with 2.
unfold roundup.
change (16-1) with 15; omega.
assert (n/4 >= 0).
apply Z_div_ge0; omega.
assert (n/4+3>0) by omega.
forget (n/4+3) as d.
clear - H1.
replace (d+15) with ((1*16)+ (d-1)) by (simpl Z.mul; omega).
rewrite Z_div_plus_full_l by omega.
rewrite Z.mul_add_distr_r.
change (1*16) with 16.
assert ((d-1)/16*16 + 15 >= d-1); [ | omega].
assert (d-1>=0) by omega.
forget (d-1) as e.
clear - H.
pattern e at 2; rewrite (Z_div_mod_eq e 16) by omega.
rewrite Z.mul_comm.
 assert (15 >= e mod 16); [| omega].
destruct (Z.mod_pos_bound e 16); omega.
Qed.

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
rewrite withspacer_spacer. simpl.
destruct v; inv Pv. unfold add_ptr_int;  simpl.
forget  (Int.add i0 (Int.mul (Int.repr (align 1 1)) (Int.repr 0))) as z.
unfold spacer; simpl. normalize.
clear.
fold tuchar.
rewrite mapsto_tuchar_isbyteZ.
normalize. apply prop_right; split; auto.
* (* rest of bytes, using induction hyp *)
rewrite (split_array_at 1) by omega.
apply derives_trans with (TT *  !!Forall isbyteZ (firstn n (map Int.unsigned dd))); auto.
apply sepcon_derives; auto.
replace v with (offset_val (Int.repr (sizeof tuchar * -1)) (offset_val (Int.repr 1%Z) v))
 by (destruct v; inv Pv; simpl; f_equal; normalize).
rewrite <- offset_val_array_at.
eapply derives_trans; [ | apply (IHn (offset_val (Int.repr 1) v)); normalize].
apply derives_refl'; apply equal_f; apply array_at_ext'; intros; try omega.
unfold ZnthV. if_tac. omega. if_tac; try omega.
replace (Z.to_nat (i0 - -1)) with (S (Z.to_nat i0)).
simpl. auto.
replace (i0 - -1)%Z with (1+i0)%Z by omega.
rewrite Z2Nat.inj_add by omega. simpl.  auto. 
clear.
rewrite <- (andp_TT (!! _)).
normalize.
Qed.


Lemma isbyte_zeros: forall n, Forall isbyteZ (map Int.unsigned (zeros n)).
Proof.
intros.
destruct (zlt n 0).
destruct n; inv l; constructor.
rewrite <- (Z2Nat.id n) by omega.
clear g; induction (Z.to_nat n).
constructor.
rewrite zeros_equation. 
replace (Z.of_nat (S n0) >? 0) with true.
constructor. split; computable.
replace (Z.of_nat (S n0) - 1)%Z with (Z.of_nat n0).
apply IHn0.
rewrite inj_S.
omega.
symmetry; rewrite Z.gtb_lt. rewrite inj_S; omega.
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

Lemma zeros_app:
  forall n m, (n >= 0 -> m >=0 -> zeros n ++ zeros m = zeros (n+m))%Z.
Proof.
intro.
intros ? ?.
rewrite <- (Z2Nat.id n).
induction (Z.to_nat n); intros; try reflexivity.
rewrite inj_S. unfold Z.succ.
rewrite zeros_equation; symmetry; rewrite zeros_equation; symmetry.
replace ( Z.of_nat n0 + 1 + m >? 0) with true.
replace (Z.of_nat n0 + 1 >? 0) with true.
simpl.
f_equal.
rewrite Z.add_simpl_r.
rewrite IHn0; auto.
f_equal; omega.
symmetry; apply Z.gtb_lt; auto; omega.
symmetry; apply Z.gtb_lt; auto; omega.
omega.
Qed.

Lemma zeros_Zsucc:
 forall n, n >= 0 -> zeros (Z.succ n) = Int.repr 0 :: zeros n.
Proof.
intros.
rewrite zeros_equation.
replace (Z.succ n >? 0) with true.
f_equal. f_equal. omega.
symmetry.
apply Z.gtb_lt; omega.
Qed.

Lemma intlist_to_Zlist_zeros:
  forall n:Z, intlist_to_Zlist (zeros n) = map Int.unsigned (zeros (4*n))%Z.
Proof.
intro.
destruct (zlt n 0).
destruct n; try omega. inv l. reflexivity.
rewrite <- (Z2Nat.id n) by omega.
induction (Z.to_nat n).
simpl; auto.
rewrite inj_S.
rewrite zeros_Zsucc by omega.
unfold intlist_to_Zlist; fold intlist_to_Zlist.
unfold Z.succ.
rewrite Z.add_comm.
rewrite Z.mul_add_distr_l.
replace (4 * 1 + 4 * Z.of_nat n0) with (Z.succ (Z.succ (Z.succ (Z.succ (4 * Z.of_nat n0))))) by omega.
repeat rewrite zeros_Zsucc by omega.
rewrite IHn0.
reflexivity.
Qed.

Lemma firstn_app1:
 forall A n (al bl: list A), 
  (n <= length al -> firstn n (al++bl) = firstn n al)%nat.
Proof.
intros. revert n al H; induction n; destruct al; simpl; intros; auto.
inv H.
f_equal; auto.
apply IHn.
omega.
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

Lemma roundup_minus:
   forall a b,  b > 0 -> roundup a b - a = (- a) mod b.
Proof.
unfold roundup; intros.
replace (a+(b-1)) with (a-1+1*b) by omega.
rewrite Z_div_plus_full by omega.
rewrite Z.mul_add_distr_r.
assert (H4 := Zmod_eq a b H).
assert (a mod b = 0 \/ a mod b <> 0) by omega.
destruct H0; [rewrite Z.mod_opp_l_z | rewrite Z.mod_opp_l_nz]; try omega.
rewrite H0 in H4.
assert (a = a/b*b) by omega.
rewrite H1 at 1.
replace (a/b*b-1) with (a/b*b+ -1) by omega.
rewrite Z_div_plus_full_l by omega.
rewrite Z.mul_add_distr_r.
rewrite <- H1.
assert (b=1 \/ b>1) by omega.
destruct H2.
subst b. simpl. omega.
rewrite (Z_div_nz_opp_full 1) by (rewrite Z.mod_small; omega).
rewrite  Z.div_small by omega.
omega.
rewrite H4.
assert ( (a-1)/b*b = a/b*b); [ | omega].
f_equal.
assert (a = a mod b + a/b*b) by omega.
replace (a-1) with (a mod b - 1 + a/b*b) by omega.
rewrite Z_div_plus_full by omega.
rewrite Z.div_small; try omega.
pose proof (Z_mod_lt a b H).
omega.
Qed.

Lemma Forall_isbyteZ_unsigned_repr:
 forall l, Forall isbyteZ l -> Forall isbyteZ (map Int.unsigned (map Int.repr l)).
Proof. induction 1. constructor.
constructor. rewrite Int.unsigned_repr; auto.
unfold isbyteZ in H; repable_signed.
apply IHForall.
Qed.

Lemma local_and_retval: 
 forall (i: ident) (P: val -> Prop) (R: mpred),
    `(local (`P retval) && `R) (get_result1 i) = local (`P (eval_id i)) && `R.
Proof.
intros.
extensionality rho.
super_unfold_lift.
unfold get_result1. simpl.
unfold local, lift1.
f_equal; auto.
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

Lemma and_mone':
 forall x, Int.and x (Int.repr (-1)) = x.
Proof.
apply Int.and_mone.
Qed.

Lemma Sigma_1_eq: forall f_,
  Sigma_1 f_ =
            (Int.xor
              (Int.xor
                 (Int.or (Int.shl f_ (Int.repr 26))
                    (Int.shru (Int.and f_ (Int.repr (-1)))
                       (Int.sub (Int.repr 32) (Int.repr 26))))
                 (Int.or (Int.shl f_ (Int.repr 21))
                    (Int.shru (Int.and f_ (Int.repr (-1)))
                       (Int.sub (Int.repr 32) (Int.repr 21)))))
              (Int.or (Int.shl f_ (Int.repr 7))
                 (Int.shru (Int.and f_ (Int.repr (-1)))
                    (Int.sub (Int.repr 32) (Int.repr 7))))).
Proof.
intros.
unfold Sigma_1, Rotr.
repeat rewrite and_mone'.
repeat rewrite <- Int.or_ror by reflexivity.
change (Int.sub (Int.repr 32) (Int.repr 26)) with (Int.repr 6).
change (Int.sub (Int.repr 32) (Int.repr 21)) with (Int.repr 11).
change (Int.sub (Int.repr 32) (Int.repr 7)) with (Int.repr 25).
reflexivity.
Qed.

Lemma  Sigma_0_eq: forall b_,
   Sigma_0 b_ = 
      (Int.xor
        (Int.xor
           (Int.or (Int.shl b_ (Int.repr 30))
              (Int.shru (Int.and b_ (Int.repr (-1)))
                 (Int.sub (Int.repr 32) (Int.repr 30))))
           (Int.or (Int.shl b_ (Int.repr 19))
              (Int.shru (Int.and b_ (Int.repr (-1)))
                 (Int.sub (Int.repr 32) (Int.repr 19)))))
        (Int.or (Int.shl b_ (Int.repr 10))
           (Int.shru (Int.and b_ (Int.repr (-1)))
              (Int.sub (Int.repr 32) (Int.repr 10))))).
Proof.
intros.
unfold Sigma_0, Rotr.
repeat rewrite and_mone'.
repeat rewrite <- Int.or_ror by reflexivity.
change (Int.sub (Int.repr 32) (Int.repr 19)) with (Int.repr 13).
change (Int.sub (Int.repr 32) (Int.repr 10)) with (Int.repr 22).
change (Int.sub (Int.repr 32) (Int.repr 30)) with (Int.repr 2).
reflexivity.
Qed.

Lemma Ch_eq: forall f_ g_ h_,
  Ch f_ g_ h_ =
        (Int.xor (Int.and f_ g_) (Int.and (Int.not f_) h_)).
Proof. reflexivity.
Qed.

Lemma Maj_eq:
  forall b c d, 
  Maj b c d =
  (Int.xor (Int.xor (Int.and b c) (Int.and b d)) (Int.and c d)).
Proof.
intros.
unfold Maj.
rewrite (Int.xor_commut) at 1.
rewrite Int.xor_assoc. auto.
Qed.

Lemma sigma_1_eq:
 forall s, sigma_1 s = 
   Int.xor
     (Int.xor
        (Int.or (Int.shl s (Int.repr 15))
           (Int.shru s (Int.sub (Int.repr 32) (Int.repr 15))))
        (Int.or (Int.shl s (Int.repr 13))
           (Int.shru s (Int.sub (Int.repr 32) (Int.repr 13)))))
  (Int.shru s (Int.repr 10)).
Proof.
intros.
unfold sigma_1.
f_equal. f_equal.
repeat rewrite <- Int.or_ror by reflexivity.
unfold Rotr. f_equal.
repeat rewrite <- Int.or_ror by reflexivity.
unfold Rotr. f_equal.
Qed.

Lemma sigma_0_eq:
 forall s, sigma_0 s = 
  Int.xor
   (Int.xor
     (Int.or (Int.shl s (Int.repr 25))
        (Int.shru s (Int.sub (Int.repr 32) (Int.repr 25))))
     (Int.or (Int.shl s (Int.repr 14))
        (Int.shru s (Int.sub (Int.repr 32) (Int.repr 14)))))
   (Int.shru s (Int.repr 3)).
Proof.
intros.
unfold sigma_0.
f_equal. f_equal.
repeat rewrite <- Int.or_ror by reflexivity.
unfold Rotr. f_equal.
repeat rewrite <- Int.or_ror by reflexivity.
unfold Rotr. f_equal.
Qed.


(* MOVE THESE TO FLOYD *)

Lemma assert_PROP:
 forall P1 Espec Delta P Q R c Post,
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! P1 ->
   (P1 -> @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post) ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre.
apply andp_right.
apply H.
rewrite <- insert_local.
apply andp_left2; apply derives_refl.
apply semax_extract_prop.
auto.
Qed.

Lemma drop_LOCAL':
  forall (n: nat)  P Q R Post,
   PROPx P (LOCALx (delete_nth n Q) (SEPx R)) |-- Post ->
   PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
intros.
eapply derives_trans; try apply H.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. apply prop_derives; simpl.
clear.
revert Q; induction n; destruct Q; simpl; intros; intuition.
Qed.

Lemma assert_LOCAL:
 forall Q1 Espec Delta P Q R c Post,
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local Q1 ->
   @semax Espec Delta (PROPx P (LOCALx (Q1::Q) (SEPx R))) c Post ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; try apply H0.
rewrite <- (insert_local Q1); apply andp_right; auto.
rewrite <- insert_local; apply andp_left2; auto.
Qed.

Lemma drop_LOCAL:
  forall (n: nat) Espec Delta P Q R c Post,
   @semax Espec Delta (PROPx P (LOCALx (delete_nth n Q) (SEPx R))) c Post ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; try apply H.
rewrite <- insert_local. apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. apply prop_derives; simpl.
clear.
revert Q; induction n; destruct Q; simpl; intros; intuition.
Qed.

(* END move these to Floyd *)

Lemma divide_hashed:
 forall (bb: list int), 
    NPeano.divide LBLOCK (length bb) <->
    (16 | Zlength bb).
Proof.
intros; split; intros [n ?].
exists (Z.of_nat n). rewrite Zlength_correct, H.
change 16%Z with (Z.of_nat 16).
rewrite <- Nat2Z.inj_mul; auto.
exists (Z.to_nat n).
rewrite Zlength_correct in H.
assert (0 <= n).
rewrite Z.mul_comm in H; omega.
rewrite <- (Z2Nat.id (n*16)%Z) in H by omega.
apply Nat2Z.inj in H. rewrite H.
change LBLOCK with (Z.to_nat 16).
rewrite Z2Nat.inj_mul; try omega.
Qed.
