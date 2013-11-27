Require Import proofauto.
Require Import progs.SHA256.

Definition swap (i: int) : int :=
 Int.or (Int.shl (Int.and i (Int.repr 255)) (Int.repr 24))
   (Int.or (Int.shl (Int.and (Rt 8 i) (Int.repr 255)) (Int.repr 16))
      (Int.or (Int.shl (Int.and (Rt 16 i) (Int.repr 255)) (Int.repr 8))
         (Rt 24 i))).

Definition big_endian_integer (contents: Z -> int) : int :=
  Int.or (Int.shl (contents 3) (Int.repr 24))
  (Int.or (Int.shl (contents 2) (Int.repr 16))
   (Int.or (Int.shl (contents 1) (Int.repr 8))
      (contents 0))).

Open Scope nat.

Lemma big_endian_integer_ext:
 forall f f', (forall z, (0 <= z < 4)%Z -> f z = f' z) ->
    big_endian_integer f = big_endian_integer f'.
Proof.
unfold big_endian_integer;
intros.
repeat f_equal; intros; apply H; omega.
Qed.

Definition force_option {A} (x:A) (i: option A) := 
  match i with Some y => y | None => x end.

Lemma swap_swap: forall w, swap (swap w) = w.
Proof.
unfold swap; intros.
Admitted.

Lemma nth_big_endian_int:
 forall i b, 
   i < length b ->
 nth_error b i =
Some
  (big_endian_integer
     (fun z : Z =>
      force_option Int.zero
        (nth_error (map Int.repr (intlist_to_Zlist (map swap b)))
           (Z.to_nat (z + Z.of_nat i * 4))))).
Proof.
induction i; destruct b; intros.
inv H.
simpl. apply f_equal_Some.
unfold big_endian_integer; simpl.
repeat rewrite Int.repr_unsigned.
symmetry; apply swap_swap.
inv H.
simpl in H.
simpl nth_error at 1.
rewrite IHi by omega. 
f_equal.
apply big_endian_integer_ext; intros.
f_equal.
rewrite inj_S.
replace (Z.to_nat (z + Z.succ (Z.of_nat i) * 4))
 with (S (S (S (S(Z.to_nat (z + Z.of_nat i * 4))))));
  [reflexivity | ].
unfold Z.succ.
rewrite Z.mul_add_distr_r.
rewrite <- (Zplus_comm (1*4)%Z).
replace  (z + (1 * 4 + Z.of_nat i * 4))%Z
  with  (4 + (z + Z.of_nat i * 4))%Z by omega.
symmetry.
rewrite Z2Nat.inj_add  by omega.
reflexivity.
Qed.

Lemma nth_big_endian_integer'':
  forall i bl w, 
   nth_error bl i = Some w ->
    w = big_endian_integer
                 (fun z : Z =>
                  force_option Int.zero
                    (ZnthV tuchar (map Some (map Int.repr (intlist_to_Zlist (map swap bl))))
                       (z + Z.of_nat i * 4))).
Proof.
induction i; destruct bl; intros; inv H.
simpl.
unfold big_endian_integer; simpl.
repeat rewrite Int.repr_unsigned.
change (w = swap (swap w)).
symmetry; apply swap_swap.
specialize (IHi _ _ H1).
rewrite IHi; clear IHi.
apply big_endian_integer_ext; intros j ?.
f_equal.
rewrite inj_S.
unfold Z.succ.
unfold ZnthV.
assert (i < length bl).
revert w bl H1; induction i; destruct bl; intros; inv H1; simpl; try omega.
apply IHi in H2. omega.
clear w H1.
if_tac; [rewrite if_true by omega | rewrite if_false by omega]; auto.
simpl default_val.
rewrite Z.mul_add_distr_r.
change (1*4)%Z with 4%Z.
simpl.
assert (Z.to_nat (j + (Z.of_nat i * 4 + 4)) = 4 + Z.to_nat (j + Z.of_nat i * 4)).
repeat rewrite (Z2Nat.inj_add j) by omega.
rewrite Z2Nat.inj_add by omega.
change (Z.to_nat 4) with 4.
omega.
rewrite H2. simpl.
auto.
Qed.

Lemma firstn_same:
  forall A n (b: list A), n >= length b -> firstn n b = b.
Proof.
induction n; destruct b; simpl; intros; auto.
inv H.
f_equal; auto.
apply IHn.
omega.
Qed.

Definition LBLOCK : nat := 16.   (* length of a block, in 32-bit integers *)
Definition CBLOCK : nat := LBLOCK * 4.  (* length of a block, in characters *)

Lemma LBLOCK_zeq: Z.of_nat LBLOCK = 16%Z.
Proof. reflexivity. Qed.

Global Opaque LBLOCK.  (* so that LBLOCK-i  does not inappropriately simplify *)

Definition s256state := (list (option int) * (option int * (option int
                                          * (list (option int) * option int))))%type.
Definition s256_h (s: s256state) := fst s.
Definition s256_Nl (s: s256state) := fst (snd s).
Definition s256_Nh (s: s256state) := fst (snd (snd s)).
Definition s256_data (s: s256state) := fst (snd (snd (snd s))).
Definition s256_num (s: s256state) := snd (snd (snd (snd s))).
Arguments s256_h  !s.
Arguments s256_Nl  !s.
Arguments s256_Nh  !s.
Arguments s256_data  !s.
Arguments s256_num  !s.
Arguments fst _ _ !p.
Arguments snd _ _ !p.

Inductive s256abs :=  (* SHA-256 abstract state *)
 S256abs: forall (hashed: list int)   (* words hashed, so far *)
                         (data: list Z)  (* bytes in the partial block not yet hashed *),
                     s256abs.

Definition hilo hi lo := (Int.unsigned hi * Int.modulus + Int.unsigned lo)%Z.

Definition s256_relate (a: s256abs) (r: s256state) : Prop :=
     match a with S256abs hashed data =>
         s256_h r = map Some (process_msg init_registers hashed) 
       /\ (exists hi, exists lo, s256_Nh r = Some hi /\ s256_Nl r = Some lo /\
            Zlength (intlist_to_Zlist (hashed)++data) = hilo hi lo)
       /\ (exists dd, data = map Int.unsigned dd /\ s256_data r = map Some dd)
       /\ length data < CBLOCK
       /\ NPeano.divide LBLOCK (length hashed)
       /\ s256_num r = Some (Int.repr (Zlength data))
     end.

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
 unfold registers_add.
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

Definition init_s256abs : s256abs := S256abs nil nil.

Definition sha_finish (a a': s256abs) :=
 match a, a' with
 | S256abs hashed data,
   S256abs hashed' data' =>
     hashed' = generate_and_pad (intlist_to_Zlist hashed ++ data) 0
  /\ data'=nil
 end.

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

Lemma length_intlist_to_Zlist:
  forall l, length (intlist_to_Zlist l) = (4 * length l).
Proof.
induction l.
simpl. reflexivity. simpl. omega.
Qed.

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
unfold j,process_block, registers_add. simpl rev.
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
 forall {A} n m (al: list A), firstn n al ++ firstn m (list_drop n al) =
  firstn (n+m) al.
Proof. induction n; destruct al; intros; simpl; auto.
destruct m; reflexivity.
f_equal; auto.
Qed.

Lemma list_drop_length:
  forall {A} n (al: list A), length al >= n -> length (list_drop n al) = length al -n.
Proof.
 induction n; destruct al; simpl; intros; auto.
 apply IHn. omega.
Qed.

Lemma exists_intlist_to_Zlist:
  forall n (al: list Z), 
   length al = (n * 4)%nat ->
   exists bl, al = intlist_to_Zlist bl /\ length bl = n.
Admitted.
       



