Require Import hmacdrbg.spec_hmac_drbg.
(*Require Import fcf.HMAC_DRBG_definitions_only.*)
Require Import fcf.HMAC_DRBG_nonadaptive.
Require Import sha.ByteBitRelations.
Require Import BinInt.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import fcf.DetSem.
Require Import sha.general_lemmas.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import Coqlib.
Require Import fcf.Fold.
Import ListNotations.

(* 
Definition Instantiate (entropy nonce: list Z) : DRBG_functions.DRBG_working_state :=
HMAC256_DRBG_instantiate_algorithm  entropy nonce nil 0. 
*)

Lemma bytesToBits_InBlocks l: InBlocks 8 (bytesToBits l).
Proof.
  apply InBlocks_len; rewrite bytesToBits_len. exists (length l); omega.
Qed.

Lemma flatten_bytes_bits: forall m (M: Forall (Forall isbyteZ) m), 
      flatten m = bitsToBytes (flatten (map bytesToBits m)).
Proof.
  induction m; simpl; trivial; intros.
  inv M. rewrite IHm; clear IHm; trivial. 
  rewrite bitsToBytes_app, bytes_bits_bytes_id; trivial.
  apply bytesToBits_InBlocks. 
Qed.

Lemma Forall_rev {A} P: forall (l:list A), Forall P l -> Forall P (rev l).
Proof.
  induction l; intros; simpl; trivial. inv H.
  rewrite hmac_pure_lemmas.Forall_app; auto.
Qed. 

Lemma to_list_eq (A : Type) (n : nat) l: to_list l = @Vector.to_list A n l.
Proof. reflexivity. Qed.

Definition HMAC_Blist (k: Blist)(data: Blist): Blist :=
  bytesToBits (HMAC256 (bitsToBytes data) (bitsToBytes k)).

Definition HMAC_Bvec (k: Bvector.Bvector 256)(data: Blist): Bvector.Bvector 256.
  apply (of_list_length (bytesToBits (HMAC256 (bitsToBytes data) (bitsToBytes (to_list k)) ))).
  rewrite bytesToBits_len, hmac_common_lemmas.HMAC_length. reflexivity.
Defined.

Lemma HMAC_Blist_Bvec v k: HMAC_Blist (to_list k) v = to_list (HMAC_Bvec k v).
Proof. unfold HMAC_Blist, HMAC_Bvec. rewrite HMAC_equivalence.of_length_proof_irrel; trivial. Qed.

Goal forall k' v, bitsToBytes (to_list (HMAC_Bvec k' v)) = HMAC256  (bitsToBytes v) (bitsToBytes (to_list k')).
Proof. unfold HMAC_Bvec; intros.
  rewrite to_list_eq, HMAC_equivalence.of_length_proof_irrel, bytes_bits_bytes_id; trivial.
  apply isbyteZ_HMAC256.
Qed.

Lemma HMAC_DRBG_generate_helper_Z_equation':
  forall (HMAC : list Z -> list Z -> list Z) (key v : list Z) (requested_number_of_bytes : Z),
  0 < requested_number_of_bytes ->
  HMAC_DRBG_generate_helper_Z HMAC key v requested_number_of_bytes =
    let (v0, rest) := HMAC_DRBG_generate_helper_Z HMAC key v (requested_number_of_bytes - Z.of_nat 32) in
    (HMAC v0 key, rest ++ HMAC v0 key).
Proof. intros. rewrite HMAC_DRBG_generate_helper_Z_equation.
  remember (0 >=? requested_number_of_bytes). destruct b; trivial.
  symmetry in Heqb;  apply Z.geb_le in Heqb. omega.
Qed. 
Lemma HMAC_DRBG_generate_helper_Z_equation0:
  forall (HMAC : list Z -> list Z -> list Z) (key v : list Z),
  HMAC_DRBG_generate_helper_Z HMAC key v 0 = (v, nil).
Proof. intros. rewrite HMAC_DRBG_generate_helper_Z_equation. trivial. Qed.

Lemma Genloop_Zlength_blocks : forall n eta k f v blocks u,
  @Gen_loop eta f k v n = (blocks,u) -> 
  Zlength blocks = Z.of_nat n.
Proof. 
  induction n.
+ simpl; intros. inv H. apply Zlength_nil. 
+ intros. simpl in H. unfold to_list in *. remember (Gen_loop f k (f k (Vector.to_list v)) n).
  destruct p. inversion H; clear H. subst.
  symmetry in Heqp. apply IHn in Heqp. 
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z. 
  2: symmetry; apply (Nat2Z.inj_add 1 n).
  rewrite <- Heqp. rewrite Zlength_cons. omega. 
Qed. 

(*Variant of fcf.HMAC_DRBG_definitions_only.Gen_loop that
  - specializes eta to 256
  - specializes f to HMAC256
  - replaces v'::bits with bits++[v']*)
Fixpoint Gen_loop_Bvec (k : Bvector 256) (v : Bvector 256) (n : nat)
  : list (Bvector 256) * Bvector 256 :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := HMAC_Bvec k (to_list v) in
    let (bits, v'') := Gen_loop_Bvec k v' n' in
    (List.app bits (List.cons v' List.nil), v'')     
  end.

(*A statement suitable for isntantiating the Variable HMAC_DRBG_nonadaptive.eqDecState*)
Lemma eqDecState : EqDec (HMAC_DRBG_nonadaptive.KV 256).
Proof. unfold KV, Bvector. specialize (@Vector_EqDec _ bool_EqDec 256); intros.
  apply pair_EqDec; trivial.
Qed.

Lemma GenloopBvec_ZlengthBlocks k: forall n v blocks u,
  Gen_loop_Bvec k v n = (blocks,u) -> Zlength blocks = Z.of_nat n.
Proof. 
  induction n.
+ simpl; intros. inv H. apply Zlength_nil.
+ intros. simpl in H. remember (Gen_loop_Bvec k (HMAC_Bvec k (to_list v)) n).
  destruct p. inv H. 
  symmetry in Heqp. apply IHn in Heqp. 
  replace (Z.of_nat (S n)) with (1+Z.of_nat n)%Z. 
  2: symmetry; apply (Nat2Z.inj_add 1 n).
  rewrite sublist.Zlength_app, Zlength_cons, Zlength_nil, Heqp. omega. 
Qed.

(*Lemma stating the relationship between Genloop_bvec and the corresponding
  specialization of Gen_loop*)
Lemma GenloopBvec_Gen_loop k: forall n v blocks u,
  Gen_loop_Bvec k v n = (blocks,u) ->
  Gen_loop HMAC_Bvec k v n = (rev blocks, u).
Proof. 
  induction n; simpl; intros.
+ inv H; trivial.
+ (*unfold to_list in H. *)
  remember (Gen_loop_Bvec k (HMAC_Bvec k (to_list v)) n) as p.
  destruct p; inv H. 
  symmetry in Heqp. apply IHn in Heqp. rewrite Heqp; clear Heqp IHn.
  rewrite rev_app_distr; trivial.
Qed.

(*Variant of Gen_loop_bvec that uses Blist instead of Bvector 256*)
Fixpoint Gen_loop_Blist (k : Blist) (v : Blist) (n : nat)
  : list Blist * Blist :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := HMAC_Blist k v in
    let (bits, v'') := Gen_loop_Blist k v' n' in
    (List.app bits (List.cons v' List.nil), v'')     
  end.

(*Relationship between Gen_loop_Blist and Gen_loop_bvec*)
Lemma Gen_loop_Blist_Bvec k: forall n v blocks u,
  Gen_loop_Blist (to_list k) (to_list v) n = (blocks, u) ->
  forall blocks' u', Gen_loop_Bvec k v n = (blocks', u') ->
  u = to_list u' /\ blocks = map (@Vector.to_list _ 256) blocks'.
Proof. 
induction n; simpl; intros; subst.
+ inv H; inv H0. split; trivial.
+ remember (Gen_loop_Blist (to_list k) (HMAC_Blist (to_list k) (to_list v)) n) as p; destruct p.
  inv H; symmetry in Heqp.
  remember (Gen_loop_Bvec k (HMAC_Bvec k (to_list v)) n) as q; destruct q.
  inv H0; symmetry in Heqq. rewrite HMAC_Blist_Bvec in Heqp.
  destruct (IHn _ _ _ Heqp _ _ Heqq) as [A B]; subst.
  rewrite HMAC_Blist_Bvec, to_list_eq, list_append_map. split; trivial.
Qed.

(*Variant of Gen_loop_bvec that uses list Z instead of Bvector 256*)
Fixpoint Gen_loop_Zlist (k : list Z) (v : list Z) (n : nat)
  : list (list Z) * (list Z) :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := HMAC256 v k in
    let (bits, v'') := Gen_loop_Zlist k v' n' in
    (List.app bits (List.cons v' List.nil), v'')     
  end.

Lemma Gen_loop_Zlist_isbyteZ k (K: Forall isbyteZ k): 
  forall n v (V: Forall isbyteZ v),
  match Gen_loop_Zlist k v n with (blocks,u) => 
        Forall (Forall isbyteZ) blocks /\ Forall isbyteZ u 
  end.
Proof. induction n; simpl; intros.
+ split; trivial.
+ remember (Gen_loop_Zlist k (HMAC256 v k) n) as p; destruct p.
  specialize (IHn (HMAC256 v k)). rewrite <- Heqp in IHn; destruct IHn. apply isbyteZ_HMAC256.
  split; trivial. rewrite hmac_pure_lemmas.Forall_app. split; trivial.
  constructor. apply isbyteZ_HMAC256. eauto.
Qed. 

Lemma Gen_loop_Zlist_ZlengthBlocks k: forall n v blocks u,
  Gen_loop_Zlist k v n = (blocks,u) -> Zlength blocks = Z.of_nat n.
Proof. induction n; intros.
+ inv H; simpl. apply Zlength_nil.
+ rewrite Nat2Z.inj_succ; simpl in H.
  remember (Gen_loop_Zlist k (HMAC256 v k) n) as p; destruct p; inv H.
  specialize (IHn (HMAC256 v k)). rewrite <- Heqp in IHn; clear Heqp.
  rewrite sublist.Zlength_app, Zlength_cons, (IHn _ _ (eq_refl _)). simpl; omega.
Qed. 

Lemma Gen_loop_Zlist_Blist k (K: Forall isbyteZ k):
  forall n v (V: Forall isbyteZ v),
  match Gen_loop_Zlist k v n with (blocks,u) =>
        Gen_loop_Blist (bytesToBits k) (bytesToBits v) n
        = (map bytesToBits blocks, bytesToBits u)
  end.
Proof. induction n; intros.
+ simpl; trivial.
+ simpl. remember (Gen_loop_Zlist k (HMAC256 v k) n). 
  destruct p. specialize (IHn (HMAC256 v k)).
  rewrite <- Heqp in IHn; clear Heqp.
  remember (Gen_loop_Blist (bytesToBits k)
     (HMAC_Blist (bytesToBits k) (bytesToBits v)) n) as q.
  destruct q. unfold HMAC_Blist in *.
  rewrite ! bytes_bits_bytes_id in *; trivial.
  rewrite IHn in Heqq; clear IHn. inv Heqq. f_equal.
  rewrite map_app; trivial. apply isbyteZ_HMAC256.
Qed.

Lemma Gen_loop_Zlist_nestedV k: forall n v blocks u blocks' u',
  Gen_loop_Zlist k (HMAC256 v k) n = (blocks, u) ->
  Gen_loop_Zlist k v n = (blocks', u') ->
  u = HMAC256 u' k /\
  blocks = map (fun z => HMAC256 z k) blocks'.
Proof. induction n; simpl; intros.
+ inv H; inv H0. split; trivial.
+ remember (Gen_loop_Zlist k (HMAC256 v k) n) as p.
  remember (Gen_loop_Zlist k (HMAC256 (HMAC256 v k) k) n) as q.
  destruct p; destruct q. inv H. symmetry in Heqp, Heqq.
  specialize (IHn (HMAC256 v k)).
  rewrite Heqq, Heqp in IHn; clear Heqq Heqp. inv H0.
  specialize (IHn _ _ _ _ (eq_refl _) (eq_refl _)). 
  destruct IHn as [? ?]; subst.  rewrite map_app. split; trivial.
Qed.

Lemma Gen_loop_Zlist_nestedV' k: forall n v blocks u,
  Gen_loop_Zlist k (HMAC256 v k) n = (blocks, u) ->
  exists blocks' u',
  Gen_loop_Zlist k v n = (blocks', u') /\
  u = HMAC256 u' k /\
  blocks = map (fun z => HMAC256 z k) blocks'.
Proof. induction n; simpl; intros.
+ inv H. exists nil, v. split; trivial. split; trivial.
+ remember (Gen_loop_Zlist k (HMAC256 v k) n) as p.
  remember (Gen_loop_Zlist k (HMAC256 (HMAC256 v k) k) n) as q.
  destruct p; destruct q. inv H. symmetry in Heqp, Heqq.
  specialize (IHn (HMAC256 v k) _ _ Heqq).
  rewrite Heqp in IHn; clear Heqq Heqp. 
  destruct IHn as [aa [bb [AB [? ?]]]]; subst. 
  inv AB. eexists; eexists; split. reflexivity. rewrite map_app.
  split; trivial. 
Qed.

Definition Equiv n:= forall k v blocks u,
   Gen_loop_Zlist k v n = (blocks, u) ->
   HMAC_DRBG_generate_helper_Z HMAC256 k v (32*(Z.of_nat n-1)+1) = (u,flatten (rev blocks)).

Lemma E1: Equiv 1.
Proof. unfold Equiv, HMAC_DRBG_generate_helper_Z; simpl; intros.
  inv H; simpl. rewrite app_nil_r; trivial. 
Qed.

Lemma E2: Equiv 2.
Proof. unfold Equiv, HMAC_DRBG_generate_helper_Z; simpl; intros.
  inv H; simpl. rewrite app_nil_r; trivial. 
Qed.

Lemma E3: Equiv 3.
Proof. unfold Equiv, HMAC_DRBG_generate_helper_Z; simpl; intros.
  inv H; simpl. rewrite app_assoc, app_nil_r; trivial. 
Qed.

Lemma E4: Equiv 4.
Proof. unfold Equiv, HMAC_DRBG_generate_helper_Z; simpl; intros.
  inv H; simpl. rewrite ! app_assoc, app_nil_r; trivial. 
Qed.

Lemma E10: Equiv 10.
Proof. unfold Equiv, HMAC_DRBG_generate_helper_Z; simpl; intros.
  inv H; simpl. rewrite ! app_assoc, app_nil_r; trivial. 
Qed.

(*Hence, by induction this should be the equivalence property*)

Lemma E_aux k: forall n v blocks u,
               Gen_loop_Zlist k (HMAC256 v k) n = (blocks, u) ->
      flatten (rev blocks) ++ HMAC256 u k =
      HMAC256 (HMAC256 v k) k ++ flatten (rev (map (fun z : list Z => HMAC256 z k) blocks)).
Proof. induction n; intros.
+ inv H; simpl. rewrite app_nil_r; trivial.
+ simpl in H.
  remember (Gen_loop_Zlist k (HMAC256 (HMAC256 v k) k) n). 
  destruct p. inv H. specialize (IHn (HMAC256 v k)).
  rewrite <- Heqp in IHn; clear Heqp. 
  specialize (IHn _ _ (eq_refl _)).
  rewrite rev_app_distr in *. rewrite flatten_app, <- app_assoc, IHn; clear IHn.
  simpl. rewrite app_nil_r. f_equal. rewrite map_app, rev_app_distr.
  simpl; trivial.
Qed.

Lemma E: forall n, Equiv (S n).
Proof. induction n; unfold Equiv in *; intros.
+ simpl in *. inv H; subst; unfold HMAC_DRBG_generate_helper_Z; simpl.
  rewrite app_nil_r; trivial.
+ remember (S n) as N. simpl in H.
  remember (Gen_loop_Zlist k (HMAC256 v k) N) as p.
  destruct p; symmetry in Heqp. inv H.
  rewrite HMAC_DRBG_generate_helper_Z_equation'.
  Focus 2. specialize (Nat2Z.inj_sub (S (S n)) 1). intros Q.
   replace (Z.of_nat 1) with 1 in Q; trivial. rewrite <- Q; omega.
  remember (S n) as N. 
  assert (W: 32 * (Z.of_nat (S N) - 1) + 1 - Z.of_nat 32 =
          32 * (Z.of_nat N - 1) + 1).
  { specialize (Nat2Z.inj_sub (S N) 1). intros Q.
    replace (Z.of_nat 1) with 1 in Q; trivial. rewrite <- Q by omega; clear Q.
    simpl. rewrite <- minus_n_O, Z.mul_sub_distr_l; omega. }
  rewrite W; clear W. 
  apply Gen_loop_Zlist_nestedV' in Heqp.
  destruct Heqp as [aa [bb [G [X L]]]]; subst. 
  rewrite (IHn _ _ _ _ G); clear IHn. 
  simpl. f_equal. rewrite rev_app_distr. 

  simpl in G. remember (Gen_loop_Zlist k (HMAC256 v k) n).
  destruct p. inv G. rewrite map_app, ! rev_app_distr, ! flatten_app.
  simpl. rewrite ! app_nil_r, <- app_assoc. f_equal.
  symmetry in Heqp. apply (E_aux k n); trivial.
Qed.

Definition GenUpdate_original_core (state : KV 256) (n : nat) :
  (list (Bvector 256) * KV 256) :=
  match state with (k, v) =>
    match Gen_loop HMAC_Bvec k v n with (bits, v') => 
        let k' := HMAC_Bvec k (to_list v' ++ zeroes) in
        let v'' := HMAC_Bvec k' (to_list v') in (bits, (k', v''))
    end
  end.

Definition GenUpdate_original_Bvec (state : KV 256) (n : nat) :
  (list (Bvector 256) * KV 256) :=
  match state with (k, v) =>
    match Gen_loop_Bvec k v n with (bits, v') => 
        let k' := HMAC_Bvec k (to_list v' ++ zeroes) in
        let v'' := HMAC_Bvec k' (to_list v') in (bits, (k', v''))
    end
  end.

Lemma GenUpdate_original_Bvec_correct state n:
  match GenUpdate_original_Bvec state n with (blocks, u) => 
     GenUpdate_original_core state n = (rev blocks, u) end.
Proof. unfold GenUpdate_original_Bvec, GenUpdate_original_core.
  destruct state as [k v].
  remember (Gen_loop_Bvec k v n) as p; destruct p; symmetry in Heqp.
  apply GenloopBvec_Gen_loop in Heqp. rewrite Heqp; trivial.
Qed.

Definition GenUpdate_original_Blist (state : Blist * Blist) (n : nat) :
  (list Blist * (Blist * Blist)) :=
  match state with (k, v) =>
    match Gen_loop_Blist k v n with (bits, v') => 
        let k' := HMAC_Blist k (v' ++ zeroes) in
        let v'' := HMAC_Blist k' v' in (bits, (k', v''))
    end
  end.

Lemma GenUpdate_original_Blist_Bvec k v n:
  match GenUpdate_original_Bvec (k,v) n with (blocks,(kk,u)) =>
    GenUpdate_original_Blist (@Vector.to_list _ 256 k, @Vector.to_list _ 256 v) n =
      (map (@Vector.to_list _ 256) blocks, (@Vector.to_list _ 256 kk, @Vector.to_list _ 256 u))
  end.
Proof. unfold GenUpdate_original_Bvec, GenUpdate_original_Blist.
  remember (Gen_loop_Bvec k v n) as p; symmetry in Heqp. destruct p as [bits v'].
  remember (Gen_loop_Blist (Vector.to_list k) (Vector.to_list v) n) as q; symmetry in Heqq.
  destruct q as [Bits V].
  destruct (Gen_loop_Blist_Bvec k n v Bits V Heqq _ _ Heqp); subst.
  rewrite ! HMAC_Blist_Bvec; trivial.
Qed.

Definition GenUpdate_original_Zlist (state : list Z * list Z) (n : nat) :
  (list (list Z) * (list Z * list Z)) :=
  match state with (k, v) =>
    match Gen_loop_Zlist k v n with (blocks, v') => 
        let k' := HMAC256 (v' ++ [Z0]) k in
        let v'' := HMAC256 v' k' in (blocks, (k', v''))
    end
  end.

Lemma GenUpdate_original_Zlist_ZlengthBlocks state n blocks state':
  GenUpdate_original_Zlist state n = (blocks,state') -> 
  Zlength blocks = Z.of_nat n.
Proof. destruct state; simpl; intros.
  remember (Gen_loop_Zlist l l0 n) as p; destruct p; symmetry in Heqp.
  inv H. apply Gen_loop_Zlist_ZlengthBlocks in Heqp; rewrite Heqp; trivial.
Qed.
 
Lemma GenUpdate_original_Zlist_isbyteZ k (K: Forall isbyteZ k) v (V: Forall isbyteZ v) n blocks state':
  GenUpdate_original_Zlist (k,v) n = (blocks,state') -> 
  Forall (Forall isbyteZ) blocks /\ Forall isbyteZ (fst state') /\ Forall isbyteZ (snd state').
Proof. simpl.
  remember (Gen_loop_Zlist k v n) as p; destruct p; symmetry in Heqp.
  specialize (Gen_loop_Zlist_isbyteZ _ K n _ V); rewrite Heqp. intros [A B] C; inv C.
  split; trivial. simpl. split; apply isbyteZ_HMAC256.
Qed.

Lemma GenUpdate_original_Zlist_Blist k v n
  (K: Forall isbyteZ k) (V: Forall isbyteZ v):
  match GenUpdate_original_Zlist (k,v) n with (blocks,(k',v')) =>
    GenUpdate_original_Blist (bytesToBits k, bytesToBits v) n =
         (map bytesToBits blocks,(bytesToBits k', bytesToBits v'))
  end.
Proof. unfold GenUpdate_original_Zlist, GenUpdate_original_Blist. 
  remember (Gen_loop_Zlist k v n) as p; symmetry in Heqp. destruct p as [bits v'].
  specialize (Gen_loop_Zlist_Blist _ K n _ V). rewrite Heqp; intros Q. simpl in Q. 
  remember (Gen_loop_Blist (bytesToBits k) (bytesToBits v) n) as q; destruct q.
  assert (W: (l, b) =(@map (list Z) ByteBitRelations.Blist bytesToBits bits, bytesToBits v')) by (rewrite <- Q, Heqq; trivial). 
  clear Q Heqq; inv W. f_equal. unfold HMAC_Blist.
  assert (T: Forall (Forall isbyteZ) nil) by eauto.
  specialize (Gen_loop_Zlist_isbyteZ _ K n _ V); rewrite Heqp. intros [? ?]. 
  rewrite ! bitsToBytes_app, ! bytes_bits_bytes_id; trivial.
  f_equal. unfold zeroes. simpl. apply  isbyteZ_HMAC256. 
  apply bytesToBits_InBlocks. 
Qed. 

(*Specialization of HMAC256_DRBG_generate_algorithm: no additional input*)
Definition Generate RI (WS: DRBG_functions.DRBG_working_state) n: DRBG_functions.DRBG_generate_algorithm_result :=
           HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm RI
                                           WS
                                           n
                                           nil.

Lemma GenerateCorrect RI k v z n (Z: (z<=RI)%Z):
  match GenUpdate_original_Zlist (k,v) (S n) with (blocks,(k',v')) => 
    Generate RI (v, k, z) (Z.of_nat ((32 * n +1)%nat)) = 
    generate_algorithm_success (firstn ((32 * n +1)%nat) (fcf.Fold.flatten (rev blocks))) (v',k',(z+1)%Z) 
  end.
Proof. remember (GenUpdate_original_Zlist (k, v) (S n)) as p; destruct p as [kk [vv zz]]; symmetry in Heqp. 
  unfold GenUpdate_original_Zlist in Heqp.
  remember (Gen_loop_Zlist k v (S n)) as q; destruct q as [blocks v']; symmetry in Heqq; inv Heqp.
  apply (E n) in Heqq. remember (32 * n + 1)%nat as a.
  simpl. remember (z >? RI) as d. destruct d; symmetry in Heqd. 
  + apply Zgt_is_gt_bool in Heqd; omega.
  + rewrite Z.mul_sub_distr_l in Heqq.
    assert (W: (32 * Z.of_nat (S n) - 32 * 1 + 1 = Z.of_nat a)%Z).
    { subst a; clear. change (S n) with (1+n)%nat; rewrite (Nat2Z.inj_add (32*n) 1), (Nat2Z.inj_add 1 n). 
      rewrite Z.mul_add_distr_l, Nat2Z.inj_mul. simpl; omega. }
    rewrite W in Heqq. rewrite Heqq, Nat2Z.id; trivial.
Qed.

Lemma Generate_Blist_ok RI k v z n (Z: (z<=RI)%Z) l kk vv zz 
    (K: Forall isbyteZ k) (V:Forall isbyteZ v):
    Generate RI (v, k, z) (Z.of_nat ((32 * n +1)%nat)) = generate_algorithm_success l (kk,vv, zz) ->
    exists y,
    GenUpdate_original_Blist (bytesToBits k, bytesToBits v) (S n) = 
    (map bytesToBits y,(bytesToBits vv, bytesToBits kk)) /\ zz=z+1 /\ 
    l = firstn (32 * n + 1) (flatten (rev y)).
Proof.
  remember (GenUpdate_original_Zlist (k,v) (S n)) as g. symmetry in Heqg; destruct g as [a [b c]].
  specialize (GenerateCorrect RI k v z n Z). rewrite Heqg; intros HH1 HH2.
  rewrite HH1 in HH2. exists a. inv HH2. repeat split; trivial. 
  specialize (GenUpdate_original_Zlist_Blist k v (S n) K V).
  rewrite Heqg; intros HH; rewrite HH; trivial.
Qed.

Lemma Generate_Bvec_ok' RI k v z n (Z: (z<=RI)%Z) l kk vv zz 
    (K: Forall isbyteZ k) (KL: length (bytesToBits k) = 256%nat) (V:Forall isbyteZ v) (VL:length (bytesToBits v) = 256%nat):
    Generate RI (v, k, z) (Z.of_nat ((32 * n +1)%nat)) = generate_algorithm_success l (kk,vv, zz) ->
    match GenUpdate_original_Bvec (of_list_length _ KL, of_list_length _ VL) (S n) with (blocks, kv) =>
    zz=z+1 /\ 
    bitsToBytes (@Vector.to_list _ 256 (fst kv)) = vv /\ 
    bitsToBytes (@Vector.to_list _ 256 (snd kv)) = kk /\
          l = firstn (32 * n + 1) (bitsToBytes (flatten (rev (map (@Vector.to_list _ 256) blocks))))
    end.
Proof.
  remember (GenUpdate_original_Zlist (k,v) (S n)) as g. symmetry in Heqg; destruct g as [a [b c]].
  specialize (GenerateCorrect RI k v z n Z). rewrite Heqg; intros HH1 HH2.
  rewrite HH1 in HH2. Opaque mult. inv HH2. 
  specialize (GenUpdate_original_Zlist_Blist k v (S n) K V).
  rewrite Heqg. intros HH.
  specialize (GenUpdate_original_Blist_Bvec (of_list_length (bytesToBits k) KL)
                (of_list_length (bytesToBits v) VL) (S n)); intros X. 
  remember (GenUpdate_original_Bvec
    (of_list_length (bytesToBits k) KL, of_list_length (bytesToBits v) VL)
    (S n)) as w. destruct w; symmetry in Heqw.
  simpl in X. simpl in Heqw. rewrite Heqw in X; clear Heqw.
  destruct k0 as [w u]. rewrite ! HMAC_equivalence.of_length_proof_irrel in X.
  simpl in HH. rewrite HH in X; clear HH. inv X. split. trivial. simpl.
  apply  GenUpdate_original_Zlist_isbyteZ in Heqg; trivial. destruct Heqg as [isbyteA [isbyteVV isbyteKK]].
  rewrite <- H1, <- H2, ! bytes_bits_bytes_id; trivial.
  repeat split; trivial.
  rewrite <- map_rev. f_equal. apply flatten_bytes_bits. apply Forall_rev; trivial.
Qed.
Lemma Generate_Bvec_ok RI k v z n (Z: (z<=RI)%Z) 
              (K: Forall isbyteZ k) (KL: length (bytesToBits k) = 256%nat)
              (V:Forall isbyteZ v) (VL:length (bytesToBits v) = 256%nat):
    match GenUpdate_original_Bvec (of_list_length _ KL, of_list_length _ VL) (S n) with (blocks, (kk,vv)) =>
          Generate RI (v, k, z) (Z.of_nat ((32 * n +1)%nat)) 
          = generate_algorithm_success (firstn (32 * n + 1) (bitsToBytes (flatten (rev (map (@Vector.to_list _ 256) blocks)))))
                                       (bitsToBytes (@Vector.to_list _ 256 vv), bitsToBytes (@Vector.to_list _ 256 kk), z+1)
    end.
Proof.
  remember (GenUpdate_original_Zlist (k,v) (S n)) as g. symmetry in Heqg; destruct g as [a [b c]].
  specialize (GenerateCorrect RI k v z n Z). rewrite Heqg; intros HH; rewrite HH.
  specialize (GenUpdate_original_Zlist_Blist _ _ (S n) K V); rewrite Heqg; intros.
  remember ( GenUpdate_original_Bvec
    (of_list_length (bytesToBits k) KL, of_list_length (bytesToBits v) VL)
    (S n)) as p. destruct p as [blocks [kk vv]]; symmetry in Heqp. 
  specialize (GenUpdate_original_Blist_Bvec (of_list_length (bytesToBits k) KL)
                 (of_list_length (bytesToBits v) VL) (S n)).
  simpl. simpl in Heqp. rewrite Heqp; clear Heqp. simpl in H.
  rewrite ! HMAC_equivalence.of_length_proof_irrel. rewrite H; clear H. intros. inv H.
  apply  GenUpdate_original_Zlist_isbyteZ in Heqg; trivial. destruct Heqg as [isbyteA [isbyteVV isbyteKK]].
  f_equal.
  - f_equal. rewrite <- map_rev. apply flatten_bytes_bits. apply Forall_rev; trivial. 
  - rewrite ! bytes_bits_bytes_id; trivial.
Qed.

Lemma Generate_ok' RI k v z n (Z: (z<=RI)%Z) l kk vv zz 
    (K: Forall isbyteZ k) (KL: length (bytesToBits k) = 256%nat) (V:Forall isbyteZ v) (VL:length (bytesToBits v) = 256%nat):
    Generate RI (v, k, z) (Z.of_nat ((32 * n +1)%nat)) = generate_algorithm_success l (kk,vv, zz) ->
    match GenUpdate_original_core (of_list_length _ KL, of_list_length _ VL) (S n) with (blocks, kv) =>
    zz=z+1 /\ 
    bitsToBytes (@Vector.to_list _ 256 (fst kv)) = vv /\ 
    bitsToBytes (@Vector.to_list _ 256 (snd kv)) = kk /\
          l = firstn (32 * n + 1) (bitsToBytes (flatten (map (@Vector.to_list _ 256) blocks)))
    end.
Proof. intros.
  specialize (Generate_Bvec_ok' RI k v z n Z l kk vv zz K KL V VL H); clear H; intros.
  remember (GenUpdate_original_Bvec
        (of_list_length (bytesToBits k) KL,
        of_list_length (bytesToBits v) VL) (S n)) as p; symmetry in Heqp; destruct p as [blocks state]. 
  specialize (GenUpdate_original_Bvec_correct
               (of_list_length (bytesToBits k) KL,
                of_list_length (bytesToBits v) VL) (S n)). 
  rewrite Heqp; clear Heqp; intros Q; rewrite Q, map_rev; apply H.
Qed.
Lemma Generate_ok RI k v z n (Z: (z<=RI)%Z) 
              (K: Forall isbyteZ k) (KL: length (bytesToBits k) = 256%nat)
              (V:Forall isbyteZ v) (VL:length (bytesToBits v) = 256%nat):
    match GenUpdate_original_core (of_list_length _ KL, of_list_length _ VL) (S n) with (blocks, (kk,vv)) =>
          Generate RI (v, k, z) (Z.of_nat ((32 * n +1)%nat)) 
          = generate_algorithm_success (firstn (32 * n + 1) (bitsToBytes (flatten (map (@Vector.to_list _ 256) blocks))))
                                       (bitsToBytes (@Vector.to_list _ 256 vv), bitsToBytes (@Vector.to_list _ 256 kk), z+1)
    end.
Proof.
  remember (GenUpdate_original_Bvec
        (of_list_length (bytesToBits k) KL,
        of_list_length (bytesToBits v) VL) (S n)) as p; destruct p as [blocks [kk vv]]; symmetry in Heqp.
  
  specialize (GenUpdate_original_Bvec_correct (of_list_length (bytesToBits k) KL,
         of_list_length (bytesToBits v) VL) (S n)). rewrite Heqp. 
  intros Q; rewrite Q; clear Q.
  specialize (Generate_Bvec_ok RI k v z n Z K KL V VL). rewrite Heqp; clear Heqp.
  intros W; rewrite W, map_rev; trivial. 
Qed.
(*
Require Import fcf.FCF.
Definition GenUpdate_original_refactored (state : KV 256) (n : nat) :
  Comp (list (Bvector 256) * KV 256) := ret (GenUpdate_original_core state n).

Lemma Refactored kv n: 
     comp_spec (fun x y => x=y)
               (GenUpdate_original HMAC_Bvec kv n)
               (GenUpdate_original_refactored kv n).
Proof.
  unfold GenUpdate_original, GenUpdate_original_refactored, GenUpdate_original_core.
  destruct kv as [k v]. prog_simp. apply comp_spec_ret; trivial. 
Qed.
*)
(*Could now optionally FCF-relate GenUpdate_original_refactored to Generate, for 
  relational spec relating bvectors to list Z,  using the above Gallina equalities*)