Require Import hmacdrbg.spec_hmac_drbg.
Require Import VST.floyd.functional_base.
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
Require Import compcert.lib.Coqlib.
Require Import fcf.Fold.
Import ListNotations.

Lemma false_zgt z a: false = (z >? a) -> z<=a. 
Proof. unfold Z.gtb.
  remember (z ?= a). destruct c. symmetry in Heqc; apply Z.compare_eq in Heqc. subst; intros. omega.
  symmetry in Heqc. destruct (Z.compare_lt_iff z a); intros. apply H in Heqc. omega.
  discriminate.
Qed. 
Lemma false_zge z a: false = (z >=? a) -> z<a. 
Proof. unfold Z.geb.
  remember (z ?= a). destruct c; intros; try discriminate.
  symmetry in Heqc. destruct (Z.compare_lt_iff z a); intros. apply H0 in Heqc. omega.
Qed.
Lemma false_zge' z a (A:z<a): false = (z >=? a). 
Proof.
  remember ((z >=? a)). destruct b; trivial. symmetry in Heqb. apply Z.geb_le in Heqb. omega.
Qed.

Lemma bytesToBits_InBlocks l: InBlocks 8 (bytesToBits l).
Proof.
  apply InBlocks_len; rewrite bytesToBits_len. exists (Datatypes.length l); omega.
Qed.

Lemma flatten_bytes_bits: forall m, 
      flatten m = bitsToBytes (flatten (map bytesToBits m)).
Proof.
  induction m; simpl; trivial; intros.
  rewrite IHm; clear IHm; trivial. 
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
Qed.

Lemma HMAC_DRBG_generate_helper_Z_equation':
  forall (HMAC : list byte -> list byte -> list byte) (key v : list byte) (requested_number_of_bytes : Z),
  0 < requested_number_of_bytes ->
  HMAC_DRBG_generate_helper_Z HMAC key v requested_number_of_bytes =
    let (v0, rest) := HMAC_DRBG_generate_helper_Z HMAC key v (requested_number_of_bytes - Z.of_nat 32) in
    (HMAC v0 key, rest ++ HMAC v0 key).
Proof. intros. rewrite HMAC_DRBG_generate_helper_Z_equation.
  remember (0 >=? requested_number_of_bytes). destruct b; trivial.
  symmetry in Heqb;  apply Z.geb_le in Heqb. omega.
Qed. 
Lemma HMAC_DRBG_generate_helper_Z_equation0:
  forall (HMAC : list byte -> list byte -> list byte) (key v : list byte),
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

(*Variant of Gen_loop_bvec that uses list byte instead of Bvector 256*)
Fixpoint Gen_loop_Zlist (k : list byte) (v : list byte) (n : nat)
  : list (list byte) * (list byte) :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := HMAC256 v k in
    let (bits, v'') := Gen_loop_Zlist k v' n' in
    (List.app bits (List.cons v' List.nil), v'')     
  end.

Lemma Gen_loop_Zlist_ZlengthBlocks k: forall n v blocks u,
  Gen_loop_Zlist k v n = (blocks,u) -> Zlength blocks = Z.of_nat n.
Proof. induction n; intros.
+ inv H; simpl. apply Zlength_nil.
+ rewrite Nat2Z.inj_succ; simpl in H.
  remember (Gen_loop_Zlist k (HMAC256 v k) n) as p; destruct p; inv H.
  specialize (IHn (HMAC256 v k)). rewrite <- Heqp in IHn; clear Heqp.
  rewrite sublist.Zlength_app, Zlength_cons, (IHn _ _ (eq_refl _)). simpl; omega.
Qed. 

Lemma Gen_loop_Zlist_Blist k:
  forall n v,
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
  rewrite map_app; trivial.
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

Definition Equiv n:= forall k v blocks u 
   (G: Gen_loop_Zlist k v n = (blocks, u)) m
   (M: 32*(Z.of_nat n-1) < m <=32*(Z.of_nat n)),
   HMAC_DRBG_generate_helper_Z HMAC256 k v m = (u,flatten (rev blocks)).

Lemma E1: Equiv 1.
Proof. unfold Equiv. simpl; intros. inv G. simpl. rewrite app_nil_r.
 rewrite HMAC_DRBG_generate_helper_Z_equation'; try omega. simpl.
 rewrite HMAC_DRBG_generate_helper_Z_equation.
 assert (0 >=? m - 32 = true). apply Z.geb_le; omega.
 rewrite H; trivial.
Qed.

Lemma E2: Equiv 2.
Proof. unfold Equiv; simpl; intros.
  inv G; simpl.
 rewrite HMAC_DRBG_generate_helper_Z_equation'; try omega. simpl.
 rewrite HMAC_DRBG_generate_helper_Z_equation.
 assert (false = (0 >=? m - 32)) by (apply false_zge'; omega).
 rewrite <- H. simpl.
 rewrite HMAC_DRBG_generate_helper_Z_equation.
 assert ((0 >=? m - 32 - 32)= true) by (apply Z.geb_le; omega).
 rewrite H0. rewrite app_nil_r; trivial. 
Qed. (*

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
*)
(*Hence, by induction the following equivalence property holds*)

Lemma E_aux k: forall n v blocks u,
               Gen_loop_Zlist k (HMAC256 v k) n = (blocks, u) ->
      flatten (rev blocks) ++ HMAC256 u k =
      HMAC256 (HMAC256 v k) k ++ flatten (rev (map (fun z : list byte => HMAC256 z k) blocks)).
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
Proof. induction n.
+ apply E1. 
+ unfold Equiv in *; intros. remember (S n) as N. 
  simpl in G.
  remember (Gen_loop_Zlist k (HMAC256 v k) N) as p.
  destruct p; symmetry in Heqp. inversion G; clear G. subst blocks l0. 
  rewrite HMAC_DRBG_generate_helper_Z_equation'.
  2:{ rewrite Zmult_minus_distr_l in M.
    assert (64 <= 32 * Z.of_nat (S N)).
    { subst. replace 64 with (32*2) by omega. apply Z.mul_le_mono_nonneg_l. omega.
      clear. apply (Nat2Z.inj_le 2). omega. }
    omega.
  }
  simpl.
  apply Gen_loop_Zlist_nestedV' in Heqp. 
  destruct Heqp as [aa [bb [G [X L]]]]. subst u l.
  rewrite (IHn _ _ _ _ G); clear IHn.
  2:{  clear - M. 
           rewrite Zmult_minus_distr_l in *. rewrite Nat2Z.inj_succ in M. simpl in *.
           omega.
  }
  f_equal. rewrite rev_app_distr. 

  subst N; simpl in G. remember (Gen_loop_Zlist k (HMAC256 v k) n).
  destruct p. inv G. rewrite map_app, ! rev_app_distr, ! flatten_app.
  simpl. rewrite ! app_nil_r, <- app_assoc. f_equal.
  symmetry in Heqp. apply (E_aux k n); trivial.
Qed.

Lemma EE n (N:(0<n)%nat): Equiv n.
Proof. destruct n. omega. apply E; trivial. Qed.

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

Definition GenUpdate_original_Zlist (state : list byte * list byte) (n : nat) :
  (list (list byte) * (list byte * list byte)) :=
  match state with (k, v) =>
    match Gen_loop_Zlist k v n with (blocks, v') => 
        let k' := HMAC256 (v' ++ [Byte.zero]) k in
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

Lemma GenUpdate_original_Zlist_Blist k v n:
  match GenUpdate_original_Zlist (k,v) n with (blocks,(k',v')) =>
    GenUpdate_original_Blist (bytesToBits k, bytesToBits v) n =
         (map bytesToBits blocks,(bytesToBits k', bytesToBits v'))
  end.
Proof. unfold GenUpdate_original_Zlist, GenUpdate_original_Blist. 
  remember (Gen_loop_Zlist k v n) as p; symmetry in Heqp. destruct p as [bits v'].
  specialize (Gen_loop_Zlist_Blist k n v). rewrite Heqp; intros Q. simpl in Q. 
  remember (Gen_loop_Blist (bytesToBits k) (bytesToBits v) n) as q; destruct q.
  assert (W: (l, b) =(@map (list byte) ByteBitRelations.Blist bytesToBits bits, bytesToBits v')) by (rewrite <- Q, Heqq; trivial). 
  clear Q Heqq; inv W. f_equal. unfold HMAC_Blist.
  rewrite ! bitsToBytes_app, ! bytes_bits_bytes_id; trivial.
  f_equal. unfold zeroes. simpl.
  apply bytesToBits_InBlocks. 
Qed. 

(*Specialization of HMAC256_DRBG_generate_algorithm: no additional input*)
Definition FunGenerate RI (WS: DRBG_functions.DRBG_working_state) n: DRBG_functions.DRBG_generate_algorithm_result :=
           HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm RI
                                           WS
                                           n
                                           nil.
Opaque mult. 

Lemma GenerateCorrect RI k v z n (Z: (z<=RI)%Z) (N:(0<n)%nat):
  match GenUpdate_original_Zlist (k,v) n with (blocks,(k',v')) => 
    FunGenerate RI (v, k, z) (Z.of_nat ((32 * n)%nat)) = 
    generate_algorithm_success (firstn ((32 * n)%nat) (fcf.Fold.flatten (rev blocks))) (v',k',(z+1)%Z) 
  end.
Proof. remember (GenUpdate_original_Zlist (k, v) n) as p; destruct p as [kk [vv zz]]; symmetry in Heqp. 
  unfold GenUpdate_original_Zlist in Heqp.
  remember (Gen_loop_Zlist k v n) as q; destruct q as [blocks v']; symmetry in Heqq; inv Heqp.
  apply EE in Heqq; trivial. remember (Z.of_nat (32 * n)) as a.  
  simpl. remember (z >? RI) as d. destruct d; symmetry in Heqd. 
  + apply Zgt_is_gt_bool in Heqd; omega.
  + rewrite Z.mul_sub_distr_l in Heqq. 
    rewrite Heqq. subst a; rewrite Nat2Z.id; trivial.
    subst a; clear -N. simpl. rewrite Nat2Z.inj_mul. simpl; omega.
Qed.
Opaque FunGenerate.

Lemma Generate_Blist_ok RI k v z n (Z: (z<=RI)%Z) l kk vv zz 
    (N:(0<n)%nat):
    FunGenerate RI (v, k, z) (Z.of_nat ((32 * n)%nat)) = generate_algorithm_success l (kk,vv, zz) ->
    exists y,
    GenUpdate_original_Blist (bytesToBits k, bytesToBits v) n = 
    (map bytesToBits y,(bytesToBits vv, bytesToBits kk)) /\ zz=z+1 /\ 
    l = firstn (32 * n) (flatten (rev y)).
Proof.
  remember (GenUpdate_original_Zlist (k,v) n) as g. symmetry in Heqg; destruct g as [a [b c]].
  specialize (GenerateCorrect RI k v z n Z N). rewrite Heqg; intros HH1 HH2.
  rewrite HH1 in HH2. exists a. inv HH2. repeat split; trivial. 
  specialize (GenUpdate_original_Zlist_Blist k v n).
  rewrite Heqg; intros HH; rewrite HH; trivial.
Qed. 

Lemma Generate_Bvec_ok' RI (k: list byte) v z n (Z: (z<=RI)%Z) l kk vv zz (N:(0<n)%nat)
    (KL: Datatypes.length (bytesToBits k) = 256%nat) (VL:Datatypes.length (bytesToBits v) = 256%nat):
    FunGenerate RI (v, k, z) (Z.of_nat ((32 * n)%nat)) = generate_algorithm_success l (kk,vv, zz) ->
    match GenUpdate_original_Bvec (of_list_length _ KL, of_list_length _ VL) n with (blocks, kv) =>
    zz=z+1 /\ 
    bitsToBytes (@Vector.to_list _ 256 (fst kv)) = vv /\ 
    bitsToBytes (@Vector.to_list _ 256 (snd kv)) = kk /\
          l = firstn (32 * n) (bitsToBytes (flatten (rev (map (@Vector.to_list _ 256) blocks))))
    end.
Proof.
  remember (GenUpdate_original_Zlist (k,v) n) as g. symmetry in Heqg; destruct g as [a [b c]].
  specialize (GenerateCorrect RI k v z n Z N). rewrite Heqg; intros HH1 HH2.
  rewrite HH1 in HH2. inv HH2. 
  specialize (GenUpdate_original_Zlist_Blist k v n).
  rewrite Heqg. intros HH.
  specialize (GenUpdate_original_Blist_Bvec (of_list_length (bytesToBits k) KL)
                (of_list_length (bytesToBits v) VL) n); intros X. 
  remember (GenUpdate_original_Bvec
    (of_list_length (bytesToBits k) KL, of_list_length (bytesToBits v) VL) n) as w.
  destruct w; symmetry in Heqw.
  simpl in X. simpl in Heqw. rewrite Heqw in X; clear Heqw.
  destruct k0 as [w u]. rewrite ! HMAC_equivalence.of_length_proof_irrel in X.
  simpl in HH. rewrite HH in X; clear HH. inv X. split. trivial. simpl.
  rewrite <- H1, <- H2, ! bytes_bits_bytes_id; trivial.
  repeat split; trivial.
  rewrite <- map_rev. f_equal. apply flatten_bytes_bits.
Qed.

Lemma Generate_Bvec_ok RI k v z n (Z: (z<=RI)%Z) (N:(0<n)%nat)
              (KL: Datatypes.length (bytesToBits k) = 256%nat)
              (VL:Datatypes.length (bytesToBits v) = 256%nat):
    match GenUpdate_original_Bvec (of_list_length _ KL, of_list_length _ VL) n with (blocks, (kk,vv)) =>
          FunGenerate RI (v, k, z) (Z.of_nat ((32 * n)%nat)) 
          = generate_algorithm_success (firstn (32 * n) (bitsToBytes (flatten (rev (map (@Vector.to_list _ 256) blocks)))))
                                       (bitsToBytes (@Vector.to_list _ 256 vv), bitsToBytes (@Vector.to_list _ 256 kk), z+1)
    end.
Proof.
  remember (GenUpdate_original_Zlist (k,v) n) as g. symmetry in Heqg; destruct g as [a [b c]].
  specialize (GenerateCorrect RI k v z n Z N). rewrite Heqg; intros HH; rewrite HH.
  specialize (GenUpdate_original_Zlist_Blist k v n); rewrite Heqg; intros.
  remember ( GenUpdate_original_Bvec
    (of_list_length (bytesToBits k) KL, of_list_length (bytesToBits v) VL) n) as p.
  destruct p as [blocks [kk vv]]; symmetry in Heqp. 
  specialize (GenUpdate_original_Blist_Bvec (of_list_length (bytesToBits k) KL)
                 (of_list_length (bytesToBits v) VL) n).
  simpl. simpl in Heqp. rewrite Heqp; clear Heqp. simpl in H.
  rewrite ! HMAC_equivalence.of_length_proof_irrel. rewrite H; clear H. intros. inv H.
  f_equal.
  - f_equal. rewrite <- map_rev. apply flatten_bytes_bits.
  - rewrite ! bytes_bits_bytes_id; trivial.
Qed.

Lemma Generate_ok' RI k v z n (Z: (z<=RI)%Z) l kk vv zz (N:(0<n)%nat)
    (KL: Datatypes.length (bytesToBits k) = 256%nat) (VL:Datatypes.length (bytesToBits v) = 256%nat):
    FunGenerate RI (v, k, z) (Z.of_nat ((32 * n)%nat)) = generate_algorithm_success l (kk,vv, zz) ->
    match GenUpdate_original_core (of_list_length _ KL, of_list_length _ VL) n with (blocks, kv) =>
    zz=z+1 /\ 
    bitsToBytes (@Vector.to_list _ 256 (fst kv)) = vv /\ 
    bitsToBytes (@Vector.to_list _ 256 (snd kv)) = kk /\
          l = firstn (32 * n) (bitsToBytes (flatten (map (@Vector.to_list _ 256) blocks)))
    end.
Proof. intros.
  specialize (Generate_Bvec_ok' RI k v z n Z l kk vv zz N KL VL H); clear H; intros.
  remember (GenUpdate_original_Bvec
        (of_list_length (bytesToBits k) KL,
        of_list_length (bytesToBits v) VL) n) as p; symmetry in Heqp; destruct p as [blocks state]. 
  specialize (GenUpdate_original_Bvec_correct
               (of_list_length (bytesToBits k) KL,
                of_list_length (bytesToBits v) VL) n). 
  rewrite Heqp; clear Heqp; intros Q; rewrite Q, map_rev; apply H.
Qed.

Lemma Generate_ok RI k v z n (Z: (z<=RI)%Z) (N:(0<n)%nat)
              (KL: Datatypes.length (bytesToBits k) = 256%nat)
              (VL:Datatypes.length (bytesToBits v) = 256%nat):
    match GenUpdate_original_core (of_list_length _ KL, of_list_length _ VL) n with (blocks, (kk,vv)) =>
          FunGenerate RI (v, k, z) (Z.of_nat ((32 * n)%nat)) 
          = generate_algorithm_success (firstn (32 * n) (bitsToBytes (flatten (map (@Vector.to_list _ 256) blocks))))
                                       (bitsToBytes (@Vector.to_list _ 256 vv), bitsToBytes (@Vector.to_list _ 256 kk), z+1)
    end.
Proof.
  remember (GenUpdate_original_Bvec
        (of_list_length (bytesToBits k) KL,
        of_list_length (bytesToBits v) VL) n) as p; destruct p as [blocks [kk vv]]; symmetry in Heqp.
  
  specialize (GenUpdate_original_Bvec_correct (of_list_length (bytesToBits k) KL,
         of_list_length (bytesToBits v) VL) n). rewrite Heqp. 
  intros Q; rewrite Q; clear Q.
  specialize (Generate_Bvec_ok RI k v z n Z N KL VL). rewrite Heqp; clear Heqp.
  intros W; rewrite W, map_rev; trivial. 
Qed.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.

Lemma Bridge s I n bytes J ss (M: mbedtls_HMAC256_DRBG_generate_function s I n [] = ENTROPY.success (bytes, J) ss):
  match I with HMAC256DRBGabs K V reseed_counter entropy_len prediction_resistance reseed_interval =>
  reseed_counter <= reseed_interval -> prediction_resistance = false ->
  match J with (ws,sstrength,prflag) =>
  s=ss /\ FunGenerate reseed_interval (V,K,reseed_counter) n = DRBG_functions.generate_algorithm_success bytes ws
  end end.
Proof. destruct I. destruct J as [[ws sstrength] prf].
Transparent FunGenerate. simpl. Opaque FunGenerate. simpl in M.
remember (n >? 1024) as d; destruct d; try discriminate.
rewrite andb_negb_r in M. intros; subst.
apply Zgt_is_gt_bool_f in H. rewrite H.
remember (HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z HMAC256 key V n) as p; destruct p.
unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm in M; simpl in M.
rewrite H, <- Heqp in M. inv M; split; trivial.
Qed.

(*The function occurring in the VST spec of mbedtls' random function ie no additional input*) 
Definition mbedtls_generate s I n :=
   match mbedtls_HMAC256_DRBG_generate_function s I n [] 
   with ENTROPY.success (bytes, J) ss =>
          match J with ((((VV, KK), RC), _), PR) =>
            Some (bytes, ss, HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                                 (hmac256drbgabs_reseed_interval I))
          end
      | _ => None  
   end.

Lemma Bridge' s I n bytes F ss (M: mbedtls_generate s I n = Some(bytes, ss, F)):
  match I with HMAC256DRBGabs K V reseed_counter entropy_len prediction_resistance reseed_interval =>
  reseed_counter <= reseed_interval -> prediction_resistance = false ->
  match F with HMAC256DRBGabs KK VV rc _ _ _ =>
  s=ss /\ rc=reseed_counter+1 /\
  FunGenerate reseed_interval (V,K,reseed_counter) n = DRBG_functions.generate_algorithm_success bytes ((VV,KK), rc)
  end end.
Proof. destruct I. destruct F. Transparent FunGenerate. simpl. Opaque FunGenerate.
unfold mbedtls_generate in M. simpl in M.
remember (n >? 1024) as d; destruct d; try discriminate.
rewrite andb_negb_r in M. intros; subst.
apply Zgt_is_gt_bool_f in H.  rewrite H.
remember (HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z HMAC256 key V n) as p; destruct p.
unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm in M; simpl in M.
rewrite H, <- Heqp in M. inv M; auto. 
Qed.

Lemma Bridge_ok' s I (n:nat) bytes F ss (M: mbedtls_generate s I (32 * Z.of_nat n) = Some(bytes, ss, F)) (N:(0 < n)%nat):
  match I with HMAC256DRBGabs k v reseed_counter entropy_len prediction_resistance reseed_interval =>
  reseed_counter <= reseed_interval -> prediction_resistance = false ->
  forall (KL: Datatypes.length (bytesToBits k) = 256%nat) (VL:Datatypes.length (bytesToBits v) = 256%nat),
  match F with HMAC256DRBGabs KK VV rc _ _ _ =>
  s=ss /\ rc=reseed_counter+1 /\
    match GenUpdate_original_core (Blist.of_list_length _ KL, Blist.of_list_length _ VL) n with (blocks, kv) =>
    bitsToBytes (@Vector.to_list _ 256 (fst kv)) = KK /\ 
    bitsToBytes (@Vector.to_list _ 256 (snd kv)) = VV /\
          bytes = firstn (32 * n) (bitsToBytes (Fold.flatten (map (@Vector.to_list _ 256) blocks)))
    end
  end end.
Proof.
 specialize (Bridge' _ _ _ _ _ _ M); destruct I; intros.
 specialize (H H0 H1). destruct F. destruct H as [HH1 [HH2 HH3]].
 split; trivial. split; trivial.
 specialize (Generate_ok' reseed_interval key V reseed_counter n H0 bytes V0 key0 reseed_counter0).
 rewrite Nat2Z.inj_mul. simpl. rewrite HH3.
 clear HH3 M.
 intros ZZ. specialize (ZZ N KL VL (eq_refl _)).
 remember (HMAC_DRBG_nonadaptive.Gen_loop HMAC_Bvec
           (Blist.of_list_length (bytesToBits key) KL)
           (Blist.of_list_length (bytesToBits V) VL) n) as q.
 destruct q. destruct ZZ as [_ ZZ].   apply ZZ.
Qed.

Lemma GenUpdate_original_core_length: forall n state l m
  (G: GenUpdate_original_core state n = (l,m)),
   Datatypes.length l = n%nat.
Proof. induction n; destruct state; simpl; intros. 
+ inv G. simpl; omega.
+ remember (HMAC_DRBG_nonadaptive.Gen_loop HMAC_Bvec b
           (HMAC_Bvec b (HMAC_DRBG_nonadaptive.to_list b0)) n) as q.
  destruct q.  inv G. simpl. symmetry in Heqq. apply Genloop_Zlength_blocks in Heqq. 
  rewrite (Zlength_correct l0) in Heqq. apply Nat2Z.inj in Heqq. subst; trivial.
Qed.

Lemma fold_vector_length: forall l m,
fold_left
  (fun (acc : nat) (a : Vector.t bool 256) =>
   (acc + Datatypes.length (Vector.to_list a))%nat) l m =
  (m + Datatypes.length l * 256)%nat.
Proof. induction l; simpl; intros. + omega.
+ rewrite IHl, Blist.to_list_length; clear IHl. omega.
Qed. 

Lemma mbedtls_generate_Bridge s I (n:nat) bytes F ss (M: mbedtls_generate s I (32 * Z.of_nat n) = Some(bytes, ss, F)) (N:(0 < n)%nat):
  match I with HMAC256DRBGabs k v reseed_counter entropy_len prediction_resistance reseed_interval =>
  reseed_counter <= reseed_interval -> prediction_resistance = false ->
  forall (KL: Datatypes.length (bytesToBits k) = 256%nat) (VL:Datatypes.length (bytesToBits v) = 256%nat),
  match F with HMAC256DRBGabs KK VV rc _ _ _ =>
  s=ss /\ rc=reseed_counter+1 /\
    match GenUpdate_original_core (Blist.of_list_length _ KL, Blist.of_list_length _ VL) n with (blocks, kv) =>
    bitsToBytes (@Vector.to_list _ 256 (fst kv)) = KK /\ 
    bitsToBytes (@Vector.to_list _ 256 (snd kv)) = VV /\
          bytes = (bitsToBytes (Fold.flatten (map (@Vector.to_list _ 256) blocks)))
    end
  end end.
Proof.
 specialize (Bridge_ok' _ _ _ _ _ _ M N); destruct I; intros.
 specialize (H H0 H1 KL VL). destruct F. destruct H as [HH1 [HH2 HH3]].
 split; trivial. split; trivial.
 remember (GenUpdate_original_core
          (Blist.of_list_length (bytesToBits key) KL,
          Blist.of_list_length (bytesToBits V) VL) n) as q. destruct q.
 rewrite sublist.firstn_same in HH3. trivial.
 symmetry in Heqq. apply GenUpdate_original_core_length in Heqq.
 assert (Datatypes.length (bitsToBytes (Fold.flatten (map Vector.to_list l))) = (32*n)%nat).
 apply bitsToBytes_len_gen. rewrite CompFold.length_flatten. simpl. rewrite CompFold.fold_left_map_eq.
 subst n. rewrite fold_vector_length. simpl. rewrite (mult_comm 32). rewrite <- mult_assoc.
 replace (32*8)%nat with 256%nat. trivial. omega.
 rewrite H. omega.
Qed.  

Require Import fcf.FCF.
Definition AsGame {A} f (a:A) : Comp (list (Bvector 256) * KV 256) := ret(f a).
Definition Generate_refactored state := AsGame (GenUpdate_original_core state). 

Lemma Refactored kv n: 
     comp_spec (fun x y => x=y)
               (@Generate _ HMAC_Bvec eqDecState kv n)
               (*(AsGame (GenUpdate_original_core kv) n)*) (ret (GenUpdate_original_core kv n)).
Proof.
  unfold AsGame, Generate, GenUpdate_original_core.
  destruct kv as [k v]. prog_simp. apply comp_spec_ret; trivial. 
Qed.

Lemma OK256: (256 <> 0)%nat. Proof. omega. Qed.

Definition Instantiated_G1_G2_close := G1_G2_close OK256 HMAC_Bvec eqDecState.
(*How should we instantiate blocksPerCall numCalls : nat,
       (numCalls > 0)%nat ->
       (blocksPerCall > 0)%nat ->?*)
(* final theorem? 
Theorem X_close kv :
  | Pr[AsGame (GenUpdate_original_core kv)] - Pr[@G_ideal 256] | <= (numCalls / 1) * Gi_Gi_plus_1_bound.
Proof.
  rewrite Generate_move_v_update.
  rewrite G_real_is_first_hybrid.
  rewrite G_ideal_is_last_hybrid.
  specialize (hybrid_argument (fun i => Pr[Gi_prg i]) Gi_adjacent_hybrids_close numCalls).
  intuition.
Qed.

(*Temporary stuff
Definition Generate_refactored (state : KV 256) (n : nat) :
  Comp (list (Bvector 256) * KV 256) := ret (GenUpdate_original_core state n).

Lemma Refactored kv n: 
     comp_spec (fun x y => x=y)
               (@Generate _ HMAC_Bvec eqDecState kv n)
               (Generate_refactored kv n).
Proof.
  unfold Generate, Generate_refactored, GenUpdate_original_core.
  destruct kv as [k v]. prog_simp. apply comp_spec_ret; trivial. 
Qed.*)
(*Could now optionally FCF-relate GenUpdate_original_refactored to Generate, for 
  relational spec relating bvectors to list byte,  using the above Gallina equalities*)*)
