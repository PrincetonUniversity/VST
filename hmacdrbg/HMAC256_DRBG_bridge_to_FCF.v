Require Import hmacdrbg.spec_hmac_drbg.
Require Import fcf.HMAC_DRBG_definitions_only.
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

Fixpoint flatten {A} (l: list (list A)):list A :=
  match l with nil => nil
  | List.cons h t => h ++ (flatten t)
  end.

Lemma flatten_app {A}: forall (l1 l2:list (list A)), flatten (l1++l2) = flatten l1 ++ flatten l2.
Proof. induction l1; simpl; intros. trivial.
rewrite IHl1, app_assoc; trivial.
Qed.

Definition Instantiate (entropy nonce: list Z) : DRBG_functions.DRBG_working_state :=
HMAC256_DRBG_instantiate_algorithm  entropy nonce nil 0. 

Definition reseedInterval:Z := 100000.
Definition Generate_NoAddin_C (WS: DRBG_functions.DRBG_working_state) n: DRBG_functions.DRBG_generate_algorithm_result :=
           HMAC256_DRBG_generate_algorithm reseedInterval
                                           WS
                                           n
                                           nil.

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

Lemma Genloop_lenV : forall n eta k f v v' k',
  @Gen_loop eta f k v n = (v',k') -> 
  Zlength v' = Z.of_nat n.
Proof. 
  induction n.
+ simpl; intros. inv H. apply Zlength_nil. 
+ intros. simpl in H. remember (Gen_loop f k (f k (to_list v)) n).
  destruct p. inversion H; clear H. subst.
  symmetry in Heqp. apply IHn in Heqp. 
  replace (Z.of_nat (S n)) with (1+Z.of_nat n). 
  2: symmetry; apply (Nat2Z.inj_add 1 n).
  rewrite <- Heqp. rewrite Zlength_cons. omega. 
Qed. 

Lemma to_list_eq (A : Type) (n : nat) l: to_list l = @Vector.to_list A n l.
Proof. reflexivity. Qed.

(*rc: reseedcounter*)
Definition KVasWS (rc:Z)(kv:KV 256): DRBG_working_state :=
  match kv with (k,v) => (bitsToBytes (to_list v), bitsToBytes (to_list k), rc) end.

Definition HMAC_Blist (k: Blist)(data: Blist): Blist :=
  bytesToBits (HMAC256 (bitsToBytes data) (bitsToBytes k)).

Definition HMAC_Bvec (k: Bvector.Bvector 256)(data: Blist): Bvector.Bvector 256.
  apply (of_list_length (bytesToBits (HMAC256 (bitsToBytes data) (bitsToBytes (to_list k)) ))).
  rewrite bytesToBits_len, hmac_common_lemmas.HMAC_length. reflexivity.
Defined.

Lemma CONV k' v: bitsToBytes (to_list (HMAC_Bvec k' v)) = HMAC256  (bitsToBytes v) (bitsToBytes (to_list k')).
Proof. unfold HMAC_Bvec. rewrite to_list_eq, HMAC_equivalence.of_length_proof_irrel, bytes_bits_bytes_id; trivial.
  apply isbyteZ_HMAC256.
Qed.

(*Variant of fcf.HMAC_DRBG_definitions_only.Gen_loop that
  - specializes eta to 256
  - specializes f to HMAC256
  - carries around t (=temp, the list of bits generated so far -- note different base case
  - replaces v'::bits with bits++[v']*)
Fixpoint Gen_loop_Bvec (k : Bvector 256) (t: list (Bvector 256)) (v : Bvector 256) (n : nat)
  : list (Bvector 256) * Bvector 256 :=
  match n with
  | O => (t, v)
  | S n' =>
    let v' := HMAC_Bvec k (to_list v) in
    let (bits, v'') := Gen_loop_Bvec k t v' n' in
    (List.app bits (List.cons v' List.nil), v'')     
  end.

Lemma GenloopBvec_lenV k: forall n v t v' k',
  Gen_loop_Bvec k t v n = (v',k') -> 
  Zlength v' = Zlength t + Z.of_nat n.
Proof. 
  induction n.
+ simpl; intros. inv H. omega. 
+ intros. simpl in H. remember (Gen_loop_Bvec k t(HMAC_Bvec k (to_list v)) n).
  destruct p. inversion H; clear H. subst.
  symmetry in Heqp. apply IHn in Heqp. 
  replace (Z.of_nat (S n)) with (1+Z.of_nat n). 
  2: symmetry; apply (Nat2Z.inj_add 1 n).
  rewrite sublist.Zlength_app, Zlength_cons, Zlength_nil, Heqp. omega. 
Qed.

(*Lemma stating the relationship between Genloop_bvec and the corresponding
  specialization of Gen_loop*)
Lemma GenloopBvec_Gen_loop k: forall n t v v' k',
  Gen_loop_Bvec k t v n = (v',k') ->
  exists vv', v'=t++vv' /\  
              Gen_loop HMAC_Bvec k v n = (rev vv', k').
Proof. 
  induction n.
+ simpl; intros. inv H. exists nil. rewrite app_nil_r. split; trivial.
+ intros. simpl in H. remember (Gen_loop_Bvec k t (HMAC_Bvec k (to_list v)) n).
  destruct p. inversion H; clear H. subst.
  symmetry in Heqp. apply IHn in Heqp; clear IHn.
  destruct Heqp as [vv' [L VV']]; subst l.
  exists (vv' ++ (HMAC_Bvec k (to_list v)::nil)).
  split. rewrite app_assoc. reflexivity. 
  rewrite rev_app_distr. simpl. rewrite VV'; trivial.
Qed.

(*Variant of Gen_loop_bvec that uses Blist instead of Bvector 256*)
Fixpoint Gen_loop_Blist (k : Blist) (t: list Blist) (v : Blist) (n : nat)
  : list Blist * Blist :=
  match n with
  | O => (t, v)
  | S n' =>
    let v' := HMAC_Blist k v in
    let (bits, v'') := Gen_loop_Blist k t v' n' in
    (List.app bits (List.cons v' List.nil), v'')     
  end.

Lemma HMAC_Blist_Bvec v k: HMAC_Blist (to_list k) v = to_list (HMAC_Bvec k v).
Proof. unfold HMAC_Blist, HMAC_Bvec. rewrite HMAC_equivalence.of_length_proof_irrel; trivial. Qed.

(*Relationship between Gen_loop_Blist and Gen_loop_bvec*)
Lemma Gen_loop_Blist_Bvec k: forall n t v bytes V,
  Gen_loop_Blist k t v n = (bytes, V) -> forall kv tv vv bytesv Vv,
  Gen_loop_Bvec kv tv vv n = (bytesv, Vv) ->
  k = to_list kv -> t = (map (@Vector.to_list _ 256) tv) -> v = to_list vv ->
  V = to_list Vv /\ bytes = map (@Vector.to_list _ 256) bytesv.
Proof. 
induction n; simpl; intros; subst.
+ inv H; inv H0. split; trivial.
+ remember (Gen_loop_Blist (to_list kv) (map Vector.to_list tv) (HMAC_Blist (to_list kv) (to_list vv)) n) as p. destruct p.
  inv H; symmetry in Heqp.
  remember (Gen_loop_Bvec kv tv (HMAC_Bvec kv (to_list vv)) n) as q. destruct q.
  inv H0; symmetry in Heqq. 
  destruct (IHn _ _ _ _ Heqp kv tv (HMAC_Bvec kv (to_list vv)) _ _ Heqq) as [A B]; trivial.
    apply HMAC_Blist_Bvec.
  subst. rewrite HMAC_Blist_Bvec. split; trivial.
  rewrite to_list_eq, list_append_map. trivial.
Qed.

Lemma Gen_loop_Blist_cons k: forall n t v bytes V x,
  Gen_loop_Blist k (x::t) v n = (bytes, V) -> 
  exists bytes1, Gen_loop_Blist k t v n = (bytes1, V) /\ bytes = cons x bytes1.
Proof. induction n; simpl; intros.
+ inv H. exists t. split; trivial.
+ remember (Gen_loop_Blist k (x :: t) (HMAC_Blist k v) n) as q. 
  destruct q; symmetry in Heqq. 
  inv H.
  destruct (IHn _ _ _ _ _ Heqq) as [zz [ZZ A]]; clear IHn.
  subst. rewrite ZZ. exists (zz ++ HMAC_Blist k v :: nil).
  split; trivial.
Qed.
Lemma Gen_loop_Blist_app k: forall n t1 t2 v bytes V,
  Gen_loop_Blist k (t1++t2) v n = (bytes, V) -> 
  exists bytes1, Gen_loop_Blist k t2 v n = (bytes1, V) /\ bytes = t1 ++ bytes1.
Proof. induction n; simpl; intros.
+ inv H. exists t2. split; trivial.
+ remember (Gen_loop_Blist k (t1++t2) (HMAC_Blist k v) n) as q. 
  destruct q; symmetry in Heqq. 
  inv H.
  destruct (IHn _ _ _ _ _ Heqq) as [zz [ZZ A]]; clear IHn.
  subst. rewrite ZZ, <- app_assoc. exists (zz ++ HMAC_Blist k v :: nil).
  split; trivial.
Qed.

(*Variant of Gen_loop_bvec that uses list Z instead of Bvector 256*)
Fixpoint Gen_loop_Zlist (k : list Z) (t: list (list Z)) (v : list Z) (n : nat)
  : list (list Z) * (list Z) :=
  match n with
  | O => (t, v)
  | S n' =>
    let v' := HMAC256 v k in
    let (bits, v'') := Gen_loop_Zlist k t v' n' in
    (List.app bits (List.cons v' List.nil), v'')     
  end.

Lemma Gen_loop_Zlist_Blist k (K: Forall isbyteZ k): forall n t v (V: Forall isbyteZ v),
  match Gen_loop_Zlist k t v n with (uu,vv) =>
        Gen_loop_Blist (bytesToBits k) (map bytesToBits t) (bytesToBits v) n
        = (map bytesToBits uu, bytesToBits vv)
  end.
Proof. induction n; intros.
+ simpl; trivial.
+ simpl. remember (Gen_loop_Zlist k t (HMAC256 v k) n). 
  destruct p. specialize (IHn t (HMAC256 v k)).
  rewrite <- Heqp in IHn; clear Heqp.
  remember (Gen_loop_Blist (bytesToBits k) (map bytesToBits t)
     (HMAC_Blist (bytesToBits k) (bytesToBits v)) n) as q.
  destruct q. unfold HMAC_Blist in *.
  rewrite ! bytes_bits_bytes_id in *; trivial.
  rewrite IHn in Heqq; clear IHn. inv Heqq. f_equal.
  rewrite map_app; trivial. apply isbyteZ_HMAC256.
Qed.

Lemma Gen_loop_Zlist_cons k: forall n t v bytes V x,
  Gen_loop_Zlist k (x::t) v n = (bytes, V) -> 
  exists bytes1, Gen_loop_Zlist k t v n = (bytes1, V) /\ bytes = cons x bytes1.
Proof. induction n; simpl; intros.
+ inv H. exists t. split; trivial.
+ remember (Gen_loop_Zlist k (x :: t) (HMAC256 v k) n) as q. 
  destruct q; symmetry in Heqq. 
  inv H.
  destruct (IHn _ _ _ _ _ Heqq) as [zz [ZZ A]]; clear IHn.
  subst. rewrite ZZ. exists (zz ++ HMAC256 v k :: nil).
  split; trivial.
Qed.
Lemma Gen_loop_Zlist_app k: forall n t1 t2 v bytes V,
  Gen_loop_Zlist k (t1++t2) v n = (bytes, V) -> 
  exists bytes1, Gen_loop_Zlist k t2 v n = (bytes1, V) /\ bytes = t1 ++ bytes1.
Proof. induction n; simpl; intros.
+ inv H. exists t2. split; trivial.
+ remember (Gen_loop_Zlist k (t1++t2) (HMAC256 v k) n) as q. 
  destruct q; symmetry in Heqq. 
  inv H.
  destruct (IHn _ _ _ _ _ Heqq) as [zz [ZZ A]]; clear IHn.
  subst. rewrite ZZ, <- app_assoc. exists (zz ++ HMAC256 v k :: nil).
  split; trivial.
Qed.

Import ListNotations.
Goal forall k v, Gen_loop_Zlist k nil v 3 = 
  ( ([HMAC256 (HMAC256 (HMAC256 v k) k) k;
      HMAC256 (HMAC256 v k) k;
      HMAC256 v k]%list),
    HMAC256 (HMAC256 (HMAC256 v k) k) k). reflexivity. Qed. 

Goal forall k v P, HMAC_DRBG_generate_algorithm HMAC256 10000
            (v,k,0) 3 nil = P.
intros. simpl. Admitted.

Goal forall k v P Q, HMAC_DRBG_generate_helper_Z HMAC256 k v 65 = (P,Q).
intros. unfold HMAC_DRBG_generate_helper_Z. simpl. Admitted.

Lemma Gen_loop_Zlist_nestedV k: forall n t v a b aa bb,
  Gen_loop_Zlist k t (HMAC256 v k) n = (a, b) ->
  Gen_loop_Zlist k t v n = (aa, bb) ->
  b = HMAC256 bb k /\
  exists x, a = t++ map (fun z => HMAC256 z k) x /\ aa = t++x.
Proof. induction n; intros.
+ simpl in *. inv H; inv H0. split; trivial.
  exists nil; simpl; rewrite app_nil_r. split; trivial.
+ simpl in *. remember (Gen_loop_Zlist k t (HMAC256 v k) n) as p.
  remember (Gen_loop_Zlist k t (HMAC256 (HMAC256 v k) k) n) as q.
  destruct p; destruct q. inv H. symmetry in Heqp, Heqq.
  specialize (IHn t (HMAC256 v k)).
  rewrite Heqq, Heqp in IHn; clear Heqq Heqp. inv H0.
  specialize (IHn _ _ _ _ (eq_refl _) (eq_refl _)). 
  destruct IHn as [? [? [? ?]]]. subst l l1 b.
  split; trivial. 
  exists (x ++ [HMAC256 v k]). rewrite map_app. 
  do 2 rewrite <- app_assoc. split; trivial.
Qed.

Lemma Gen_loop_Zlist_nestedV' k: forall n t v a b,
  Gen_loop_Zlist k t (HMAC256 v k) n = (a, b) ->
  exists aa bb,
  Gen_loop_Zlist k t v n = (aa, bb) /\
  b = HMAC256 bb k /\
  exists x, a = t++ map (fun z => HMAC256 z k) x /\ aa = t++x.
Proof. induction n; intros.
+ simpl in *. inv H. exists a, v. split; trivial. split; trivial.
  exists nil; simpl; rewrite app_nil_r. split; trivial.
+ simpl in *. remember (Gen_loop_Zlist k t (HMAC256 v k) n) as p.
  remember (Gen_loop_Zlist k t (HMAC256 (HMAC256 v k) k) n) as q.
  destruct p; destruct q. inv H. symmetry in Heqp, Heqq.
  specialize (IHn t (HMAC256 v k) _ _ Heqq).
  rewrite Heqp in IHn; clear Heqq Heqp. 
  destruct IHn as [aa [bb [AB [? [? [? ?]]]]]]. subst aa l1 b.
  inv AB. eexists; eexists; split. reflexivity.
  split; trivial. 
  exists (x ++ [HMAC256 v k]). rewrite map_app. 
  do 2 rewrite <- app_assoc. split; trivial.
Qed.

Definition Equiv n:= forall k v a b,
   Gen_loop_Zlist k nil v n = (a,b) ->
   HMAC_DRBG_generate_helper_Z HMAC256 k v (32*(Z.of_nat n-1)+1) = (b,flatten (rev a)).

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

Lemma E_aux k: forall n v l bb,
               Gen_loop_Zlist k [] (HMAC256 v k) n = (l, bb) ->
      flatten (rev l) ++ HMAC256 bb k =
      HMAC256 (HMAC256 v k) k ++ flatten (rev (map (fun z : list Z => HMAC256 z k) l)).
Proof. induction n; intros.
+ inv H; simpl. rewrite app_nil_r; trivial.
+ simpl in H.
  remember (Gen_loop_Zlist k [] (HMAC256 (HMAC256 v k) k) n). 
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
  remember (Gen_loop_Zlist k [] (HMAC256 v k) N) as p.
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
  destruct Heqp as [aa [bb [G [X [x [L A]]]]]]. subst.
  rewrite (IHn _ _ _ _ G); clear IHn. replace ([] ++ x) with x in G; trivial.
  simpl. f_equal. rewrite rev_app_distr. simpl.

  simpl in G. remember (Gen_loop_Zlist k [] (HMAC256 v k) n).
  destruct p. inv G. rewrite map_app, ! rev_app_distr, ! flatten_app.
  simpl. rewrite ! app_nil_r, <- app_assoc. f_equal.
  symmetry in Heqp. apply (E_aux k n); trivial.
Qed.
