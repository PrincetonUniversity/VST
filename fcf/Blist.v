(* Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Lists of booleans and related theory. *)

Set Implicit Arguments.

Require Import fcf.StdNat.
Require Export List.
Require Export Bvector.
Require Import Omega.
Require Import fcf.EqDec.
Require Import fcf.Fold.
Require Import Coq.NArith.Ndigits.
Require Import ZArith.
Local Open Scope list_scope.

Definition Blist := list bool.

Definition Blist_eq_dec := (list_eq_dec bool_dec).

Definition Bvector_eq_dec(n : nat)(v1 v2 : Bvector n) : {v1 = v2} + {v1 <> v2}.
apply (EqDec_dec (Bvector_EqDec n)).
Defined.

(* shiftOut gets bits from the head of the list. *)
(* return None when we run out *)
Fixpoint shiftOut(s : Blist)(n : nat) : option (Bvector n * Blist) :=
  match n with
    | 0 => Some ((@Vector.nil bool), s)
    | S n' => 
      match s with
        | nil => None
        | b :: s' => 
          match (shiftOut s' n') with
            | Some (v', s'') => Some (Vector.cons _ b _ v', s'')
            | None => None
          end
      end
  end.

Theorem shiftOut_app : forall (n : nat)(s1 s1' s2 : Blist) v,
  shiftOut s1 n = Some (v, s1') ->
  shiftOut (s1 ++ s2) n = Some (v, s1' ++ s2).

  induction n; simpl in *; intuition.
  destruct s1; simpl in *.
  inversion H; clear H; subst.
  destruct s2; simpl.
  trivial.
  trivial.
  inversion H; clear H; subst.
  rewrite app_comm_cons.
  trivial.
  
  destruct s1; simpl in *.
  discriminate.
  case_eq (shiftOut s1 n); intuition.
  rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.
  erewrite IHn; eauto.
  
  rewrite H0 in H.
  discriminate.

Qed.

Lemma shiftOut_lt : forall ls n,
  length ls < n ->
  shiftOut ls n = None.
  
  induction ls; intuition; simpl in *.
  destruct n.
  omega.
  trivial.
  destruct n.
  omega.
  rewrite IHls.
  trivial.
  omega.
Qed.

Lemma shiftOut_Some : forall (ls : Blist) n,
  length ls >= n ->
  exists p, shiftOut ls n = Some p.
  
  induction ls; intuition; simpl in *.
  assert (n = O).
  omega.
  subst.
  exists ([], nil).
  trivial.
  
  destruct n.
  exists ([], a :: ls).
  trivial.
  assert (length ls >= n).
  omega.
  destruct (IHls n).
  trivial.
  destruct x.
  econstructor.
  rewrite H1.
  eauto.
Qed.

Theorem shiftOut_None_inv : forall n ls,
  shiftOut ls n = None ->
  n > length ls.
  
  induction n; destruct ls; intuition; simpl in *; try discriminate.
  apply gt_n_S.
  eapply IHn.
  case_eq (shiftOut ls n); intuition; trivial.
  rewrite H0 in H.
  destruct p.
  discriminate.
Qed.

Theorem shiftOut_Some_inv : forall n ls v ls',
  shiftOut ls n = Some (v, ls') ->
  (n <= length ls)%nat.
  
  induction n; destruct ls; intuition; simpl in *; try discriminate.
  
  apply le_n_S.
  case_eq (shiftOut ls n); intuition.
  destruct p.
  eauto.
  
  rewrite H0 in H.
  discriminate.
Qed.

Theorem shiftOut_correct_inv : forall n ls ls' v,
  shiftOut ls n = Some (v, ls') ->
  ls = (Vector.to_list v) ++ ls'.
  
  induction n; destruct ls; intuition; simpl in *.
  
  inversion H; clear H; subst.
  simpl.
  trivial.
  
  inversion H; clear H; subst.
  simpl.
  trivial.
  
  discriminate.
  
  case_eq (shiftOut ls n); intuition.
  rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.
  simpl.
  f_equal.
  apply IHn in H0.
  subst.
  trivial.
  
  rewrite H0 in H.
  discriminate.
Qed.



Lemma to_list_length : forall (A : Set)(m : nat)(v : Vector.t A m),
  length (Vector.to_list v) = m.
  
  induction m; intuition.
  rewrite (vector_0 v).
  simpl.
  trivial.
  
  destruct (vector_S v).
  destruct H.
  subst.
  simpl.
  
  f_equal. 
  eapply IHm.
Qed.

Definition of_list_length (A : Set)(m : nat)(ls : list A)(pf : length ls = m) : Vector.t A m :=
  match pf with
    | eq_refl => Vector.of_list ls
  end.

Definition of_sig_list (A : Set)(m : nat)(l : {ls : list A | length ls = m}) : Vector.t A m :=
  match l with
    | exist _ ls pf => (of_list_length ls pf)
  end.

Lemma vector_hd_cons_eq : forall(A : Set)(v : Vector.t A 1),
  v = Vector.cons _ (Vector.hd v) _ (Vector.nil A).

  intuition.
  destruct (vector_S v).
  destruct H.
  subst.
  destruct (vector_0 x0).
  simpl.
  trivial.
Qed.

Lemma shiftOut_0 : forall (s : Blist),
  shiftOut s 0 = Some ([], s).

  intuition.
  destruct s; simpl in *; trivial.
Qed.

Theorem shiftOut_S_None : forall (n : nat)(s s1 : Blist)(v1 : Bvector 1),
  shiftOut s 1 = Some (v1, s1) ->
  shiftOut s1 n = None ->
  shiftOut s (S n) = None.
Abort.

Theorem shiftOut_1_None : forall (n1 n2 : nat)(s : Blist),
  shiftOut s n1 = None ->
  n2 >= n1 ->
  shiftOut s n2 = None.
Abort.

(* Todo : we need a general theorem that covers these sorts of facts.  Something like:
   shiftOut s n1 = Some(_, s1) ->
   shiftOut s1 n2 = x ->
   shiftOut s (n1 + n2) = x *)

Theorem shiftOut_S : forall (n : nat)(s s1 s2 : Blist)(v1 : Bvector 1)(v2 : Bvector n),
  shiftOut s 1 = Some (v1, s1) ->
  shiftOut s1 n = Some (v2, s2) ->
  shiftOut s (S n) = Some (Vector.cons _ (Vector.hd v1) _  v2, s2). 

  destruct n; intuition; simpl in *.
  eapply eq_trans.
  eapply H.
  specialize (shiftOut_0 s1); intuition.
  rewrite H0 in H1.
  inversion H1; clear H1; subst.
  f_equal.
  f_equal.
  eapply vector_hd_cons_eq.
  
  destruct s; intuition; simpl in *.
  discriminate.
  rewrite shiftOut_0 in H.
  inversion H; clear H; subst.
  rewrite H0.
  f_equal.
Qed.

Fixpoint oneList(n : nat) : Blist :=
  match n with
    | 0 => nil
    | S n' => true :: (oneList n')
  end.

Theorem oneList_length : forall n,
  length (oneList n) = n.

  induction n; intuition; simpl in *.
  auto.
Qed.

(* TODO: remove oneVector and replace it with Bvect_true *)
Fixpoint oneVector(n : nat) : Bvector n :=
  match n with
    | 0 => Vector.nil bool
    | S n' => Vector.cons _ true _ (oneVector n')
  end.

Theorem shiftOut_oneList : forall (n : nat),
  shiftOut (oneList n) n = Some (oneVector n, nil).

  induction n; intuition; simpl in *.
  rewrite IHn.
  trivial.
Qed.

Fixpoint getAllBlists(n : nat) : (list Blist) :=
  match n with
    | 0 => nil :: nil
    | S n' => (map (cons true) (getAllBlists n')) ++
      (map (cons false) (getAllBlists n'))
  end.


Fixpoint getAllBlists_app(n : nat) : list Blist :=
  match n with
    | 0 => nil :: nil
    | S n' => (map (fun ls => ls ++ (true :: nil)) (getAllBlists_app n')) ++
      (map (fun ls => ls ++ (false :: nil)) (getAllBlists_app n'))
  end.

Fixpoint getAllBvectors(n : nat) : (list (Bvector n)) :=
  match n with
    | 0 => (Vector.nil bool) :: nil
    | S n' => (map (Vector.cons _ true _) (getAllBvectors n')) ++
      (map (Vector.cons _ false _) (getAllBvectors n'))
  end.

Lemma getAllBvectors_length : forall n,
  length (getAllBvectors n) = (expnat 2 n).
  
  induction n; intuition; simpl in *.
  rewrite app_length.
  repeat rewrite map_length.
  rewrite plus_0_r.
  f_equal; eauto.
Qed.

Lemma getAllBvectors_length_nz : forall n,
  length (getAllBvectors n) > 0.
  
  induction n; intuition; simpl in *.
  rewrite app_length.
  repeat rewrite map_length.
  rewrite <- plus_0_r.
  eapply gt_trans.
  eapply plus_gt_compat_l.
  apply IHn.
  repeat rewrite plus_0_r.
  apply IHn.
Qed.

Theorem in_getAllBvectors : forall (n : nat)(v : Bvector n),
  In v (getAllBvectors n).

  induction v; intuition; simpl.
  auto.
  eapply in_or_app; intuition.
  destruct h.
  left.
  eapply in_map; eauto.
  right.
  eapply in_map; eauto.
Qed.

Lemma vector_tl_eq : forall (A : Set)(n : nat)(v1 v2 : Vector.t A (S n)),
  v1 = v2 ->
  Vector.tl v1 = Vector.tl v2.
  
  intuition.
  specialize (vector_S v1).
  specialize (vector_S v2).
  intuition.
  destruct H0. destruct H0.
  destruct H1. destruct H1.
  subst.
  simpl.
  trivial.
Qed.

Lemma vector_cons_eq : forall (A : Set)(n : nat)(v1 v2 : Vector.t A n)(a1 a2 : A),
  Vector.cons A a1 n v1 = Vector.cons A a2 n v2 ->
  v1 = v2.

  intuition.
  
  apply vector_tl_eq in H.
  simpl in *.
  trivial.

Qed.

Lemma vector_cons_ne : forall (A : Set)(n : nat)(a1 a2 : Vector.t A n)(a : A),
  a1 <> a2 -> 
  Vector.cons A a n a1 <> Vector.cons A a n a2.

  intuition.
  eapply H.
  eapply vector_cons_eq.
  eauto.
Qed.

Lemma map_NoDup : forall (A B : Set)(ls : list A)(f : A -> B),
  NoDup ls ->
  (forall a1 a2, a1 <> a2 -> (f a1) <> (f a2)) ->
  NoDup ((map f) ls).

  induction ls; intuition; simpl in *.

  econstructor.

  inversion H; subst; clear H.
  econstructor.
  intuition.
  apply in_map_iff in H.
  destruct H.
  intuition.
  eapply H0; eauto.
  intuition.
  subst.
  intuition.

  eapply IHls; eauto.
Qed.

Lemma getAllBvectors_NoDup : forall (n : nat),
  NoDup (getAllBvectors n).

  induction n; intuition; simpl in *.
  econstructor.
  eapply in_nil.
  econstructor.

  eapply app_NoDup.
  eapply map_NoDup; eauto.
  intros.
  eapply vector_cons_ne; eauto.
  
  eapply map_NoDup; eauto.
  intros.
  
  eapply vector_cons_ne; eauto.

  intuition.
  apply in_map_iff in H.
  apply in_map_iff in H0.
  destruct H.
  destruct H0.
  intuition.
  subst.
  inversion H.

  intuition.
  apply in_map_iff in H.
  apply in_map_iff in H0.
  destruct H.
  destruct H0.
  intuition.
  subst.
  inversion H.
Qed.

Require Import Permutation.

Lemma getAllBlists_NoDup : forall n,
  NoDup (getAllBlists n).
  
  induction n; intuition; simpl in *.
  econstructor.
  simpl.
  intuition.
  econstructor.
  
  eapply app_NoDup; intuition.
  
  eapply map_NoDup; intuition.
  eapply H.
  inversion H0; subst; intuition.
  
  eapply map_NoDup; intuition.
  eapply H.
  inversion H0; subst; intuition.
  
  apply in_map_iff in H.
  apply in_map_iff in H0.
  destruct H.
  destruct H0.
  intuition.
  subst.
  discriminate.
  
  apply in_map_iff in H.
  apply in_map_iff in H0.
  destruct H.
  destruct H0.
  intuition.
  subst.
  discriminate.
  
Qed.

Lemma getAllBlists_app_NoDup : forall n,
  NoDup (getAllBlists_app n).
  
  induction n; intuition; simpl in *.
  econstructor.
  simpl.
  intuition.
  econstructor.
  
  eapply app_NoDup; intuition.
  
  eapply map_NoDup; intuition.
  eapply H.
  apply app_inj_tail in H0.
  intuition.
  
  eapply map_NoDup; intuition.
  eapply H.
  eapply app_inj_tail in H0.
  intuition.
  
  apply in_map_iff in H.
  apply in_map_iff in H0.
  destruct H.
  destruct H0.
  intuition.
  subst.
  apply app_inj_tail in H; intuition.
  
  apply in_map_iff in H.
  apply in_map_iff in H0.
  destruct H.
  destruct H0.
  intuition.
  subst.
  apply app_inj_tail in H; intuition.

Qed.
    Lemma ls_last_exists : forall (A : Type)(ls : list A) n,
      length ls = (S n) ->
      exists a ls', (length ls' = n /\ ls = ls' ++ (a :: nil)).

      induction ls; intuition; simpl in *.
      omega.

      destruct n.
      destruct ls; simpl in *; try omega.
      exists a. exists nil.
      simpl.
      intuition.

      inversion H; clear H.
      edestruct IHls; intuition.
      eauto.
      destruct H.
      intuition.
      exists x.
      exists (a :: x0).
      subst.
      simpl.
      intuition.
Qed. 

Lemma getAllBlists_app_rel_map : forall n,
  rel_map (fun ls1 ls2 => ls1 = (rev ls2)) (getAllBlists_app n) (getAllBlists n).

  induction n; intuition; simpl in *.
  econstructor.
  econstructor.
  simpl.
  trivial.

  eapply rel_map_app.
  eapply rel_map_map2.
  
  eapply rel_map_impl; eauto; intuition.
  subst.
  simpl.
  trivial.

  eapply rel_map_map2.
  
  eapply rel_map_impl; eauto; intuition.
  subst.
  simpl.
  trivial.
Qed.

Lemma getAllBlists_rel_map : forall n,
  rel_map (fun ls1 ls2 => ls1 = (rev ls2)) (getAllBlists n) (getAllBlists_app n).

  induction n; intuition; simpl in *.
  econstructor.
  econstructor.
  trivial.

  eapply rel_map_app.
  eapply rel_map_map2.
  eapply rel_map_impl; eauto; intuition.
  subst.
  rewrite rev_unit.
  trivial.

  eapply rel_map_map2.
  eapply rel_map_impl; eauto; intuition.
  subst.
  rewrite rev_unit.
  trivial.    
Qed.

Lemma getAllBlists_app_In_length : forall n ls,
  In ls (getAllBlists_app n) ->
  length ls = n.

  induction n; intuition; simpl in *.
  destruct H; subst; intuition.

  apply in_app_or in H;
  destruct H;
  apply in_map_iff in H;
  destruct H;
  intuition;

  subst;
  rewrite app_length; simpl;
  rewrite plus_comm; simpl;
  f_equal;
  eapply IHn; eauto.
Qed.


Lemma getAllBlists_app_length_In : forall n ls,
  length ls = n ->
  In ls (getAllBlists_app n).

  induction n; intuition; simpl in *;
  destruct ls; simpl in *; intuition; try omega.



  edestruct (ls_last_exists (b :: ls)).
  simpl.
  eauto.
  destruct H0.
  intuition.
  rewrite H2.
  eapply in_or_app.
  destruct x; [left | right];
  eapply in_map_iff;
  econstructor; intuition.

Qed.

Lemma getAllBlists_In_length : forall n ls,
  In ls (getAllBlists n) ->
  length ls = n.

  induction n; intuition; simpl in *.
  destruct H; subst; intuition.

  apply in_app_or in H;
  destruct H;
  apply in_map_iff in H;
  destruct H;
  intuition;

  subst;
  simpl;
  f_equal;
  eapply IHn; eauto.
Qed.

Lemma getAllBlists_length_In : forall n ls,
  length ls = n ->
  In ls (getAllBlists n).

  induction n; intuition; simpl in *;
  destruct ls; simpl in *; intuition; try omega.

  apply in_or_app.
 
  destruct b; [left | right];
  eapply in_map_iff; eauto.
Qed. 

Lemma getAllBlists_perm : forall n,
  Permutation (getAllBlists n) (getAllBlists_app n).

  intuition.
  eapply NoDup_Permutation.

  apply getAllBlists_NoDup.
  apply getAllBlists_app_NoDup.

  intuition.

  specialize (getAllBlists_rel_map n); intuition.
  specialize (rel_map_in_inv H0 x); intuition.
  destruct H2.
  intuition.
  subst.

  eapply getAllBlists_app_length_In.
  rewrite rev_length.
  eapply getAllBlists_app_In_length.
  eauto. 

  specialize (getAllBlists_app_rel_map n); intuition.
  specialize (rel_map_in_inv H0 x); intuition.
  destruct H2.
  intuition.
  subst.
  eapply getAllBlists_length_In.
  rewrite rev_length.
  eapply getAllBlists_In_length.
  eauto.
Qed.

Theorem getAllBlists_length : forall n,
  length (getAllBlists n) = (expnat 2 n).
  
  induction n; intuition; simpl in *.
  rewrite app_length.
  repeat rewrite map_length.
  rewrite plus_0_r.
  rewrite <- IHn.
  trivial.
Qed.

Fixpoint tailOpt(A : Set)(n : nat)(v : Vector.t A n) : option (Vector.t A (pred n)):=
  match v with
    | [] => None
    | Vector.cons _ _ _ v => Some v
  end.

Lemma tailOpt_eq : forall (A : Set)(n : nat)(v1 v2 : Vector.t A n),
  v1 = v2 ->
  tailOpt v1 = tailOpt v2.
          
  intuition.
  subst.
  trivial.
Qed.

Lemma vector_cons_eq_inv : forall (A : Set)(n : nat)(a1 a2 : A)(v1 v2 : Vector.t A n),
  Vector.cons A a1 n v1 = Vector.cons A a2 n v2 ->
  a1 = a2 /\ v1 = v2.
  
  intuition.
  inversion H; trivial.
  
  assert (tailOpt (Vector.cons A a1 n v1) = tailOpt (Vector.cons A a2 n v2)).
  
  eapply tailOpt_eq.
  trivial.
  
  simpl in *.
  inversion H0; clear H0; subst.
  trivial.            
Qed.

Lemma pair_eq_inv : forall (A B : Type)(a1 a2 : A)(b1 b2 : B),
  (a1, b1) = (a2, b2) ->
  a1 = a2 /\ b1 = b2.
  
  intros.
  inversion H; clear H; subst.
  intuition.
Qed.

Lemma opt_eq_inv : forall (A : Type)(a1 a2 : A),
  Some a1 = Some a2 ->
  a1 = a2.
  
  intuition.
  inversion H; clear H; subst.
  trivial.
Qed.

Lemma shiftOut_ls_eq : forall n ls1 ls2 v ls1' ls2',
  shiftOut ls1 n = Some (v, ls1') ->
  shiftOut ls2 n = Some (v, ls2') ->
  (firstn n ls1) = (firstn n ls2).
  
  induction n; intuition; simpl in *.
  destruct ls1; simpl in *; try discriminate.
  destruct ls2; simpl in *; try discriminate.
  case_eq (shiftOut ls1 n); intuition.
  rewrite H1 in H.
  case_eq (shiftOut ls2 n); intuition.
  rewrite H2 in H0.
  destruct p.
  destruct p0.
  inversion H; clear H; subst.
  
  apply opt_eq_inv in H0.
  apply pair_eq_inv in H0; intuition.
  apply vector_cons_eq_inv in H; intuition; subst.
  
  f_equal.
  eapply IHn.
  eapply H1.
  eapply H2.
  
  rewrite H2 in H0.
  discriminate.
  rewrite H1 in H.
  discriminate.
Qed.

Lemma le_refl_gen : forall n1 n2,
  (n1 = n2 ->
    n1 <= n2)%nat.
  
  intuition.
Qed.

Lemma app_first_eq : forall (A : Type)(ls2 ls1 ls3 : list A),
  ls1 = ls2 ++ ls3 ->
  length ls1 = length ls2 ->
  ls1 = ls2 /\ ls3 = nil.
  
  intros; subst.
  assert (ls3 = nil).
  rewrite app_length in H0.
  assert (length ls3 = O).
  omega.
  destruct ls3; simpl in *; try omega; trivial.
  subst.
  rewrite app_nil_r.
  intuition.
Qed.

Lemma to_list_eq_inv : forall (A : Set) n (v1 v2 : Vector.t A n),
  VectorDef.to_list v1 = VectorDef.to_list v2 ->
        v1 = v2.
  
  induction n; intuition.
  rewrite (vector_0 v2).
  rewrite (vector_0 v1).
  trivial.
  
  destruct (vector_S v1).
  destruct (vector_S v2).
  destruct H0. 
  destruct H1.
  subst.
  unfold VectorDef.to_list in *.
  inversion H; clear H; subst.
  f_equal.
  eauto.
Qed.

Lemma shiftOut_to_list : forall n (v : Bvector n),
  shiftOut (VectorDef.to_list v) n = Some (v, nil).
  
  intuition.
  
  edestruct (shiftOut_Some (VectorDef.to_list v)).
  eapply le_refl_gen.
  symmetry.
  eapply (to_list_length v).
  destruct x.
  rewrite H.
  apply shiftOut_correct_inv in H.
  
  
  apply app_first_eq in H.
  intuition; subst.
  
  
  apply to_list_eq_inv in H0; subst.
  trivial.
  
  repeat rewrite to_list_length.
  trivial.
Qed.

Lemma shiftOut_app_None : forall ls1 ls2 n,
  shiftOut (ls1 ++ ls2) n = None ->
  shiftOut ls1 n = None.
  
  induction ls1; intuition; simpl in *.
  destruct n; destruct ls2; try discriminate; trivial.
  
  destruct n.
  discriminate.
  
  case_eq (shiftOut (ls1 ++ ls2) n); intuition.
  rewrite H0 in H.
  destruct p.
  discriminate.
  rewrite H0 in H.
  erewrite IHls1.
  trivial.
  eauto.
  
Qed.

Lemma BVxor_same_id : forall n (v : Bvector n),
  BVxor n v v = Bvect_false n.

  induction n; intuition.
  rewrite (vector_0 v).
  simpl.
  unfold Bvect_false.
  simpl.
  trivial.

  destruct (vector_S v).
  destruct H.
  rewrite H.
  unfold Bvect_false.
  simpl.
  rewrite IHn.
  rewrite xorb_nilpotent.
  trivial.

Qed.

Lemma BVxor_comm : forall n (v1 v2 : Bvector n),
  BVxor n v1 v2 = BVxor n v2 v1.

  induction n; intuition.
  rewrite (vector_0 v1).
  rewrite (vector_0 v2).
  trivial.

  destruct (vector_S v1).
  destruct H.
  destruct (vector_S v2).
  destruct H0.
  subst.
  simpl.
  rewrite IHn.
  rewrite xorb_comm.
  trivial.
Qed.

Lemma BVxor_id_r : forall n (v : Bvector n),
  BVxor n v (Bvect_false n) = v.

  induction n; intuition.
  rewrite (vector_0 v).
  unfold Bvect_false.
  simpl.
  trivial.

  destruct (vector_S v).
  destruct H.
  unfold Bvect_false.
  subst.
  simpl.
  rewrite IHn.
  rewrite xorb_false_r.
  trivial.
Qed.


Lemma BVxor_id_l : forall n (v : Bvector n),
  BVxor n (Bvect_false n) v = v.

  intuition.
  rewrite BVxor_comm.
  apply BVxor_id_r.
Qed.

Lemma BVxor_assoc : forall n (v1 v2 v3 : Bvector n),
  BVxor n (BVxor n v1 v2) v3 = BVxor n v1 (BVxor n v2 v3).
  
  induction n; intuition.
  rewrite (vector_0 v1).
  rewrite (vector_0 v2).
  rewrite BVxor_same_id.
  rewrite BVxor_id_l.
  rewrite (vector_0).
  rewrite (vector_0 v3).
  trivial.

  destruct (vector_S v1).
  destruct H.
  destruct (vector_S v2).
  destruct H0.
  destruct (vector_S v3).
  destruct H1.
  subst.
  simpl.
  rewrite IHn.
  rewrite xorb_assoc.
  trivial.
Qed.

Lemma BVxor_id_r_inv : forall n (v1 v2 : Bvector n),
  BVxor n v1 v2 = v1 ->
  v2 = (Bvect_false n).

  intuition.
  rewrite <- BVxor_id_l at 1.
  rewrite <- (BVxor_same_id v1).
  rewrite BVxor_assoc.
  f_equal; intuition.
Qed.

Lemma BVxor_id_inv : forall n (v1 v2 : Bvector n),
  BVxor n v1 v2 = Bvect_false n ->
  v1 = v2.

  intuition.
  rewrite <- BVxor_id_l at 1.
  rewrite <- (BVxor_id_l v2).
  rewrite <- (BVxor_same_id v2) at 1.
  rewrite BVxor_assoc.
  rewrite BVxor_comm.
  f_equal; intuition.
  rewrite BVxor_comm.
  trivial.
Qed.


Definition lognat(n : nat) : nat := 
  N.size_nat (N.of_nat n).

Definition bvToNat(k : nat)(v : Bvector k) :=
  N.to_nat (Bv2N k v).

Lemma Bv2N_zero : forall (n : nat),
  Bv2N n (Bvect_false n) = N0.
  
  induction n; intuition; simpl in *.
  unfold N.double in *.
  unfold Bvect_false in *.
  rewrite IHn.
  trivial.
Qed.

Lemma bvNat_zero : forall n, 
  bvToNat (Bvect_false n) = O.

  intuition.
  unfold bvToNat.
  assert (N.to_nat N0 = O).
  simpl.
  trivial.
  rewrite <- H.
  f_equal.
  eapply Bv2N_zero.
  
Qed.

Definition natToBv(k : nat)(v : nat) : Bvector k :=
  N2Bv_gen k (N.of_nat v).


Lemma Bv2N_app_false : forall n1 n2 (v1 : Bvector n1),
  Bv2N (n1 + n2) (Vector.append v1 (Bvect_false n2)) = Bv2N n1 v1.
  
  induction n1; intuition.
  rewrite (vector_0 v1).
  simpl.
  apply Bv2N_zero.
  
  destruct (vector_S v1).
  destruct H.
  rewrite H.
  simpl.
  destruct x.
  rewrite IHn1.
  trivial.
  rewrite IHn1.
  trivial.
  
Qed.

Lemma Bv2N_N2Bv_gen : forall n0 k,
  n0 >= N.size_nat k ->
  Bv2N n0 (N2Bv_gen n0 k) = k.
  
  intuition.
  assert (exists x, n0 = N.size_nat k + x)%nat.
  exists (minus n0 (N.size_nat k)).
  omega.
  destruct H0.
  rewrite H0.
  rewrite N2Bv_N2Bv_gen_above.
  rewrite Bv2N_app_false.
  apply Bv2N_N2Bv.
Qed.
  
Lemma bvToNat_natToBv_inverse : forall n k,
  n >= lognat k ->
  bvToNat (natToBv n k) = k.
  
  intuition.
  unfold bvToNat, natToBv.
  rewrite Bv2N_N2Bv_gen.
  apply Nnat.Nat2N.id.
  trivial.
Qed.

Lemma Nat_size_nat_monotonic : forall n1 n2,
  (n1 < n2)%N ->
  (N.size_nat n1 <= N.size_nat n2)%nat.
  
  intuition.
  destruct n1; simpl.
  omega.
  destruct n2; simpl.
  inversion H.
  eapply Pos.size_nat_monotone.
  intuition.
Qed.
  
Lemma lognat_monotonic : forall n1 n2,
  (n1 < n2 ->
    lognat n1 <= lognat n2)%nat.
  
  intuition.
  unfold lognat.
  eapply Nat_size_nat_monotonic.
  specialize (Nnat.Nat2N.inj_compare n1 n2); intuition.
  apply nat_compare_lt in H.
  rewrite H in H0.
  case_eq (N.of_nat n1 ?= N.of_nat n2)%N; intuition;
    congruence.
Qed.

Lemma natToBv_bvToNat_inverse : forall n k,
  (natToBv n (bvToNat k)) = k.

  intuition.
  unfold natToBv, bvToNat.
  rewrite Nnat.N2Nat.id.
  apply N2Bv_Bv2N.
Qed.

Lemma bvToNat_natToBv_eq : forall n (v : Bvector n) k,
  bvToNat v = k ->
  v = natToBv n k.

  intuition.
  rewrite <- H.
  symmetry.
  apply natToBv_bvToNat_inverse.
Qed.
