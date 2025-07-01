(* This file are developed by Qinxiang Cao, Shengyi Wang and Aquinas Hobor in 2015 *)
(* summer in Yale-NUS.                                                             *)

Require Import VST.msl.base.
Require Import VST.msl.Extensionality.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.zlist.sublist.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Sorting.Permutation.
Require Export Stdlib.Classes.Morphisms.

Lemma In_Permutation_cons: forall {A : Type} (l : list A) (x : A),
  In x l ->
  exists l', Permutation l (x :: l').
Proof.
  intros.
  induction l.
  + inversion H.
  + destruct H.
    - exists l; subst; reflexivity.
    - destruct (IHl H) as [l' ?].
      exists (a :: l').
      rewrite H0.
      constructor.
Qed.

Lemma incl_Permutation {A: Type}: forall (l1 l2: list A), NoDup l2 -> incl l2 l1 -> exists l', Permutation l1 (l2 ++ l').
Proof.
  intros l1 l2. revert l1. induction l2; intros.
  - exists l1. simpl. auto.
  - rewrite NoDup_cons_iff in H. destruct H. hnf in H0. assert (In a l1) by (apply H0; simpl; auto). assert (incl l2 l1) by (hnf; intros; apply H0; simpl; auto).
    specialize (IHl2 l1 H1 H3). destruct IHl2 as [l3 ?]. assert (In a l3) by (rewrite H4 in H2; apply in_app_or in H2; destruct H2; [exfalso|]; auto).
    apply In_Permutation_cons in H5. destruct H5 as [l4 ?]. rewrite H5 in H4. exists l4. rewrite H4. rewrite <- app_comm_cons. symmetry. apply Permutation_middle.
Qed.

Local Open Scope logic.

Set Implicit Arguments.

Definition sepcon_unique1 {X A} `{SepLog A} (P: X -> A): Prop :=
  forall x, P x * P x |-- FF.

Definition sepcon_unique2 {X Y A} `{SepLog A} (P: X -> Y -> A): Prop :=
  forall x y1 y2, P x y1 * P x y2 |-- FF.

Section IterSepCon.

  Context {A : Type}.
  Context {B : Type}.
  Context {ND : NatDed A}.
  Context {SL : SepLog A}.
  Context {ClS: ClassicalSep A}.
  Context {CoSL: CorableSepLog A}.

Section SingleSepPred.

  Context (p : B -> A).

Fixpoint iter_sepcon (l : list B) : A :=
  match l with
    | nil => emp
    | x :: xl => p x * iter_sepcon xl
  end.

Lemma iter_sepcon_app:
  forall (l1 l2 : list B), iter_sepcon (l1 ++ l2) = iter_sepcon l1 * iter_sepcon l2.
Proof.
  induction l1; intros; simpl. rewrite emp_sepcon; auto. rewrite IHl1. rewrite sepcon_assoc. auto.
Qed.

Lemma iter_sepcon_app_comm: forall (l1 l2 : list B), iter_sepcon (l1 ++ l2) = iter_sepcon (l2 ++ l1).
Proof. intros. do 2 rewrite iter_sepcon_app. rewrite sepcon_comm. auto. Qed.

Lemma iter_sepcon_permutation: forall  (l1 l2 : list B), Permutation l1 l2 -> iter_sepcon l1 = iter_sepcon l2.
Proof.
  intros. induction H; simpl; auto.
  + rewrite IHPermutation. auto.
  + do 2 rewrite <- sepcon_assoc. rewrite (sepcon_comm (p y)). auto.
  + rewrite IHPermutation1. auto.
Qed.

Lemma iter_sepcon_in_true: forall (l : list B) x, In x l -> iter_sepcon l |-- p x * TT.
Proof.
  intros. apply in_split in H. destruct H as [l1 [l2 ?]]. subst.
  rewrite iter_sepcon_app_comm. rewrite <- app_comm_cons. simpl.
  apply sepcon_derives; auto. apply TT_right.
Qed.

Lemma iter_sepcon_incl_true: forall (l s: list B),
    NoDup s -> incl s l -> iter_sepcon l |-- iter_sepcon s * TT.
Proof.
  intros. destruct (incl_Permutation l s H H0) as [l' ?].
  apply iter_sepcon_permutation in H1. rewrite H1, iter_sepcon_app.
  apply sepcon_derives; auto. apply TT_right.
Qed.

Lemma iter_sepcon_unique_nodup: forall (l : list B), sepcon_unique1 p -> iter_sepcon l |-- !!(NoDup l).
Proof.
  intros. induction l.
  + apply prop_right. constructor.
  + simpl.
    assert (p a * iter_sepcon l |-- !!(~ In a l)). {
      apply not_prop_right.
      intros. apply iter_sepcon_in_true in H0.
      apply derives_trans with (p a * p a * TT).
      + rewrite sepcon_assoc. apply sepcon_derives. apply derives_refl. auto.
      + specialize (H a). apply derives_trans with (FF * TT).
        apply sepcon_derives; auto. rewrite sepcon_comm, sepcon_FF. apply derives_refl.
    }
  apply derives_trans with (!!(NoDup l) && !!(~ In a l)).
  - apply andp_right; auto. rewrite (add_andp _ _ IHl). normalize.
  - normalize. constructor; auto.
Qed.

Lemma iter_sepcon_emp': forall (l : list B), (forall x, In x l -> p x = emp) -> iter_sepcon l = emp.
Proof.
  induction l; intros; simpl; auto.
  rewrite H, IHl, sepcon_emp; simpl; auto.
  intros; apply H; simpl; auto.
Qed.

Lemma iter_sepcon_emp: forall (l l' : list B), (forall x, p x |-- emp) -> NoDup l' -> incl l' l -> iter_sepcon l |-- iter_sepcon l'.
Proof.
  intros.
  revert l H1; induction l'; intros.
  + simpl; clear H1.
    induction l; simpl; auto.
    rewrite <- (emp_sepcon emp).
    apply sepcon_derives; auto.
  + inversion H0; subst.
    spec IHl'; [auto |].
    assert (In a l) by (specialize (H1 a); simpl in H1; auto).
    apply in_split in H2.
    destruct H2 as [l1 [l2 ?]].
    specialize (IHl' (l1 ++ l2)).
    spec IHl'.
    {
      clear - H2 H1 H4.
      intros x ?H.
      specialize (H1 x).
      spec H1; [simpl; auto |].
      subst.
      rewrite in_app_iff in H1; simpl in H1.
      rewrite in_app_iff.
      assert (a = x -> False) by (intros; subst; tauto).
      tauto.
    }
    subst.
    rewrite iter_sepcon_app in *.
    simpl.
    rewrite (sepcon_comm (p a)), <- sepcon_assoc, (sepcon_comm _ (p a)).
    apply sepcon_derives; auto.
Qed.

Lemma iter_sepcon_nil: iter_sepcon nil = emp.
Proof. intros; reflexivity. Qed.

End SingleSepPred.

Lemma iter_sepcon_sepcon: forall (f g1 g2: B -> A) l,
     (forall b : B, f b = g1 b * g2 b) ->
  iter_sepcon f l = iter_sepcon g1 l * iter_sepcon g2 l.
Proof.
  intros; induction l; simpl.
  autorewrite with norm; auto.
  rewrite H, IHl.
  rewrite !sepcon_assoc.
  f_equal.
  rewrite sepcon_comm.
  rewrite !sepcon_assoc.
  f_equal.
  apply sepcon_comm.
Qed.

Lemma iter_sepcon_sepcon': forall g1 g2 (l : list B),
  iter_sepcon (fun x => g1 x * g2 x) l = iter_sepcon g1 l * iter_sepcon g2 l.
Proof.
  intros. apply iter_sepcon_sepcon. easy.
Qed.

Lemma iter_sepcon_derives :
   forall f g (l : list B), (forall x, In x l -> f x |-- g x) -> iter_sepcon f l |-- iter_sepcon g l.
Proof.
  induction l; simpl; auto; intros.
  apply sepcon_derives; auto.
Qed.

Lemma iter_sepcon_func: forall l P Q, (forall x, P x = Q x) -> iter_sepcon P l = iter_sepcon Q l.
Proof. intros. induction l; simpl; [|f_equal]; auto. Qed.

Lemma iter_sepcon_func_strong: forall l P Q, (forall x, In x l -> P x = Q x) -> iter_sepcon P l = iter_sepcon Q l.
Proof.
  intros. induction l.
  + reflexivity.
  + simpl.
    f_equal.
    - apply H.
      simpl; auto.
    - apply IHl.
      intros; apply H.
      simpl; auto.
Qed.

#[global] Instance iter_sepcon_permutation_proper : Proper ((pointwise_relation B eq) ==> (@Permutation B) ==> eq) iter_sepcon.
Proof.
  repeat intro. transitivity (iter_sepcon x y0).
  + apply iter_sepcon_permutation. auto.
  + apply iter_sepcon_func.
    exact H.
Qed.

Lemma iter_sepcon_Znth: forall {d : Inhabitant B} f (l : list B) (i: Z), (0 <= i < Zlength l)%Z ->
  iter_sepcon f l = f (Znth i l) * iter_sepcon f (remove_Znth i l).
Proof.
  intros; unfold remove_Znth.
  rewrite <- sublist_same at 1 by auto.
  rewrite sublist_split with (mid := i) by lia.
  rewrite (sublist_next i) by lia.
  rewrite !iter_sepcon_app; simpl.
  rewrite <- !sepcon_assoc. f_equal.
  apply sepcon_comm.
Qed.

#[global] Arguments iter_sepcon_Znth {d} f l i.

Lemma iter_sepcon_Znth_remove : forall {d : Inhabitant B} f (l: list B) i j,
  (0 <= i < Zlength l)%Z -> (0 <= j < Zlength l)%Z -> i <> j ->
  iter_sepcon f (remove_Znth j l) =
  f (Znth i l) * iter_sepcon f (remove_Znth (if Z_lt_dec i j then i else i - 1) (remove_Znth j l)).
Proof.
  intros ????? Hi Hj Hn.
  pose proof (Zlength_remove_Znth _ _ Hj) as Hlen.
  unfold remove_Znth at 1 2; rewrite Hlen.
  unfold remove_Znth in *.
  destruct (Z_lt_dec i j).
  - rewrite -> !sublist_app by (rewrite -> ?Zlength_app in *; lia).
    autorewrite with sublist.
    rewrite -> (sublist_split 0 i j) by lia.
    rewrite !iter_sepcon_app.
    rewrite -> (sublist_next i _) by lia; simpl.
    replace (Zlength l - _ - _ + _)%Z with (Zlength l) by lia.
    rewrite <- !sepcon_assoc. do 2 f_equal. apply sepcon_comm.
  - rewrite -> !sublist_app by (rewrite -> ?Zlength_app in *; lia).
    autorewrite with sublist.
    rewrite -> (sublist_split (j + 1) i (Zlength l)) by lia.
    rewrite !iter_sepcon_app.
    rewrite -> (sublist_next i _) by lia; simpl.
    replace (Zlength l - _ - _ + _)%Z with (Zlength l) by lia.
    replace (i - _ - _ + _)%Z with i by lia.
    replace (i - _ + _)%Z with (i + 1)%Z by lia.
    rewrite (sepcon_comm (f _) (_ * _ * _)).
    rewrite <- !sepcon_assoc. do 2 rewrite (sepcon_assoc (_ * _)).
    f_equal. apply sepcon_comm.
Qed.

Lemma iter_sepcon_Znth' : forall {d : Inhabitant B} f (l: list B) i,
  (0 <= i < Zlength l)%Z -> iter_sepcon f l = f (Znth i l) * (f (Znth i l) -* iter_sepcon f l).
Proof.
  intros; eapply wand_eq, iter_sepcon_Znth; auto.
Qed.

Lemma iter_sepcon_remove_wand : forall {d : Inhabitant B} f (l: list B) i,
  (0 <= i < Zlength l)%Z -> iter_sepcon f (remove_Znth i l) |-- f (Znth i l) -* iter_sepcon f l.
Proof.
  intros; rewrite <- wand_sepcon_adjoint.
  erewrite (iter_sepcon_Znth _ l) by eauto.
  rewrite sepcon_comm. auto.
Qed.

Lemma iter_sepcon_In : forall (x : B) f (l: list B), In x l -> iter_sepcon f l = f x * (f x -* iter_sepcon f l).
Proof.
  intros.
  apply (@In_Znth _ x) in H as (? & ? & Heq).
  rewrite <- Heq; apply iter_sepcon_Znth'; auto.
Qed.

End IterSepCon.

Lemma iter_sepcon_map: forall {A B C: Type} {ND : NatDed A} {SL : SepLog A} (l : list C) (f : B -> A) (g: C -> B),
                         iter_sepcon (fun x : C => f (g x)) l = iter_sepcon f (map g l).
Proof. intros. induction l; simpl; [|f_equal]; auto. Qed.

Global Existing Instance iter_sepcon_permutation_proper.

Definition uncurry {A B C} (f: A -> B -> C) (xy: A*B) : C :=
  f (fst xy) (snd xy).

Section IterSepCon2.

  Context {A : Type}.
  Context {B1 B2 : Type}.
  Context {ND : NatDed A}.
  Context {SL : SepLog A}.
  Context {ClS: ClassicalSep A}.
  Context {CoSL: CorableSepLog A}.
  Context (p : B1 -> B2 -> A).

Fixpoint iter_sepcon2 (l : list B1) : list B2 -> A :=
    match l with
    | nil => fun l2 =>
       match l2 with
       | nil => emp
       | _ => FF
       end
    | x :: xl => fun l' =>
       match l' with
       | nil => FF
       | y :: yl => p x y * iter_sepcon2 xl yl
       end
  end.

Lemma iter_sepcon2_spec: forall l1 l2,
  iter_sepcon2 l1 l2 = EX l: list (B1 * B2), !! (l1 = map fst l /\ l2 = map snd l) && iter_sepcon (uncurry p) l.
Proof.
  intros.
  apply pred_ext.
  + revert l2; induction l1; intros; destruct l2.
    - apply (exp_right nil); simpl.
      apply andp_right; auto.
      apply prop_right; auto.
    - simpl.
      apply FF_left.
    - simpl.
      apply FF_left.
    - simpl.
      specialize (IHl1 l2).
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IHl1] | clear IHl1].
      normalize.
      destruct H.
      apply (exp_right ((a, b) :: l)).
      simpl.
      apply andp_right; [apply prop_right; subst; auto |].
      apply derives_refl.
  + apply exp_left; intros l.
    normalize.
    destruct H; subst.
    induction l.
    - simpl. auto.
    - simpl.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IHl] | clear IHl].
      apply derives_refl.
Qed.

Lemma iter_sepcon2_Znth: forall {d1 : Inhabitant B1} {d2 : Inhabitant B2}
  (l1 : list B1) (l2 : list B2) i, (0 <= i < Zlength l1)%Z -> Zlength l1 = Zlength l2 ->
  iter_sepcon2 l1 l2 =
  p (Znth i l1) (Znth i l2) * iter_sepcon2 (remove_Znth i l1) (remove_Znth i l2).
Proof.
  intros; rewrite !iter_sepcon2_spec.
  apply pred_ext.
  - apply exp_left. intros l. apply derives_extract_prop. intros [? ?].
    subst. rewrite Zlength_map in *.
    rewrite !remove_Znth_map, !Znth_map, (iter_sepcon_Znth (uncurry p) l i) by auto.
    unfold uncurry at 1. apply sepcon_derives; auto.
    apply exp_right with (remove_Znth i l). apply prop_and_same_derives.
    apply prop_right. auto.
  - rewrite exp_sepcon2. apply exp_left; intros l. apply exp_right with (combine l1 l2).
    rewrite sepcon_andp_prop. apply derives_extract_prop. intros [? ?].
    rewrite combine_fst, combine_snd
      by (rewrite <- !ZtoNat_Zlength; apply Nat2Z.inj; rewrite !Z2Nat.id; lia).
    rewrite (iter_sepcon_Znth _ (combine _ _) i)
      by (rewrite Zlength_combine, Z.min_l; lia).
    rewrite Znth_combine, remove_Znth_combine by auto.
    rewrite H1, H2, combine_eq; unfold uncurry. cbn [fst snd].
    apply prop_and_same_derives. apply prop_right. auto.
all:    apply derives_refl.  (*  We need this for Coq 8.14 and before. *)
Qed.

End IterSepCon2.

Section IterPredSepCon.

  Context {A : Type}.
  Context {B : Type}.
  Context {ND : NatDed A}.
  Context {SL : SepLog A}.
  Context {ClS: ClassicalSep A}.

Definition pred_sepcon (p: B -> A) (P: B -> Prop): A :=
  EX l: list B, !! (forall x, In x l <-> P x) && !! NoDup l && iter_sepcon p l.

Lemma pred_sepcon_eq: forall (P: B -> Prop) (p: B -> A),
    pred_sepcon p P =
    (EX l: list B, !! ((forall x, In x l <-> P x) /\ NoDup l) && iter_sepcon p l).
Proof.
  intros. unfold pred_sepcon. f_equal. extensionality l. rewrite prop_and. auto.
Qed.

Lemma pred_sepcon_strong_proper: forall P1 P2 p1 p2,
  (forall x, P1 x <-> P2 x) ->
  (forall x, P1 x -> P2 x -> p1 x = p2 x) ->
  pred_sepcon p1 P1 = pred_sepcon p2 P2.
Proof.
  assert (forall P1 P2 p1 p2,
    (forall x, P1 x <-> P2 x) ->
    (forall x, P1 x -> P2 x -> p1 x = p2 x) ->
    pred_sepcon p1 P1 |-- pred_sepcon p2 P2).
  2: intros; apply pred_ext; apply H; [auto | auto | symmetry; auto | symmetry; auto].
  intros.
  unfold pred_sepcon.
  apply exp_left; intro l; apply (exp_right l).
  normalize.
  assert (forall x : B, In x l <-> P2 x) by (intros; rewrite H1, H; reflexivity).
  normalize.
  erewrite iter_sepcon_func_strong; [apply derives_refl |].
  intros.
  specialize (H1 x); specialize (H3 x).
  apply H0; tauto.
Qed.

#[global] Instance pred_sepcon_proper: Proper (pointwise_relation B eq ==> pointwise_relation B iff ==> eq) pred_sepcon.
Proof.
  intros.
  do 2 (hnf; intros).
  apply pred_sepcon_strong_proper; intros; auto.
Defined.

Global Existing Instance pred_sepcon_proper.

Lemma pred_sepcon1: forall p x0,
  pred_sepcon p (fun x => x = x0) = p x0.
Proof.
  intros.
  unfold pred_sepcon.
  apply pred_ext.
  + apply exp_left; intro l.
    normalize.
    destruct l as [| ? [|]].
    - specialize (H x0); simpl in H.
      tauto.
    - specialize (H x0); simpl in H.
      assert (b = x0) by tauto; subst b.
      simpl.
      rewrite sepcon_emp; auto.
    - pose proof proj1 (H b) as HH; simpl in HH.
      spec HH; [auto |].
      subst b.
      pose proof proj1 (H b0) as HH; simpl in HH.
      spec HH; [auto |].
      subst b0.
      clear - H0.
      inversion H0; subst.
      simpl in H2; tauto.
  + apply (exp_right (x0 :: nil)).
    repeat apply andp_right.
    - apply prop_right.
      intros.
      simpl.
      split; [intros [? | ?]; [congruence | tauto] | left; congruence].
    - apply prop_right.
      constructor; [simpl; tauto | constructor].
    - simpl.
      rewrite sepcon_emp; auto.
Qed.

(*
Lemma pred_sepcon_sepcon: forall (P Q R: B -> Prop) p,
  Prop_join P Q R ->
  pred_sepcon P p * pred_sepcon Q p = pred_sepcon R p.
Proof.
  intros.
  destruct H.
  unfold pred_sepcon; apply pred_ext.
  + rewrite exp_sepcon1. apply exp_left; intro lP.
    rewrite exp_sepcon2. apply exp_left; intro lQ.
    normalize.
    apply (exp_right (lP ++ lQ)).
    apply andp_right; [apply andp_right |].
    - apply prop_right.
      intros.
      rewrite in_app_iff.
      firstorder.
    - apply prop_right.
      apply NoDup_app_inv; auto.
      firstorder.
    - rewrite <- iter_sepcon_app; auto.
  + apply exp_left; intro l.
    rewrite andp_assoc.
    do 2 (apply derives_extract_prop; intro).
    destruct (spec_list_split l P Q R H2 H1 (conj H H0)) as [lp [lq [? [? [? [? ?]]]]]].
    rewrite exp_sepcon1. apply (exp_right lp).
    rewrite exp_sepcon2. apply (exp_right lq).
    normalize.
    rewrite H7, iter_sepcon_app; auto.
Qed.

Lemma pred_sepcon_sepcon1: forall (P P': B -> Prop) p x0,
  (forall x, P' x <-> P x \/ x = x0) ->
  ~ P x0 ->
  pred_sepcon P' p = pred_sepcon P p * p x0.
Proof.
  intros.
  rewrite <- pred_sepcon_sepcon with (Q := fun x => x = x0) (P := P).
  + f_equal.
    apply pred_sepcon1.
  + split; intros.
    - specialize (H a).
      assert (a = x0 -> ~ P a) by (intro; subst; auto).
      tauto.
    - subst.
      specialize (H x0).
      tauto.
Qed.
*)

Lemma pred_sepcon_unique_sepcon1: forall (P: B -> Prop) p x0,
  sepcon_unique1 p ->
  pred_sepcon p P * p x0 |-- !! (~ P x0).
Proof.
  intros.
  apply not_prop_right; intro.
  unfold pred_sepcon; normalize.
  rewrite <- H1 in H0.
  eapply derives_trans; [apply sepcon_derives; [apply iter_sepcon_in_true; eauto| apply derives_refl] |].
  rewrite sepcon_comm, <- sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply H | apply derives_refl] |].
  normalize.
Qed.

Lemma prop_forall_allp: forall (P: B -> Prop),
  !! (forall x, P x) = ALL x: B, !! P x.
Proof.
  intros.
  apply pred_ext.
  + apply allp_right; intros.
    apply prop_derives; intros.
    auto.
  + apply allp_prop_left.
Qed.

Lemma prop_impl_imp: forall (P Q: Prop),
  !! (P -> Q) = !! P --> !! Q.
Proof.
  intros.
  apply pred_ext.
  + apply imp_andp_adjoint.
    normalize.
  + apply prop_imp_prop_left.
Qed.

Lemma pred_sepcon_prop_true: forall (P: B -> Prop) p x,
  P x ->
  pred_sepcon p P |-- p x * TT.
Proof.
  intros.
  unfold pred_sepcon; normalize.
  intros.
  normalize.
  rename x0 into l.
  rewrite <- H0 in H.
  eapply iter_sepcon_in_true; auto.
Qed.

(*
Lemma pred_sepcon_prop_true_weak:
  forall (P Q: B -> Prop) (qdec: forall x, Decidable (Q x)) p,
    (forall x, Q x -> P x) -> pred_sepcon P p |-- pred_sepcon Q p * TT.
Proof.
  intros. unfold pred_sepcon. normalize.
  apply (exp_right (filter (fun x => if (qdec x) then true else false) l)).
  rewrite <- prop_and, sepcon_andp_prop'.
  remember (filter (fun x0 : B => if qdec x0 then true else false) l) as l'.
  assert (forall x : B, In x l' <-> Q x). {
    intros. subst l'. rewrite filter_In. destruct (qdec x); split; intros; auto.
    - split; auto. apply H in H2. rewrite H0. auto.
    - destruct H2; inversion H3.
    - exfalso; auto.
  } assert (NoDup l') by (subst l'; apply NoDup_filter; auto). apply andp_right.
  - apply prop_right. split; auto.
  - apply iter_sepcon_incl_true; auto. intro. rewrite H0, H2. apply H.
Qed.
*)
Lemma pred_sepcon_False: forall p,
  pred_sepcon p (fun _ => False) = emp.
Proof.
  intros.
  unfold pred_sepcon.
  apply pred_ext.
  + apply exp_left; intros.
    normalize.
    destruct x; [apply derives_refl |].
    specialize (H b); simpl in H; tauto.
  + apply (exp_right nil).
    normalize.
    apply andp_right.
    apply prop_right; constructor.
    apply derives_refl.
Qed.

Lemma pred_sepcon_False':
 forall (P: B -> Prop) (p : B -> A),
  (forall x, ~ P x) ->
  pred_sepcon p P = emp.
Proof.
intros.
replace P with (fun _:B  => False).
apply pred_sepcon_False.
extensionality i.
apply prop_ext; split; intros. contradiction.
apply (H i); auto.
Qed.

End IterPredSepCon.

Lemma pred_sepcon_isolate:
  forall {A B: Type}{NA: NatDed A}{SA: SepLog A}
  (x: B)
  (DECB: forall x y: B, {x=y}+{x<>y})
  (f: B -> A) (u: B -> Prop),
  (u x) ->
  pred_sepcon f u = pred_sepcon f (fun y => u y /\ y<>x) * f x.
Proof.
intros.
rewrite !pred_sepcon_eq.
pose (neqx y := if DECB x y then false else true).
apply pred_ext.
apply exp_left; intro l.
normalize.
destruct H0.
apply exp_right with (filter neqx l).
rewrite prop_true_andp.
apply derives_trans with (iter_sepcon f (x :: filter neqx l)).
apply derives_refl'.
apply iter_sepcon_permutation.
apply NoDup_Permutation; auto.
constructor.
intro. apply filter_In in H2. destruct H2.
unfold neqx in H3.
destruct (DECB x x). inversion H3. contradiction n; auto.
apply NoDup_filter; auto.
intro.
split; intro.
destruct (DECB x0 x).
subst. left; auto. right. apply filter_In. split; auto.
unfold neqx.
destruct (DECB x x0); auto.
destruct H2.
subst.
rewrite <- H0 in H. auto.
apply filter_In in H2. destruct H2; auto.
simpl. rewrite sepcon_comm; auto.
split.
intro. split; intro.
apply filter_In in H2. destruct H2.
rewrite H0 in H2.
split; auto.
intro; subst.
unfold neqx in H3.
destruct (DECB x x); auto. inv H3.
destruct H2.
apply filter_In. split; auto.
rewrite H0; auto.
unfold neqx.
destruct (DECB x x0); auto.
apply NoDup_filter. auto.
normalize.
destruct H0.
apply exp_right with (x::l).
rewrite prop_true_andp.
simpl.
rewrite sepcon_comm; auto.
split.
intro.
specialize (H0 x0).
simpl. rewrite H0.
split; intro.
destruct H2.
subst; auto.
destruct H2. auto.
destruct (DECB x0 x).
subst.
auto.
right; auto.
constructor; auto.
rewrite H0.
intros [? ?].
contradiction.
Qed.
