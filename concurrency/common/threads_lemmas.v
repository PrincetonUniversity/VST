Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Set Implicit Arguments.
Import Axioms.
(* tactics to support Omega for ssrnats*)
Ltac arith_hypo_ssrnat2coqnat :=
  match goal with
    | H : context [andb _ _] |- _ => let H0 := fresh in case/andP: H => H H0
    | H : context [orb _ _] |- _ => case/orP: H => H
    | H : context [?L <= ?R] |- _ => move/leP: H => H
    | H : context [?L < ?R] |- _ => move/ltP : H => H
    | H : context [?L == ?R] |- _ => move/eqP : H => H
    | H : context [addn ?L ?R] |- _ => rewrite -plusE in H
    | H : context [muln ?L ?R] |- _ => rewrite -multE in H
    | H : context [subn ?L ?R] |- _ => rewrite -minusE in H
  end.

Ltac arith_goal_ssrnat2coqnat :=
  rewrite ?NatTrec.trecE -?plusE -?minusE -?multE -?leqNgt -?ltnNge;
  repeat match goal with
           | |- is_true (andb _ _) => apply/andP; split
           | |- is_true (orb _ _) => try apply/orP
           | |- is_true (_ <= _) => try apply/leP
           | |- is_true (_ < _) => try apply/ltP
         end.

Ltac ssromega :=
  repeat arith_hypo_ssrnat2coqnat;
  arith_goal_ssrnat2coqnat; simpl;
  omega.

Class monad (mon : Type -> Type) :=
  {
    ret : forall {A : Type},  A -> mon A;
    bind : forall {A B : Type}, mon A -> (A -> mon B) -> mon B
  }.

Notation "x >>= f" := (bind x f) (at level 40, left associativity).
Notation "'do!' X <- A ; B" := (bind A (fun X => B)) (at level 40).

Lemma if_true : forall {A : Type} b (x y : A)
                  (Htrue: is_true b),
                  (if b then x else y) = x.
Proof.
  intros. now rewrite Htrue.
Defined.

Lemma if_false : forall {A : Type} b (x y : A)
                   (Hfalse: is_true (~~b)),
                   (if b then x else y) = y.
Proof.
  intros. rewrite <- Bool.if_negb. by rewrite Hfalse.
Defined.

Lemma not_in_filter :
  forall {A:eqType} (i : A) xs
    (HIn: ~ List.In i xs),
    [seq x <- xs | x == i] = [::].
Proof.
  intros.
  induction xs as [|j xs]; first by reflexivity.
  simpl.
  destruct (j == i) eqn:Hji; move/eqP:Hji=>Hji;
    first by (subst j; simpl in *; exfalso; apply HIn; by auto).
  apply IHxs. intros Hcontra.
  apply HIn. simpl; by auto.
Qed.

Lemma nth_error_app_inv:
  forall (A : Type) (i : nat) (v: A) (ys xs : seq.seq A), nth_error xs i = Some v ->
                                                   nth_error (xs ++ ys) i = Some v.
  intros.
  generalize dependent i.
  generalize dependent v.
  induction xs;
    intros.
  rewrite Coqlib.nth_error_nil in H.
  discriminate.
  destruct i; simpl in *;
    now auto.
Qed.

Lemma app_eq_refl_nil:
  forall {A:Type} (xs ys : list A),
    xs = xs ++ ys ->
    ys = nil.
Proof.
  intros.
  erewrite <- app_nil_r in H at 1.
  apply app_inv_head in H; auto.
Qed.
  
Lemma app_assoc_l:
  forall (A : Type) (l m n : seq.seq A),
    l ++ m ++ n = l ++ (m ++ n).
Proof.
  intros;
    by rewrite app_assoc.
Qed.

Lemma filter_neq_eq :
  forall {A :eqType} (xs : seq.seq A) i j (Hneq: i <> j),
    [seq x <- [seq x <- xs | x != i] | x == j] = [seq x <- xs | x == j].
Proof.
  intros. induction xs.
  - reflexivity.
  - simpl. destruct (a != i) eqn:Hai; move/eqP:Hai=>Hai.
    simpl.
    destruct (a ==j) eqn:Haj; move/eqP:Haj=>Haj;
                                             [by apply f_equal | assumption].
    subst. erewrite if_false by (apply/eqP; auto).
    assumption.
Qed.

Lemma nth_error_app:
  forall {A:Type} i (ys xs : list A),
    nth_error xs i = nth_error (ys ++ xs) (length ys + i).
Proof.
  intros A i ys.
  generalize dependent i.
  induction ys; intros.
  - simpl. rewrite add0n.
    reflexivity.
  - simpl.
    eauto.
Qed.

Lemma list_cons_irrefl:
  forall {A: Type} (x : A) xs,
    ~ x :: xs = xs.
Proof.
  intros.
  induction xs; intro Hcontra; simpl; try discriminate.
  inversion Hcontra; subst a; auto.
Qed.

Lemma lt_succ_neq:
  forall x y z,
    (x <= y < x + Z.succ z)%Z ->
    y <> (x + z)%Z ->
    (x <= y < x + z)%Z.
Proof.
  intros.
  omega.
Qed.


Lemma le_sub:
  forall x y z,
    (x < z)%positive ->
    (z <= y)%positive ->
    (x <= Z.to_pos (Z.pos_sub y (z - x)))%positive.
Proof.
  intros x y z H H0.
  zify.
  rewrite <-Pos2Z.add_pos_neg.
  assert (x < z)%positive by auto.
  rewrite Z2Pos.id; zify; omega.
Qed.

Lemma lt_sub_bound:
  forall x y,
    (x < y)%positive ->
    (Z.to_pos (Z.pos_sub y (y - x)) < Pos.succ x)%positive.
Proof.
  intros x y H.
  zify.
  rewrite <-Pos2Z.add_pos_neg.
  rewrite Z2Pos.id; zify; omega.
Qed.

Lemma lt_lt_sub:
  forall a b c,
    (a < b)%positive ->
    (b <= c)%positive ->
    (b - a < c)%positive.
Proof.
  intros a b c H H0.
  zify; omega.
Qed.

Lemma prod_fun :
  forall {A B C : Type}
    (f g: A -> (B * C)),
    f = g ->
    (fun x : A => fst (f x)) =  (fun x : A => fst (g x)) /\
    (fun x : A => snd (f x)) = (fun x : A => snd (g x)).
Proof.
  intros.
  assert ((fun x => fst (f x)) = (fun x => fst (g x))).
    by (eapply extensionality; intros x;
         pose (f x);
         pose (g x);
           by subst).
  assert ((fun x => snd (f x)) = (fun x => snd (g x)))
    by (eapply extensionality; intros x;
         pose (f x);
         pose (g x);
           by subst).
  rewrite H0 H1.
    by split.
Qed.

Lemma forall_and:
  forall {A : Type} (f g : A -> Prop),
    (forall x : A, f x /\ g x) <->
    (forall x : A, f x) /\ (forall x : A, g x).
Proof.
  intros. split; intros.
  split; intros; [eapply (proj1 (H x))| eapply (proj2 (H x))].
  destruct H; eauto.
Qed.

Lemma forall2_and:
  forall {A B : Type} (f g : A -> B -> Prop),
    (forall x y, f x y /\ g x y) <->
    (forall x y, f x y) /\ (forall x y, g x y).
Proof.
  intros.
  split; intros.
  split; intros; [eapply (proj1 (H x y)) | eapply (proj2 (H x y))].
  destruct H; eauto.
Qed.

Definition proj_sumbool_is_false : forall (P : Prop) (a : {P} + {~ P}), ~ P -> Coqlib.proj_sumbool a = false.
Proof.
  intros.
  unfold Coqlib.proj_sumbool.
  destruct a; auto; try by exfalso.
Qed.



Module BlockList.
  Import ListNotations.

  Fixpoint mkBlockList (n : nat) : list nat :=
    match n with
      | 0 => nil
      | S 0 => nil
      | S n =>  n :: (mkBlockList n)
    end.

  Lemma mkBlockList_unfold : forall n (Hn: n > 1),
                               n :: (mkBlockList n) = mkBlockList (S n).
  Proof.
    intros; simpl; destruct n. exfalso; auto.
    reflexivity.
  Qed.

  Lemma mkBlockList_unfold' : forall n,
                                (S n) :: (mkBlockList (S n)) = mkBlockList (S (S n)).
  Proof.
    intros; reflexivity.
  Qed.

  Lemma mkBlockList_include : forall n k (Hk: k > 0) (Hineq: k < n) (Hn: n > 1),
                                List.In k (mkBlockList n).
  Proof.
    intros n.
    induction n;
      intros.
    simpl. ssromega.
    destruct n. ssromega.
    rewrite <- mkBlockList_unfold'. simpl. simpl in IHn.
    destruct (beq_nat k (S n)) eqn:?. apply beq_nat_true in Heqb. subst.
    now left.
    right. apply IHn; auto;  clear IHn.
    apply beq_nat_false in Heqb. ssromega.
    apply beq_nat_false in Heqb. ssromega.
  Qed.

  Lemma mkBlockList_not_in : forall n m
                               (Hge: m >= n)
                               (HIn: List.In m (mkBlockList n)),
                               False.
  Proof.
    intros.
    destruct n. auto.
    destruct n. auto. generalize dependent m.
    induction n; intros. simpl in HIn. destruct HIn; subst; auto.
    rewrite <- mkBlockList_unfold' in HIn.
    apply List.in_inv in HIn. destruct HIn as [? | HIn]; subst.
    rewrite ltnn in Hge. auto.
    eapply IHn. Focus 2. eauto.
    eapply leq_ltn_trans; eauto.
  Qed.

  Lemma mkBlockList_range:
    forall n k
      (HIn: List.In k (mkBlockList (S (S n)))),
      k < (S (S n)) /\ k > 0.
  Proof.
    intro n. induction n; intros. simpl in HIn.
    destruct HIn; subst; auto.
    rewrite <- mkBlockList_unfold' in HIn.
    apply List.in_inv in HIn.
    destruct HIn as [? | HIn]; subst.
    auto. apply IHn in HIn. destruct HIn. auto.
  Qed.

End BlockList.

(*
Module SeqLemmas.

  Definition subSeq {T:eqType} (s1 s2 : seq T) :=
    drop ((size s2)-(size s1)) s2 == s1.

  Lemma dropS:
    forall {T:Type} n (x:T) l l'
      (Hdrop: drop n l = x :: l'), drop n.+1 l = l'.
  Proof.
    intros. generalize dependent n.
    induction l; intros. simpl in *. discriminate.
    simpl in *. destruct n. inversion Hdrop; subst. apply drop0.
    eapply IHl; eassumption.
  Defined.

  Lemma drop_size_lt : forall {T : Type} (s s' : seq T) n
                         (Hdrop: drop n s = s'),
                         size s >= size s'.
  Proof.
    intros T s. induction s; intros.
    destruct n; simpl in Hdrop; rewrite <- Hdrop; auto.
    simpl in *. destruct n. rewrite <- Hdrop. auto.
    eapply IHs in Hdrop. ssromega.
  Defined.
  Lemma subSeq_det : forall {T:eqType} (s s' s'' : seq T) (Hsize: size s' = size s'')
                       (Hsub': subSeq s' s) (Hsub'': subSeq s'' s),
                       s' = s''.
  Proof.
    intros T s. induction s; intros.
    - unfold subSeq in *. simpl in *. move/eqP:Hsub'=>Hsub'. subst. move/eqP:Hsub''; auto.
    - unfold subSeq in Hsub', Hsub''. simpl in Hsub', Hsub''.
      rewrite Hsize in Hsub'.
      destruct ((size s).+1 - size s'') eqn:Heq.
      move/eqP:Hsub''. move/eqP:Hsub'. intros. destruct s'; inversion Hsub'; subst.
      reflexivity.
      apply IHs. assumption.
      unfold subSeq.
        by replace n with (size s - size s') in Hsub' by ssromega.
          by replace n with (size s - size s'') in Hsub'' by ssromega.
  Defined.

  Lemma in_rcons : forall {T:Type} x y (s : seq T) (HIn: List.In x (rcons s y)),
                     x = y \/ List.In x s.
  Proof.
    intros. induction s.
    - simpl in HIn. destruct HIn; auto.
      simpl in HIn. destruct HIn as [|HIn]; subst.
      right. simpl. left. reflexivity.
      apply IHs in HIn. destruct HIn; subst; auto.
      right. simpl. auto.
  Defined.

  Lemma in_rcons_refl : forall {T:Type} x (s : seq T),
                          List.In x (rcons s x).
  Proof.
    intros. induction s. simpl. by left.
    simpl. by right.
  Defined.

  Lemma in_rcons_weaken:
    forall {T:Type} x y (s : seq T) (HIn: List.In x s),
      List.In x (rcons s y).
  Proof.
    intros. induction s.
    - inversion HIn.
    - inversion HIn; subst. simpl. by left.
      simpl. right. auto.
  Defined.

End SeqLemmas.
 *)


