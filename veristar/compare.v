Load loadpath.
Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Sorted.
Require Import Coq.Sorting.Mergesort.
Require Import Permutation.

Definition StrictCompSpec {A} (eq lt: A -> A -> Prop)
                          (cmp: A -> A -> comparison) :=
  StrictOrder lt /\ forall x y, CompSpec eq lt x y (cmp x y).

Definition CompSpec' {A} (cmp: A -> A -> comparison) :=
   StrictCompSpec (@Logic.eq A) (fun x y => Lt = cmp x y) cmp.

Ltac do_comp cspec x y := destruct (CompSpec2Type (proj2 cspec x y)).

Lemma lt_comp: forall {A} lt cmp,
             StrictCompSpec Logic.eq lt cmp ->
             forall x y: A,  (lt x y <-> Lt = cmp x y).
Proof.
intros.
  generalize H; intros [[?H ?H] _].
  do_comp H x y; intuition; subst; try discriminate; auto.
  contradiction (H0 y).
  contradiction (H0 _ (H1 _ _ _ l H2)).
Qed.

Lemma eq_comp: forall {A} lt cmp,
        StrictCompSpec Logic.eq lt cmp ->
       forall x y: A,   (x = y <-> Eq = cmp x y).
Proof.
 intros.
  generalize H; intros [[?H ?H] _].
  do_comp H x y; intuition; subst; try discriminate; auto;
  contradiction (H0 y).
Qed.

Lemma gt_comp: forall {A} lt cmp,
        StrictCompSpec Logic.eq lt cmp ->
        forall x y: A,   (lt x y <-> Gt = cmp y x).
Proof.
intros.
  generalize H; intros [[?H ?H] _].
  do_comp H x y; intuition; subst; try discriminate; auto.
  contradiction (H0 y).
  destruct (eq_comp _ _ H y y).
  rewrite <- H3 in H2; auto. inversion H2.
  do_comp H y x; subst; auto.
  contradiction (H0 x).
  contradiction (H0 _ (H1 _ _ _ l0 H2)).
  contradiction (H0 _ (H1 _ _ _ l H2)).
  rewrite (lt_comp _ _ H) in l; eauto.
  rewrite <- H2 in l; inversion l.
Qed.

Lemma comp_refl: forall {A} (cmp: A -> A -> comparison) (cspec: CompSpec' cmp),
      forall x, cmp x x = Eq.
Proof.
 intros.
 do_comp cspec x x; auto.
 destruct cspec as [[H _] _].
 contradiction (H _ e).
 destruct cspec as [[H _] _].
 contradiction (H _ e).
Qed.

Lemma comp_eq: forall {A} (cmp: A -> A -> comparison) (cspec: CompSpec' cmp),
   forall x y, Eq = cmp x y -> x=y.
Proof.
intros. do_comp cspec x y; congruence.
Qed.

Lemma comp_trans:  forall {A} (cmp: A -> A -> comparison) (cspec: CompSpec' cmp),
      forall x y z, Lt = cmp x y -> Lt = cmp y z -> Lt = cmp x z.
Proof.
 intros.
 destruct cspec as [[_ ?H] _].
 eapply H1; eauto.
Qed.


Definition isGe (c: comparison) := match c with Lt => False | _ => True end.
Definition isGeq cc := match cc with Lt => false | _ => true end.


Fixpoint insert {A: Type} (cmp: A -> A -> comparison) (a: A) (l: list A)
  : list A:=
  match l with
  | h :: t => if isGeq (cmp a h)
                 then a :: l
                 else h :: (insert cmp a t)
  | nil => a :: nil
  end.

Fixpoint rsort {A: Type} (cmp: A -> A -> comparison) (l: list A) : list A :=
  match l with nil => nil | h::t => insert cmp h (rsort cmp t)
  end.

Fixpoint insert_uniq {A: Type} (cmp: A -> A -> comparison) (a: A) (l: list A)
  : list A:=
  match l with
  | h :: t => match cmp a h with
              | Eq => l
              | Gt => a :: l
              | Lt => h :: (insert_uniq cmp a t)
              end
  | nil => a::nil
  end.

Fixpoint rsort_uniq {A: Type} (cmp: A -> A -> comparison) (l: list A)
  : list A :=
  match l with nil => nil | h::t => insert_uniq cmp h (rsort_uniq cmp t)
  end.

(*put somewhere else, maybe in datatypes.v*)
Lemma perm_insert {T} cmp (a : T) l : Permutation (insert cmp a l) (a :: l).
Proof with auto.
induction l; simpl; auto.
destruct (isGeq (cmp a a0)); try repeat constructor.
apply Permutation_refl.
apply Permutation_sym; apply Permutation_trans with (l' := a0 :: a :: l).
apply perm_swap. constructor; apply Permutation_sym...
Qed.

Fixpoint compare_list {A: Type} (f: A -> A -> comparison) (xl yl : list A)
  : comparison :=
  match xl , yl with
  | x :: xl', y :: yl' => match f x y with
                          | Eq => compare_list f xl' yl'
                          | c => c
                          end
  | nil , _ :: _ => Lt
  | _ :: _ , nil => Gt
  | nil, nil => Eq
  end.

Lemma list_cspec:
  forall  {A} (cmp: A -> A -> comparison) (cmp_spec: CompSpec' cmp),
    CompSpec' (compare_list cmp).
Proof.
 intros.
 repeat constructor; repeat intro.
 revert H; induction x; simpl; intros; try congruence.
 rewrite comp_refl in H; auto.
 revert y z H H0; induction x; destruct y; destruct z; simpl; intros; try congruence.
 do_comp cmp_spec a a0; subst; auto.
 do_comp cmp_spec a0 a1; subst; auto.
 eauto.
 do_comp cmp_spec a0 a1; subst; auto. rewrite <- e; auto.
 replace (cmp a a1) with Lt; auto.
 eapply comp_trans; eauto.
 inversion H0. inversion H.
 revert y; induction x; destruct y; subst; try solve [constructor; simpl; auto].
 simpl.
 do_comp cmp_spec a a0.
 subst.
 destruct (CompSpec2Type ( IHx y)).
 subst; constructor; auto.
 econstructor; simpl; eauto. rewrite comp_refl; auto.
 econstructor; simpl; eauto. rewrite comp_refl; auto.
 econstructor; simpl; eauto. rewrite <- e; auto.
 econstructor; simpl; eauto. rewrite <- e; auto.
Qed.

Hint Resolve @list_cspec.

Lemma comp_antisym:  forall {A} (cmp: A -> A -> comparison) (cspec: CompSpec' cmp),
      forall x y, Lt = cmp x y <-> Gt = cmp y x.
Proof.
 intros.
 do_comp cspec y x; subst; try congruence.
 rewrite comp_refl; auto. intuition congruence.
 intuition (try congruence).
 generalize (comp_trans _ cspec _ _ _ H e).
 rewrite comp_refl; auto; congruence.
 intuition.
Qed.

Lemma NoDup_rsort_uniq:
  forall {A} (cmp: A -> A -> comparison) (cspec: CompSpec' cmp),
  forall  l, NoDup (rsort_uniq cmp l).
Proof.
intros.
assert (Sorted (fun x y => Gt = cmp x y) (rsort_uniq cmp l)).
induction l.
simpl. constructor.
simpl.
remember (rsort_uniq cmp l) as l0; clear - IHl cspec.
induction IHl.
constructor. constructor. constructor.
simpl.
do_comp cspec a a0.
subst.
constructor; auto.
constructor; auto.
destruct l; simpl. constructor.
apply comp_antisym; auto.
do_comp cspec a a1; simpl; constructor; auto.
subst. apply comp_antisym; auto.
inversion H; clear H; subst; auto.
apply comp_antisym; auto.
constructor; auto. constructor; auto.
apply comp_antisym; auto.
(* End Sorted proof *)
induction H. constructor.
constructor; auto.
intro.
clear IHSorted.
revert H0 H1; induction H; intros.
contradiction H1.
simpl in H2; destruct H2.
subst.
inversion H1; clear H1; subst.
clear -cspec H3. rewrite comp_refl in H3; [congruence|auto].
inversion H1; clear H1; subst.
apply IHSorted; auto.
inversion H0; clear H0; subst; constructor.
clear - cspec H1 H4.
apply comp_antisym; apply comp_antisym in H4; apply comp_antisym in H1; auto.
eapply comp_trans; eauto.
Qed.

Lemma Forall_sortu:
  forall  {A} (f: A -> Prop) (cmp: A -> A -> comparison) l,
    Forall f l -> Forall f  (rsort_uniq cmp l).
Proof.
induction l;  intros; try constructor.
simpl.
inversion  H; clear H; subst.
specialize (IHl H3).
clear H3; induction IHl.
simpl; constructor; auto.
simpl.
destruct (cmp a x); constructor; auto.
Qed.

Lemma rsort_uniq_in:
  forall {A} (R: A -> A -> comparison)
          (EQ: forall a b, (a=b) <-> (Eq = R a b))
          x l,
      List.In x (rsort_uniq  R l) <-> List.In x l.
Proof.
induction l; simpl; intros.
intuition.
rewrite <- IHl.
remember (rsort_uniq R l) as l'.
clear - EQ.
induction l'; simpl. intuition.
case_eq (R a a0); intros; simpl in *; subst; intuition.
symmetry in H; rewrite <- EQ in H.
simpl; subst; intuition.
Qed.

