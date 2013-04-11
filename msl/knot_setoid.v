(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import Relations.
Require Import Compare_dec.
Require Import Peano_dec.
Require Import Eqdep_dec.
Require Import SetoidClass.
Require Import Morphisms.
Require Omega.

Local Open Scope nat_scope.

Program Definition EqSetoid (A:Type) : Setoid A := @Build_Setoid A (@eq A) _.
Next Obligation.
  constructor; hnf; intuition.
  transitivity y; auto.
Qed.

Program Instance ProdSetoid `(Setoid A) `(Setoid B) : Setoid (A * B) :=
  { equiv := fun z w => equiv (fst z) (fst w) /\ equiv (snd z) (snd w)
  }.
Next Obligation.
  constructor; hnf; intuition; simpl in *.
  transitivity a0; auto.
  transitivity b0; auto.
Qed.

Inductive Mor `(As:Setoid A) `(Bs:Setoid B) :=
  { mor_fun :> A -> B
  ; mor_prf :> @Morphism (A -> B) (equiv ==> equiv)%signature mor_fun
  }.
Implicit Arguments Build_Mor [A B].

Program Definition fstM `{As:Setoid A} `{Bs:Setoid B} : Mor (ProdSetoid As Bs) As
 := Build_Mor _ _ (@fst A B) _.
Next Obligation.
  hnf; simpl; intuition.
Qed.

Program Definition sndM `{As:Setoid A} `{Bs:Setoid B} : Mor (ProdSetoid As Bs) Bs
 := Build_Mor _ _ (@snd A B) _.
Next Obligation.
  hnf; simpl; intuition.
Qed.

Definition ext_equiv `(As:Setoid A) `(Bs:Setoid B) : relation (Mor As Bs) :=
  fun f g => forall a a':A, a == a' -> f a == g a'.

Lemma ext_is_equiv `(As:Setoid A) `(Bs:Setoid B) : Equivalence (ext_equiv As Bs).
Proof.
  intros; constructor; do 2 (hnf; intros).
  apply mor_prf; auto.
  transitivity (y a').
  apply mor_prf; auto.
  symmetry; apply H; auto.
  reflexivity.
  transitivity (y a').
  apply H; auto.
  apply H0; reflexivity.
Qed.

Instance MorSetoid  `(As:Setoid A) `(Bs:Setoid B) : Setoid (Mor As Bs) :=
  { equiv := ext_equiv As Bs
  ; setoid_equiv := ext_is_equiv As Bs
  }.

Program Definition idM `(As:Setoid A) : Mor As As := Build_Mor As As (@id A) _.
Next Obligation.
  hnf; auto.
Qed.

Program Definition composeM `{As:Setoid A} `{Bs:Setoid B} `{Cs:Setoid C} 
  (f:Mor Bs Cs) `(g:Mor As Bs) := Build_Mor As Cs (fun x => f (g x)) _.
Next Obligation.
  hnf; intros.
  apply f; apply g; auto.
Qed.
Infix "oo" := composeM (at level 54, right associativity).

Module Type TY_FUNCTOR.
  Parameter F : Type -> Type.
  Instance Fs : forall {A}, Setoid A -> Setoid (F A).

  Parameter fmap : forall `{As:Setoid A} `{Bs:Setoid B}, Mor As Bs -> Mor (Fs As) (Fs Bs).

  Axiom fmap_mor : forall `{As:Setoid A} `{Bs:Setoid B},
    Morphism (equiv ==> equiv) fmap.

  Axiom fmap_id : forall `{As:Setoid A}, fmap (idM As) == idM (Fs As).
  Axiom fmap_comp : forall `{As:Setoid A} `{Bs:Setoid B} `{Cs:Setoid C}
    (f:Mor Bs Cs) (g:Mor As Bs),
    fmap f oo fmap g == fmap (f oo g).

  Parameter T : Type.
  Instance Ts : Setoid T.
  Parameter T_bot : T.

  Parameter other : Type.
  Parameter otherS : Setoid other.
End TY_FUNCTOR.

Module Type KNOT.
  Declare Module TF:TY_FUNCTOR.
  Import TF.

  Parameter knot : Type.
  Instance knotS : Setoid knot.
  Definition koS : Setoid (knot * other) := @ProdSetoid knot knotS other otherS.
  Definition predicate := Mor koS Ts.
  Definition predS : Setoid predicate := MorSetoid koS Ts.
  Definition natFS : Setoid (nat * F predicate) := @ProdSetoid nat (EqSetoid nat) (F predicate) (Fs predS).
  Existing Instance koS.
  Existing Instance predS.
  Existing Instance natFS.

  Parameter squash : Mor natFS knotS.
  Parameter unsquash : Mor knotS natFS.

  Definition level : Mor knotS (EqSetoid nat) := fstM oo unsquash.
  Parameter approx : forall n:nat, Mor predS predS.

  Axiom approx_spec : forall n p w, approx n p w ==
    if (le_gt_dec n (level (fst w))) then T_bot else p w.

  Axiom squash_unsquash : forall x, squash (unsquash x) == x.
  Axiom unsquash_squash : forall n x', unsquash (squash (n,x')) == (n,fmap (approx n) x').

  Definition knot_age1 (k:knot) : option knot :=
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Definition knot_age := fun x y => knot_age1 x = Some y.
End KNOT.

Module Knot (TF':TY_FUNCTOR) : KNOT with Module TF:=TF'.
  Module TF := TF'.
  Import TF.

  (* Put the discrete topped order on rhs *)
  Inductive le_T : T -> T -> Prop :=
   | le_T_refl : forall t1 t2,
     t1 == t2 -> le_T t1 t2
   | le_T_bot: forall t, 
     le_T T_bot t.

  Lemma le_T_asym: forall t1 t2,
    le_T t1 t2 -> le_T t2 t1 -> t1 == t2.
  Proof.
  intros.
  inversion H; subst; auto.
  inversion H0; subst; auto.
  symmetry; auto.
  reflexivity.
  Qed.

  Fixpoint sinv (n: nat) : { T:Type & Setoid T } :=
    match n with
      | O => existT (fun T => Setoid T) unit (EqSetoid unit)
      | S n => existT (fun T => Setoid T)
                  (prodT (projT1 (sinv n))
                         (Mor (ProdSetoid  (Fs (projT2 (sinv n))) otherS) (Ts)))
                  (ProdSetoid (projT2 (sinv n)) (MorSetoid _ _))
    end.

  Fixpoint floor (m:nat) (n:nat) (p:projT1 (sinv (m+n))) : projT1 (sinv n) :=
    match m as m' return forall (p : projT1 (sinv (m'+n))), projT1 (sinv n) with
    | O => fun p => p
    | S m' => fun p => floor m' n (fst p)
    end p.

  Lemma floor_mor : forall m n, Morphism ( (@equiv _ (projT2 (sinv (m+n)))) ==> (@equiv _ (projT2 (sinv n)))) (floor m n).
  Proof.
    induction m; simpl; hnf; intros; hnf; simpl; intros; auto.
    destruct x; destruct y; simpl in *.
    destruct H.
    apply IHm; auto.
  Qed.

  Definition knot := { n:nat & F (projT1 (sinv n)) }.

  Inductive knotEq : knot -> knot -> Prop :=
    keq : forall n (f1 f2:F (projT1 (sinv n))),
      @equiv _ (Fs (projT2 (sinv n))) f1 f2 ->
      knotEq (existT (fun x => F (projT1 (sinv x))) n f1)
             (existT (fun x => F (projT1 (sinv x))) n f2).
  Program Instance knotS : Setoid knot := { equiv := knotEq }.
  Next Obligation.
    constructor; hnf; intros.
    destruct x; constructor.
    reflexivity.
    destruct x; destruct y; simpl in *.
    inversion H; subst; simpl in *.
    constructor.
    replace f with f3.
    symmetry; auto.
    revert H2.
    apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))).
    destruct x; destruct y; destruct z.
    inversion H; clear H; subst.
    inversion H0; clear H0; subst.
    simpl.
    constructor.
    transitivity f5.
    replace f with f4; auto.
    revert H3.
    apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))).
    replace f5 with f0.
    replace f0 with f6; auto.
    revert H4.
    apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))).
    symmetry.
    revert H5.
    apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))).
  Qed.

  Definition koS : Setoid (knot * other) := @ProdSetoid knot knotS other otherS.
  Definition predicate := Mor koS Ts.
  Definition predS : Setoid predicate := MorSetoid koS Ts.
  Definition natFS : Setoid (nat * F predicate) := @ProdSetoid nat (EqSetoid nat) (F predicate) (Fs predS).
  Existing Instance koS.
  Existing Instance predS.
  Existing Instance natFS.

  Program Definition wrap (n:nat) : Mor (ProdSetoid (Fs (projT2 (sinv n))) otherS) (ProdSetoid knotS otherS) :=
    @Build_Mor _ _ _ _ (fun v => (existT (fun x => F (projT1 (sinv x))) n (fst v), snd v)) _.
  Next Obligation.
    hnf; simpl; intuition.
    destruct y.
    constructor.
    simpl in *; auto.
  Qed.

  Fixpoint stratify0 (n:nat) (Q:predicate) {struct n} : projT1 (sinv n) :=
    match n as n' return projT1 (sinv n') with
    | O => tt
    | S n' => ( stratify0 n' Q, Q oo (wrap n'))
    end.

  Lemma stratify_mor : forall n, Morphism (equiv ==> (@equiv _ (projT2 (sinv n)))) (stratify0 n).
  Proof.
    induction n; simpl; intros; hnf; simpl; intros; auto.
    split.
    apply IHn.
    apply H.
    hnf; intros.
    simpl.
    apply H.
    destruct H0.
    simpl; split; auto.
    constructor; auto.
  Qed.

  Definition stratify (n:nat) : Mor predS (projT2 (sinv n)) :=
    Build_Mor predS (projT2 (sinv n)) (stratify0 n) (stratify_mor n).

  Lemma decompose_nat : forall (x y:nat), { m:nat & y = (m + S x) } + { ge x y }.
  Proof.
    intros x y; revert x; induction y; simpl; intros.
    right; auto with arith.
    destruct (IHy x) as [[m H]|H].
    left; exists (S m); omega.
    destruct (eq_nat_dec x y).
    left; exists O; omega.
    right; omega.
  Qed.

  Definition proof_irr_nat := eq_proofs_unicity dec_eq_nat.
  Implicit Arguments proof_irr_nat.

  Program Definition unstratify (n:nat) : Mor (projT2 (sinv n)) predS :=
    Build_Mor _ _ (fun p =>
      Build_Mor _ _ (fun w =>
      match w with (existT nw w',e) =>
        match decompose_nat nw n with
          | inleft (existT m Hm) => snd (floor m (S nw) (eq_rect n (fun x => projT1 (sinv x)) p (m + S nw) Hm)) (w', e)
          | inright H => T_bot
        end
      end) _) _.
  Next Obligation.
    hnf; simpl; intros.
    destruct x; destruct y; simpl.
    destruct k; destruct k0; simpl in *.
    destruct H.
    inversion H; clear H; subst.
    assert (f3 = f) by (apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))); auto).
    subst f3.
    assert (f4 = f0) by (apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))); auto).
    subst f4.
    clear H3 H5.
    simpl.
    destruct (decompose_nat x0 n); simpl.
    destruct s; simpl.
    generalize e.
    subst n; intro e.
    replace e with (refl_equal (x + S x0)) by apply proof_irr_nat; simpl.
    generalize (floor_mor x (S x0) p p (setoid_refl _ p)).
    intro H.
    simpl in H.
    destruct H.
    apply H1.
    simpl; split; auto.
    apply setoid_refl.
  Qed.
  Next Obligation.
    repeat (hnf; simpl in *; intros).
    destruct a; destruct a'; simpl in *.
    destruct k; destruct k0; destruct H0; simpl in *.
    inversion H0; clear H0; subst.
    assert (f3 = f) by (apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))); auto).
    subst f3.
    assert (f4 = f0) by (apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))); auto).
    subst f4.
    simpl.
    destruct (decompose_nat x1 n); simpl.
    destruct s; simpl.
    generalize e; subst n.
    intro e.
    replace e with (refl_equal (x0 + S x1)) by (apply proof_irr_nat; auto); simpl.
    generalize (floor_mor x0 (S x1) x y H); simpl.
    intros [? ?].
    apply H2.
    split; auto.
    reflexivity.
  Qed.

  Lemma floor_shuffle:
    forall (m1 n : nat)
      (p1 : projT1 (sinv (m1 + S n))) (H1 : (m1 + S n) = (S m1 + n)),
      floor (S m1) n (eq_rect (m1 + S n) (fun x => (projT1 (sinv x))) p1 (S m1 + n) H1) = fst (floor m1 (S n) p1).
  Proof.
    intros.
    remember (fst (floor m1 (S n) p1)) as p.
    revert n p1 H1 p Heqp.
    induction m1; simpl; intros.
    replace H1 with (refl_equal (S n)) by (apply proof_irr_nat); simpl; auto.
    assert (m1 + S n = S m1 + n) by omega.
    destruct p1 as [p1 f'].
    generalize (IHm1 n p1 H p Heqp).
    simpl.
    clear.
    revert H1; generalize H.
    revert p1 f'.
    rewrite H.
    simpl; intros.
    replace H1 with (refl_equal (S (S (m1 + n)))) by (apply proof_irr_nat).
    simpl.
    replace H0 with (refl_equal (S (m1+n))) in H2 by (apply proof_irr_nat).
    simpl in H2.
    trivial.
  Qed.

  Lemma stratify_unstratify_more : forall n m1 m2 p1 p2,
    @equiv _ (projT2 (sinv n)) (floor m1 n p1) (floor m2 n p2) ->

    @equiv _ (projT2 (sinv n))
    (stratify n (unstratify (m1+n) p1))
    (stratify n (unstratify (m2+n) p2)).
  Proof.
    induction n; simpl; intros; auto.
    split.

    assert ((m1 + S n) =  (S m1 + n)) by omega.
    assert ((m2 + S n) =  (S m2 + n)) by omega.
    assert (@equiv _ (projT2 (sinv n))
      (floor (S m1) n (eq_rect (m1 + S n) (fun x => projT1 (sinv x)) p1 _ H0))
      (floor (S m2) n (eq_rect (m2 + S n) (fun x => (projT1 (sinv x))) p2 _ H1))).
    do 2 rewrite floor_shuffle.
    destruct H; auto.
    generalize (IHn (S m1) (S m2) _ _ H2).
    clear.
    generalize H0 H1.
    revert p1 p2.
    rewrite H0; clear H0.
    rewrite H1; clear H1.
    intros p1 p2 H1 H2.
    replace H1 with (refl_equal (S m1 + n)) by (apply proof_irr_nat).
    replace H2 with (refl_equal (S m2 + n)) by (apply proof_irr_nat).
    simpl; auto.

    hnf; intros.
    destruct a; destruct a'.
    unfold unstratify.
    simpl.
    destruct (decompose_nat n (m2 + S n)) as [[r Hr]|Hr].
    2: elimtype False; omega.
    destruct (decompose_nat n (m1 + S n)) as [[s Hs]|Hs].
    2: elimtype False; omega.
    assert (m2 = r) by omega; subst r.
    assert (m1 = s) by omega; subst s.
    replace Hr with (refl_equal (m2 + S n)) by (apply proof_irr_nat).
    replace Hs with (refl_equal (m1 + S n)) by (apply proof_irr_nat).
    simpl.
    destruct H; auto.
  Qed.

  Lemma stratify_unstratify : forall n,
         stratify n oo unstratify n == idM (projT2 (sinv n)).
  Proof.
    simpl; induction n.
    hnf; simpl; intros.
    destruct a'; auto.
    simpl; intros a a' H.
    split.
    destruct a; destruct a'; destruct H; simpl in *.
    change (@equiv _ (projT2 (sinv n)) (stratify n (unstratify (S n) (p,m))) p0).
    transitivity (stratify n (unstratify n p)).
    symmetry.
    apply (stratify_unstratify_more _ 0 1 p (p,m)).
    simpl; reflexivity.
    apply (IHn p p0 H).
    
    hnf; intros.
    destruct a0; destruct a'0; destruct H; simpl.
    destruct (decompose_nat n (S n)).
    2: elimtype False; omega.
    destruct s.
    assert (x = 0) by omega; subst x; simpl in *.
    replace e with (refl_equal (S n)) by (apply proof_irr_nat; auto); simpl.
    auto.
  Qed.

  Lemma unstratify_stratify1 : forall n (p:predicate) w,
    le_T ((unstratify n oo stratify n) p w) (p w).
  Proof.
    induction n; simpl; intros; unfold unstratify.

    (* 0 case *)
    destruct w as [nw rm]; simpl.
    destruct nw as [nw e].
    destruct (decompose_nat nw O) as [[r Hr]|?].
    elimtype False; omega.
    apply le_T_bot.

    (* S n case *)
    destruct w; simpl; intros.
    destruct k as [nw e].
    destruct (decompose_nat nw (S n)) as [[r Hr]|?]; try (apply lt_rhs_bot).
    destruct r; simpl.

    assert (n = nw) by omega.
    subst nw.
    simpl in Hr.
    replace Hr with (refl_equal (S n)) by apply proof_irr_nat; simpl.
    apply le_T_refl.
    reflexivity.

    simpl in Hr.
    assert (n = r + S nw) by omega.
    revert Hr; subst n.
    intro Hr.
    replace Hr with (refl_equal (S (r+S nw))) by apply proof_irr_nat; simpl.
    clear Hr.

    generalize (IHn p (existT (fun x => F (projT1 (sinv x))) nw e, o)).
    unfold unstratify; simpl.
    destruct (decompose_nat nw (r + S nw)) as [[x Hx]|?].
    assert (x = r) by omega; subst x.
    replace Hx with (refl_equal (r + S nw)) by apply proof_irr_nat.
    simpl; auto.
    elimtype False; omega.
    apply le_T_bot.
  Qed.

  Lemma unstratify_stratify2 : forall n (p:predicate) (w:knot * other),
     projT1 (fst w) < n ->
        le_T (p w) ((unstratify n oo stratify n) p w).
  Proof.
    induction n; simpl; intros.

    (* 0 case *)
    inversion H.

    (* S n case *)
    destruct w; simpl in *.
    destruct k; simpl.

    destruct (decompose_nat x (S n)) as [[r Hr]|?].
    destruct r; simpl.

    assert (n = x) by omega.
    subst x.
    simpl in Hr; replace Hr with (refl_equal (S n)) by apply proof_irr_nat; simpl.
    apply le_T_refl.
    reflexivity.

    simpl in Hr.
    assert (n = r + S x) by omega.
    revert Hr; subst n.
    intro Hr.
    replace Hr with (refl_equal (S (r+S x))) by apply proof_irr_nat; simpl.
    clear Hr.
    simpl in H.
    assert (x < r + S x) by omega.
    generalize (IHn p (existT (fun x => F (projT1 (sinv x))) x f,o) H0).
    simpl.
    destruct (decompose_nat x (r + S x)) as [[y Hy]|?].
    assert (y = r) by omega; subst y.
    replace Hy with (refl_equal (r + S x)) by apply proof_irr_nat.
    simpl; auto.
    elimtype False; omega.
    simpl in *.
    elimtype False; omega.
  Qed.

  Lemma unstratify_stratify3 : forall n (p:predicate) w,
    projT1 (fst w) >= n -> le_T ((unstratify n oo stratify n) p w) T_bot.
  Proof.
    intros n p w H; simpl.
    destruct w; simpl in *.
    destruct s; simpl in *.
    destruct (decompose_nat x n) as [[r Hr]|?].
    elimtype False; omega.
    apply le_T_bot.
  Qed.

  Program Definition squash : Mor natFS knotS :=
    Build_Mor _ _ 
     (fun x =>
       match x with (n,y) => existT (fun x => F (projT1 (sinv x))) n (fmap (stratify n) y) end) _.
  Next Obligation.
    hnf; simpl; intros.
    destruct x; destruct y; destruct H; simpl in *.
    subst n0.
    constructor.
    apply mor_prf; auto.
  Qed.
 
  Program Definition unsquash : Mor knotS natFS :=
    Build_Mor _ _
      (fun x =>
        match x with existT n y => (n, fmap (unstratify n) y) end) _.
  Next Obligation.
    hnf; simpl; intros.
    destruct x; destruct y; inversion H; clear H; subst; simpl.
    split; auto.
    apply mor_prf.
    transitivity f3; auto.
    replace f with f3.
    reflexivity.
    apply (inj_pair2_eq_dec nat eq_nat_dec) with (P:=fun x => F (projT1 (sinv x))); auto.
  Qed.

  Definition level : Mor knotS (EqSetoid nat) := fstM oo unsquash.
  Definition approx (n:nat) := unstratify n oo stratify n.

  Lemma approx_spec : forall n p w, approx n p w ==
    if (le_gt_dec n (level (fst w))) then T_bot else p w.
  Proof.
    intros.
    replace (level (fst w)) with (projT1 (fst w)).
    destruct (le_gt_dec n (projT1 (fst w))).
    apply le_T_asym.
    unfold approx.
    apply unstratify_stratify3; auto.
    apply le_T_bot.
    apply le_T_asym.
    apply unstratify_stratify1.
    apply unstratify_stratify2; auto.
    unfold level; destruct w; simpl.
    destruct k; simpl; auto.
  Qed.

  Lemma squash_unsquash : forall x, squash (unsquash x) == x.
  Proof.
    intros; destruct x; simpl.
    constructor.
    change (@equiv _ (Fs (projT2 (sinv x))) ((fmap (stratify x) oo fmap (unstratify x)) f)f).
    transitivity (fmap (stratify x oo unstratify x) f).
    apply (fmap_comp (stratify x) (unstratify x) f f (setoid_refl _ f)).
    transitivity (fmap (idM (projT2 (sinv x))) f).
    apply fmap_mor.
    apply stratify_unstratify.
    reflexivity.
    transitivity (idM (Fs (projT2 (sinv x))) f).
    apply fmap_id; reflexivity.
    simpl; reflexivity.
  Qed.

  Lemma unsquash_squash : forall n x', unsquash (squash (n,x')) == (n,fmap (approx n) x').
  Proof.
    intros; simpl; split; auto.
    unfold approx.
    change ((fmap (unstratify n) oo fmap (stratify n)) x' == fmap (unstratify n oo stratify n) x').
    apply fmap_comp.
    reflexivity.
  Qed.

  Definition knot_age1 (k:knot) : option knot :=
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Definition knot_age := fun x y => knot_age1 x = Some y.

End Knot.
