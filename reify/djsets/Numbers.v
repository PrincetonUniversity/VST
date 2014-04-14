(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** This file describes an interface [NUM] for abstract numbers and a
    functor that gives properties about them. One specificity of this
    interface is that we require an implemantation of both FSet and
    FMap on our numbers.
    
    This interface is then instanciated with positive, and we are able
    to use positive maps in our development.

    In [NUMUTILS] we define a tactic [num_omega] (and its couterparts
    [num_omega_false]), that reflects equalities and inequalities from
    [num] into [nat] and then calls [omega]. This tactic is implemented
    with autorewrite libraires. 
    
    In [NUMUTILS], we also define tactics [num_analyse] and [num_prop]
    which respectively performs case analysis on function calls, and
    reflection from boolean functions into the underlying
    relations. (See [BoolView.v] for more details)
*)

Require Import Common.
Require Import BoolView.
Require Import MyFSets MyFSetProperties MyFMapProperties FSetPositive FMapPositive.

Set Implicit Arguments.

(** * The [NUM] interface  *)
Module Type NUM.

  Variable num : Type.
  
  Parameter nat_of_num : num -> nat.
  Parameter num_of_nat : nat -> num.

  Parameter leb : num -> num -> bool. 
  Parameter ltb : num -> num -> bool.
  Parameter eqb : num -> num -> bool.
  Parameter compare : num -> num -> comparison.

  Parameter le : num -> num -> Prop.
  Parameter lt : num -> num -> Prop.

  Parameter S : num -> num.
  Parameter max: num -> num -> num.
  
  Parameter fold_num : forall A, (num -> A -> A) -> num -> A -> A.
  Parameter fold_num_sum : forall E T, (num -> T -> T + E) -> num -> T -> (T + E).

  Parameter pi0: num -> num.
  Parameter pi1: num -> num.
  Parameter pimatch: num -> num + num.

  Declare Module NumOTA: OrderedTypeAlt with Definition t := num.
  Declare Module NumSet: FSetInterface.S with Definition E.t := num. 
  Declare Module NumMap: FMapInterface.S with Definition E.t := num. 

  Parameter code: NumSet.t -> num.
  
  Notation "0" := (num_of_nat O).
  Notation "n < m" := (lt n m) (at level 70).
  Notation "n <= m" := (le n m) (at level 70).

  (* bijection with nat  *)
  Hypothesis id_num : forall n, num_of_nat (nat_of_num n) = n.
  Hypothesis id_nat : forall n, nat_of_num (num_of_nat n) = n.

  (* specification of the boolean operations w.r.t. the predicates *)
  Hypothesis le_spec : forall n m, reflect (le n m) (leb n m).
  Hypothesis lt_spec : forall n m, reflect (lt n m) (ltb n m).
  Hypothesis eq_spec : forall n m, reflect (n = m)  (eqb n m).
  Hypothesis compare_spec : forall n m, compare_spec eq lt n m (compare n m).

  (* specification of operations and predicates, w.r.t. nat *)
  Hypothesis S_nat_spec : forall n, nat_of_num (S n) = Datatypes.S (nat_of_num n).
  Hypothesis max_spec : forall n m, nat_of_num (max n m) = Max.max (nat_of_num n) (nat_of_num m).
  Hypothesis le_nat_spec : forall n m, n <= m <-> (nat_of_num n <= nat_of_num m)%nat.
  Hypothesis lt_nat_spec : forall n m, n <  m <-> (nat_of_num n <  nat_of_num m)%nat.

  (* specifications of the equalities on maps and sets *)
  Hypothesis set_eq_spec : forall x y, NumSet.E.eq x y <-> x = y.
  Hypothesis map_eq_spec : forall x y, NumMap.E.eq x y <-> x = y.

  (* fold_num specification *)
  Hypothesis fold_num_O: forall A (a: A) f, fold_num f 0 a = a.
  Hypothesis fold_num_S: forall A (a: A) f n, fold_num f (S n) a = fold_num f n (f n a).

  (* fold_num_sum specification *)
  Hypothesis fold_num_sum_O: forall E T a f, @fold_num_sum E T f 0 a = inl a.
  Hypothesis fold_num_sum_S: forall E T a f n, @fold_num_sum E T f (S n) a = 
    match f n a with 
      | inl a => fold_num_sum f n a
      | e => e
    end.

  (* pi/match specification *)
  Hypothesis match_pi0: forall n, pimatch (pi0 n) = inl n.
  Hypothesis match_pi1: forall n, pimatch (pi1 n) = inr n.
  Hypothesis lt_pi0: forall n m, n < m -> pi0 n < pi0 m.
  Hypothesis lt_pi1: forall n m, n < m -> pi1 n < pi1 m.

End NUM.



(** * Notations, lemmas and tactics derivable from the [NUM] interface *)
Module NumUtils (N : NUM).
  Export N.
  Module NumSetProps := MySetProps NumSet.
  Module NumMapProps := MyMapProps NumMap.

  Notation "0" := (num_of_nat O) : num_scope.
  Notation "1" := (num_of_nat 1) : num_scope.
  Notation "2" := (num_of_nat 2) : num_scope.
  Notation "3" := (num_of_nat 3) : num_scope.
  Notation "5" := (num_of_nat 5) : num_scope.
  Notation "7" := (num_of_nat 7) : num_scope.

  Notation "n < m" := (lt n m) (at level 70) : num_scope.
  Notation "n <= m" := (le n m) (at level 70) : num_scope.

  Open Scope num_scope.
  Bind Scope num_scope with num.
  
  (* TODO: the following instances could be in the standard library *)
  Instance le_preorder: PreOrder le.
  Proof.
    constructor.
    intros x; unfold Ple. rewrite le_nat_spec. auto with arith.
    intros x y z Hxy Hyz. rewrite le_nat_spec in *. apply (le_trans _ (nat_of_num y)); auto. 
  Qed.

  Instance lt_transitive: Transitive lt.
  Proof.
    intros x y z Hxy Hyz. rewrite lt_nat_spec in *. apply (lt_trans _ (nat_of_num y)); auto. 
  Qed.

  Lemma num_peano_rec : 
    forall (P : num -> Type), P (num_of_nat O) -> (forall p, P p -> P (S p)) -> forall p, P p.
  Proof.
    intros P H IH p.
    rewrite <- id_num. 
    generalize (nat_of_num p) as n. clear p. 
    intros. 
    induction n. 
    apply H.
    rewrite <- (id_nat n). rewrite <- S_nat_spec. rewrite id_num. apply IH. auto.
  Qed.

  Lemma eq_nat_spec : forall n m, n = m <-> nat_of_num n = nat_of_num m.
  Proof.
    intuition subst. reflexivity.
    setoid_rewrite <- id_num. rewrite H. reflexivity.
  Qed.

  Coercion num_of_nat : nat >-> num.
  Coercion nat_of_num : num >-> nat.

  Lemma pi0_inj: forall i j, pi0 i = pi0 j -> i = j.
  Proof.
    intros. cut (@inl num num i = @inl num num j). intro H'. injection H'. auto. 
    rewrite <- match_pi0, H. apply match_pi0. 
  Qed.

  Lemma pi1_inj: forall i j, pi1 i = pi1 j -> i = j.
  Proof.
    intros. cut (@inr num num i = @inr num num j). intro H'. injection H'. auto. 
    rewrite <- match_pi1, H. apply match_pi1. 
  Qed.
  
  Instance fold_num_compat' {A} {R} `{E: Equivalence A R}: 
  Proper (pointwise_relation num (R ==> R) ==> pointwise_relation num (R ==> R)) (@fold_num A).
  Proof.
    intros f g H n. induction n using num_peano_rec; intros a b H'; simpl. 
    rewrite 2fold_num_O. assumption.
    rewrite 2fold_num_S. apply IHn, H, H'.
  Qed.
    
  Instance fold_num_compat T: Proper 
    (pointwise_relation num (pointwise_relation T (@eq T))
      ==>
     pointwise_relation num (pointwise_relation T (@eq T))) (@fold_num T).
  Proof.
    intros f g H n. induction n using num_peano_rec; intro a; simpl. 
     rewrite 2fold_num_O. reflexivity.
     rewrite 2fold_num_S. rewrite IHn. rewrite H. reflexivity.
  Qed.


  (** * num_analyse : destroys the boolean expressions *)

  Instance eqb_view : Type_View eqb := { type_view := eq_spec }.
  Instance leb_view : Type_View leb := { type_view := le_spec }.
  Instance ltb_view : Type_View ltb := { type_view := lt_spec }.
    
  Ltac num_analyse := 
    repeat first [ type_view eqb | type_view leb | type_view ltb ].

  (** * num_prop : transforms atoms like [leb x y = true] into [le x y] *)
  Lemma leb_true : forall x y, leb x y = true <-> le x y. 
  Proof. intros. case le_spec; intuition discriminate. Qed.
  Lemma leb_false : forall x y, leb x y = false <-> lt y x.
  Proof.
    intros. rewrite eq_not_negb. rewrite leb_true. 
    rewrite le_nat_spec, lt_nat_spec. omega.
  Qed.
  Lemma ltb_true : forall x y, ltb x y = true <-> lt x y. 
  Proof. intros. case lt_spec; intuition discriminate. Qed.
  Lemma ltb_false : forall x y, ltb x y = false <-> le y x.
  Proof.
    intros. rewrite eq_not_negb. rewrite ltb_true. 
    rewrite le_nat_spec, lt_nat_spec. omega.
  Qed.
  Lemma eqb_true : forall x y, eqb x y = true <-> x = y. 
  Proof. intros. case eq_spec; intuition discriminate. Qed.
  Lemma eqb_false : forall x y, eqb x y = false <-> x <> y. 
  Proof. intros. case eq_spec; intuition. Qed.

  Lemma eq_num_dec: forall (n m: num), {n=m} + {n<>m}.
  Proof.
    intros n m. case_eq (eqb n m); intro H.
     rewrite eqb_true in H. auto.
     rewrite eqb_false in H. auto.
  Qed.

  Hint Rewrite 
    leb_true leb_false 
    ltb_true ltb_false
    eqb_true eqb_false : num_prop.

  Ltac num_prop := autorewrite with num_prop in *.

  Lemma eqb_refl: forall x, eqb x x = true.
  Proof. intro. num_prop. reflexivity. Qed.
  Lemma leb_refl: forall x, leb x x = true.
  Proof. intro. num_prop. reflexivity. Qed.
  Hint Rewrite  eqb_refl leb_refl id_nat id_num: bool_simpl.


  (** * num_omega : injects every prop about nums into equivalent props about nats, then call omega*)
  Lemma num_of_nat_comm : forall x y, x = num_of_nat y <-> nat_of_num x = y.
  Proof. 
    intros x y. split; [intros -> | intros <-]. 
    rewrite id_nat. reflexivity.
    rewrite id_num. reflexivity.
  Qed.
  
  Lemma nat_of_num_comm : forall x y, num_of_nat y = x <-> y = nat_of_num x .
  Proof. 
    intros x y. split; [intros <- | intros ->]. 
    rewrite id_nat. reflexivity.
    rewrite id_num. reflexivity.
  Qed.

  Hint Rewrite eq_nat_spec le_nat_spec lt_nat_spec S_nat_spec max_spec : num_omega.
  Hint Rewrite nat_of_num_comm num_of_nat_comm : num_omega .
  Hint Rewrite id_nat id_num : num_omega.

  Ltac num_simpl := autorewrite with num_omega in *.
  Ltac num_omega := num_simpl; intuition (subst; omega).
  Ltac num_omega_false := exfalso; num_omega.

  Lemma eqb_eq_nat_bool: forall i j, 
    eqb i j = eq_nat_bool (nat_of_num i) (nat_of_num j). 
  Proof.
    intros. num_analyse. subst. bool_simpl. reflexivity.
    symmetry. nat_prop. num_omega.
  Qed.

  Lemma numseteqb_eq_nat_bool: forall i j, 
    NumSetProps.eqb i j = eq_nat_bool (nat_of_num i) (nat_of_num j). 
  Proof.
    intros. rewrite <- eqb_eq_nat_bool. unfold NumSetProps.eqb. destruct (NumSetProps.P.Dec.F.eq_dec i j). 
    rewrite set_eq_spec in e. subst. bool_simpl.  reflexivity. 
    rewrite set_eq_spec in n. symmetry. num_prop. auto.
  Qed.
  Hint Rewrite numseteqb_eq_nat_bool : bool_simpl.

  Lemma le_antisym: forall n m: num, n <= m -> m <= n -> n = m.
  Proof. intros. num_omega. Qed. 

End NumUtils.



(** * Instance of [NUM] with [positive] as base type *)
Module Positive <: NUM.
  Definition num := positive.
  Definition nat_of_num n := pred (nat_of_P n).
  Definition num_of_nat := P_of_succ_nat.
  Definition le := Ple.
  Definition lt := Plt.
  Definition compare n m := Pcompare n m Eq.

  Definition leb (n m: num) := 
    match Pcompare n m Eq with 
      | Gt => false
      | _ => true
    end.
  Definition ltb (n m: num) :=  
    match Pcompare n m Eq with 
      | Lt => true
      | _ => false
    end.
  Definition eqb := eq_pos_bool.

  Definition S := Psucc.
  Definition max := Pmax.
  Definition fold_num T (f: num -> T -> T) :=
    Prect (fun _ => T -> T) (fun acc => acc) (fun a aux acc => aux (f a acc)).

  Fixpoint PeanoView_sum_iter E T (f: positive -> T -> T + E) p (q: PeanoView p) a :=
    match q with
      | PeanoOne => inl a
      | PeanoSucc p q => 
        match f p a with 
          | inl a => PeanoView_sum_iter f q a
          | e => e
        end
    end.
  Definition fold_num_sum E T (f: num -> T -> T + E) p a :=  PeanoView_sum_iter f (peanoView p) a. 

  Definition pi0 := xO.
  Definition pi1 := xI.
  Definition pimatch i := match i with xO i => inl i | xI i => inr i | xH => inl xH end.

  (* bijection with nat  *)
  Lemma id_num : forall n, num_of_nat (nat_of_num n) = n.
  Proof.
      intros n.  
      unfold nat_of_num.
      pattern n.
      apply Pcase. simpl. reflexivity.
      clear n. intros n. replace (nat_of_P (Psucc n)) with (Datatypes.S (nat_of_P n)). simpl.
      apply P_of_succ_nat_o_nat_of_P_eq_succ.
      symmetry; apply nat_of_P_succ_morphism.
  Qed.

  Lemma id_nat : forall n, nat_of_num (num_of_nat n) = n. 
  Proof.
    intros n.
    unfold nat_of_num. 
    assert (Hn : 0 < nat_of_P (num_of_nat n) ). apply lt_O_nat_of_P. 
    assert (forall s n, 0 <s -> s = Datatypes.S n -> pred s = n). intros. omega.
    apply H. auto.  
    apply nat_of_P_o_P_of_succ_nat_eq_succ.
  Qed.


  (* specification of the boolean operations w.r.t. the predicates *)
  Lemma le_spec : forall n m, reflect (le n m) (leb n m). 
  Proof.  
    intros n m; unfold leb.
    case_eq ( Pos.compare_cont n m Eq ); intro H; try constructor.
    apply Pcompare_Eq_eq in H. subst.  unfold le ,Ple.  
    rewrite Pos.compare_refl. intro; discriminate.
    unfold le. unfold Ple. intro. unfold Pos.compare in *.  congruence. 
    apply ZC1 in H. intro H'. unfold le, Ple in H'. apply ZC2 in H.  rewrite H in H'. tauto_false.
  Qed.

  Lemma lt_spec : forall n m, reflect (lt n m) (ltb n m).
  Proof. 
    intros n m; unfold ltb.
    case_eq ( Pos.compare_cont n m Eq ); intro H; try constructor.
    intro H'. apply Pcompare_Eq_eq in H. subst. refine (Plt_irrefl _ H').
    auto.
    intro H'. apply ZC1 in H. assert (H'' := Plt_trans _ _ _ H H'). refine (Plt_irrefl _ H''). 
  Qed.

  Definition eq_spec := eq_pos_spec.
  Lemma compare_spec : forall n m, compare_spec eq lt n m (compare n m). 
  Proof. 
   intros.
   case_eq (compare n m); intro H;  constructor.
   apply Pcompare_Eq_eq. apply H.
   apply H.
   
   unfold compare in H.
   apply ZC1. auto.
  Qed.

  (* specification of operations and predicates, w.r.t. nat *)
  Lemma S_nat_spec : forall n, nat_of_num (S n) = Datatypes.S (nat_of_num n). 
  Proof.
    intros n.
    unfold nat_of_num. rewrite nat_of_P_succ_morphism. simpl.
    assert (H := lt_O_nat_of_P n).
    omega.
  Qed.
  Lemma le_nat_spec : forall n m, le n m <-> (nat_of_num n <= nat_of_num m)%nat. 
  Proof.
    intros x y.
    assert (Hx := lt_O_nat_of_P x).
    assert (Hy := lt_O_nat_of_P y).

    split; intro H.
      assert (H' : ~nat_of_P x > nat_of_P y). unfold Ple in H. intro H'. 
      apply H.
      apply nat_of_P_gt_Gt_compare_complement_morphism. auto. 
      unfold nat_of_num .
      omega.

      intro H'.   
      apply nat_of_P_gt_Gt_compare_morphism in H'.
      unfold nat_of_num in H.
      omega.
  Qed.


  Lemma lt_nat_spec : forall n m, lt n m <-> (nat_of_num n <  nat_of_num m)%nat.
  Proof.
    intros x y.
    assert (Hx := lt_O_nat_of_P x).
    assert (Hy := lt_O_nat_of_P y).

    split; intro.
    assert (nat_of_P x < nat_of_P y).
    apply    nat_of_P_lt_Lt_compare_morphism. apply H.
    unfold nat_of_num.
    omega.
    
    apply nat_of_P_lt_Lt_compare_complement_morphism.
    unfold nat_of_num in H.
    omega.
  Qed.

  Lemma max_spec : forall n m, nat_of_num (max n m) = Max.max (nat_of_num n) (nat_of_num m).
  Proof.
    intros n m. unfold max, Pmax. case_eq ((n ?= m) %positive); intros.
    apply Pcompare_Eq_eq in H; subst. rewrite Max.max_l; auto.
    rewrite Max.max_r; trivial. apply lt_le_weak. rewrite <- lt_nat_spec. assumption.
    rewrite Max.max_l; trivial. apply lt_le_weak. rewrite <- lt_nat_spec. 
    unfold lt. rewrite Pos.compare_gt_iff in *.  auto.
  Qed.


  (* fold_num specification *)
  Lemma fold_num_O: forall A (a: A) f, fold_num f xH a = a. 
  Proof. reflexivity. Qed.

  Lemma fold_num_S: forall A (a: A) f n, fold_num f (S n) a = fold_num f n (f n a).
  Proof.
    intros. unfold fold_num at 1. rewrite Prect_succ. reflexivity.  
  Qed.


  (* fold_num_sum specification *)
  Lemma fold_num_sum_O: forall E T a f, @fold_num_sum E T f (num_of_nat 0) a = inl a.
  Proof. intros. reflexivity. Qed.

  Lemma fold_num_sum_S: forall E T a f n, @fold_num_sum E T f (S n) a = 
    match f n a with 
      | inl a => fold_num_sum f n a
      | e => e
    end.
  Proof.
    intros. unfold fold_num_sum. 
    replace (peanoView (S n)) with (PeanoSucc n (peanoView n)). reflexivity.
    apply PeanoViewUnique.
  Qed.


  (* pi/match specification *)
  Lemma match_pi0: forall n, pimatch (pi0 n) = inl n. Proof. reflexivity. Qed.
  Lemma match_pi1: forall n, pimatch (pi1 n) = inr n. Proof. reflexivity. Qed.
    
  Lemma lt_pi0: forall n m, lt n m -> lt (pi0 n) (pi0 m).
  Proof. intros n m. setoid_rewrite lt_nat_spec. unfold pi0, nat_of_num. rewrite 2 nat_of_P_xO. omega. Qed.
  Lemma lt_pi1: forall n m, lt n m -> lt (pi1 n) (pi1 m).
  Proof. intros n m. setoid_rewrite lt_nat_spec. unfold pi1, nat_of_num. rewrite 2 nat_of_P_xI. omega. Qed.

  Module NumOTA := Pos_as_OTA.
(*   Module NumSet' := FSetList.Make Pos_as_OT. Module NumSet := FSetHide NumSet'.  *)
  Module NumSet' := FSetPositive.PositiveSet. Module NumSet := FSetHide NumSet'.
  Module NumMap' := FMapPositive.PositiveMap. Module NumMap := FMapHide NumMap'.

  Local Open Scope positive_scope.
  Definition triangle k i := (*  k*(k-1)/2 + i  *)
    match k with
      | 1 => i
      | k'~0 => k'*Pdouble_minus_one k'+i
      | k'~1 => k'*k+i
    end.
  Definition enc i j := triangle (Ppred (i+j)) i.
  Fixpoint code (x: NumSet.t): num :=
    match x with
      | NumSet'.Leaf => 1
      | NumSet'.Node l true  r => enc (code l) (code r)~0
      | NumSet'.Node l false r => enc (code l) (code r)~1
    end.

  (* we need this tactic to substitute some positive equalities *)
  Ltac psubst :=
    (repeat match goal with 
              | H: Pos_as_OTA.compare _ _ = Eq |- _ => apply Pos_as_OTA.reflect in H
            end); subst.

  (* and this hints to automatically prove some trivial facts, by reflexivity *)
  Hint Extern 0 (Pos_as_OTA.compare _ _ = Eq) => apply Pos_as_OT.eq_refl.

  Lemma pcompare_prop: forall x y, Pos_as_OTA.compare x y = Eq <-> x = y. 
  Proof. intros. intuition; psubst; trivial. Qed. 
  Hint Rewrite pcompare_prop : num_prop.

  (* specifications of the equalities on maps and sets *)
  Lemma set_eq_spec : forall x y, NumSet.E.eq x y <-> x = y. 
  Proof. intros. reflexivity. Qed. 
  Lemma map_eq_spec : forall x y, NumMap.E.eq x y <-> x = y. 
  Proof. intros. reflexivity. Qed. 

End Positive.

Module PositiveUtils := NumUtils Positive.

