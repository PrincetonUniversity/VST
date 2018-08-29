(* Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* A theory of constructed rational numbers *)

Set Implicit Arguments.

Require Import Omega.
Require Import List.
Require Import fcf.StdNat.
Require Import Arith.
Require Import Lia.

Inductive Rat :=
    RatIntro : nat -> posnat -> Rat.

Definition ratCD(r1 r2 : Rat) : (nat * nat * posnat) :=
  match (r1, r2) with
    | (RatIntro n1 d1, RatIntro n2 d2) =>
      ((n1 * d2), (n2 * d1), (posnatMult d1 d2))
  end.

Definition ratMult(r1 r2 : Rat) : Rat :=
  match (r1, r2) with
    | (RatIntro n1 d1, RatIntro n2 d2) =>
      RatIntro (n1 * n2) (posnatMult d1 d2)
  end.

Definition rat1 := (RatIntro 1 (pos 1)).
Definition rat0 := (RatIntro 0 (pos 1)).


Definition ratAdd(r1 r2 : Rat) : Rat :=
  match ratCD r1 r2 with
    | (n1, n2, d) => 
      RatIntro (n1 + n2) d
  end.

Definition ratSubtract(r1 r2: Rat) : Rat :=
  match ratCD r1 r2 with
    | (n1, n2, d) =>
      RatIntro (n1 - n2) d
  end.

Definition beqRat(r1 r2 : Rat) :=
  match (ratCD r1 r2) with
    | (n1, n2, _) => 
      if (eq_nat_dec n1 n2) then true else false
  end.

Definition bleRat(r1 r2 : Rat) :=
  match (ratCD r1 r2) with
    | (n1, n2, _) => 
      if (le_gt_dec n1 n2) then true else false
  end.

Definition eqRat(r1 r2 : Rat) :=
  beqRat r1 r2 = true.

Definition leRat(r1 r2 : Rat) := 
  bleRat r1 r2 = true.

Definition maxRat(r1 r2 : Rat) :=
  if (bleRat r1 r2) then r2 else r1.

Definition minRat(r1 r2 : Rat) :=
  if (bleRat r1 r2) then r1 else r2.

Definition ratDistance(r1 r2 : Rat) :=
  ratSubtract (maxRat r1 r2) (minRat r1 r2).

Ltac rattac_one := 
  match goal with 
    (* rules that solve goals *)
    | [|- posnatMult ?x1 ?x2 = posnatMult ?x2 ?x1] => apply posnatMult_comm
    | [|- posnatToNat (posnatMult ?x1 ?x2) = posnatToNat (posnatMult ?x2 ?x1)] => rewrite posnatMult_comm; trivial
    | [|- ?x1 * ?x2 = ?x2 * ?x1 ] => apply mult_comm
    | [|- (mult (?x1 + ?x2) _)  = (mult (?x2 + ?x1) _ )] => f_equal
    | [|- ?x1 * ?x2 * _ = ?x2 * ?x1 * _ ] => f_equal
    | [ |- posnatToNat ?p > 0 ] => destruct p; unfold posnatToNat; omega
      (* inversion on hypotheses *)
    | [H1 : ?n * ?x = ?n0 * ?x1, H2: ?n1 * ?x1 = ?n * ?x0 |- ?n1 * ?x = ?n0 * ?x0 ] => eapply (@mult_same_l x1)(* ;
      [idtac | rewrite mult_assoc ;
        rewrite (mult_comm x1 n1);
          rewrite H2;
            rewrite <- mult_assoc ;
              rewrite (mult_comm x x0) ;
                repeat rewrite mult_assoc;
                  f_equal] *) 
    | [H : ?x = ?n * (posnatToNat ?p) |- ?x = (posnatToNat ?p) * ?n ] => rewrite H
    | [H : RatIntro _ _ = RatIntro _ _ |- _ ] => inversion H; clear H; subst
    | [H : (eqRat _ _) |- _ ] => unfold eqRat, beqRat in H
    | [H : (leRat _ _) |- _ ] => unfold leRat, bleRat in H
    | [H : ?r = RatIntro _ _ |- context[match ?r with | RatIntro _ _ => _ end] ] => rewrite r
    
    | [|- context[match ?r with | RatIntro _ _ => _ end] ] => case_eq r; intuition
    | [H : (_ , _) = (_ , _) |- _ ] => inversion H; clear H; subst
    | [|- (_, _) = (_, _) ] => f_equal
    | [H: context[ratCD _ _] |- _ ] => unfold ratCD in *
    | [H : context[match rat0 with | RatIntro _ _ => _ end ] |- _ ] => unfold rat0 in H
    | [H1 : context[match ?r with | RatIntro _ _ => _ end], H2 : ?r = RatIntro _ _ |- _ ] => rewrite H2 in H1
    | [H : context[match ?r with | RatIntro _ _ => _ end ] |- _ ] => case_eq r; intuition
    | [|- context[let (_, _) := ?x in _] ] => case_eq x; intuition
    | [H : context[ratAdd _ _] |- _ ] => unfold ratAdd in H    
    | [H : context[ratMult _ _] |- _ ] => unfold ratMult in H   
    | [H: context [eq_nat_dec ?x ?y] |- _] => destruct (eq_nat_dec x y)
    | [H: context [le_gt_dec ?x ?y] |- _] => destruct (le_gt_dec x y)
    | [|- (if (eq_nat_dec ?x ?y) then true else false) = true ] => assert (x = y); destruct (eq_nat_dec x y); trivial
     | [|- (if (le_gt_dec ?x ?y) then true else false) = true ] => assert (x <= y); [idtac | destruct (le_gt_dec x y); trivial]
    | [|- context[posnatMult _ _ ] ] => unfold posnatMult
    | [|- (eqRat _ _) ] => unfold eqRat, beqRat
    | [|- (leRat _ _) ] => unfold leRat, bleRat
    | [|- (posnatEq _ _ ) ] => econstructor
    | [|- context[(posnatToNat _)] ] => unfold posnatToNat in *
    | [H : context[let (_, _) := ?p in _] |- _] => destruct p
    end.
Ltac rattac :=
  intuition; unfold ratCD in *; 
    repeat (rattac_one; subst); repeat rewrite mult_1_r; repeat rewrite plus_0_r; trivial; try congruence; try omega.

Lemma ratCD_comm : forall r1 r2 n1 n2 d n1' n2' d',
  ratCD r1 r2 = (n1, n2, d) ->
  ratCD r2 r1 = (n1', n2', d') ->
  n1 = n2' /\ n1' = n2 /\ (posnatEq d d').

  rattac.
Qed.

Infix "*" := ratMult : rat_scope.
Local Open Scope rat_scope.


Notation "n / d" := (RatIntro n (pos d)) : rat_scope.

Notation "0" := rat0 : rat_scope.
Notation "1" := rat1 : rat_scope.

Infix "+" := ratAdd : rat_scope.

Delimit Scope rat_scope with rat.

Notation " |  a - b |" := (ratDistance a%rat b%rat) (at level 30, a at next level, b at next level) : rat_scope.

Infix "<=" := leRat : rat_scope.
Infix "==" := eqRat (at level 70) : rat_scope.


Theorem le_Rat_dec : forall r1 r2,
  {r1 <= r2} + {~r1 <= r2}.

  intuition.
  case_eq (bleRat r1 r2); intuition.
  right.
  intuition.
  congruence.
Qed.

Theorem eq_Rat_dec : forall r1 r2,
  {r1 == r2} + {~r1 == r2}.

  intuition.
  case_eq (beqRat r1 r2); intuition.
  right.
  intuition.
  congruence.
Qed.

Theorem eqRat_refl : forall r,
  eqRat r r.

  rattac.
Qed.

Theorem eqRat_symm : forall r1 r2,
  eqRat r1 r2 ->
  eqRat r2 r1.

  rattac.
Qed.

Theorem eqRat_trans : forall r1 r2 r3,
  eqRat r1 r2 ->
  eqRat r2 r3 ->
  eqRat r1 r3.

  rattac.
  match goal with H:_, G:_ |- _ => ring [H G] end.
Qed.

Theorem leRat_refl : forall r,
  leRat r r.

  rattac.
Qed.

Lemma mult_le_compat_r_iff_h : forall n2 n3 n1,
    n1 > O ->
    (n2 * n1 <= n3 * n1)%nat ->
    (n2 <= n3)%nat.
  
  induction n2; destruct n3; intuition; simpl in *; try omega.
  
  exfalso.
  remember (n2 * n1)%nat as x.
  omega.

  eapply le_n_S.
  eapply IHn2; eauto.
  omega.
Qed.

Lemma mult_le_compat_r_iff : forall n1 n2 n3,
    n1 > O ->
    (n2 * n1 <= n3 * n1)%nat ->
    (n2 <= n3)%nat.
  
  intuition.
  eapply mult_le_compat_r_iff_h; eauto.
Qed.

Theorem leRat_trans : forall r1 r2 r3,
  leRat r1 r2 ->
  leRat r2 r3 ->
  leRat r1 r3.

  rattac.

  eapply (@mult_le_compat_r_iff x1); trivial.
  rewrite <- mult_assoc.
  rewrite (mult_comm x).
  rewrite mult_assoc.
  eapply le_trans.
  eapply mult_le_compat.
  eapply l.
  eauto.

  repeat rewrite <- mult_assoc.
  repeat rewrite (mult_comm x0).
  repeat rewrite mult_assoc.
  eapply mult_le_compat; eauto.
Qed.

Theorem eqRat_impl_leRat : forall r1 r2,
  eqRat r1 r2 ->
  leRat r1 r2.

  rattac.
Qed.

Theorem leRat_impl_eqRat : forall r1 r2,
  leRat r1 r2 ->
  leRat r2 r1 ->
  eqRat r1 r2.

  rattac.
Qed.


Require Import Setoid.

(*
Definition eqRat_setoid : Setoid_Theory Rat eqRat.
econstructor; red.
eapply eqRat_refl.
eapply eqRat_symm.
eapply eqRat_trans.
Defined.
*)

Add Parametric Relation : Rat leRat
  reflexivity proved by leRat_refl
  transitivity proved by leRat_trans
    as leRat_rel.

Add Parametric Relation : Rat eqRat 
  reflexivity proved by eqRat_refl
  symmetry proved by eqRat_symm
  transitivity proved by eqRat_trans
  as eqRat_rel.

Require Import RelationClasses.
Require Import Coq.Classes.Morphisms.

Global Instance Subrelation_eq_le : subrelation eqRat leRat.
repeat red.
intuition.
eapply eqRat_impl_leRat.
trivial.
Qed.

Global Instance eqRat_resp_leRat : 
  forall x,
    Proper (eqRat ==> Basics.flip Basics.impl)
                                  (leRat x).

intuition.
repeat red; intuition.
simpl.
unfold respectful.
intuition.
eapply leRat_trans.
eapply H0.
eapply eqRat_impl_leRat.
symmetry.
trivial.

Qed.

Local Open Scope rat_scope.
Theorem rat0_le_all : forall r,
  0 <= r.

  rattac.
Qed.

Theorem rat1_ne_rat0 : ~ (eqRat 1 0).
  intuition.
Qed.

Theorem rat0_ne_rat1 : ~ (eqRat 0 1).
  intuition.
Qed.

Theorem ratAdd_comm : forall r1 r2,
  r1 + r2 == r2 + r1.
 
  rattac.
Qed.

Theorem ratAdd_0_r : forall r,
  r == r + 0.

  rattac;
  inversion H;
  subst;
  rewrite mult_1_r;
  trivial.
Qed.

Theorem ratAdd_0_l : forall r,
  r == 0 + r.

  intuition.
  rewrite ratAdd_comm.
  apply ratAdd_0_r.
Qed.

Theorem ratMult_comm : forall (r1 r2 : Rat),
  eqRat (ratMult r1 r2) (ratMult r2 r1).

  rattac.
Qed.

Theorem ratAdd_assoc : forall r1 r2 r3,
  r1 + r2 + r3 == r1 + (r2 + r3).

  rattac. 
  inversion H; clear H; subst.

  Local Open Scope nat_scope.

  Ltac arithNormalize_step :=
    repeat rewrite mult_succ_r in *;
      repeat rewrite mult_plus_distr_r in *;
        repeat rewrite mult_plus_distr_l in *;
          repeat rewrite mult_minus_distr_r in *;
            repeat rewrite mult_minus_distr_l in *;
              repeat rewrite plus_assoc in *;
                repeat rewrite mult_assoc in *.

  Ltac arithNormalize := repeat arithNormalize_step.

  Ltac arithSimplify :=
    match goal with
      | [|- _ + ?x = _ + ?x] => f_equal
      | [|- _ + (?x1 * ?x2) = _ + (?x2 * ?x1) ] => f_equal
      | [|- _ + (?x1 * ?x2 * ?x3) = _ + (?x1 * ?x3 * ?x2) ] => f_equal
      | [|- _ + (?x1 * ?x2 * ?x3 * ?x4 * ?x5 * ?x6) = _ + (?x1 * ?x3 * ?x2 * ?x4 * ?x5 * ?x6) ] => f_equal
      | [|- _ * ?x1 = _ * ?x1] => f_equal
      | [|- _ * ?x = _ ] => rewrite mult_comm; repeat rewrite mult_assoc; arithSimplify
      | [|- _ + ?x = _ ] => rewrite plus_comm; repeat rewrite plus_assoc; arithSimplify
      | [|- _ * ?x1 <= _ * ?x1] => apply mult_le_compat; auto
      | [|- _ * ?x1 <= _ * ?x1] => apply plus_le_compat; auto
      | [|- _ * ?x <= _ ] => rewrite mult_comm; repeat rewrite mult_assoc; arithSimplify
      | [|- _ + ?x <= _ ] => rewrite plus_comm; repeat rewrite plus_assoc; arithSimplify
      
    end.

  arithNormalize.
  arithSimplify.
  arithSimplify.
  do 5 arithSimplify.
  do 5 arithSimplify.
Qed.

Local Open Scope rat_scope.
Theorem ratMult_assoc : forall r1 r2 r3,
  r1 * r2 * r3 == r1 * (r2 * r3).

  rattac;

  inversion H0; clear H0; subst;
  inversion H; clear H; subst;
  arithNormalize;
  arithSimplify.
  
Qed.

Lemma ratAdd_eqRat_compat_l : forall r1 r2 r3,
  eqRat r1 r2 ->
  r1 + r3 == r2 + r3.

  rattac.
  arithNormalize.
  f_equal.
  f_equal.
  rewrite mult_comm.
  rewrite (mult_comm _ x1).
  repeat rewrite mult_assoc.
  f_equal.
  rewrite mult_comm.
  rewrite e.
  apply mult_comm.
  do 3 arithSimplify.
Qed.

Theorem ratAdd_eqRat_compat : forall r1 r2 r3 r4,
  eqRat r1 r2 ->
  eqRat r3 r4 ->
  r1 + r3 == r2 + r4.

  intuition.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat_l; eauto.
  repeat rewrite (ratAdd_comm r2).
  eapply ratAdd_eqRat_compat_l; eauto.
Qed.

Lemma ratAdd_leRat_compat_l : forall r1 r2 r3,
  leRat r1 r2 ->
  r1 + r3 <= r2 + r3.

  rattac.
  
  unfold leRat, bleRat in *.
  rattac.
  arithNormalize.  
  apply plus_le_compat.

  apply mult_le_compat; trivial.
  repeat rewrite <- mult_assoc.
  repeat rewrite (mult_comm x0).
  repeat rewrite mult_assoc.
  apply mult_le_compat; trivial.
  
  apply mult_le_compat; trivial.
  rewrite <- mult_assoc.
  rewrite (mult_comm x1).
  rewrite mult_assoc.
  apply mult_le_compat; trivial.  
Qed.

Theorem ratAdd_leRat_compat : forall r1 r2 r3 r4,
  leRat r1 r2 ->
  leRat r3 r4 ->
  r1 + r3 <= r2 + r4.

  intuition.
  eapply leRat_trans.

  eapply ratAdd_leRat_compat_l; eauto.
  rewrite ratAdd_comm.

  eapply leRat_trans.
  apply ratAdd_leRat_compat_l; eauto.
  rewrite ratAdd_comm.
  intuition.
Qed.

Theorem ratMult_leRat_compat : forall (r1 r2 r3 r4 : Rat),
  leRat r1 r2 ->
  leRat r3 r4 ->
  leRat (ratMult r1 r3) (ratMult r2 r4).

  rattac.
  nia.
Qed.

Add Parametric Morphism : ratAdd
  with signature (leRat ==> leRat ==> leRat)
  as ratAdd_leRat_mor.

  intuition.
  eapply ratAdd_leRat_compat; trivial.
Qed.

Add Parametric Morphism : ratAdd
  with signature (eqRat ==> eqRat ==> eqRat)
  as ratAdd_eqRat_mor.

  intuition.
  eapply ratAdd_eqRat_compat; trivial.
Qed.

Theorem ratMult_eqRat_compat : forall (r1 r2 r3 r4 : Rat),
  eqRat r1 r2 ->
  eqRat r3 r4 ->
  eqRat (ratMult r1 r3) (ratMult r2 r4).

  rattac.
  
  repeat rewrite mult_assoc.
  rewrite <- (mult_assoc n1).
  rewrite (mult_comm n).
  rewrite mult_assoc.
  rewrite <- mult_assoc.
  rewrite e.
  rewrite e0.
  rewrite mult_assoc.
  do 3 arithSimplify.

Qed.

Add Parametric Morphism : ratMult
  with signature (leRat ==> leRat ==> leRat)
  as ratMult_leRat_mor.

  intuition.
  eapply ratMult_leRat_compat; trivial.
Qed.

Add Parametric Morphism : ratMult
  with signature (eqRat ==> eqRat ==> eqRat)
  as ratMult_eqRat_mor.

  intuition.
  eapply ratMult_eqRat_compat; trivial.
Qed.


Theorem ratAdd_0 : forall r1 r2,
  r1 + r2 == 0 <->
  r1 == 0 /\ r2 == 0.

  intuition.
  rattac.
  rewrite mult_0_l in e.
  unfold posnatToNat in *.
  simpl in *.
  destruct p1.
  destruct p0.
  rewrite mult_1_r in e.
  apply plus_is_O in e.
  intuition.
  eapply mult_is_O in H0.
  intuition.
  
  rattac.
  rewrite mult_0_l in e.
  unfold posnatToNat in *.
  simpl in *.
  destruct p1.
  destruct p0.
  rewrite mult_1_r in e.
  apply plus_is_O in e.
  intuition.
  eapply mult_is_O in H1.
  intuition.

  rewrite (ratAdd_0_r 0).
  eapply ratAdd_eqRat_compat; eauto.
Qed.

Theorem ratAdd_nz : forall r1 r2,
  ~(r1 + r2 == 0) <->
  (~r1 == 0) \/ (~r2 == 0).


  intuition.
  destruct (eq_Rat_dec r1 0); intuition.
  destruct (eq_Rat_dec r2 0); intuition.
  exfalso.
  eapply H.
  apply ratAdd_0; eauto.
 
  apply H1.
  specialize (ratAdd_0 r1 r2); intuition.

  apply H1.
  specialize (ratAdd_0 r1 r2); intuition.
Qed.

Theorem rat_num_0 : forall d,
  (RatIntro O d) == 0.

  rattac.
Qed.

Lemma ratMult_0_l : forall r,
  0 * r == 0.
  
  intuition; destruct r.
  unfold ratMult.
  simpl.
  unfold natToPosnat, posnatMult; simpl.
  destruct p.
  apply rat_num_0.
Qed.

Lemma ratMult_0_r : forall r,
  r * 0 == 0.
  
  rattac.
Qed.

Lemma ratMult_1_l : forall r,
  1 * r == r.
  
  rattac.
  inversion H; clear H; subst.
  repeat rewrite mult_1_l in *.
  trivial.
Qed.

Theorem ratMult_0 : forall r1 r2,
  r1 * r2 == 0 <-> 
  r1 == 0 \/ r2 == 0.

  intuition.
  rattac.
  rewrite mult_0_l in e.
  unfold posnatToNat in *.
  simpl in *.
  rewrite mult_1_r in e.
  apply mult_is_O in e.
  intuition; subst.
  left.
  apply rat_num_0.
  
  right.
  apply rat_num_0.

  rewrite <- (ratMult_0_l r2).
  eapply ratMult_eqRat_compat; intuition.

  rewrite <- (ratMult_0_r r1).
  eapply ratMult_eqRat_compat; intuition.
Qed.

Theorem ratMult_nz : forall r1 r2,
  (~r1 * r2 == 0) <->
  (~r1 == 0) /\ (~r2 == 0).

  intuition.
  
  eapply H.
  specialize (ratMult_0 r1 r2); intuition.

  eapply H.
  specialize (ratMult_0 r1 r2); intuition.

  apply ratMult_0 in H0.
  intuition.

Qed.

Theorem leRat_num : forall n1 n2 d,
  le n1 n2 ->
  leRat (RatIntro n1 d) (RatIntro n2 d).

  rattac.
  eapply mult_le_compat; eauto.
Qed.


Theorem eqRat_terms : forall n1 d1 n2 d2,
  n1 = n2 ->
  posnatToNat d1 = posnatToNat d2 ->
  eqRat (RatIntro n1 d1) (RatIntro n2 d2).

  rattac.
Qed.

Lemma leRat_mult : forall n1 n2 d1 d2 (pf1 : d1 > 0) (pf2 : d2 > 0),
                     RatIntro n1 (exist (fun d => d > 0) _ pf1) <= RatIntro n2 (exist (fun d => d > 0) _ pf2) ->
                     (n1 * d2 <= n2 * d1)%nat.
  
  rattac.
Qed.

Lemma nat_minus_eq : forall (n1 n2 : nat),
                       (n1 <= n2)%nat ->
                       n2 - n1 = O ->
                       n1 = n2.

  intuition. 
Qed.


Lemma bleRat_total : forall r1 r2,
                       bleRat r1 r2 = false -> bleRat r2 r1 = true.
  
  intuition.
  unfold bleRat in *.
  rattac.
Qed.

Theorem ratIdentityIndiscernables : forall r1 r2,
  r1 == r2 <->
  ratDistance r1 r2 == rat0.

  rattac;
  unfold ratDistance, ratSubtract in *;
  rattac;
  unfold minRat, maxRat in *;
  rattac.
  case_eq (bleRat (RatIntro n (exist (fun n : nat => n > 0) x2 g2))
             (RatIntro n0 (exist (fun n : nat => n > 0) x1 g1))); intuition.
  rewrite H1 in H2.
  rewrite H1 in H0.
  rattac.

  rewrite H1 in H2.
  rewrite H1 in H0.
  rattac.

  case_eq (bleRat (RatIntro n0 (exist (fun n : nat => n > 0) x0 g0))
             (RatIntro n1 (exist (fun n : nat => n > 0) x g))); intuition.
  rewrite H0 in H1.
  rewrite H0 in H2.
  rattac.
  inversion e; clear e; subst.
  apply mult_is_O in H2; intuition.
  unfold posnatMult in *.
  inversion H5; clear H5; subst.
  assert ((RatIntro n4 (exist (fun n : nat => n > 0) x0 g0)) <= (RatIntro n3 (exist (fun n : nat => n > 0) x g))).
  unfold leRat.
  trivial.
  
  eapply nat_minus_eq.
  apply (leRat_mult H2).
  trivial.

  rewrite H0 in H1.
  rewrite H0 in H2.
  rattac.
  unfold posnatMult in *.
  simpl in *.
  inversion H5; clear H5; subst.
  apply mult_is_O in e. intuition.
  symmetry.
  eapply nat_minus_eq; trivial.

  apply bleRat_total in H0.
  assert (leRat (RatIntro n4 (exist (fun n : nat => n > 0) x g))
         (RatIntro n3 (exist (fun n : nat => n > 0) x0 g0))).
  apply H0.
  apply (leRat_mult H2).
Qed.

(* is this even true ? 
Lemma ratDistance_comm_2 : forall r1 r2 r3 r4,
    ratDistance (ratDistance r1 r2) (ratDistance r3 r4) ==
    ratDistance (ratDistance r1 r3) (ratDistance r2 r4).

    intuition.
    
    unfold ratDistance, ratSubtract.
    rattac.
    arithNormalize.

    Lemma minus_eq_compat : forall n1 n2 n3 n4,
      n1 = n2 ->
      n3 = n4 ->
      n1 - n3 = n2 - n4.

      intuition.
    Qed.

    apply minus_eq_compat.
    arithSimplify.
    rewrite (mult_comm _ x).
    arithNormalize.
    arithSimplify.
    unfold minRat, maxRat in *.
    case_eq (bleRat (RatIntro (n7 * p8 - n8 * p7) (posnatMult p7 p8))
            (RatIntro (n9 * p10 - n10 * p9) (posnatMult p9 p10))); intuition;
    case_eq ( bleRat (RatIntro (n3 * p4 - n4 * p3) (posnatMult p3 p4))
             (RatIntro (n5 * p6 - n6 * p5) (posnatMult p5 p6))); intuition.
    case_eq (bleRat (RatIntro (n7 * p8 - n8 * p7) (posnatMult p7 p8))
             (RatIntro (n9 * p10 - n10 * p9) (posnatMult p9 p10))); intuition.
    case_eq (bleRat (RatIntro (n3 * p4 - n4 * p3) (posnatMult p3 p4))
             (RatIntro (n5 * p6 - n6 * p5) (posnatMult p5 p6))); intuition.
    rewrite H11 in H.
    rewrite H12 in H1.
    rewrite H13 in H0.
    rewrite H14 in H2.

    inversion H; clear H; subst.
    inversion H0; clear H0; subst.
    inversion H1; clear H1; subst.
    inversion H2; clear H2; subst.

    unfold posnatMult in *.
    destruct p9; destruct p10.
    destruct p5; destruct p6.
    destruct p7; destruct p8.
    destruct p3; destruct p4.
    simpl in *.
    inversion H1; clear H1; subst.
    inversion H15; clear H15; subst.
    inversion H16; clear H16; subst.
    inversion H17; clear H17; subst.

    unfold minRat in *.

    destruct p7.

    SearchAbout minus.
    rattac_one.
    rattac_one.
  Abort.
*)

Lemma ratSubtract_partition : forall r1 r2 r3,
  r1 <= r2 ->
  r2 <= r3 ->
  (ratSubtract r3 r1) == (ratSubtract r2 r1) + (ratSubtract r3 r2).

  rattac.
  unfold ratSubtract in *.
  rattac.
  arithNormalize.
  rewrite <- NPeano.Nat.add_sub_swap.
  eapply minus_eq_compat.
  rewrite minus_add_assoc.
  rewrite plus_comm.
  rewrite <- minus_add_assoc.
  rewrite <- plus_0_r at 1.
  apply plus_eq_compat.
  do 4 arithSimplify.
  symmetry.
  eapply minus_diag_eq.
  do 4 arithSimplify.
  apply le_eq.
  do 5 arithSimplify.
  do 4 (apply mult_le_compat; trivial).
  do 4 arithSimplify.
  do 4 (apply mult_le_compat; trivial).

Qed.

Lemma ratAdd_any_leRat_l : forall r1 r2 r3,
  r1 <= r3 ->
  r1 <= r3 + r2.
  
  rattac.
  arithNormalize.
  assert (n * x * x0 <= n0 * x0 * x1)%nat.
  rewrite (mult_comm (n0 * x0) x1).
  rewrite mult_assoc.
  apply mult_le_compat; trivial.
  rewrite (mult_comm x1).
  trivial.
  rewrite <- plus_0_r at 1.
  apply plus_le_compat; eauto.
  apply le_0_n.
Qed.

Lemma ratAdd_any_leRat_r : forall r1 r2 r3,
  r1 <= r2 ->
  r1 <= r3 + r2.
  
  intros.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    apply ratAdd_comm.
  }
  apply ratAdd_any_leRat_l; eauto.
Qed.

Lemma ratAdd_eq_impl_leRat_l : forall r1 r2 r3,
  r1 == r2 + r3 ->
  r2 <= r1.
  
  intuition.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply eqRat_symm.
    eapply H.
  }
  apply ratAdd_any_leRat_l.
  apply leRat_refl.
Qed.

Lemma ratAdd_eq_impl_leRat_r : forall r1 r2 r3,
  r1 == r2 + r3 ->
  r3 <= r1.
  
  intuition.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply eqRat_symm.
    eapply H.
  }
  apply ratAdd_any_leRat_r.
  apply leRat_refl.
Qed.

Lemma ratSubtract_leRat_r : forall r1 r2 r3,
  r1 <= r2 ->
  ratSubtract r3 r2 <= ratSubtract r3 r1.
  
  rattac.
  unfold ratSubtract in *.
  rattac.
  unfold posnatMult in *.
  inversion H4; clear H4; subst.
  inversion H3; clear H3; subst.
  arithNormalize.
  assert (n * x3 * x3 * x1 <= n0 * x3 * x3 * x2)%nat.
  rewrite <- mult_comm.
  rewrite <- (mult_comm x2).
  repeat rewrite mult_assoc.
  eapply mult_le_compat; trivial.
  eapply mult_le_compat; trivial.
  rewrite mult_comm.
  rewrite l.
  rewrite mult_comm.
  trivial.
  assert (n3 * x1 * x3 * x2 = n3 * x2 * x3 * x1)%nat.
  do 3 arithSimplify.
  omega.
  
Qed.

Lemma ratSubtract_leRat_l:
  forall r1 r2 r3 : Rat, r1 <= r2 -> ratSubtract r1 r3 <= ratSubtract r2 r3.
  
  rattac.
  unfold ratSubtract in *.
  rattac.
  unfold posnatMult in *.
  inversion H4; clear H4; subst.
  inversion H3; clear H3; subst.
  arithNormalize.
  
  assert (n * x3 * x1 * x3 <= n0 * x3 * x2 * x3)%nat.
  apply mult_le_compat; trivial.
  rewrite <- (mult_comm x1).
  rewrite <- (mult_comm x2).
  repeat rewrite mult_assoc.
  apply mult_le_compat; trivial.
  rewrite mult_comm.
  rewrite l.
  rewrite mult_comm.
  trivial.
  
  assert (n3 * x2 * x1 * x3 = n3 * x1 * x2 * x3)%nat.
  do 3 arithSimplify.
  omega.
Qed.

Lemma ratSubtract_leRat : forall r1 r2 r3 r4,
  r1 <= r2 ->
  r3 <= r4 ->
  ratSubtract r1 r4 <= ratSubtract r2 r3.
  
  intuition.
  eapply leRat_trans.
  eapply ratSubtract_leRat_l; eauto.
  eapply ratSubtract_leRat_r; eauto.
Qed.

Lemma ratSubtract_0 : forall r1 r2,
  r1 <= r2 ->
  ratSubtract r1 r2 == 0.
  
  intuition.
  unfold ratSubtract.
  rattac.
  inversion l; clear l; subst.
  omega.
  rewrite H0.
  unfold posnatToNat in *.
  
  omega.
Qed.

Lemma ratSubtract_partition_leRat : forall r3 r1 r2 d1 d2,
  ratSubtract r1 r3 <= d1 ->
  ratSubtract r3 r2 <= d2 -> 
  ratSubtract r1 r2 <= d1 + d2.
  
  intuition.
  case_eq (bleRat r3 r1); intuition.
  case_eq (bleRat r2 r3); intuition.
  rewrite ratSubtract_partition; eauto.
  rewrite ratAdd_comm.
  eapply ratAdd_leRat_compat;
    intuition.
  eapply bleRat_total in H2.
  rewrite ratAdd_0_r.
  eapply ratAdd_leRat_compat.
  eapply leRat_trans; eauto.
  eapply ratSubtract_leRat;
    intuition.
  eapply rat0_le_all.
  
  apply bleRat_total in H1.
  case_eq (bleRat r2 r3); intuition.
  rewrite ratAdd_0_l.
  eapply ratAdd_leRat_compat.
  eapply rat0_le_all.
  eapply leRat_trans; eauto.
  eapply ratSubtract_leRat;
    intuition.
  
  apply bleRat_total in H2.
  rewrite ratSubtract_0.
  eapply rat0_le_all.
  eapply leRat_trans; eauto.
  
Qed.

Theorem ratTriangleInequality : forall r1 r2 r3,
  (ratDistance r1 r2) <= (ratDistance r1 r3) + (ratDistance r3 r2).

  intuition.
  unfold ratDistance, maxRat, minRat in *.
  case_eq (bleRat r1 r3); intuition.
  case_eq (bleRat r3 r2); intuition.
  assert (bleRat r1 r2 = true).
  eapply leRat_trans; eauto.
  rewrite H1.

  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply ratAdd_comm.
  }
  eapply ratSubtract_partition_leRat; eapply leRat_refl.

  case_eq (bleRat r1 r2); intuition.  
  apply bleRat_total in H0.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply ratAdd_comm.
  }
  eapply ratSubtract_partition_leRat.
  eapply ratSubtract_leRat; eauto.
  intuition.

  apply bleRat_total in H1.
  apply bleRat_total in H0.
  eapply ratSubtract_partition_leRat.
  rewrite ratSubtract_0.
  eapply rat0_le_all.
  eapply leRat_refl.
  eapply ratSubtract_leRat; intuition.

  apply bleRat_total in H.
  case_eq (bleRat r1 r2); intuition.
  assert (bleRat r3 r2 = true).
  eapply leRat_trans; eauto.
  rewrite H1.
  apply ratAdd_any_leRat_r.
  eapply ratAdd_eq_impl_leRat_r.
  eapply ratSubtract_partition; eauto.

  apply bleRat_total in H0.
  case_eq (bleRat r3 r2); intuition.
  apply ratAdd_any_leRat_l.
  eapply ratAdd_eq_impl_leRat_r.
  eapply ratSubtract_partition; eauto.

  apply bleRat_total in H1.
  eapply eqRat_impl_leRat.
  rewrite ratAdd_comm.
  eapply ratSubtract_partition; eauto.
Qed.

Theorem ratMult_1_r : forall r,
  r * 1 == r.

  intuition.
  rewrite ratMult_comm.
  apply ratMult_1_l.
  
Qed.

Lemma minus_le : forall n1 n2 n3,
    (n1 <= n3 ->
     n1 - n2 <= n3)%nat.
  
  intuition.
Qed.

Theorem ratSubtract_le : forall r1 r2 d,
  r1 <= d ->
  ratSubtract r1 r2 <= d.

  intuition.

  unfold ratSubtract.
  rattac.
  arithNormalize.

  apply minus_le.
  rewrite <- (mult_assoc n).
  rewrite (mult_comm x0).
  rewrite mult_assoc.
  apply mult_le_compat; trivial.

Qed.


Theorem ratDistance_le_trans : forall r1 r2 r3 d1 d2,
  ratDistance r1 r2 <= d1 ->
  ratDistance r2 r3 <= d2 ->
  ratDistance r1 r3 <= d1 + d2.

  intuition.

  eapply leRat_trans.
  eapply ratTriangleInequality.
  eapply ratAdd_leRat_compat; eauto.
Qed.


Theorem ratDistance_le : forall r1 r2 d,
  r1 <= d ->
  r2 <= d ->
  (ratDistance r1 r2) <= d.

  intuition.
  unfold ratDistance, maxRat, minRat.
  case_eq (bleRat r1 r2); intuition;
  apply ratSubtract_le; eauto.
Qed.

Lemma ratSubtract_eqRat_compat : forall r1 r2 r3 r4,
  r1 == r3 ->
  r2 == r4 ->
  ratSubtract r1 r2 == ratSubtract r3 r4.

  intuition.
  unfold ratSubtract.
  rattac.
  inversion e0; clear e0; subst.
  inversion e; clear e; subst.
  arithNormalize.
  apply minus_eq_compat.
  arithSimplify.
  rewrite <- (mult_assoc n1).
  rewrite (mult_comm x2).
  rewrite mult_assoc.
  arithSimplify.
  trivial.

  rewrite <- (mult_assoc (n2 * x1)).
  rewrite (mult_comm x).
  rewrite mult_assoc.
  arithSimplify.
  rewrite <- (mult_assoc n2).
  rewrite (mult_comm x1 x0).
  rewrite mult_assoc.
  arithSimplify.
  rewrite mult_comm.
  trivial.
Qed.

Add Parametric Morphism : ratSubtract
  with signature (eqRat ==> eqRat ==> eqRat)
  as ratSubtract_eqRat_mor.

  intuition.
  eapply ratSubtract_eqRat_compat; trivial.
Qed.

Theorem leRat_antisymm : forall r1 r2,
  r1 <= r2 ->
  r2 <= r1 ->
  r1 == r2.

  rattac.
Qed.

Lemma maxRat_eqRat_compat : forall r1 r2 r3 r4,
  r1 == r3 ->
  r2 == r4 ->
  maxRat r1 r2 == maxRat r3 r4.

  intuition.
  unfold maxRat.
  case_eq (bleRat r1 r2); intuition;
  case_eq (bleRat r3 r4); intuition.
  apply bleRat_total in H2.
  eapply leRat_impl_eqRat;
  eauto using leRat_trans, eqRat_impl_leRat, eqRat_symm.
  
  apply bleRat_total in H1.
  eapply leRat_impl_eqRat;
  eauto using leRat_trans, eqRat_impl_leRat, eqRat_symm.
Qed.

Add Parametric Morphism : maxRat
  with signature (eqRat ==> eqRat ==> eqRat)
  as maxRat_eqRat_mor.

  intuition.
  eapply maxRat_eqRat_compat; trivial.
Qed.


Lemma minRat_eqRat_compat : forall r1 r2 r3 r4,
  r1 == r3 ->
  r2 == r4 ->
  minRat r1 r2 == minRat r3 r4.

  intuition.
  unfold minRat.
  case_eq (bleRat r1 r2); intuition;
  case_eq (bleRat r3 r4); intuition.
  apply bleRat_total in H2.
  eapply leRat_impl_eqRat;
  eauto using leRat_trans, eqRat_impl_leRat, eqRat_symm.
  
  apply bleRat_total in H1.
  eapply leRat_impl_eqRat;
  eauto using leRat_trans, eqRat_impl_leRat, eqRat_symm.
Qed.

Add Parametric Morphism : minRat
  with signature (eqRat ==> eqRat ==> eqRat)
  as minRat_eqRat_mor.

  intuition.
  eapply minRat_eqRat_compat; trivial.
Qed.

Theorem ratDistance_eqRat_compat : forall r1 r2 r3 r4,
  r1 == r3 ->
  r2 == r4 ->
  ratDistance r1 r2 == ratDistance r3 r4.

  intuition.
  unfold ratDistance.
  eauto using ratSubtract_eqRat_compat, maxRat_eqRat_compat, minRat_eqRat_compat.
Qed.

Add Parametric Morphism : ratDistance
  with signature (eqRat ==> eqRat ==> eqRat)
  as ratDistance_eqRat_mor.

  intuition.
  eapply ratDistance_eqRat_compat; trivial.
Qed.

Lemma ratSubtract_add_same_r : forall r1 r2 r3,
  r1 <= r3 ->
  ratSubtract (r3 + r2) (r1 + r2) == ratSubtract r3 r1.
  
  intuition.
  unfold ratSubtract.
  rattac.
  arithNormalize.
  rewrite (plus_comm (n2 * x0 * x1 * x0 * x1 * x)).
  rewrite NPeano.Nat.sub_add_distr.
  apply minus_eq_compat.
  rewrite <- NPeano.Nat.add_sub_assoc.
  rewrite minus_diag_eq.
  rewrite plus_0_r.
  do 5 arithSimplify.
  do 5 arithSimplify.
  eapply le_eq.
  do 5 arithSimplify.
  do 5 arithSimplify.
Qed.

Lemma ratSubtract_add_same_l : forall r1 r2 r3,
  r1 <= r3 ->
  ratSubtract (r2 + r3) (r2 + r1) == ratSubtract r3 r1.
  
  intuition.
  unfold ratSubtract.
  rattac.
  arithNormalize.
  rewrite NPeano.Nat.sub_add_distr.
  apply minus_eq_compat.
  rewrite plus_comm.
  rewrite <- NPeano.Nat.add_sub_assoc.
  rewrite minus_diag_eq.
  rewrite plus_0_r.
  do 5 arithSimplify.
  do 5 arithSimplify.
  eapply le_eq.
  do 5 arithSimplify.
  do 5 arithSimplify.
Qed.

Lemma minus_plus_assoc : forall n1 n2 n3,
  (n3 <= n2 ->
    (n1 + n2) - n3 = n1 + (n2 - n3))%nat.
  
  intuition.
Qed.

Lemma ratSubtract_ratAdd_assoc: forall r1 r2 r3,
  r3 <= r2 ->
  ratSubtract (r1 + r2) r3 == r1 + (ratSubtract r2 r3).
  
  intuition.
  unfold ratSubtract.
  rattac.
  arithNormalize.
  rewrite  minus_plus_assoc.
  f_equal.
  f_equal.
  do 5 arithSimplify.
  do 5 arithSimplify.
  do 3 (eapply mult_le_compat; trivial).
  repeat rewrite <- mult_assoc.
  repeat rewrite (mult_comm x).
  repeat rewrite mult_assoc.
  apply mult_le_compat; trivial.
Qed.

Lemma ratAdd_add_same_r : forall r1 r2 r3,
  r1 + r2 == r3 + r2 ->
  r1 == r3.
  
  intuition.
  assert (ratSubtract (r1 + r2) r2 == ratSubtract (r3 + r2) r2).
  eapply ratSubtract_eqRat_compat; intuition.
  
  rewrite ratSubtract_ratAdd_assoc in H0.
  setoid_rewrite ratAdd_0_r.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  eapply eqRat_refl.
  eapply eqRat_symm.
  apply (@ratSubtract_0 r2 r2).
  eapply leRat_refl.
  rewrite H0.
  rewrite ratSubtract_ratAdd_assoc.
  eapply ratAdd_eqRat_compat.
  intuition.
  apply ratSubtract_0.
  eapply leRat_refl.
  apply leRat_refl.
  apply leRat_refl.
Qed.

Lemma ratAdd_add_same_l : forall r1 r2 r3,
  r2 + r1 == r2 + r3 ->
  r1 == r3.

  intuition.
  eapply ratAdd_add_same_r.
  eapply eqRat_trans.
  apply ratAdd_comm.
  rewrite H.
  apply ratAdd_comm.
Qed.

Lemma ratDistance_add_same_r : forall r1 r2 r3,
  (ratDistance (r1 + r2) (r3 + r2)) == (ratDistance r1 r3).
  
  intuition.
  unfold ratDistance, maxRat, minRat.
  case_eq (bleRat r1 r3); intuition.
  assert (r1 + r2 <= r3 + r2).
  eapply ratAdd_leRat_compat; trivial.
  eapply leRat_refl.
  rewrite H0.
  
  apply ratSubtract_add_same_r; eauto.
  
  apply bleRat_total in H.
  assert (r3 + r2 <= r1 + r2).
  eapply ratAdd_leRat_compat; trivial.
  apply leRat_refl.
  
  case_eq (bleRat (r1 + r2) (r3 + r2)); intuition.
  assert (r1 + r2 == r3 + r2).
  eapply leRat_antisymm; eauto.
  repeat rewrite ratSubtract_0.
  intuition.
  eapply eqRat_impl_leRat.
  
  eapply ratAdd_add_same_r.
  eauto.
  eapply eqRat_impl_leRat.
  eapply eqRat_symm.
  trivial.
  
  apply ratSubtract_add_same_r; eauto.
Qed.

Lemma ratDistance_add_same_l : forall r1 r2 r3,
  (ratDistance (r2 + r3) (r2 + r1)) == (ratDistance r3 r1).
  
  intuition.
  unfold ratDistance, maxRat, minRat.
  case_eq (bleRat r3 r1); intuition.
  assert (r2 + r3 <= r2 + r1).
  eapply ratAdd_leRat_compat; trivial.
  eapply leRat_refl.
  rewrite H0.
  
  apply ratSubtract_add_same_l; eauto.
  
  apply bleRat_total in H.
  assert (r2 + r1 <= r2 + r3).
  eapply ratAdd_leRat_compat; trivial.
  apply leRat_refl.

  case_eq (bleRat (r2 + r3) (r2 + r1)); intuition.
  assert (r2 + r3 == r2 + r1).
  eapply leRat_antisymm; eauto.
  repeat rewrite ratSubtract_0.
  intuition.
  eapply eqRat_impl_leRat.

  eapply ratAdd_add_same_l.
  eauto.
  eapply eqRat_impl_leRat.
  eapply eqRat_symm.
  trivial.
  
  apply ratSubtract_add_same_l; eauto.

Qed.

Theorem rat_distance_of_sum : forall r1 r2 r3 r4,
  ratDistance (r1 + r2) (r3 + r4) <= (ratDistance r1 r3) + (ratDistance r2 r4).

  intuition.
  eapply leRat_trans.
  eapply (ratTriangleInequality _ _ (r3 + r2)).
  eapply ratAdd_leRat_compat.
  
  eapply eqRat_impl_leRat.
  eapply ratDistance_add_same_r.

  eapply eqRat_impl_leRat.
  eapply ratDistance_add_same_l.
  
Qed.

Theorem ratMult_distrib : forall r1 r2 r3,
  r1 * (r2 + r3) == r1 * r2 + r1 * r3.

  rattac.
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  inversion H; clear H; subst.
  arithNormalize.
  f_equal.
  do 5 arithSimplify.
  do 5 arithSimplify.
Qed.


Theorem num_dem_same_rat1 : forall n d,
  n = posnatToNat d ->
  RatIntro n  d == rat1.

  rattac.
  inversion H0; clear H0; subst.
  omega.
Qed.

Lemma ratAdd_num : forall n1 n2 d,
  RatIntro (n1 + n2) d == (ratAdd (RatIntro n1 d) (RatIntro n2 d)).
  
  rattac.
  arithNormalize.
  trivial.
Qed.

Lemma ratMult_denom : forall n d1 d2,
  (RatIntro n (posnatMult d1 d2)) == (ratMult (RatIntro 1 d1) (RatIntro n d2)).

  rattac.
Qed.

Lemma ratMult_num_den : forall n1 n2 d1 d2,
  (RatIntro (n1 * n2)%nat (posnatMult d1 d2)) == (RatIntro n1 d1) * (RatIntro n2 d2).
  
  intuition.
  
  unfold ratMult, natToPosnat, posnatMult.
  eapply eqRat_refl.
Qed.

Theorem ratAdd_den_same : forall n1 n2 d,
  RatIntro (n1 + n2)%nat d == (RatIntro n1 d) + (RatIntro n2 d).
  
  rattac.
  arithNormalize.
  arithSimplify.
Qed.

Lemma rat_mult_den : forall n d1 d2,
  (RatIntro n (posnatMult d1 d2)) == (RatIntro 1 d1) * (RatIntro n d2).
  
  intuition.
  assert (n = 1 * n)%nat.
  omega.
  rewrite H at 1.
  apply ratMult_num_den; omega.
Qed.

Lemma ratOneHalf_add: 
  1 / 2 + 1 / 2 == 1.
  
  unfold ratAdd.
  simpl.
  unfold posnatMult.
  simpl.
  apply (@num_dem_same_rat1 4 _).
  simpl.
  trivial.
Qed.


Theorem ratS_num : forall n,
  (S n) / (S O) == 1 + (n / (S O)).

  rattac.
  unfold natToPosnat in *.
  inversion H0; clear H0; subst.
  repeat rewrite mult_1_r.
  inversion H; clear H; subst.
  trivial.
Qed.

Theorem ratDistance_comm : forall r1 r2,
  eqRat (ratDistance r1 r2) (ratDistance r2 r1).

  intuition.
  unfold ratDistance, maxRat, minRat.
  case_eq (bleRat r1 r2); case_eq (bleRat r2 r1); intuition.
  apply ratSubtract_eqRat_compat;
  eapply leRat_antisymm; eauto.

  apply bleRat_total in H.
  apply bleRat_total in H0.
  apply ratSubtract_eqRat_compat;
  eapply leRat_antisymm; eauto.
Qed.

Theorem ratMult_distrib_r : forall r1 r2 r3,
  ratMult (ratAdd r2 r3) r1  == ratAdd (ratMult r2 r1) (ratMult r3 r1).
  
  intuition.
  rewrite ratMult_comm.
  rewrite ratMult_distrib.
  eapply ratAdd_eqRat_compat; eapply ratMult_comm.
Qed.

Lemma ratSubtract_ratAdd_inverse : forall r1 r2,
  ratSubtract (r1 + r2) r1 == r2.
  
  intuition.
  unfold ratSubtract.
  rattac.
  arithNormalize.
  rewrite <- (mult_assoc (n1 * x)).
  rewrite (mult_comm x x0).
  rewrite mult_assoc.
  remember (n1 * x * x0 * x)%nat as a.
  repeat rewrite <- (mult_assoc n0).
  rewrite (mult_comm x).
  omega.
Qed.

Lemma ratSubtract_ratAdd_inverse_2 : forall r1 r2,
  r2 <= r1 ->
  r2 + ratSubtract r1 r2 == r1.
  
  intuition.
  apply eqRat_symm.
  eapply eqRat_trans.
  2:{
    apply ratSubtract_ratAdd_assoc.
    trivial.
  }
  apply eqRat_symm.
  apply ratSubtract_ratAdd_inverse.
Qed.

Lemma leRat_difference_exists : forall r1 r2,
  r2 <= r1 ->
  exists r3, r1 == r2 + r3.
  
  intuition.
  exists (ratSubtract r1 r2).
  apply eqRat_symm.
  apply ratSubtract_ratAdd_inverse_2.
  trivial.
Qed.

Lemma ratSubtract_ratMult_le : forall r1 r2 r3 r4,
  r1 <= r2 ->
  r3 <= r4 ->
  ratSubtract (r2 * r4) (r1 * r3) == (ratSubtract r2 r1) * r3 + (ratSubtract r4 r3) * r1 + (ratSubtract r2 r1) * (ratSubtract r4 r3).
  
  intuition.
  destruct (leRat_difference_exists H).
  destruct (leRat_difference_exists H0).
  eapply eqRat_trans.
  apply ratSubtract_eqRat_compat.
  eapply eqRat_trans.
  apply ratMult_eqRat_compat.
  apply H1.
  apply H2.
  eapply eqRat_trans.
  apply ratMult_distrib_r.
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  apply ratMult_comm.
  apply ratMult_comm.
  apply ratAdd_eqRat_compat.
  apply ratMult_distrib_r.
  apply ratMult_distrib_r.
  apply eqRat_refl.
  eapply eqRat_trans.
  eapply ratSubtract_eqRat_compat.
  apply ratAdd_assoc.
  apply ratMult_comm.
  eapply eqRat_trans.
  apply ratSubtract_ratAdd_inverse.
  rewrite <- ratAdd_assoc.
  apply ratAdd_eqRat_compat.
  rewrite ratAdd_comm.
  apply ratAdd_eqRat_compat.
  rewrite ratMult_comm.
  apply ratMult_eqRat_compat.
  eapply eqRat_symm.
  eapply eqRat_trans.
  eapply ratSubtract_eqRat_compat.
  apply H1.
  apply eqRat_refl.
  apply ratSubtract_ratAdd_inverse.
  intuition.
  apply ratMult_eqRat_compat.
  apply eqRat_symm.
  eapply eqRat_trans.
  apply ratSubtract_eqRat_compat.
  apply H2.
  apply eqRat_refl.
  apply ratSubtract_ratAdd_inverse.
  intuition.

  rewrite ratMult_comm.
  apply ratMult_eqRat_compat.
  apply eqRat_symm.
  eapply eqRat_trans.
  apply ratSubtract_eqRat_compat.
  apply H1.
  apply eqRat_refl.
  apply ratSubtract_ratAdd_inverse.
  
  apply eqRat_symm.
  eapply eqRat_trans.
  apply ratSubtract_eqRat_compat.
  apply H2.
  apply eqRat_refl.
  apply ratSubtract_ratAdd_inverse.

Qed.



Lemma ratSubtract_eq_r : forall r1 r2 r3,
  r2 <= r1 ->
  r3 <= r1 ->
  (ratSubtract r1 r2) == (ratSubtract r1 r3) ->
  r2 == r3.
  
  rattac.
  unfold ratSubtract in *.
  rattac.
  match goal with
    H: (_ * (?x*_) = _ * (?x*_))%nat |- _
    => eapply (@mult_same_l (x * x)); nia
  end.
Qed.

Lemma ratDistance_le_max : forall r1 r2 r3 v,
  r1 <= r2 ->
  r2 <= r3 ->
  (ratDistance r2 v) <= (maxRat (ratDistance r1 v) (ratDistance r3 v)).
  
  intuition.
  unfold ratDistance, maxRat, minRat.
  case_eq (bleRat r3 v); intuition.
  assert (r2 <= v).
  rewrite H0.
  eauto.
  rewrite H2.
  assert (r1 <= v).
  rewrite H.
  eauto.
  rewrite H3.
  
  assert ((ratSubtract v r3) <= (ratSubtract v r1)).
  eapply ratSubtract_leRat_r.
  eauto using leRat_trans.
  
  case_eq (bleRat (ratSubtract v r1) (ratSubtract v r3)); intuition.
  assert (r1 == r3).
  assert ((ratSubtract v r1) == (ratSubtract v r3)).
  eapply leRat_antisymm; eauto.
  
  eapply ratSubtract_eq_r; eauto.
  
  eapply ratSubtract_leRat_r.
  rewrite <- H6.
  trivial.
  
  eapply ratSubtract_leRat_r.
  trivial.
  
  eapply bleRat_total in H1.
  case_eq (bleRat r2 v); intuition.
  assert (r1 <= v).
  eauto using leRat_trans.
  rewrite H3.
  case_eq (bleRat (ratSubtract v r1) (ratSubtract r3 v)); intuition.
  eapply leRat_trans.
  eapply ratSubtract_leRat_r.
  eapply H.
  eapply H4.
      
  eapply ratSubtract_leRat_r; trivial.

  apply bleRat_total in H2.
  case_eq (bleRat r1 v); intuition.
  case_eq (bleRat (ratSubtract v r1) (ratSubtract r3 v)); intuition.
  
  assert (r1 <= v).
  eauto using leRat_trans.
  eapply ratSubtract_leRat_l; trivial.
  
  apply bleRat_total in H4.
  eapply leRat_trans.
  eapply ratSubtract_leRat_l.
  eapply H0.
  trivial.
  
  assert (bleRat (ratSubtract r1 v) (ratSubtract r3 v) = true).
  eapply ratSubtract_leRat_l.
  eauto using leRat_trans.
  rewrite H4.
  
  eapply ratSubtract_leRat_l; trivial.
Qed.

Lemma maxRat_leRat_same : forall r1 r2 r3,
  r1 <= r3 ->
  r2 <= r3 ->
  maxRat r1 r2 <= r3.
  
  intuition.
  unfold maxRat in *.
  case_eq (bleRat r1 r2); intuition.

Qed.

Lemma ratMult_3_ratAdd : forall r,
  (3 / 1) * r == r + r + r.
  
  rattac.
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  simpl.
  arithNormalize.
  repeat rewrite mult_0_r.
  repeat rewrite plus_0_r.
  trivial.
Qed.

Lemma ratMult_small_le : forall r1 r2,
  r2 <= 1 ->
  r1 * r2 <= r1.
  
  rattac.
  inversion H0; clear H0; subst.
  rewrite mult_1_r in l.
  rewrite mult_1_l in l.
  rewrite mult_assoc.
  rewrite <- (mult_assoc n2).
  rewrite (mult_comm n).
  rewrite mult_assoc.
  apply mult_le_compat;
    auto.
  
Qed.

Lemma ratDistance_ratMult_le : forall r1 r2 r3 r4 d,
  (ratDistance r1 r3) <= d ->
  (ratDistance r2 r4) <= d ->
  r1 <= 1 ->
  r2 <= 1 ->
  r3 <= 1 ->
  r4 <= 1 ->
  (ratDistance (r1 * r2) (r3 * r4)) <= (3 / 1) * d.
  
  intuition.
  
  unfold ratDistance, maxRat, minRat in *.
  case_eq (bleRat r1 r3); intuition;
    rewrite H5 in H.
  case_eq (bleRat r2 r4); intuition;
    rewrite H6 in H0.
  
  assert (r1 * r2 <= r3 * r4).
  apply ratMult_leRat_compat; eauto.
  rewrite H7.
  
  rewrite ratSubtract_ratMult_le; eauto.
  repeat rewrite ratMult_small_le.
  rewrite H.
  rewrite H0.
  eapply eqRat_impl_leRat.
  symmetry.
  eapply ratMult_3_ratAdd.
  eapply ratSubtract_le.
  trivial.
  trivial.
  trivial.
  
  apply bleRat_total in H6.
  case_eq (bleRat (r1 * r2) (r3 * r4)); intuition.
  
  rewrite ratSubtract_leRat.
  2:{
    eapply ratMult_leRat_compat.
    eapply leRat_refl.
    eapply H6.
  }
  2:{
    eapply ratMult_leRat_compat.
    eapply leRat_refl.
    eapply H6.
  }
  
  rewrite ratSubtract_ratMult_le; eauto.
  repeat rewrite ratMult_small_le.
  rewrite H.
  rewrite H0.
  eapply eqRat_impl_leRat.
  symmetry.
  eapply ratMult_3_ratAdd.
  eapply ratSubtract_le.
  trivial.
  trivial.
  trivial.
  
  apply bleRat_total in H7.
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  eapply ratMult_leRat_compat.
  eapply H5.
  eapply leRat_refl.
  eapply ratMult_leRat_compat.
  eapply H5.
  eapply leRat_refl.
  rewrite ratSubtract_ratMult_le; eauto.
  repeat rewrite ratMult_small_le.
  rewrite H.
  rewrite H0.
  eapply eqRat_impl_leRat.
  symmetry.
  eapply ratMult_3_ratAdd.
  eapply ratSubtract_le.
  trivial.
  trivial.
  trivial.
  
  apply bleRat_total in H5.
  case_eq (bleRat r2 r4); intuition.
  rewrite H6 in H0.
  case_eq (bleRat (r1 * r2) (r3 * r4)); intuition.
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  eapply ratMult_leRat_compat.
  eapply H5.
  eapply leRat_refl.
  eapply ratMult_leRat_compat.
  eapply H5.
  eapply leRat_refl.
  rewrite ratSubtract_ratMult_le; eauto.
  repeat rewrite ratMult_small_le.
  rewrite H.
  rewrite H0.
  eapply eqRat_impl_leRat.
  symmetry.
  eapply ratMult_3_ratAdd.
  eapply ratSubtract_le.
  trivial.
  trivial.
  trivial.
  
  apply bleRat_total in H7.
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  eapply ratMult_leRat_compat.
  eapply leRat_refl.
  eapply H6.
  eapply ratMult_leRat_compat.
  eapply leRat_refl.
  eapply H6.
  rewrite ratSubtract_ratMult_le; eauto.
  repeat rewrite ratMult_small_le.
  rewrite H.
  rewrite H0.
  eapply eqRat_impl_leRat.
  symmetry.
  eapply ratMult_3_ratAdd.
  eapply ratSubtract_le.
  trivial.
  trivial.
  trivial.
  
  rewrite H6 in H0.
  
  apply bleRat_total in H6.
  assert (r3 * r4 <= r1 * r2).
  eapply ratMult_leRat_compat; eauto.
  case_eq (bleRat (r1 * r2) (r3 * r4)); intuition.
  
  rewrite ratSubtract_0; eauto.
  eapply rat0_le_all.
  apply bleRat_total in H8.
  
  rewrite ratSubtract_ratMult_le; eauto.
  repeat rewrite ratMult_small_le.
  rewrite H.
  rewrite H0.
  eapply eqRat_impl_leRat.
  symmetry.
  eapply ratMult_3_ratAdd.
  eapply ratSubtract_le.
  trivial.
  trivial.
  trivial.
  
Qed.

Lemma ratAdd_any_le : forall r1 r2 r3,
  r1 + r2 <= r3 ->
  r1 <= r3.
  
  intuition.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  apply ratAdd_0_r.
  eapply leRat_trans.
  eapply ratAdd_leRat_compat.
  apply leRat_refl.
  apply rat0_le_all.
  eauto.
Qed.

Lemma posnatMult_1_r : forall p,
  posnatToNat (posnatMult p (pos 1)) = posnatToNat p.
  
  intuition.
  unfold posnatMult.
  destruct p.
  remember (pos 1) as p2.
  destruct p2.
  unfold posnatToNat.
  inversion Heqp2; subst.
  apply mult_1_r.
  
Qed.

Lemma rat_num_nz : forall n d,
  n > 0 ->
  RatIntro n d == 0 ->
  False.
  
  rattac.
  unfold posnatToNat, natToPosnat in *.
  destruct d.
  simpl in *.
  omega.
Qed.


Lemma ratMult_inverse : forall r1 r2 (p1 p2 : posnat),
  r1 == r2 * (RatIntro p1 p2) ->
  r1 * (RatIntro p2 p1) == r2.
  
  intuition.
  rewrite H.
  rewrite <- (ratMult_1_r r2) at 2.
  rewrite ratMult_assoc.
  eapply ratMult_eqRat_compat.
  intuition.
  rewrite <- ratMult_num_den.
  eapply num_dem_same_rat1.
  rattac.
Qed.

Lemma ratMult_inverse_nat : forall r1 r2 n d (nzn : nz n), 
  r1 == r2 * (RatIntro n d) ->
  r1 * (RatIntro d (natToPosnat nzn)) == r2.
  
  intuition.
  eapply ratMult_inverse.
  rewrite H.
  eapply ratMult_eqRat_compat.
  intuition.
  eapply eqRat_terms; eauto.
Qed.

Lemma ratMult_same_r_inv : forall r1 r2 r3,
  r1 * r2 == r3 * r2 ->
  ~ r2 == 0 ->
  r1 == r3.
  
  intuition.
  unfold ratMult in *.
  destruct r1.
  destruct r2.
  destruct r3.
  unfold eqRat, beqRat in *.
  simpl in *.
  unfold posnatMult, posnatToNat, natToPosnat in *.
  destruct p1.
  destruct p0.
  destruct p.
  destruct (eq_nat_dec (n * n0 * (x * x0)) (n1 * n0 * (x1 * x0))); try congruence.
  destruct (eq_nat_dec (n * x) (n1 * x1)).
  trivial.
  exfalso.
  eapply n2.
  clear n2.
  arithNormalize.
  rewrite <- (mult_assoc n) in e.
  rewrite (mult_comm n0) in e.
  arithNormalize.
  rewrite <- mult_assoc in e.
  rewrite <- (mult_assoc n1) in e.
  rewrite <- (mult_comm x1) in e.
  rewrite (mult_assoc n1) in e.
  rewrite <- (mult_assoc (n1 * x1)) in e.
  eapply mult_same_r.
  2:{
    eapply e.
  }
  rewrite mult_0_r in H0.
  rewrite plus_0_l in H0.
  destruct (eq_nat_dec n0 0); intuition.
  assert (~n0 * x0 = O)%nat.
  intuition.
  eapply mult_is_O in H1.
  intuition.
  remember (n0 * x0)%nat as a.
  omega.
Qed.

Lemma rat_le_1 : forall n (d : posnat),
  (n <= d)%nat -> (RatIntro n d) <= 1.
  
  rattac.
  inversion H1; clear H1; subst.
  rewrite mult_1_r.
  rewrite mult_1_l.
  trivial.
Qed.

Lemma rat_remove_common_factor : forall (n num : nat)(nzn : nz n) den,
  RatIntro (n * num) (posnatMult (natToPosnat nzn) den) == RatIntro num den.
  
  rattac.
  inversion H; clear H; subst.
  arithNormalize.
  do 2 arithSimplify.
Qed.

Lemma ratMult_2 : forall r,
  r + r == r * (2/1).
  
  rattac.
  inversion H; clear H; subst.
  arithNormalize.
  rewrite mult_0_r.
  rewrite plus_0_r.
  f_equal.
  f_equal.
  rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  rewrite mult_comm.
  simpl.
  trivial.
Qed.


(* ratInverse only works correctly when the number is positive *)
Definition ratInverse (r : Rat) :=
  match r with
    | RatIntro n d =>
      match n with
        | O => RatIntro d (pos (S O))
        | S n' => RatIntro d (pos (S n'))
      end
  end.

Lemma ratInverse_prod_1 : forall r,
  ~ r == 0 ->
  (ratInverse r) * r == 1.
  
  intuition.
  unfold ratInverse.
  destruct r.
  destruct n.
  
  exfalso.
  eapply H.
  eapply rat_num_0.
  
  rewrite <- ratMult_num_den.
  eapply num_dem_same_rat1.
  unfold posnatMult, natToPosnat, posnatToNat.
  destruct p.
  apply mult_comm.
Qed.

Fixpoint expRat r n :=
  match n with
    | O => rat1 
    | S n' => r * (expRat r n')
  end.

Lemma ratInverse_nz : forall (r : Rat),
  ratInverse r == 0 ->
  False.

  intuition.
  unfold ratInverse in *.
  rattac.
  destruct n0.
  unfold posnatToNat, natToPosnat in *.
  destruct p.
  destruct p0.
  inversion H0; clear H0; subst.
  rewrite mult_1_r in e.
  rewrite mult_1_r in e.
  omega.

  unfold posnatToNat, natToPosnat in *.
  destruct p.
  destruct p0.
  inversion H0; clear H0; subst.
  rewrite mult_1_r in e.
  rewrite mult_0_l in e.
  omega.  

Qed.

Lemma ratInverse_1_swap : forall r,
  ~ r == 0 ->
  r <= 1 ->
  1 <= ratInverse r.
  
  intuition.
  unfold ratInverse.
  destruct r.
  destruct n.
  exfalso.
  eapply H.
  eapply rat_num_0.
  
  rattac.
  inversion H1; clear H1; subst.
  omega.
  
Qed.

Lemma ratInverse_1 : 
  ratInverse 1 == 1.
  
  unfold ratInverse.
  case_eq rat1; intuition.
  inversion H; clear H; subst.
  eapply eqRat_terms;
    trivial.
  
Qed.

Lemma ratInverse_leRat : forall r1 r2,
  ~ r2 == 0 ->
  r2 <= r1 ->
  ratInverse r1 <= ratInverse r2.
  
  intuition.
  unfold ratInverse.
  rattac.
  destruct n0.
  exfalso.
  eapply H.
  eapply rat_num_0.
  destruct n.
  exfalso.
  rewrite mult_0_l in l.
  simpl in *.
  remember (n0 * x1)%nat as a.
  nia.
  
  inversion H3; clear H3; subst.
  inversion H2; clear H2; subst.
  nia.
Qed.

Lemma ratAdd_not_leRat : forall r1 r2,
  r1 + r2 <= r1 ->
  (~r2 == 0) ->
  False.
  
  rattac.
  eapply H0.
  unfold posnatMult, natToPosnat, posnatToNat in *.
  destruct p1.
  destruct p0.
  rewrite mult_plus_distr_r in l.
  rewrite <- mult_assoc in l.
  rewrite (mult_comm x) in l.
  assert ((n1 * x0 * x0) = O)%nat.
  remember (n0 * (x0 * x))%nat as a.
  remember (n1 * x0 * x0)%nat as b.
  omega.
  apply mult_is_O in H1;
    intuition; 
      subst.
  apply mult_is_O in H2;
    intuition;
      subst.
  apply rat_num_0.
  omega.
  omega.
Qed.


(* relational versions of arithmetic operations. *)
Definition ratSubtract_rel (r1 r2 : Rat -> Prop) d :=
  forall r1' r2', r1 r1' -> r2 r2' -> d == ratSubtract r1' r2'.
  
Definition ratAdd_rel(r1 r2 : Rat -> Prop) r :=
  forall r1' r2', r1 r1' -> r2 r2' -> r == r1' + r2'.

Definition ratMult_rel (r1 r2 : Rat -> Prop)(r : Rat) :=
  forall r1' r2', r1 r1' -> r2 r2' -> r == r1' * r2'.

Definition expRat_rel (r1 : Rat -> Prop) n r :=
  forall r1', r1 r1' -> r == expRat r1' n.

Definition ratInverse_rel (r : Rat -> Prop) v :=
  forall r',
    r r' -> v == ratInverse r'.

Lemma eqRat_flip : forall (p1 p2 p3 p4 : posnat),
  RatIntro p1 p2 == RatIntro p3 p4 ->
  RatIntro p2 p1 == RatIntro p4 p3.

  rattac.
  rewrite mult_comm.
  rewrite <- e.
  apply mult_comm.

Qed.

Lemma ratInverse_eqRat_compat : forall r1 r2,
  ~ r1 == 0 ->
  r1 == r2 ->
  ratInverse r1 == ratInverse r2.

  intuition.
  unfold ratInverse.
  destruct r1. destruct r2.
  destruct n.
  exfalso.
  eapply H.
  eapply rat_num_0.
  destruct n0.
  exfalso.
  
  eapply rat_num_nz.
  2:{
    rewrite rat_num_0 in H0.
    eauto.
  }
  omega.

  eapply eqRat_flip.
  eapply H0.

Qed.

Lemma ratSubtract_ratAdd_distr : forall r1 r2 r3,
  ratSubtract r1 (r2 + r3) == ratSubtract (ratSubtract r1 r2) r3.
  
  intuition.
  unfold ratSubtract, ratAdd.
  rattac.
  arithNormalize.
  rewrite NPeano.Nat.sub_add_distr.
  f_equal.
  f_equal.
  do 5 arithSimplify.
  do 5 arithSimplify.
Qed.

Lemma ratSubtract_ratAdd_assoc_1 : forall r1 r2 r3,
  r3 <= r2 ->
  ratSubtract (r1 + r2) r3 == r1 + (ratSubtract r2 r3).
  
  intuition.
  unfold ratSubtract, ratAdd.
  rattac.
  arithNormalize.
  rewrite minus_plus_assoc.
  f_equal.
  f_equal.
  do 5 arithSimplify.
  do 5 arithSimplify.
  unfold natToPosnat, posnatToNat in *.
  eapply mult_le_compat; trivial.
  eapply mult_le_compat; trivial.
  eapply mult_le_compat; trivial.
  
  rewrite <- (mult_assoc).
  rewrite (mult_comm x).
  rewrite mult_assoc.
  rewrite <- (mult_assoc n3).
  rewrite (mult_comm x).
  rewrite mult_assoc.
  eapply mult_le_compat; trivial.
  
Qed.


Lemma eqRat_ratMult_same_r : forall r1 r2 r3,
  ~r1 == 0 ->
  r2 * r1 == r3 * r1 ->
  r2 == r3.

  intuition.
  destruct r1.
  destruct r2.
  destruct r3.
  unfold ratMult in *.
  unfold eqRat in *.
  unfold beqRat in *.
  unfold ratCD in *.
  case_eq (0); intuition.
  rewrite H1 in H.
  destruct (eq_nat_dec (n * p2) (n2 * p)).
  intuition.
  destruct (eq_nat_dec (n0 * n * (posnatMult p1 p)) (n1 * n * (posnatMult p0 p))); intuition.
  inversion H1; clear H1; subst.
  unfold posnatMult, natToPosnat, posnatToNat in *.
  destruct p1.
  destruct p.
  destruct p0.
  destruct (eq_nat_dec (n0 * x) (n1 * x1)); trivial.
  exfalso.
  eapply n2.
  eapply (@mult_same_l (n * x0)).
  eapply mult_gt_0.
  rewrite mult_1_r in n3.
  rewrite mult_0_l in n3.
  omega.
  trivial.
  rewrite (mult_comm).
  rewrite mult_assoc.
  rewrite <- (mult_assoc n0).
  rewrite (mult_comm x).
  arithNormalize.
  rewrite e.
  do 3 arithSimplify.
Qed.

Lemma expRat_le_1 : forall n x,
  x <= 1 ->
  expRat x n <= 1.
  
  induction n; intuition; simpl in *.
  intuition.
  
  eapply leRat_trans.
  eapply ratMult_leRat_compat.
  eapply H.
  eapply IHn.
  trivial.
  rewrite ratMult_1_l.
  intuition.
  
Qed.

Lemma expRat_le : forall n1 n2 x,
  x <= 1 ->
  n2 >= n1 ->
  expRat x n2 <= expRat x n1.
  
  induction n1; intuition; simpl in *.
  eapply expRat_le_1; trivial.
  
  destruct n2;
    simpl.
  omega.
  eapply ratMult_leRat_compat.
  intuition.
  eapply IHn1.
  trivial.
  omega.
Qed.

Lemma expRat_leRat_compat : forall n r1 r2,
  r1 <= r2 ->
  expRat r1 n <= expRat r2 n.

  induction n; intuition; simpl in *.
  intuition.

  eapply ratMult_leRat_compat; eauto.

Qed.


Lemma expRat_le' : forall n1 n2 r v,
  expRat r n1 <= v ->
  ~ (1 <= r) ->
  n2 >= n1 ->
  expRat r n2 <= v.

  intuition.
  eapply leRat_trans.
  eapply expRat_le.
  case_eq (bleRat r 1); intuition.
  exfalso.
  eapply H0.
  eapply bleRat_total.
  trivial.
  eauto.
  trivial.
Qed.


Lemma ratSubtract_sum_1 : forall r1 r2,
  ~ r1 <= r2 ->
  r2 + (ratSubtract r1 r2) == r1.

  intuition.
  
  rewrite <- ratSubtract_ratAdd_assoc.
  eapply ratSubtract_ratAdd_inverse.
  apply bleRat_total.
  case_eq (bleRat r1 r2); intuition.

Qed.

Lemma rat_ge_1 : forall n (d : posnat),
  n >= d ->
  1 <= RatIntro n d.
  
  intuition.
  rattac.
  inversion H1; clear H1; subst.
  omega.
  
Qed.

Lemma leRat_ratAdd_same_r : forall r1 r2 r3,
  r2 + r1 <= r3 + r1 ->
  r2 <= r3.

  intuition.
  
  apply (@ratSubtract_leRat_l (r2 + r1) (r3 + r1) r1) in H.
  rewrite <- (@ratSubtract_ratAdd_inverse r1 r2).
  rewrite ratAdd_comm.
  rewrite H.
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_inverse.
  intuition.
  
Qed.

Lemma leRat_ratMult_same_r : forall r1 r2 r3,
  (~r1 == 0) ->
  r2 * r1 <= r3 * r1 ->
  r2 <= r3.
  
  intuition.
  rewrite <- ratMult_1_r.
  erewrite <- (ratInverse_prod_1 H).
  rewrite (ratMult_comm (ratInverse r1)).
  rewrite <- ratMult_assoc.
  eapply leRat_trans.
  eapply ratMult_leRat_compat.
  eapply H0.
  eapply leRat_refl.
  rewrite ratMult_assoc.
  rewrite (ratMult_comm r1).
  rewrite ratInverse_prod_1.
  rewrite ratMult_1_r.
  intuition.
  intuition.
  
Qed.

Lemma ratMult_eq_rat1 : forall n1 n2 (nz1 : nz n1)(nz2 : nz n2),
  (n1 / n2) * (n2 / n1) == 1.
  
  intuition.
  rewrite <- ratMult_num_den.
  eapply num_dem_same_rat1.
  unfold posnatMult, natToPosnat, posnatToNat.
  eapply mult_comm.
  
Qed.


Lemma half_distance_1_le : forall r,
  ~ 1 <= r ->
  ~ 1 <= r + (1 / 2) * (ratSubtract 1 r).
  
  intuition.
  eapply H.
  eapply (leRat_ratAdd_same_r 1).
  rewrite <- (@ratSubtract_sum_1 1 r) at 3; trivial.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply ratAdd_assoc.
  }
  
  repeat rewrite ratMult_2.
  rewrite ratMult_comm.
  rewrite (ratMult_comm (2/1)).
  eapply (@leRat_ratMult_same_r (1/2)).
  intuition.
  rewrite ratMult_1_l.
  rewrite ratMult_eq_rat1.
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply ratMult_distrib_r.
  }
  
  rewrite ratMult_assoc.
  rewrite ratMult_eq_rat1.
  rewrite ratMult_1_r.
  rewrite ratMult_comm.
  trivial.
Qed.

Lemma leRat_terms : forall n1 n2 (d1 d2 : posnat),
  (n1 <= n2)%nat ->
  (d2 <= d1)%nat ->
  RatIntro n1 d1 <= RatIntro n2 d2.

  rattac.
  eapply mult_le_compat; trivial.

Qed.

Lemma posnatMult_eq : forall p1 p2,
  posnatToNat (posnatMult p1 p2) = (p1 * p2)%nat.

  intuition.
  unfold posnatMult.
  destruct p1.
  destruct p2.
  unfold posnatToNat, natToPosnat.
  trivial.
Qed.

Theorem mult_gt_zero_if : 
  forall (a b : nat),
    a * b > 0 -> (a > 0  /\ b > 0).

  induction a; induction b; intuition.

Qed.

Lemma expRat_terms : forall k n (d : posnat)(p : nz (expnat d k)),
  expRat (RatIntro n d) k == (expnat n k) / (expnat d k).

  induction k; intuition; simpl in *.
  symmetry.
  eapply num_dem_same_rat1.
  trivial.
  rewrite IHk.
  rewrite <- ratMult_num_den.
  eapply eqRat_terms.
  intuition.
  eapply posnatMult_eq.

  Grab Existential Variables.
  destruct p.
  econstructor.
  eapply mult_gt_zero_if; eauto.
  
Qed.
  

Lemma expRat_le_half_exists : forall r,
  ~ 1 <= r ->
  exists n, expRat r n <= (1/2).

  intuition.
  destruct r.
  destruct (le_dec n (pred p)).

  exists (p)%nat.
  
  eapply leRat_trans.
  eapply expRat_leRat_compat.
  eapply leRat_terms.
  eapply l.
  eapply le_refl.

  rewrite expRat_terms.

  destruct p.
  destruct x.
  omega.
  simpl.
  destruct (eq_nat_dec x O); subst.
  rewrite mult_0_l.
  rewrite rat_num_0.
  eapply rat0_le_all.

  assert (nz (2 * (x * expnat x x))).
  econstructor.
  eapply mult_gt_0.
  omega.
  eapply mult_gt_0. omega.
  edestruct (@expnat_nz x x).
  econstructor.
  omega.
  eauto.

  assert (nz ((expnat (S x) x + x * expnat (S x) x))).
  econstructor.
  assert (expnat (S x) x > O).
  edestruct (expnat_nz).
  econstructor.
  eapply g.
  eauto.
  remember (x * expnat (S x) x)%nat as a.
  omega.

  assert (posnatToNat (pos (2 * (x * expnat x x))) <= posnatToNat (pos (expnat (S x) x + x * expnat (S x) x)))%nat.
  unfold natToPosnat, posnatToNat.
  rewrite mult_assoc.
  rewrite (mult_comm 2 x).
  rewrite <- mult_assoc.
  rewrite <- (plus_0_l (x * (2 * expnat x x))).
  eapply plus_le_compat.
  intuition.
  eapply mult_le_compat.
  intuition.
  eapply expnat_base_S_same.
  omega.

  eapply leRat_trans.
  eapply leRat_terms.
  rewrite <- (mult_1_l (x * expnat x x)).
  eapply le_refl.
  unfold natToPosnat, posnatToNat.
  eapply H2.
  assert (nz (x * expnat x x)).
  econstructor.
  eapply mult_gt_0.
  omega.
  edestruct (@expnat_nz x x).
  econstructor.
  omega.
  eauto.
  assert (posnatToNat (pos (2 * (x * expnat x x))) = posnatToNat (posnatMult (pos 2) (pos (x * expnat x x)))).
  unfold posnatMult, posnatToNat, natToPosnat.
  trivial.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply eqRat_trans.
  eapply eqRat_terms.
  eapply eq_refl.
  eapply H4.
  eapply ratMult_num_den.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    rewrite <- (ratMult_1_r (1/2)).
    eapply eqRat_refl.
  }
  eapply ratMult_leRat_compat.
  intuition.
  eapply eqRat_impl_leRat.
  eapply num_dem_same_rat1.
  unfold posnatToNat, natToPosnat.
  trivial.

  exfalso.
  eapply H.

  eapply rat_ge_1.
  omega.

  Grab Existential Variables.
  
  eapply expnat_nz.
  destruct p.
  econstructor.
  simpl.
  trivial.
Qed.

Lemma expRat_half_le_exp_exists : forall d,
  ~ d == 0 ->
  exists n,
    expRat (1/2) n <= d.

  intuition.
  destruct d.
  assert (1 <= n)%nat.
  destruct n.
  exfalso.
  eapply H.
  eapply rat_num_0.
  omega.
  exists p.
  rewrite expRat_terms.
  eapply leRat_trans.
  2:{
    eapply leRat_terms.
    eapply H0.
    eapply le_refl.
  }
  erewrite expnat_1.
  eapply leRat_terms.
  intuition.
  edestruct p.
  unfold natToPosnat, posnatToNat.
  eapply le_expnat_2.

  Grab Existential Variables.
  eapply expnat_nz.
  econstructor.
  destruct p.
  econstructor.
  intuition.

Qed.

Lemma expRat_1 : forall n,
  expRat 1 n == 1.

  induction n; intuition; simpl in *.
  intuition.
  rewrite ratMult_1_l.
  trivial.

Qed.

Lemma expRat_exp_sum  : forall n1 n2 r,
  expRat r (n1 + n2)%nat == (expRat r n1) * (expRat r n2).

  induction n1; intuition; simpl in *.
  symmetry.
  eapply ratMult_1_l.

  rewrite IHn1.
  rewrite ratMult_assoc.
  intuition.

Qed.

Lemma expRat_base_prod : forall n r1 r2,
  expRat (r1 * r2) n == (expRat r1 n) * (expRat r2 n).

  induction n; intuition; simpl in *.
  symmetry.
  eapply ratMult_1_l.

  rewrite IHn.
  repeat rewrite <- ratMult_assoc.
  eapply ratMult_eqRat_compat; intuition.
  repeat rewrite ratMult_assoc.
  eapply ratMult_eqRat_compat; intuition.
  eapply ratMult_comm.
Qed.

Lemma expRat_exp_prod : forall n1 n2 r,
  expRat r (n1 * n2)%nat == expRat (expRat r n1) n2.

  induction n1; intuition; simpl in *.
  symmetry.
  eapply expRat_1.

  rewrite expRat_exp_sum.
  rewrite IHn1.
  rewrite expRat_base_prod.
  intuition.

Qed.

Lemma expRat_le_exp_exists : forall r d, 
  ~ 1 <= r ->
  ~ d == 0 ->
  exists n,
    expRat r n <= d.

  intuition.
  destruct (expRat_half_le_exp_exists H0).
  destruct (expRat_le_half_exists H).
  exists (x0 * x)%nat.
  rewrite expRat_exp_prod.
  eapply leRat_trans.
  eapply expRat_leRat_compat.
  eapply H2.
  intuition.
Qed.

Lemma eqRat_ratAdd_same_r : forall r1 r2 r3,
  r2 + r1 == r3 + r1 ->
  r2 == r3.
  
  intuition.
  eapply leRat_impl_eqRat.
  eapply leRat_ratAdd_same_r;
    eapply eqRat_impl_leRat; eauto.
  symmetry in H.
  eapply leRat_ratAdd_same_r;
    eapply eqRat_impl_leRat; eauto.
Qed.

Lemma ratAdd_arg_0 : forall a b,
  a + b == a ->
  b == 0.
  
  intuition.
  eapply eqRat_ratAdd_same_r.
  rewrite ratAdd_comm.
  rewrite H.
  rewrite <- ratAdd_0_l.
  intuition.
Qed.

Definition ratHalf(r : Rat) :=
  r * (1 / 2).

Theorem ratHalf_ne_0 : forall r,
  ~ r == 0 ->
  ~ (ratHalf r) == 0.

  intuition.
  unfold ratHalf in *.
  apply ratMult_0 in H0.

  destruct H0; intuition.
Qed.

Theorem ratHalf_add : forall r,
  ratHalf r + ratHalf r == r.

  intuition.
  unfold ratHalf.
  eapply eqRat_trans.
  apply eqRat_symm.
  apply ratMult_distrib.
  eapply eqRat_trans.
  apply ratMult_eqRat_compat.
  apply eqRat_refl.
  apply ratOneHalf_add.
  rewrite ratMult_1_r.
  intuition.
Qed.

Theorem le_ratHalf_0 : forall r,
  r <= (ratHalf r) -> r == 0.

  intuition.
  unfold ratHalf in *.
  rattac.
  unfold posnatMult in *.
  destruct p.
  unfold natToPosnat in *.
  unfold posnatToNat in *.
  rewrite mult_1_r in *.
  rewrite (mult_comm x) in l.
  rewrite mult_assoc in *.
  assert (n * 2 <= n)%nat.
  eapply mult_le_compat_r_iff; eauto.
  omega.
Qed.

Lemma ratSubtract_0_r : forall r,
  ratSubtract r 0 == r.

  unfold ratSubtract in *.
  rattac.
  arithNormalize.
  inversion H; clear H; subst.
  simpl.
  rewrite <- minus_n_O.
  do 2 arithSimplify.
  
Qed.

Lemma ratDistance_0_r_le : forall r d,
  r <= d ->
  ratDistance r 0 <= d.

  intuition.
  unfold ratDistance, maxRat, minRat.
  case_eq (bleRat r 0); intuition.
  rewrite ratSubtract_0;
  eapply rat0_le_all.
  apply bleRat_total in H0.
  rewrite ratSubtract_0_r.
  trivial.
  
Qed.

Lemma ratSubtract_0_inv : forall r1 r2,
  ratSubtract r1 r2 == 0 ->
  r1 <= r2.

  intuition.
  unfold ratSubtract in *.
  rattac.
  rewrite mult_0_l in e.
  apply mult_is_O in e.
  intuition.
Qed.

Lemma ratSubtract_le_sum : forall r1 r2 d,
  r2 <= r1 ->
  ratSubtract r1 r2 <= d ->
  r1 <= r2 + d.
  
  intuition.
  
  rewrite <- (ratSubtract_ratAdd_inverse r2).
  rewrite ratSubtract_ratAdd_assoc.
  eapply ratAdd_leRat_compat; eauto.
  intuition.
  trivial.
Qed.

Lemma ratDistance_le_sum : forall r1 r2 d,
  ratDistance r1 r2 <= d ->
  r1 <= r2 + d.

  unfold ratDistance, maxRat, minRat in *.
  intuition.
  case_eq (bleRat r1 r2); intuition;
  rewrite H0 in H.
  rewrite ratAdd_0_r.
  eapply ratAdd_leRat_compat.
  trivial.
  eapply rat0_le_all.

  eapply ratSubtract_le_sum.
  eapply bleRat_total.
  trivial.
  trivial.
Qed.

Lemma ratSubtract_ratDistance_le : forall r1 r2,
  ratSubtract r1 r2 <= ratDistance r1 r2.
  
  unfold ratDistance, maxRat, minRat in *.
  intuition.
  case_eq (bleRat r1 r2); intuition.
  rewrite ratSubtract_0.
  eapply rat0_le_all.
  trivial.
Qed.

Lemma minRat_le_r : forall r1 r2,
  minRat r1 r2 <= r2.
  
  unfold minRat in *.
  intuition.
  case_eq (bleRat r1 r2); intuition.
Qed.

Lemma minRat_le_l : forall r1 r2,
  minRat r1 r2 <= r1.
  
  unfold minRat in *.
  intuition.
  case_eq (bleRat r1 r2); intuition.
  eapply bleRat_total.
  trivial.
Qed.

Lemma ratDistance_ge_difference: forall r1 r2 d,
  ratDistance r1 r2 <= d ->
  ratSubtract r1 d <= r2.
  
  intuition.
  eapply (leRat_ratAdd_same_r d).
  case_eq (bleRat r1 d); intuition.
  rewrite ratSubtract_0; trivial.
  eapply ratAdd_leRat_compat; intuition.
  eapply rat0_le_all.
  apply bleRat_total in H0.
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_inverse_2; trivial.
  eapply ratDistance_le_sum; trivial.
  
Qed.

Lemma ratSubtract_ratAdd_assoc_le : forall r1 r2 r3,
  ratSubtract (r1 + r2) r3 <= r1 + (ratSubtract r2 r3).
  
  unfold ratSubtract, ratAdd.
  rattac.
  arithNormalize.
  generalize (n1 * x0 * x1 * x * x0 * x1)%nat; intuition.
  assert (n3 * x * x1 * x * x0 * x1 = n3 * x1 * x * x * x0 * x1)%nat.
  do 5 arithSimplify.
  rewrite H.
  generalize (n3 * x1 * x * x * x0 * x1)%nat; intuition.
  assert (n0 * x * x0 * x * x0 * x1 = n0 * x0 * x * x * x0 * x1)%nat.
  do 5 arithSimplify.
  rewrite H0.
  generalize ( n0 * x0 * x * x * x0 * x1)%nat; intuition.
Qed.

Lemma ratSubtract_assoc_le : forall r1 r2 r3,
  ratSubtract r1 (ratSubtract r2 r3) <= (ratSubtract r1 r2) + r3.
  
  unfold ratSubtract.
  rattac.
  arithNormalize.
  remember (n * x * x0 * x1 * x * x0)%nat as a.
  assert (n1 * x0 * x1 * x1 * x * x0 = n1 * x1 * x0 * x1 * x * x0)%nat.
  do 5 arithSimplify.
  rewrite H.
  assert (n2 * x * x1 * x1 * x * x0 = n2 * x1 * x * x1 * x * x0)%nat.
  do 5 arithSimplify.
  rewrite H0.
  remember (n1 * x1 * x0 * x1 * x * x0)%nat as b.
  remember (n2 * x1 * x * x1 * x * x0)%nat as c.
  omega.
  
Qed.

Lemma ratDistance_leRat_both : forall r1 r2 d,
  ratSubtract r1 r2 <= d ->
  ratSubtract r2 r1 <= d ->
  ratDistance r1 r2 <= d.
  
  intuition.
  
  unfold ratDistance, maxRat, minRat.
  destruct (bleRat r1 r2); trivial.
  
Qed.

Lemma rat_distance_of_difference : forall r1 r2 r3 r4 d1 d2,
  r2 <= r1 ->
  r4 <= r3 ->
  ratDistance r1 r3 <= d1 ->
  ratDistance r2 r4 <= d2 ->
  ratDistance (ratSubtract r1 r2) (ratSubtract r3 r4) <= (d1 + d2).
  
  intuition.
  eapply ratDistance_leRat_both.
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  eapply ratSubtract_leRat.
  eapply ratDistance_le_sum.
  eauto.
  
  eapply ratDistance_ge_difference.
  rewrite ratDistance_comm.
  eauto.
  
  eapply leRat_refl.
  
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  rewrite ratAdd_comm.
  eapply ratSubtract_ratAdd_assoc_le.
  eapply leRat_refl.
  rewrite ratSubtract_ratAdd_assoc_le.
  eapply ratAdd_leRat_compat.
  intuition.
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  
  eapply ratSubtract_assoc_le.
  eapply leRat_refl.
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_assoc_le.
  rewrite ratSubtract_0.
  rewrite <- ratAdd_0_r.
  intuition.
  intuition.
  
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  eapply ratSubtract_leRat.
  eapply ratDistance_le_sum.
  rewrite ratDistance_comm.
  eauto.
  eapply ratDistance_ge_difference.
  eauto.
  eapply leRat_refl.
  
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  rewrite ratAdd_comm.
  eapply ratSubtract_ratAdd_assoc_le.
  eapply leRat_refl.
  rewrite ratSubtract_ratAdd_assoc_le.
  eapply ratAdd_leRat_compat.
  intuition.
  eapply leRat_trans.
  eapply ratSubtract_leRat.
  
  eapply ratSubtract_assoc_le.
  eapply leRat_refl.
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_assoc_le.
  rewrite ratSubtract_0.
  rewrite <- ratAdd_0_r.
  intuition.
  intuition.    
  
Qed.

Lemma ratMult_ratSubtract_distrib_r : forall f r1 r2,
  (ratSubtract r1 r2) * f  == ratSubtract (r1 * f) (r2 * f).
  
  intuition.
  unfold ratMult, ratSubtract.
  rattac.
  inversion H; clear H; subst.
  
  arithNormalize.
  f_equal.
  do 6 arithSimplify.
  do 6 arithSimplify.
Qed.

Lemma ratMult_ratDistance_factor_r : forall r1 r2 r3,
  ratDistance (r1 * r3) (r2 * r3) == (ratDistance r1 r2) * r3.
  
  intuition.
  destruct (eq_Rat_dec r3 0).
  repeat rewrite e.
  repeat rewrite ratMult_0_r.
  rewrite <- ratIdentityIndiscernables.
  intuition.
  unfold ratDistance, maxRat, minRat.
  case_eq (bleRat r1 r2); intuition.
  assert (bleRat (r1 * r3) ( r2 * r3) = true).
  eapply ratMult_leRat_compat; 
    intuition.
  rewrite H0.
  rewrite ratMult_ratSubtract_distrib_r.
  intuition.

  case_eq (bleRat (r1 * r3) (r2 * r3)); intuition.
  eapply leRat_ratMult_same_r in H0.
  congruence.
  intuition.
  
  rewrite ratMult_ratSubtract_distrib_r.
  intuition.

Qed.

Lemma ratMult_ratDistance_factor_l : forall r1 r2 r3,
  ratDistance (r3 * r1) (r3 * r2) == r3 * (ratDistance r1 r2).
  
  intuition.
  repeat rewrite (ratMult_comm r3).
  eapply ratMult_ratDistance_factor_r.
Qed.

Lemma ratAdd_rel_left_total : forall (r1 r2: Rat -> Prop),
  (exists r1', r1 r1') ->
  (exists r2', r2 r2') ->
  (forall x1 x2, r1 x1 -> r1 x2 -> x1 == x2) ->
  (forall x1 x2, r2 x1 -> r2 x2 -> x1 == x2) ->
  exists r3, ratAdd_rel r1 r2 r3.
  
  unfold ratAdd_rel in *.
  intuition.
  destruct H.
  destruct H0.
  exists (x + x0).
  intuition.
  eapply ratAdd_eqRat_compat; eauto.
Qed.

Lemma expRat_eqRat_compat : forall n r1 r2,
  r1 == r2 ->
  expRat r1 n == expRat r2 n.

  induction n; intuition; simpl in *; intuition.

  eapply ratMult_eqRat_compat; eauto.

Qed.

Lemma expRat_rel_left_total : forall (r1 : Rat -> Prop) n,
  (exists r1', r1 r1') ->
  (forall x1 x2, r1 x1 -> r1 x2 -> x1 == x2) ->
  exists r3, expRat_rel r1 n r3.
  
  unfold expRat_rel in *.
  intuition.
  destruct H.
  exists (expRat x n).
  intuition.
  eapply expRat_eqRat_compat; eauto.
  
Qed.

Lemma expRat_rel_func : forall (r : Rat -> Prop) v1 v2 n,
  expRat_rel r n v1 ->
  expRat_rel r n v2 ->
  (forall x1 x2, r x1 -> r x2 -> x1 == x2) ->
  (exists r', r r') ->
  v1 == v2.
  
  unfold expRat_rel in *.
  intuition.
  destruct H2.
  rewrite H; eauto.
  rewrite H0; eauto.
  intuition.
Qed.

Lemma ratInverse_involutive : forall r,
  ~ r == 0 ->
  ratInverse (ratInverse r) == r.
  
  intuition.
  unfold ratInverse.
  destruct r.
  destruct n.
  exfalso.
  eapply H.
  eapply rat_num_0.
  
  destruct p.
  unfold posnatToNat, natToPosnat.
  destruct x.
  omega.
  eapply eqRat_terms; intuition.
Qed.

Lemma ratInverse_ratMult : forall r1 r2,
  ~ r1 == 0 ->
  ~ r2 == 0 ->
  ratInverse (r1 * r2) == ratInverse r1 * ratInverse r2.

  intuition.
  unfold ratInverse.
  destruct r1.
  destruct n.
  exfalso.
  eapply H.
  eapply rat_num_0.
  destruct r2.
  destruct n0.
  exfalso.
  eapply H0.
  eapply rat_num_0.
  case_eq (RatIntro (S n) p * RatIntro (S n0) p0); intuition.
  inversion H1; clear H1; subst.
  unfold ratMult.
  unfold natToPosnat, posnatToNat, posnatMult.
  simpl.
  eapply eqRat_terms.
  destruct p.
  destruct p0.
  trivial.
  simpl.
  trivial.

Qed.

Lemma ratDistance_ratInverse : forall r1 r2,
  ~ r1 == 0 ->
  ~ r2 == 0 -> 
  ratDistance (ratInverse r1) (ratInverse r2) == (ratDistance r1 r2) * ratInverse (r1 * r2).

  intuition.
  rewrite ratInverse_ratMult; intuition.
  rewrite <- ratMult_ratDistance_factor_r.
  rewrite (ratMult_comm (ratInverse r1)) at 2.
  repeat rewrite <- ratMult_assoc.
  rewrite (ratMult_comm r1).
  rewrite ratInverse_prod_1; intuition.
  rewrite ratMult_1_l.
  rewrite (ratMult_comm r2).
  rewrite ratInverse_prod_1; intuition.
  rewrite ratMult_1_l.
  intuition.
  eapply ratDistance_comm.
Qed.

Lemma ratSubtract_half : forall x,
  ratSubtract x (x * (1/2)) == x * (1/2).
  
  intuition.
  unfold ratSubtract.
  rattac.
  arithNormalize.
  inversion H; clear H; subst.
  rewrite <- (mult_assoc (n * x * 2)).
  rewrite (mult_comm (n * x)).
  repeat rewrite mult_assoc.
  simpl.
  rewrite (plus_0_r).
  repeat rewrite mult_plus_distr_r.
  remember (n * x * x * 2)%nat as a.
  omega.
Qed.

Lemma ratMult_ratAdd_cd : forall r n (d : posnat),
  r + r * (RatIntro n d) == r * (RatIntro (d + n)%nat d).
  
  intuition.
  unfold ratAdd, ratMult.
  rattac.
  arithNormalize.
  arithSimplify.
  do 4 arithSimplify.
Qed.

Definition numerator r :=
  match r with
    | RatIntro n d => n
  end.

Lemma ratDistance_add_same_l_gen : forall r1 r2 r3 r4,
  r1 == r3 ->
  ratDistance (r1 + r2) (r3 + r4) == ratDistance r2 r4.
  
  intuition.
  rewrite H.
  eapply ratDistance_add_same_l.
Qed.

Lemma ratDistance_add_same_r_gen : forall r1 r2 r3 r4,
  r2 == r4 ->
  ratDistance (r1 + r2) (r3 + r4) == ratDistance r1 r3.
  
  intuition.
  rewrite H.
  eapply ratDistance_add_same_r.
Qed.

Lemma ratDistance_from_0 : forall r,
  ratDistance 0 r == r.
  
  intuition.
  unfold ratDistance, maxRat, minRat.
  rewrite rat0_le_all.
  eapply ratSubtract_0_r.
Qed.

Lemma maxRat_comm : forall r1 r2,
  maxRat r1 r2 == maxRat r2 r1.
  
  intuition.
  unfold maxRat.
  case_eq (bleRat r1 r2); intuition.
  case_eq (bleRat r2 r1); intuition.
  eapply leRat_impl_eqRat; trivial.
  apply bleRat_total in H.
  rewrite H.
  intuition.
Qed.

Lemma ratDistance_le_max_triv : forall r1 r2,
  ratDistance r1 r2 <= maxRat r1 r2.
  
  intuition.
  eapply leRat_trans.
  eapply ratDistance_le_max.
  eapply rat0_le_all.
  eapply (@ratAdd_any_leRat_l r1 r2).
  eapply leRat_refl.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply maxRat_eqRat_compat.
  eapply ratDistance_from_0.
  
  eapply eqRat_trans.
  eapply ratDistance_eqRat_compat.
  eapply eqRat_refl.
  eapply ratAdd_0_l.
  rewrite ratDistance_add_same_r.
  rewrite ratDistance_comm.
  eapply ratDistance_from_0.
  
  rewrite maxRat_comm.
  intuition.
Qed.

Lemma ratAdd_2_ratMax : 
  forall r1 r2,
    (r1 + r2 <= 2 / 1 * (maxRat r1 r2))%rat.
  
  intuition.
  
  unfold maxRat.
  case_eq (bleRat r1 r2); intuition.
  eapply leRat_trans.
  eapply ratAdd_leRat_compat.
  eapply H.
  eapply leRat_refl.
  rewrite ratMult_2.
  rewrite ratMult_comm.
  intuition.
  
  apply bleRat_total in H.
  eapply leRat_trans.
  eapply ratAdd_leRat_compat.
  eapply leRat_refl.
  eapply H.     
  rewrite ratMult_2.
  rewrite ratMult_comm.
  intuition.
Qed.

Theorem rat_num_not_le : 
  forall (d1 d2 : posnat),
    (RatIntro 1 d1 <= RatIntro 1 d2)%rat ->
    d1 < d2 ->
    False.
  
  intuition.
  rattac.
  
Qed.

Lemma leRat_0_eq : 
  forall r, 
    (r <= 0 ->
      r == 0)%rat.
  
  intuition.
  rattac.
  symmetry.
  eapply le_n_0_eq.
  unfold natToPosnat, posnatToNat in *.
  rewrite mult_1_r in l.
  rewrite l.
  destruct p.
  rewrite mult_0_l.
  intuition.
Qed.

Lemma rat_le_1_if : 
  forall n d,
    RatIntro n d <= 1 ->
    (n <= d)%nat.
  
  intuition.
  
  unfold leRat, bleRat, ratCD, rat1 in *.
  unfold natToPosnat, posnatToNat in *.
  destruct d.
  rewrite mult_1_r in H.
  rewrite mult_1_l in H.
  destruct (le_gt_dec n x); intuition.
  discriminate.
  
Qed.


Theorem ratFraction_le_1 : 
  forall r1 r2,
    r1 <= r2 ->
    r1 * (ratInverse r2) <= 1.
  
  intuition.
  unfold ratInverse.
  destruct r2.
  destruct n.
  rewrite H.
  rewrite rat_num_0.
  rewrite ratMult_0_l.
  eapply rat0_le_all.
  rewrite H.
  rewrite <- ratMult_num_den.
  eapply rat_le_1.
  
  unfold posnatMult, natToPosnat, posnatToNat.
  destruct p.
  rewrite mult_comm.
  intuition.
Qed.

Theorem ratFraction_ge_1_inv : 
  forall r1 r2,
    1 <= r1 * (ratInverse r2) ->
    r2 <= r1.
  
  intuition.
  
  destruct (eq_Rat_dec r2 0).
  rewrite e.
  eapply rat0_le_all.
  
  eapply (@leRat_ratMult_same_r (ratInverse r2)).
  intuition.
  eapply ratInverse_nz.
  eauto.
  rewrite ratMult_comm.
  rewrite ratInverse_prod_1.
  intuition.
  intuition.

Qed.

Theorem eqRat_refl_eq : 
  forall x y,
    x = y ->
    x == y.
  
  intuition; subst.
  intuition.
  
Qed.

Theorem rat_num_S : 
  forall n d,
    (RatIntro (S n) d == (RatIntro 1 d) + RatIntro n d)%rat.
  
  intuition.
  rattac.
  rewrite mult_plus_distr_r.
  f_equal.
  eapply mult_assoc.
Qed.

Theorem distance_le_prod_f :
  forall (f : nat -> Rat) k,
    (forall i, | (f i) - (f (S i)) | <= k) ->
    forall q0,
| (f 0%nat) - (f q0) | <= q0/1 * k.
  
  induction q0; intuition.
  assert (| f 0%nat - f 0%nat | == 0).
  rewrite <- ratIdentityIndiscernables.
  reflexivity.
  rewrite H0.
  eapply rat0_le_all.
  
  eapply leRat_trans.
  eapply ratTriangleInequality.
  rewrite IHq0.
  rewrite H.
  
  rewrite rat_num_S.
  rewrite ratMult_distrib_r.
  rewrite ratAdd_comm.
  eapply ratAdd_leRat_compat.
  rewrite ratMult_1_l.
  reflexivity.
  reflexivity.
Qed.
