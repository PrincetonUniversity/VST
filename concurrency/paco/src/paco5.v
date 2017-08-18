Require Export VST.concurrency.paco.src.paconotation VST.concurrency.paco.src.pacotac VST.concurrency.paco.src.pacodef VST.concurrency.paco.src.pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 5
*)

(** 1 Mutual Coinduction *)

Section Arg5_1.

Definition monotone5 T0 T1 T2 T3 T4 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall x0 x1 x2 x3 x4 r r' (IN: gf r x0 x1 x2 x3 x4) (LE: r <5= r'), gf r' x0 x1 x2 x3 x4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Implicit Arguments gf [].

Theorem paco5_acc: forall
  l r (OBG: forall rr (INC: r <5= rr) (CIH: l <_paco_5= rr), l <_paco_5= paco5 gf rr),
  l <5= paco5 gf r.
Proof.
  intros; assert (SIM: paco5 gf (r \5/ l) x0 x1 x2 x3 x4) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5_mon: monotone5 (paco5 gf).
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_mult_strong: forall r,
  paco5 gf (upaco5 gf r) <5= paco5 gf r.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Corollary paco5_mult: forall r,
  paco5 gf (paco5 gf r) <5= paco5 gf r.
Proof. intros; eapply paco5_mult_strong, paco5_mon; eauto. Qed.

Theorem paco5_fold: forall r,
  gf (upaco5 gf r) <5= paco5 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco5_unfold: forall (MON: monotone5 gf) r,
  paco5 gf r <5= gf (upaco5 gf r).
Proof. unfold monotone5; intros; destruct PR; eauto. Qed.

End Arg5_1.

Hint Unfold monotone5.
Hint Resolve paco5_fold.

Implicit Arguments paco5_acc            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_mon            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_mult_strong    [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_mult           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_fold           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_unfold         [ T0 T1 T2 T3 T4 ].

Instance paco5_inst  T0 T1 T2 T3 T4 (gf : rel5 T0 T1 T2 T3 T4->_) r x0 x1 x2 x3 x4 : paco_class (paco5 gf r x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_acc gf;
  pacomult   := paco5_mult gf;
  pacofold   := paco5_fold gf;
  pacounfold := paco5_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg5_2.

Definition monotone5_2 T0 T1 T2 T3 T4 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall x0 x1 x2 x3 x4 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4) (LE_0: r_0 <5= r'_0)(LE_1: r_1 <5= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable gf_0 gf_1 : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco5_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <5= rr) (CIH: l <_paco_5= rr), l <_paco_5= paco5_2_0 gf_0 gf_1 rr r_1),
  l <5= paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco5_2_0 gf_0 gf_1 (r_0 \5/ l) r_1 x0 x1 x2 x3 x4) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <5= rr) (CIH: l <_paco_5= rr), l <_paco_5= paco5_2_1 gf_0 gf_1 r_0 rr),
  l <5= paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco5_2_1 gf_0 gf_1 r_0 (r_1 \5/ l) x0 x1 x2 x3 x4) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5_2_0_mon: monotone5_2 (paco5_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_2_1_mon: monotone5_2 (paco5_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_2_0_mult_strong: forall r_0 r_1,
  paco5_2_0 gf_0 gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_2_1_mult_strong: forall r_0 r_1,
  paco5_2_1 gf_0 gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Corollary paco5_2_0_mult: forall r_0 r_1,
  paco5_2_0 gf_0 gf_1 (paco5_2_0 gf_0 gf_1 r_0 r_1) (paco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco5_2_0_mult_strong, paco5_2_0_mon; eauto. Qed.

Corollary paco5_2_1_mult: forall r_0 r_1,
  paco5_2_1 gf_0 gf_1 (paco5_2_0 gf_0 gf_1 r_0 r_1) (paco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco5_2_1_mult_strong, paco5_2_1_mon; eauto. Qed.

Theorem paco5_2_0_fold: forall r_0 r_1,
  gf_0 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco5_2_1_fold: forall r_0 r_1,
  gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco5_2_0_unfold: forall (MON: monotone5_2 gf_0) (MON: monotone5_2 gf_1) r_0 r_1,
  paco5_2_0 gf_0 gf_1 r_0 r_1 <5= gf_0 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone5_2; intros; destruct PR; eauto. Qed.

Theorem paco5_2_1_unfold: forall (MON: monotone5_2 gf_0) (MON: monotone5_2 gf_1) r_0 r_1,
  paco5_2_1 gf_0 gf_1 r_0 r_1 <5= gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone5_2; intros; destruct PR; eauto. Qed.

End Arg5_2.

Hint Unfold monotone5_2.
Hint Resolve paco5_2_0_fold.
Hint Resolve paco5_2_1_fold.

Implicit Arguments paco5_2_0_acc            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_1_acc            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_0_mon            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_1_mon            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_0_mult_strong    [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_1_mult_strong    [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_0_mult           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_1_mult           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_0_fold           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_1_fold           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_0_unfold         [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_2_1_unfold         [ T0 T1 T2 T3 T4 ].

Instance paco5_2_0_inst  T0 T1 T2 T3 T4 (gf_0 gf_1 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 x0 x1 x2 x3 x4 : paco_class (paco5_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_2_0_acc gf_0 gf_1;
  pacomult   := paco5_2_0_mult gf_0 gf_1;
  pacofold   := paco5_2_0_fold gf_0 gf_1;
  pacounfold := paco5_2_0_unfold gf_0 gf_1 }.

Instance paco5_2_1_inst  T0 T1 T2 T3 T4 (gf_0 gf_1 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 x0 x1 x2 x3 x4 : paco_class (paco5_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_2_1_acc gf_0 gf_1;
  pacomult   := paco5_2_1_mult gf_0 gf_1;
  pacofold   := paco5_2_1_fold gf_0 gf_1;
  pacounfold := paco5_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg5_3.

Definition monotone5_3 T0 T1 T2 T3 T4 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall x0 x1 x2 x3 x4 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4) (LE_0: r_0 <5= r'_0)(LE_1: r_1 <5= r'_1)(LE_2: r_2 <5= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco5_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <5= rr) (CIH: l <_paco_5= rr), l <_paco_5= paco5_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <5= paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco5_3_0 gf_0 gf_1 gf_2 (r_0 \5/ l) r_1 r_2 x0 x1 x2 x3 x4) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <5= rr) (CIH: l <_paco_5= rr), l <_paco_5= paco5_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco5_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \5/ l) r_2 x0 x1 x2 x3 x4) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <5= rr) (CIH: l <_paco_5= rr), l <_paco_5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \5/ l) x0 x1 x2 x3 x4) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5_3_0_mon: monotone5_3 (paco5_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_3_1_mon: monotone5_3 (paco5_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_3_2_mon: monotone5_3 (paco5_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_3_0_mult_strong: forall r_0 r_1 r_2,
  paco5_3_0 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_3_1_mult_strong: forall r_0 r_1 r_2,
  paco5_3_1 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5_3_2_mult_strong: forall r_0 r_1 r_2,
  paco5_3_2 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Corollary paco5_3_0_mult: forall r_0 r_1 r_2,
  paco5_3_0 gf_0 gf_1 gf_2 (paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco5_3_0_mult_strong, paco5_3_0_mon; eauto. Qed.

Corollary paco5_3_1_mult: forall r_0 r_1 r_2,
  paco5_3_1 gf_0 gf_1 gf_2 (paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco5_3_1_mult_strong, paco5_3_1_mon; eauto. Qed.

Corollary paco5_3_2_mult: forall r_0 r_1 r_2,
  paco5_3_2 gf_0 gf_1 gf_2 (paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco5_3_2_mult_strong, paco5_3_2_mon; eauto. Qed.

Theorem paco5_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco5_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco5_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco5_3_0_unfold: forall (MON: monotone5_3 gf_0) (MON: monotone5_3 gf_1) (MON: monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5= gf_0 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone5_3; intros; destruct PR; eauto. Qed.

Theorem paco5_3_1_unfold: forall (MON: monotone5_3 gf_0) (MON: monotone5_3 gf_1) (MON: monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5= gf_1 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone5_3; intros; destruct PR; eauto. Qed.

Theorem paco5_3_2_unfold: forall (MON: monotone5_3 gf_0) (MON: monotone5_3 gf_1) (MON: monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5= gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone5_3; intros; destruct PR; eauto. Qed.

End Arg5_3.

Hint Unfold monotone5_3.
Hint Resolve paco5_3_0_fold.
Hint Resolve paco5_3_1_fold.
Hint Resolve paco5_3_2_fold.

Implicit Arguments paco5_3_0_acc            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_1_acc            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_2_acc            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_0_mon            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_1_mon            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_2_mon            [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_0_mult_strong    [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_1_mult_strong    [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_2_mult_strong    [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_0_mult           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_1_mult           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_2_mult           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_0_fold           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_1_fold           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_2_fold           [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_0_unfold         [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_1_unfold         [ T0 T1 T2 T3 T4 ].
Implicit Arguments paco5_3_2_unfold         [ T0 T1 T2 T3 T4 ].

Instance paco5_3_0_inst  T0 T1 T2 T3 T4 (gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 : paco_class (paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco5_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco5_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco5_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco5_3_1_inst  T0 T1 T2 T3 T4 (gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 : paco_class (paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco5_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco5_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco5_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco5_3_2_inst  T0 T1 T2 T3 T4 (gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 : paco_class (paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco5_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco5_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco5_3_2_unfold gf_0 gf_1 gf_2 }.

