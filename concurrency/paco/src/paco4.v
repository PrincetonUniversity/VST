Require Export VST.concurrency.paco.src.paconotation VST.concurrency.paco.src.pacotac VST.concurrency.paco.src.pacodef VST.concurrency.paco.src.pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 4
*)

(** 1 Mutual Coinduction *)

Section Arg4_1.

Definition monotone4 T0 T1 T2 T3 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall x0 x1 x2 x3 r r' (IN: gf r x0 x1 x2 x3) (LE: r <4= r'), gf r' x0 x1 x2 x3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Implicit Arguments gf [].

Theorem paco4_acc: forall
  l r (OBG: forall rr (INC: r <4= rr) (CIH: l <_paco_4= rr), l <_paco_4= paco4 gf rr),
  l <4= paco4 gf r.
Proof.
  intros; assert (SIM: paco4 gf (r \4/ l) x0 x1 x2 x3) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4_mon: monotone4 (paco4 gf).
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_mult_strong: forall r,
  paco4 gf (upaco4 gf r) <4= paco4 gf r.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Corollary paco4_mult: forall r,
  paco4 gf (paco4 gf r) <4= paco4 gf r.
Proof. intros; eapply paco4_mult_strong, paco4_mon; eauto. Qed.

Theorem paco4_fold: forall r,
  gf (upaco4 gf r) <4= paco4 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco4_unfold: forall (MON: monotone4 gf) r,
  paco4 gf r <4= gf (upaco4 gf r).
Proof. unfold monotone4; intros; destruct PR; eauto. Qed.

End Arg4_1.

Hint Unfold monotone4.
Hint Resolve paco4_fold.

Implicit Arguments paco4_acc            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_mon            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_mult_strong    [ T0 T1 T2 T3 ].
Implicit Arguments paco4_mult           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_fold           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_unfold         [ T0 T1 T2 T3 ].

Instance paco4_inst  T0 T1 T2 T3 (gf : rel4 T0 T1 T2 T3->_) r x0 x1 x2 x3 : paco_class (paco4 gf r x0 x1 x2 x3) :=
{ pacoacc    := paco4_acc gf;
  pacomult   := paco4_mult gf;
  pacofold   := paco4_fold gf;
  pacounfold := paco4_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg4_2.

Definition monotone4_2 T0 T1 T2 T3 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall x0 x1 x2 x3 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3) (LE_0: r_0 <4= r'_0)(LE_1: r_1 <4= r'_1), gf r'_0 r'_1 x0 x1 x2 x3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable gf_0 gf_1 : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco4_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <4= rr) (CIH: l <_paco_4= rr), l <_paco_4= paco4_2_0 gf_0 gf_1 rr r_1),
  l <4= paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco4_2_0 gf_0 gf_1 (r_0 \4/ l) r_1 x0 x1 x2 x3) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <4= rr) (CIH: l <_paco_4= rr), l <_paco_4= paco4_2_1 gf_0 gf_1 r_0 rr),
  l <4= paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco4_2_1 gf_0 gf_1 r_0 (r_1 \4/ l) x0 x1 x2 x3) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4_2_0_mon: monotone4_2 (paco4_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_2_1_mon: monotone4_2 (paco4_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_2_0_mult_strong: forall r_0 r_1,
  paco4_2_0 gf_0 gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_2_1_mult_strong: forall r_0 r_1,
  paco4_2_1 gf_0 gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Corollary paco4_2_0_mult: forall r_0 r_1,
  paco4_2_0 gf_0 gf_1 (paco4_2_0 gf_0 gf_1 r_0 r_1) (paco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco4_2_0_mult_strong, paco4_2_0_mon; eauto. Qed.

Corollary paco4_2_1_mult: forall r_0 r_1,
  paco4_2_1 gf_0 gf_1 (paco4_2_0 gf_0 gf_1 r_0 r_1) (paco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco4_2_1_mult_strong, paco4_2_1_mon; eauto. Qed.

Theorem paco4_2_0_fold: forall r_0 r_1,
  gf_0 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco4_2_1_fold: forall r_0 r_1,
  gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco4_2_0_unfold: forall (MON: monotone4_2 gf_0) (MON: monotone4_2 gf_1) r_0 r_1,
  paco4_2_0 gf_0 gf_1 r_0 r_1 <4= gf_0 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone4_2; intros; destruct PR; eauto. Qed.

Theorem paco4_2_1_unfold: forall (MON: monotone4_2 gf_0) (MON: monotone4_2 gf_1) r_0 r_1,
  paco4_2_1 gf_0 gf_1 r_0 r_1 <4= gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone4_2; intros; destruct PR; eauto. Qed.

End Arg4_2.

Hint Unfold monotone4_2.
Hint Resolve paco4_2_0_fold.
Hint Resolve paco4_2_1_fold.

Implicit Arguments paco4_2_0_acc            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_1_acc            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_0_mon            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_1_mon            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_0_mult_strong    [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_1_mult_strong    [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_0_mult           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_1_mult           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_0_fold           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_1_fold           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_0_unfold         [ T0 T1 T2 T3 ].
Implicit Arguments paco4_2_1_unfold         [ T0 T1 T2 T3 ].

Instance paco4_2_0_inst  T0 T1 T2 T3 (gf_0 gf_1 : rel4 T0 T1 T2 T3->_) r_0 r_1 x0 x1 x2 x3 : paco_class (paco4_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3) :=
{ pacoacc    := paco4_2_0_acc gf_0 gf_1;
  pacomult   := paco4_2_0_mult gf_0 gf_1;
  pacofold   := paco4_2_0_fold gf_0 gf_1;
  pacounfold := paco4_2_0_unfold gf_0 gf_1 }.

Instance paco4_2_1_inst  T0 T1 T2 T3 (gf_0 gf_1 : rel4 T0 T1 T2 T3->_) r_0 r_1 x0 x1 x2 x3 : paco_class (paco4_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3) :=
{ pacoacc    := paco4_2_1_acc gf_0 gf_1;
  pacomult   := paco4_2_1_mult gf_0 gf_1;
  pacofold   := paco4_2_1_fold gf_0 gf_1;
  pacounfold := paco4_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg4_3.

Definition monotone4_3 T0 T1 T2 T3 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall x0 x1 x2 x3 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3) (LE_0: r_0 <4= r'_0)(LE_1: r_1 <4= r'_1)(LE_2: r_2 <4= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco4_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <4= rr) (CIH: l <_paco_4= rr), l <_paco_4= paco4_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <4= paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco4_3_0 gf_0 gf_1 gf_2 (r_0 \4/ l) r_1 r_2 x0 x1 x2 x3) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <4= rr) (CIH: l <_paco_4= rr), l <_paco_4= paco4_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco4_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \4/ l) r_2 x0 x1 x2 x3) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <4= rr) (CIH: l <_paco_4= rr), l <_paco_4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \4/ l) x0 x1 x2 x3) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4_3_0_mon: monotone4_3 (paco4_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_3_1_mon: monotone4_3 (paco4_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_3_2_mon: monotone4_3 (paco4_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_3_0_mult_strong: forall r_0 r_1 r_2,
  paco4_3_0 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_3_1_mult_strong: forall r_0 r_1 r_2,
  paco4_3_1 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4_3_2_mult_strong: forall r_0 r_1 r_2,
  paco4_3_2 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Corollary paco4_3_0_mult: forall r_0 r_1 r_2,
  paco4_3_0 gf_0 gf_1 gf_2 (paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco4_3_0_mult_strong, paco4_3_0_mon; eauto. Qed.

Corollary paco4_3_1_mult: forall r_0 r_1 r_2,
  paco4_3_1 gf_0 gf_1 gf_2 (paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco4_3_1_mult_strong, paco4_3_1_mon; eauto. Qed.

Corollary paco4_3_2_mult: forall r_0 r_1 r_2,
  paco4_3_2 gf_0 gf_1 gf_2 (paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco4_3_2_mult_strong, paco4_3_2_mon; eauto. Qed.

Theorem paco4_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco4_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco4_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco4_3_0_unfold: forall (MON: monotone4_3 gf_0) (MON: monotone4_3 gf_1) (MON: monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4= gf_0 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone4_3; intros; destruct PR; eauto. Qed.

Theorem paco4_3_1_unfold: forall (MON: monotone4_3 gf_0) (MON: monotone4_3 gf_1) (MON: monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4= gf_1 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone4_3; intros; destruct PR; eauto. Qed.

Theorem paco4_3_2_unfold: forall (MON: monotone4_3 gf_0) (MON: monotone4_3 gf_1) (MON: monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4= gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone4_3; intros; destruct PR; eauto. Qed.

End Arg4_3.

Hint Unfold monotone4_3.
Hint Resolve paco4_3_0_fold.
Hint Resolve paco4_3_1_fold.
Hint Resolve paco4_3_2_fold.

Implicit Arguments paco4_3_0_acc            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_1_acc            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_2_acc            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_0_mon            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_1_mon            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_2_mon            [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_0_mult_strong    [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_1_mult_strong    [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_2_mult_strong    [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_0_mult           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_1_mult           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_2_mult           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_0_fold           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_1_fold           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_2_fold           [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_0_unfold         [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_1_unfold         [ T0 T1 T2 T3 ].
Implicit Arguments paco4_3_2_unfold         [ T0 T1 T2 T3 ].

Instance paco4_3_0_inst  T0 T1 T2 T3 (gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3->_) r_0 r_1 r_2 x0 x1 x2 x3 : paco_class (paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3) :=
{ pacoacc    := paco4_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco4_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco4_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco4_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco4_3_1_inst  T0 T1 T2 T3 (gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3->_) r_0 r_1 r_2 x0 x1 x2 x3 : paco_class (paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3) :=
{ pacoacc    := paco4_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco4_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco4_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco4_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco4_3_2_inst  T0 T1 T2 T3 (gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3->_) r_0 r_1 r_2 x0 x1 x2 x3 : paco_class (paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3) :=
{ pacoacc    := paco4_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco4_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco4_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco4_3_2_unfold gf_0 gf_1 gf_2 }.

