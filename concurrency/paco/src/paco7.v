Require Export VST.concurrency.paco.src.paconotation VST.concurrency.paco.src.pacotac VST.concurrency.paco.src.pacodef VST.concurrency.paco.src.pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 7
*)

(** 1 Mutual Coinduction *)

Section Arg7_1.

Definition monotone7 T0 T1 T2 T3 T4 T5 T6 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall x0 x1 x2 x3 x4 x5 x6 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6) (LE: r <7= r'), gf r' x0 x1 x2 x3 x4 x5 x6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Implicit Arguments gf [].

Theorem paco7_acc: forall
  l r (OBG: forall rr (INC: r <7= rr) (CIH: l <_paco_7= rr), l <_paco_7= paco7 gf rr),
  l <7= paco7 gf r.
Proof.
  intros; assert (SIM: paco7 gf (r \7/ l) x0 x1 x2 x3 x4 x5 x6) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7_mon: monotone7 (paco7 gf).
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_mult_strong: forall r,
  paco7 gf (upaco7 gf r) <7= paco7 gf r.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Corollary paco7_mult: forall r,
  paco7 gf (paco7 gf r) <7= paco7 gf r.
Proof. intros; eapply paco7_mult_strong, paco7_mon; eauto. Qed.

Theorem paco7_fold: forall r,
  gf (upaco7 gf r) <7= paco7 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco7_unfold: forall (MON: monotone7 gf) r,
  paco7 gf r <7= gf (upaco7 gf r).
Proof. unfold monotone7; intros; destruct PR; eauto. Qed.

End Arg7_1.

Hint Unfold monotone7.
Hint Resolve paco7_fold.

Implicit Arguments paco7_acc            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_mon            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_mult           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_fold           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_unfold         [ T0 T1 T2 T3 T4 T5 T6 ].

Instance paco7_inst  T0 T1 T2 T3 T4 T5 T6 (gf : rel7 T0 T1 T2 T3 T4 T5 T6->_) r x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7 gf r x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_acc gf;
  pacomult   := paco7_mult gf;
  pacofold   := paco7_fold gf;
  pacounfold := paco7_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg7_2.

Definition monotone7_2 T0 T1 T2 T3 T4 T5 T6 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall x0 x1 x2 x3 x4 x5 x6 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6) (LE_0: r_0 <7= r'_0)(LE_1: r_1 <7= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable gf_0 gf_1 : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco7_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <7= rr) (CIH: l <_paco_7= rr), l <_paco_7= paco7_2_0 gf_0 gf_1 rr r_1),
  l <7= paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco7_2_0 gf_0 gf_1 (r_0 \7/ l) r_1 x0 x1 x2 x3 x4 x5 x6) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <7= rr) (CIH: l <_paco_7= rr), l <_paco_7= paco7_2_1 gf_0 gf_1 r_0 rr),
  l <7= paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco7_2_1 gf_0 gf_1 r_0 (r_1 \7/ l) x0 x1 x2 x3 x4 x5 x6) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7_2_0_mon: monotone7_2 (paco7_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_2_1_mon: monotone7_2 (paco7_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_2_0_mult_strong: forall r_0 r_1,
  paco7_2_0 gf_0 gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_2_1_mult_strong: forall r_0 r_1,
  paco7_2_1 gf_0 gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Corollary paco7_2_0_mult: forall r_0 r_1,
  paco7_2_0 gf_0 gf_1 (paco7_2_0 gf_0 gf_1 r_0 r_1) (paco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco7_2_0_mult_strong, paco7_2_0_mon; eauto. Qed.

Corollary paco7_2_1_mult: forall r_0 r_1,
  paco7_2_1 gf_0 gf_1 (paco7_2_0 gf_0 gf_1 r_0 r_1) (paco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco7_2_1_mult_strong, paco7_2_1_mon; eauto. Qed.

Theorem paco7_2_0_fold: forall r_0 r_1,
  gf_0 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco7_2_1_fold: forall r_0 r_1,
  gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco7_2_0_unfold: forall (MON: monotone7_2 gf_0) (MON: monotone7_2 gf_1) r_0 r_1,
  paco7_2_0 gf_0 gf_1 r_0 r_1 <7= gf_0 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone7_2; intros; destruct PR; eauto. Qed.

Theorem paco7_2_1_unfold: forall (MON: monotone7_2 gf_0) (MON: monotone7_2 gf_1) r_0 r_1,
  paco7_2_1 gf_0 gf_1 r_0 r_1 <7= gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone7_2; intros; destruct PR; eauto. Qed.

End Arg7_2.

Hint Unfold monotone7_2.
Hint Resolve paco7_2_0_fold.
Hint Resolve paco7_2_1_fold.

Implicit Arguments paco7_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 ].

Instance paco7_2_0_inst  T0 T1 T2 T3 T4 T5 T6 (gf_0 gf_1 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_2_0_acc gf_0 gf_1;
  pacomult   := paco7_2_0_mult gf_0 gf_1;
  pacofold   := paco7_2_0_fold gf_0 gf_1;
  pacounfold := paco7_2_0_unfold gf_0 gf_1 }.

Instance paco7_2_1_inst  T0 T1 T2 T3 T4 T5 T6 (gf_0 gf_1 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_2_1_acc gf_0 gf_1;
  pacomult   := paco7_2_1_mult gf_0 gf_1;
  pacofold   := paco7_2_1_fold gf_0 gf_1;
  pacounfold := paco7_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg7_3.

Definition monotone7_3 T0 T1 T2 T3 T4 T5 T6 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall x0 x1 x2 x3 x4 x5 x6 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6) (LE_0: r_0 <7= r'_0)(LE_1: r_1 <7= r'_1)(LE_2: r_2 <7= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco7_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <7= rr) (CIH: l <_paco_7= rr), l <_paco_7= paco7_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <7= paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco7_3_0 gf_0 gf_1 gf_2 (r_0 \7/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <7= rr) (CIH: l <_paco_7= rr), l <_paco_7= paco7_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco7_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \7/ l) r_2 x0 x1 x2 x3 x4 x5 x6) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <7= rr) (CIH: l <_paco_7= rr), l <_paco_7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \7/ l) x0 x1 x2 x3 x4 x5 x6) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7_3_0_mon: monotone7_3 (paco7_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_3_1_mon: monotone7_3 (paco7_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_3_2_mon: monotone7_3 (paco7_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_3_0_mult_strong: forall r_0 r_1 r_2,
  paco7_3_0 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_3_1_mult_strong: forall r_0 r_1 r_2,
  paco7_3_1 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7_3_2_mult_strong: forall r_0 r_1 r_2,
  paco7_3_2 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Corollary paco7_3_0_mult: forall r_0 r_1 r_2,
  paco7_3_0 gf_0 gf_1 gf_2 (paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco7_3_0_mult_strong, paco7_3_0_mon; eauto. Qed.

Corollary paco7_3_1_mult: forall r_0 r_1 r_2,
  paco7_3_1 gf_0 gf_1 gf_2 (paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco7_3_1_mult_strong, paco7_3_1_mon; eauto. Qed.

Corollary paco7_3_2_mult: forall r_0 r_1 r_2,
  paco7_3_2 gf_0 gf_1 gf_2 (paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco7_3_2_mult_strong, paco7_3_2_mon; eauto. Qed.

Theorem paco7_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco7_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco7_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco7_3_0_unfold: forall (MON: monotone7_3 gf_0) (MON: monotone7_3 gf_1) (MON: monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7= gf_0 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone7_3; intros; destruct PR; eauto. Qed.

Theorem paco7_3_1_unfold: forall (MON: monotone7_3 gf_0) (MON: monotone7_3 gf_1) (MON: monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7= gf_1 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone7_3; intros; destruct PR; eauto. Qed.

Theorem paco7_3_2_unfold: forall (MON: monotone7_3 gf_0) (MON: monotone7_3 gf_1) (MON: monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7= gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone7_3; intros; destruct PR; eauto. Qed.

End Arg7_3.

Hint Unfold monotone7_3.
Hint Resolve paco7_3_0_fold.
Hint Resolve paco7_3_1_fold.
Hint Resolve paco7_3_2_fold.

Implicit Arguments paco7_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 ].
Implicit Arguments paco7_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 ].

Instance paco7_3_0_inst  T0 T1 T2 T3 T4 T5 T6 (gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco7_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco7_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco7_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco7_3_1_inst  T0 T1 T2 T3 T4 T5 T6 (gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco7_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco7_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco7_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco7_3_2_inst  T0 T1 T2 T3 T4 T5 T6 (gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco7_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco7_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco7_3_2_unfold gf_0 gf_1 gf_2 }.

