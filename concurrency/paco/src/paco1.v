Require Export VST.concurrency.paco.src.paconotation VST.concurrency.paco.src.pacotac VST.concurrency.paco.src.pacodef VST.concurrency.paco.src.pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 1
*)

(** 1 Mutual Coinduction *)

Section Arg1_1.

Definition monotone1 T0 (gf: rel1 T0 -> rel1 T0) :=
  forall x0 r r' (IN: gf r x0) (LE: r <1= r'), gf r' x0.

Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Implicit Arguments gf [].

Theorem paco1_acc: forall
  l r (OBG: forall rr (INC: r <1= rr) (CIH: l <_paco_1= rr), l <_paco_1= paco1 gf rr),
  l <1= paco1 gf r.
Proof.
  intros; assert (SIM: paco1 gf (r \1/ l) x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1_mon: monotone1 (paco1 gf).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_mult_strong: forall r,
  paco1 gf (upaco1 gf r) <1= paco1 gf r.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Corollary paco1_mult: forall r,
  paco1 gf (paco1 gf r) <1= paco1 gf r.
Proof. intros; eapply paco1_mult_strong, paco1_mon; eauto. Qed.

Theorem paco1_fold: forall r,
  gf (upaco1 gf r) <1= paco1 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco1_unfold: forall (MON: monotone1 gf) r,
  paco1 gf r <1= gf (upaco1 gf r).
Proof. unfold monotone1; intros; destruct PR; eauto. Qed.

End Arg1_1.

Hint Unfold monotone1.
Hint Resolve paco1_fold.

Implicit Arguments paco1_acc            [ T0 ].
Implicit Arguments paco1_mon            [ T0 ].
Implicit Arguments paco1_mult_strong    [ T0 ].
Implicit Arguments paco1_mult           [ T0 ].
Implicit Arguments paco1_fold           [ T0 ].
Implicit Arguments paco1_unfold         [ T0 ].

Instance paco1_inst  T0 (gf : rel1 T0->_) r x0 : paco_class (paco1 gf r x0) :=
{ pacoacc    := paco1_acc gf;
  pacomult   := paco1_mult gf;
  pacofold   := paco1_fold gf;
  pacounfold := paco1_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg1_2.

Definition monotone1_2 T0 (gf: rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall x0 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0) (LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1), gf r'_0 r'_1 x0.

Variable T0 : Type.
Variable gf_0 gf_1 : rel1 T0 -> rel1 T0 -> rel1 T0.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco1_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <1= rr) (CIH: l <_paco_1= rr), l <_paco_1= paco1_2_0 gf_0 gf_1 rr r_1),
  l <1= paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco1_2_0 gf_0 gf_1 (r_0 \1/ l) r_1 x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <1= rr) (CIH: l <_paco_1= rr), l <_paco_1= paco1_2_1 gf_0 gf_1 r_0 rr),
  l <1= paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco1_2_1 gf_0 gf_1 r_0 (r_1 \1/ l) x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1_2_0_mon: monotone1_2 (paco1_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_2_1_mon: monotone1_2 (paco1_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_2_0_mult_strong: forall r_0 r_1,
  paco1_2_0 gf_0 gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_2_1_mult_strong: forall r_0 r_1,
  paco1_2_1 gf_0 gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Corollary paco1_2_0_mult: forall r_0 r_1,
  paco1_2_0 gf_0 gf_1 (paco1_2_0 gf_0 gf_1 r_0 r_1) (paco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco1_2_0_mult_strong, paco1_2_0_mon; eauto. Qed.

Corollary paco1_2_1_mult: forall r_0 r_1,
  paco1_2_1 gf_0 gf_1 (paco1_2_0 gf_0 gf_1 r_0 r_1) (paco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco1_2_1_mult_strong, paco1_2_1_mon; eauto. Qed.

Theorem paco1_2_0_fold: forall r_0 r_1,
  gf_0 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco1_2_1_fold: forall r_0 r_1,
  gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco1_2_0_unfold: forall (MON: monotone1_2 gf_0) (MON: monotone1_2 gf_1) r_0 r_1,
  paco1_2_0 gf_0 gf_1 r_0 r_1 <1= gf_0 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone1_2; intros; destruct PR; eauto. Qed.

Theorem paco1_2_1_unfold: forall (MON: monotone1_2 gf_0) (MON: monotone1_2 gf_1) r_0 r_1,
  paco1_2_1 gf_0 gf_1 r_0 r_1 <1= gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone1_2; intros; destruct PR; eauto. Qed.

End Arg1_2.

Hint Unfold monotone1_2.
Hint Resolve paco1_2_0_fold.
Hint Resolve paco1_2_1_fold.

Implicit Arguments paco1_2_0_acc            [ T0 ].
Implicit Arguments paco1_2_1_acc            [ T0 ].
Implicit Arguments paco1_2_0_mon            [ T0 ].
Implicit Arguments paco1_2_1_mon            [ T0 ].
Implicit Arguments paco1_2_0_mult_strong    [ T0 ].
Implicit Arguments paco1_2_1_mult_strong    [ T0 ].
Implicit Arguments paco1_2_0_mult           [ T0 ].
Implicit Arguments paco1_2_1_mult           [ T0 ].
Implicit Arguments paco1_2_0_fold           [ T0 ].
Implicit Arguments paco1_2_1_fold           [ T0 ].
Implicit Arguments paco1_2_0_unfold         [ T0 ].
Implicit Arguments paco1_2_1_unfold         [ T0 ].

Instance paco1_2_0_inst  T0 (gf_0 gf_1 : rel1 T0->_) r_0 r_1 x0 : paco_class (paco1_2_0 gf_0 gf_1 r_0 r_1 x0) :=
{ pacoacc    := paco1_2_0_acc gf_0 gf_1;
  pacomult   := paco1_2_0_mult gf_0 gf_1;
  pacofold   := paco1_2_0_fold gf_0 gf_1;
  pacounfold := paco1_2_0_unfold gf_0 gf_1 }.

Instance paco1_2_1_inst  T0 (gf_0 gf_1 : rel1 T0->_) r_0 r_1 x0 : paco_class (paco1_2_1 gf_0 gf_1 r_0 r_1 x0) :=
{ pacoacc    := paco1_2_1_acc gf_0 gf_1;
  pacomult   := paco1_2_1_mult gf_0 gf_1;
  pacofold   := paco1_2_1_fold gf_0 gf_1;
  pacounfold := paco1_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg1_3.

Definition monotone1_3 T0 (gf: rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall x0 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0) (LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1)(LE_2: r_2 <1= r'_2), gf r'_0 r'_1 r'_2 x0.

Variable T0 : Type.
Variable gf_0 gf_1 gf_2 : rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco1_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <1= rr) (CIH: l <_paco_1= rr), l <_paco_1= paco1_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <1= paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco1_3_0 gf_0 gf_1 gf_2 (r_0 \1/ l) r_1 r_2 x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <1= rr) (CIH: l <_paco_1= rr), l <_paco_1= paco1_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco1_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \1/ l) r_2 x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <1= rr) (CIH: l <_paco_1= rr), l <_paco_1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \1/ l) x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1_3_0_mon: monotone1_3 (paco1_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_3_1_mon: monotone1_3 (paco1_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_3_2_mon: monotone1_3 (paco1_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_3_0_mult_strong: forall r_0 r_1 r_2,
  paco1_3_0 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_3_1_mult_strong: forall r_0 r_1 r_2,
  paco1_3_1 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1_3_2_mult_strong: forall r_0 r_1 r_2,
  paco1_3_2 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Corollary paco1_3_0_mult: forall r_0 r_1 r_2,
  paco1_3_0 gf_0 gf_1 gf_2 (paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco1_3_0_mult_strong, paco1_3_0_mon; eauto. Qed.

Corollary paco1_3_1_mult: forall r_0 r_1 r_2,
  paco1_3_1 gf_0 gf_1 gf_2 (paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco1_3_1_mult_strong, paco1_3_1_mon; eauto. Qed.

Corollary paco1_3_2_mult: forall r_0 r_1 r_2,
  paco1_3_2 gf_0 gf_1 gf_2 (paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco1_3_2_mult_strong, paco1_3_2_mon; eauto. Qed.

Theorem paco1_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco1_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco1_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco1_3_0_unfold: forall (MON: monotone1_3 gf_0) (MON: monotone1_3 gf_1) (MON: monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_0 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone1_3; intros; destruct PR; eauto. Qed.

Theorem paco1_3_1_unfold: forall (MON: monotone1_3 gf_0) (MON: monotone1_3 gf_1) (MON: monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_1 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone1_3; intros; destruct PR; eauto. Qed.

Theorem paco1_3_2_unfold: forall (MON: monotone1_3 gf_0) (MON: monotone1_3 gf_1) (MON: monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone1_3; intros; destruct PR; eauto. Qed.

End Arg1_3.

Hint Unfold monotone1_3.
Hint Resolve paco1_3_0_fold.
Hint Resolve paco1_3_1_fold.
Hint Resolve paco1_3_2_fold.

Implicit Arguments paco1_3_0_acc            [ T0 ].
Implicit Arguments paco1_3_1_acc            [ T0 ].
Implicit Arguments paco1_3_2_acc            [ T0 ].
Implicit Arguments paco1_3_0_mon            [ T0 ].
Implicit Arguments paco1_3_1_mon            [ T0 ].
Implicit Arguments paco1_3_2_mon            [ T0 ].
Implicit Arguments paco1_3_0_mult_strong    [ T0 ].
Implicit Arguments paco1_3_1_mult_strong    [ T0 ].
Implicit Arguments paco1_3_2_mult_strong    [ T0 ].
Implicit Arguments paco1_3_0_mult           [ T0 ].
Implicit Arguments paco1_3_1_mult           [ T0 ].
Implicit Arguments paco1_3_2_mult           [ T0 ].
Implicit Arguments paco1_3_0_fold           [ T0 ].
Implicit Arguments paco1_3_1_fold           [ T0 ].
Implicit Arguments paco1_3_2_fold           [ T0 ].
Implicit Arguments paco1_3_0_unfold         [ T0 ].
Implicit Arguments paco1_3_1_unfold         [ T0 ].
Implicit Arguments paco1_3_2_unfold         [ T0 ].

Instance paco1_3_0_inst  T0 (gf_0 gf_1 gf_2 : rel1 T0->_) r_0 r_1 r_2 x0 : paco_class (paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0) :=
{ pacoacc    := paco1_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco1_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco1_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco1_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco1_3_1_inst  T0 (gf_0 gf_1 gf_2 : rel1 T0->_) r_0 r_1 r_2 x0 : paco_class (paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0) :=
{ pacoacc    := paco1_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco1_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco1_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco1_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco1_3_2_inst  T0 (gf_0 gf_1 gf_2 : rel1 T0->_) r_0 r_1 r_2 x0 : paco_class (paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0) :=
{ pacoacc    := paco1_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco1_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco1_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco1_3_2_unfold gf_0 gf_1 gf_2 }.

