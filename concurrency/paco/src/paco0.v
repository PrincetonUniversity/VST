Require Export VST.concurrency.paco.src.paconotation VST.concurrency.paco.src.pacotac VST.concurrency.paco.src.pacodef VST.concurrency.paco.src.pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 0
*)

(** 1 Mutual Coinduction *)

Section Arg0_1.

Definition monotone0 (gf: rel0 -> rel0) :=
  forall r r' (IN: gf r) (LE: r <0= r'), gf r'.

Variable gf : rel0 -> rel0.
Implicit Arguments gf [].

Theorem paco0_acc: forall
  l r (OBG: forall rr (INC: r <0= rr) (CIH: l <_paco_0= rr), l <_paco_0= paco0 gf rr),
  l <0= paco0 gf r.
Proof.
  intros; assert (SIM: paco0 gf (r \0/ l)) by eauto.
  clear PR; repeat (try left; do 1 paco_revert; paco_cofix_auto).
Qed.

Theorem paco0_mon: monotone0 (paco0 gf).
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_mult_strong: forall r,
  paco0 gf (upaco0 gf r) <0= paco0 gf r.
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Corollary paco0_mult: forall r,
  paco0 gf (paco0 gf r) <0= paco0 gf r.
Proof. intros; eapply paco0_mult_strong, paco0_mon; eauto. Qed.

Theorem paco0_fold: forall r,
  gf (upaco0 gf r) <0= paco0 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco0_unfold: forall (MON: monotone0 gf) r,
  paco0 gf r <0= gf (upaco0 gf r).
Proof. unfold monotone0; intros; destruct PR; eauto. Qed.

End Arg0_1.

Hint Unfold monotone0.
Hint Resolve paco0_fold.

Implicit Arguments paco0_acc            [ ].
Implicit Arguments paco0_mon            [ ].
Implicit Arguments paco0_mult_strong    [ ].
Implicit Arguments paco0_mult           [ ].
Implicit Arguments paco0_fold           [ ].
Implicit Arguments paco0_unfold         [ ].

Instance paco0_inst  (gf : rel0->_) r : paco_class (paco0 gf r) :=
{ pacoacc    := paco0_acc gf;
  pacomult   := paco0_mult gf;
  pacofold   := paco0_fold gf;
  pacounfold := paco0_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg0_2.

Definition monotone0_2 (gf: rel0 -> rel0 -> rel0) :=
  forall r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1) (LE_0: r_0 <0= r'_0)(LE_1: r_1 <0= r'_1), gf r'_0 r'_1.

Variable gf_0 gf_1 : rel0 -> rel0 -> rel0.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco0_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <0= rr) (CIH: l <_paco_0= rr), l <_paco_0= paco0_2_0 gf_0 gf_1 rr r_1),
  l <0= paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco0_2_0 gf_0 gf_1 (r_0 \0/ l) r_1) by eauto.
  clear PR; repeat (try left; do 1 paco_revert; paco_cofix_auto).
Qed.

Theorem paco0_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <0= rr) (CIH: l <_paco_0= rr), l <_paco_0= paco0_2_1 gf_0 gf_1 r_0 rr),
  l <0= paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco0_2_1 gf_0 gf_1 r_0 (r_1 \0/ l)) by eauto.
  clear PR; repeat (try left; do 1 paco_revert; paco_cofix_auto).
Qed.

Theorem paco0_2_0_mon: monotone0_2 (paco0_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_2_1_mon: monotone0_2 (paco0_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_2_0_mult_strong: forall r_0 r_1,
  paco0_2_0 gf_0 gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_2_1_mult_strong: forall r_0 r_1,
  paco0_2_1 gf_0 gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Corollary paco0_2_0_mult: forall r_0 r_1,
  paco0_2_0 gf_0 gf_1 (paco0_2_0 gf_0 gf_1 r_0 r_1) (paco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco0_2_0_mult_strong, paco0_2_0_mon; eauto. Qed.

Corollary paco0_2_1_mult: forall r_0 r_1,
  paco0_2_1 gf_0 gf_1 (paco0_2_0 gf_0 gf_1 r_0 r_1) (paco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco0_2_1_mult_strong, paco0_2_1_mon; eauto. Qed.

Theorem paco0_2_0_fold: forall r_0 r_1,
  gf_0 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco0_2_1_fold: forall r_0 r_1,
  gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco0_2_0_unfold: forall (MON: monotone0_2 gf_0) (MON: monotone0_2 gf_1) r_0 r_1,
  paco0_2_0 gf_0 gf_1 r_0 r_1 <0= gf_0 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone0_2; intros; destruct PR; eauto. Qed.

Theorem paco0_2_1_unfold: forall (MON: monotone0_2 gf_0) (MON: monotone0_2 gf_1) r_0 r_1,
  paco0_2_1 gf_0 gf_1 r_0 r_1 <0= gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone0_2; intros; destruct PR; eauto. Qed.

End Arg0_2.

Hint Unfold monotone0_2.
Hint Resolve paco0_2_0_fold.
Hint Resolve paco0_2_1_fold.

Implicit Arguments paco0_2_0_acc            [ ].
Implicit Arguments paco0_2_1_acc            [ ].
Implicit Arguments paco0_2_0_mon            [ ].
Implicit Arguments paco0_2_1_mon            [ ].
Implicit Arguments paco0_2_0_mult_strong    [ ].
Implicit Arguments paco0_2_1_mult_strong    [ ].
Implicit Arguments paco0_2_0_mult           [ ].
Implicit Arguments paco0_2_1_mult           [ ].
Implicit Arguments paco0_2_0_fold           [ ].
Implicit Arguments paco0_2_1_fold           [ ].
Implicit Arguments paco0_2_0_unfold         [ ].
Implicit Arguments paco0_2_1_unfold         [ ].

Instance paco0_2_0_inst  (gf_0 gf_1 : rel0->_) r_0 r_1 : paco_class (paco0_2_0 gf_0 gf_1 r_0 r_1) :=
{ pacoacc    := paco0_2_0_acc gf_0 gf_1;
  pacomult   := paco0_2_0_mult gf_0 gf_1;
  pacofold   := paco0_2_0_fold gf_0 gf_1;
  pacounfold := paco0_2_0_unfold gf_0 gf_1 }.

Instance paco0_2_1_inst  (gf_0 gf_1 : rel0->_) r_0 r_1 : paco_class (paco0_2_1 gf_0 gf_1 r_0 r_1) :=
{ pacoacc    := paco0_2_1_acc gf_0 gf_1;
  pacomult   := paco0_2_1_mult gf_0 gf_1;
  pacofold   := paco0_2_1_fold gf_0 gf_1;
  pacounfold := paco0_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg0_3.

Definition monotone0_3 (gf: rel0 -> rel0 -> rel0 -> rel0) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2) (LE_0: r_0 <0= r'_0)(LE_1: r_1 <0= r'_1)(LE_2: r_2 <0= r'_2), gf r'_0 r'_1 r'_2.

Variable gf_0 gf_1 gf_2 : rel0 -> rel0 -> rel0 -> rel0.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco0_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <0= rr) (CIH: l <_paco_0= rr), l <_paco_0= paco0_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <0= paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco0_3_0 gf_0 gf_1 gf_2 (r_0 \0/ l) r_1 r_2) by eauto.
  clear PR; repeat (try left; do 1 paco_revert; paco_cofix_auto).
Qed.

Theorem paco0_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <0= rr) (CIH: l <_paco_0= rr), l <_paco_0= paco0_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco0_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \0/ l) r_2) by eauto.
  clear PR; repeat (try left; do 1 paco_revert; paco_cofix_auto).
Qed.

Theorem paco0_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <0= rr) (CIH: l <_paco_0= rr), l <_paco_0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \0/ l)) by eauto.
  clear PR; repeat (try left; do 1 paco_revert; paco_cofix_auto).
Qed.

Theorem paco0_3_0_mon: monotone0_3 (paco0_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_3_1_mon: monotone0_3 (paco0_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_3_2_mon: monotone0_3 (paco0_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_3_0_mult_strong: forall r_0 r_1 r_2,
  paco0_3_0 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_3_1_mult_strong: forall r_0 r_1 r_2,
  paco0_3_1 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Theorem paco0_3_2_mult_strong: forall r_0 r_1 r_2,
  paco0_3_2 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 1 paco_revert; paco_cofix_auto). Qed.

Corollary paco0_3_0_mult: forall r_0 r_1 r_2,
  paco0_3_0 gf_0 gf_1 gf_2 (paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco0_3_0_mult_strong, paco0_3_0_mon; eauto. Qed.

Corollary paco0_3_1_mult: forall r_0 r_1 r_2,
  paco0_3_1 gf_0 gf_1 gf_2 (paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco0_3_1_mult_strong, paco0_3_1_mon; eauto. Qed.

Corollary paco0_3_2_mult: forall r_0 r_1 r_2,
  paco0_3_2 gf_0 gf_1 gf_2 (paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco0_3_2_mult_strong, paco0_3_2_mon; eauto. Qed.

Theorem paco0_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco0_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco0_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco0_3_0_unfold: forall (MON: monotone0_3 gf_0) (MON: monotone0_3 gf_1) (MON: monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0= gf_0 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone0_3; intros; destruct PR; eauto. Qed.

Theorem paco0_3_1_unfold: forall (MON: monotone0_3 gf_0) (MON: monotone0_3 gf_1) (MON: monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0= gf_1 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone0_3; intros; destruct PR; eauto. Qed.

Theorem paco0_3_2_unfold: forall (MON: monotone0_3 gf_0) (MON: monotone0_3 gf_1) (MON: monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0= gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone0_3; intros; destruct PR; eauto. Qed.

End Arg0_3.

Hint Unfold monotone0_3.
Hint Resolve paco0_3_0_fold.
Hint Resolve paco0_3_1_fold.
Hint Resolve paco0_3_2_fold.

Implicit Arguments paco0_3_0_acc            [ ].
Implicit Arguments paco0_3_1_acc            [ ].
Implicit Arguments paco0_3_2_acc            [ ].
Implicit Arguments paco0_3_0_mon            [ ].
Implicit Arguments paco0_3_1_mon            [ ].
Implicit Arguments paco0_3_2_mon            [ ].
Implicit Arguments paco0_3_0_mult_strong    [ ].
Implicit Arguments paco0_3_1_mult_strong    [ ].
Implicit Arguments paco0_3_2_mult_strong    [ ].
Implicit Arguments paco0_3_0_mult           [ ].
Implicit Arguments paco0_3_1_mult           [ ].
Implicit Arguments paco0_3_2_mult           [ ].
Implicit Arguments paco0_3_0_fold           [ ].
Implicit Arguments paco0_3_1_fold           [ ].
Implicit Arguments paco0_3_2_fold           [ ].
Implicit Arguments paco0_3_0_unfold         [ ].
Implicit Arguments paco0_3_1_unfold         [ ].
Implicit Arguments paco0_3_2_unfold         [ ].

Instance paco0_3_0_inst  (gf_0 gf_1 gf_2 : rel0->_) r_0 r_1 r_2 : paco_class (paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) :=
{ pacoacc    := paco0_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco0_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco0_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco0_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco0_3_1_inst  (gf_0 gf_1 gf_2 : rel0->_) r_0 r_1 r_2 : paco_class (paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) :=
{ pacoacc    := paco0_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco0_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco0_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco0_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco0_3_2_inst  (gf_0 gf_1 gf_2 : rel0->_) r_0 r_1 r_2 : paco_class (paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) :=
{ pacoacc    := paco0_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco0_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco0_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco0_3_2_unfold gf_0 gf_1 gf_2 }.

