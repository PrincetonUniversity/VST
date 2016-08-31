Require Import msl.base.

Program Definition sig_sig_iff {A: Type} {P Q: A -> Prop}
  (H: forall a, P a <-> Q a) (x: sig P): sig Q := x.
Next Obligation.
  rewrite <- H; auto.
Defined.

Program Definition sig_sig_iff' {A: Type} {P Q: A -> Prop}
  (H: forall a, P a <-> Q a) (x: sig Q): sig P := x.
Next Obligation.
  rewrite H; auto.
Defined.

Program Definition sig_sig_eq {A: Type} {P Q: A -> Prop}
  (H: forall a, P a = Q a) (x: sig P): sig Q := x.
Next Obligation.
  rewrite <- H; auto.
Defined.

Program Definition sig_sig_eq' {A: Type} {P Q: A -> Prop}
  (H: forall a, P a = Q a) (x: sig Q): sig P := x.
Next Obligation.
  rewrite H; auto.
Defined.

Program Definition sigsig_sig {A: Type} {P Q: A -> Prop}
  (x: sig (fun x: sig P => Q (proj1_sig x))): sig (fun x => P x /\ Q x) := x.

Program Definition sig_sigsig {A: Type} {P Q: A -> Prop}
  (x: sig (fun x => P x /\ Q x)): sig (fun x: sig P => Q (proj1_sig x)) := x.

Lemma sig_sig_iff_iff': forall {A: Type} {P Q: A -> Prop}
  (H: forall a, P a <-> Q a) x,
  (sig_sig_iff H) (sig_sig_iff' H x) = x.
Proof.
  intros.
  unfold sig_sig_iff, sig_sig_iff'; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sig_iff'_iff: forall {A: Type} {P Q: A -> Prop}
  (H: forall a, P a <-> Q a) x,
  (sig_sig_iff' H) (sig_sig_iff H x) = x.
Proof.
  intros.
  unfold sig_sig_iff, sig_sig_iff'; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sig_eq_eq': forall {A: Type} {P Q: A -> Prop}
  (H: forall a, P a = Q a) x,
  (sig_sig_eq H) (sig_sig_eq' H x) = x.
Proof.
  intros.
  unfold sig_sig_eq, sig_sig_eq'; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sig_eq'_eq: forall {A: Type} {P Q: A -> Prop}
  (H: forall a, P a = Q a) x,
  (sig_sig_eq' H) (sig_sig_eq H x) = x.
Proof.
  intros.
  unfold sig_sig_iff, sig_sig_iff'; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sigsig_sig: forall {A: Type} {P Q: A -> Prop} x,
  @sig_sigsig A P Q (@sigsig_sig A P Q x) = x.
Proof.
  intros.
  unfold sig_sigsig, sigsig_sig; simpl.
  destruct x as [[x ?] ?]; simpl.
  apply exist_ext; auto.
Qed.

Lemma sigsig_sig_sigsig: forall {A: Type} {P Q: A -> Prop} x,
  @sigsig_sig A P Q (@sig_sigsig A P Q x) = x.
Proof.
  intros.
  unfold sig_sigsig, sigsig_sig; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sig_iff_iff'_id: forall {A: Type} {P Q: A -> Prop}
  (H: forall a, P a <-> Q a),
  (sig_sig_iff H) oo (sig_sig_iff' H) = id _.
Proof.
  intros.
  extensionality.
  unfold id, compose, sig_sig_iff, sig_sig_iff'; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sig_iff'_iff_id: forall {A: Type} {P Q: A -> Prop}
  (H: forall a, P a <-> Q a),
  (sig_sig_iff' H) oo (sig_sig_iff H) = id _.
Proof.
  intros.
  extensionality.
  unfold id, compose, sig_sig_iff, sig_sig_iff'; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sig_eq_eq'_id: forall {A: Type} {P Q: A -> Prop}
  (H: forall a, P a = Q a),
  (sig_sig_eq H) oo (sig_sig_eq' H) = id _.
Proof.
  intros.
  extensionality.
  unfold id, compose, sig_sig_eq, sig_sig_eq'; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sig_eq'_eq_id: forall {A: Type} {P Q: A -> Prop}
  (H: forall a, P a = Q a),
  (sig_sig_eq' H) oo (sig_sig_eq H) = id _.
Proof.
  intros.
  extensionality.
  unfold id, compose, sig_sig_iff, sig_sig_iff'; simpl.
  apply exist_ext'; auto.
Qed.

Lemma sig_sigsig_sig_id: forall {A: Type} {P Q: A -> Prop},
  sig_sigsig oo (@sigsig_sig A P Q) = id _.
Proof.
  intros.
  extensionality.
  unfold id, compose, sig_sigsig, sigsig_sig; simpl.
  destruct x as [[x ?] ?]; simpl.
  apply exist_ext; auto.
Qed.

Lemma sigsig_sig_sigsig_id: forall {A: Type} {P Q: A -> Prop},
  sigsig_sig oo (@sig_sigsig A P Q) = id _.
Proof.
  intros.
  extensionality.
  unfold id, compose, sig_sigsig, sigsig_sig; simpl.
  apply exist_ext'; auto.
Qed.
