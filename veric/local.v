Require Import VST.veric.base.
Require Import VST.msl.msl_standard.
Require Import Coq.Relations.Relations.

Definition deterministic_rel {T} (R: relation T) :=
  forall s s' s'', R s s' /\ R s s'' -> s'=s''.

Definition pfunc T R := T -> option R.

Definition address := nat.

Inductive val : Type :=
| Vint : nat -> val
| Vptr : address -> val
| Vundef.

(* Generic Operational Semantics *)
Class GenericSemantics
  (W : Type) (* Worlds *)
  (V : relation W -> Prop) (* Primitive commands *)
  (G : pfunc W val -> Prop) (* Primitive expressions *)
  : Type := mkGenericSem {
}.

Section Expressions.
Variables
  (W : Type)
  (G : pfunc W val -> Prop) (* Primitive expressions *).

Inductive unop := UNeg.

Inductive binop := BAdd.

Inductive expr : Type :=
| EVal : forall (v : val), expr
| EUnop : forall (op : unop) (e : expr), expr
| EBinop : forall (op : binop) (e1 e2 : expr), expr
| EPrim : forall (f : pfunc W val), expr.

Definition is_true (v : val) :=
  exists n, (v = Vint n \/ v = Vptr n) /\ n <> O.

Lemma is_true_dec : forall v, {is_true v} + {~ is_true v}.
Proof.
unfold is_true; intros.
destruct v.
destruct (eq_nat_dec n O).
right; intros Contra.
destruct Contra as [n' [H H0]]. inv H.
inv H1. elimtype False; auto.
inv H1.
left; eexists; split; eauto.
destruct (eq_nat_dec a 0).
right; intros Contra; auto.
destruct Contra as [n'' [H H0]]. inv H.
inv H1. inv H1. elimtype False; auto.
left; eexists; split; eauto.
right; intros Contra.
destruct Contra as [n' [H H0]]. inv H; inv H1.
Qed.

Definition unopDenote (op : unop) (v : val) : val :=
  match op, is_true_dec v with
    | UNeg, left _ => Vint 0
    | UNeg, right _ => Vint 1
  end.

Definition binopDenote (op : binop) (v1 v2 : val) :=
  match op, v1, v2 with
    | BAdd, (Vint n), (Vint m) => Vint (n+m)%nat
    | BAdd, (Vptr p), (Vint n) => Vptr (p+n)%nat
    | _, _, _ => Vundef
  end.

Fixpoint expr_wellformed (e : expr) : Prop :=
  match e with
    | EVal _ => True
    | EUnop _ e => expr_wellformed e
    | EBinop _ e1 e2 => expr_wellformed e1 /\ expr_wellformed e2
    | EPrim f => G f
  end.

Fixpoint exprEval' (e : expr) : W -> option val := fun w =>
  match e with
    | EVal v => Some v
    | EUnop op e' =>
      let v := exprEval' e' w in
        match v with
          | Some v' => Some (unopDenote op v')
          | None => None
        end
    | EBinop op e1 e2 =>
      let v1 := exprEval' e1 w in
      let v2 := exprEval' e2 w in
        match v1, v2 with
          | Some v1', Some v2' => Some (binopDenote op v1' v2')
          | _, _ => None
        end
    | EPrim f => f w
  end.

Definition exprEval (e : expr) (w : W) (v : val) :=
  expr_wellformed e /\ exprEval' e w = Some v.

Fixpoint pure_expr (e : expr) :=
  match e with
    | EVal v => True
    | EUnop op e' => pure_expr e'
    | EBinop op e1 e2 => pure_expr e1 /\ pure_expr e2
    | EPrim _ => False
  end.

Lemma pure_exprEval : forall e w w' b1 b2,
  pure_expr e
  -> exprEval e w b1
  -> exprEval e w' b2
  -> b1=b2.
Proof.
intros.
revert b1 b2 H H0 H1.
induction e; intros; inv H0; inv H1; simpl in * |-; try congruence.
case_eq (exprEval' e w); intros. rewrite H1 in H3; inv H3.
case_eq (exprEval' e w'); intros. rewrite H3 in H4; inv H4.
f_equal; apply IHe; auto||split; auto.
rewrite H3 in H4; inv H4.
rewrite H1 in H3; inv H3.
case_eq (exprEval' e1 w); intros. rewrite H1 in H3; inv H3.
case_eq (exprEval' e2 w); intros. rewrite H3 in H6; inv H6.
case_eq (exprEval' e1 w'); intros. rewrite H5 in H4; inv H4.
case_eq (exprEval' e2 w'); intros. rewrite H4 in H7; inv H7.
destruct H; destruct H2; destruct H0.
f_equal. apply IHe1; auto||split; auto.
         apply IHe2; auto||split; auto.
rewrite H4 in *; congruence.
rewrite H5 in *; congruence.
rewrite H3 in *; congruence.
rewrite H1 in *; congruence.
inv H.
Qed.

Lemma pure_expr_safe : forall e w,
  pure_expr e
  -> exists b, exprEval e w b.
Proof.
induction e; intros.
eexists; split; simpl; eauto.
simpl in *.
destruct (IHe w H) as [b [? ?]].
exists (unopDenote op b). split; simpl; auto||rewrite H1; auto.
simpl in *. destruct H.
destruct (IHe1 w H) as [b1 [? ?]].
destruct (IHe2 w H0) as [b2 [? ?]].
exists (binopDenote op b1 b2).
  split; simpl; auto||rewrite H2; rewrite H4; auto.
simpl in H; inv H.
Qed.

Lemma pure_expr_dec : forall e, {pure_expr e} + {~ pure_expr e}.
Proof.
intros.
induction e.
left; simpl; auto.
inv IHe.
left; simpl; auto.
right; simpl; auto.
inv IHe1; inv IHe2.
left; simpl; auto.
right; simpl; auto.
intros [? ?]; apply H0; auto.
right; simpl; auto.
intros [? ?]; apply H; auto.
right; simpl; auto.
intros [? ?]; apply H; auto.
right; auto.
Qed.
End Expressions.
Arguments exprEval' [W] _ _.
Arguments exprEval [W] _ _ _ _.
Arguments EUnop [W] _ _.
Arguments EUnop [W] _ _.
Arguments EBinop [W] _ _ _.
Arguments EPrim [W] _.

Section ExpressionErasure.
Variables
  (W S' : Type)
  (G : pfunc W val -> Prop)
  (F : pfunc S' val -> Prop)
  (GF : pfunc W val -> pfunc S' val -> Prop)

  (world_erase : W -> S')

  (primexpr_erasure : forall g f b1 b2 w s (Hgf : GF g f),
    world_erase w = s
    -> exprEval G (EPrim g) w b1
    -> exprEval F (EPrim f) s b2
    -> b1=b2)

  (primexpr_safety : forall g f b1 w s,
    GF g f
    -> world_erase w = s
    -> exprEval G (EPrim g) w b1
    -> exists b2, exprEval F (EPrim f) s b2).

Inductive expr_erase : expr W -> expr S' -> Prop :=
| erase_EVal : forall v,
     expr_erase (EVal _ v) (EVal _ v)
| erase_EUnop : forall op e e',
     expr_erase e e'
     -> expr_erase (EUnop op e) (EUnop op e')
| erase_EBinop : forall op e1 e2 e1' e2',
     expr_erase e1 e1'
     -> expr_erase e2 e2'
     -> expr_erase (EBinop op e1 e2) (EBinop op e1' e2')
| erase_EPrim : forall g f,
     GF g f
     -> expr_erase (EPrim g) (EPrim f).

Lemma expr_erase_pure_expr : forall e e',
  expr_erase e e'
  -> pure_expr _ e
  -> pure_expr _ e'.
Proof.
intros.
induction H; auto.
inv H0.
simpl; split; auto.
Qed.

Lemma expr_erasure : forall e e' w b1 b2,
  expr_erase e e'
  -> exprEval G e w b1
  -> exprEval F e' (world_erase w) b2
  -> b1=b2.
Proof.
intros.
revert b1 b2 H0 H1.
induction H; intros.
inv H0; inv H1; simpl in *; congruence.
inv H0; inv H1; simpl in *.
case_eq (exprEval' e w); intros. rewrite H1 in H3; inv H3.
case_eq (exprEval' e' (world_erase w)); intros. rewrite H3 in H4; inv H4.
f_equal. apply IHexpr_erase; auto||split; auto.
rewrite H3 in *; congruence.
rewrite H1 in *; congruence.
destruct H1; destruct H2; simpl in *.
case_eq (exprEval' e1 w); intros.
case_eq (exprEval' e2 w); intros.
rewrite H5 in *; rewrite H6 in *; inv H3.
case_eq (exprEval' e1' (world_erase w)); intros.
case_eq (exprEval' e2' (world_erase w)); intros.
rewrite H3 in *; rewrite H7 in *; inv H4.
destruct H1; destruct H2.
f_equal. apply IHexpr_erase1; auto||split; auto.
         apply IHexpr_erase2; auto||split; auto.
rewrite H3 in *. rewrite H7 in *. congruence.
rewrite H3 in *. congruence.
rewrite H5 in *. rewrite H6 in *. congruence.
rewrite H5 in *. congruence.
eapply primexpr_erasure; eauto.
Qed.

Lemma expr_safety : forall e e' w b1,
  expr_erase e e'
  -> exprEval G e w b1
  -> exists b2, exprEval F e' (world_erase w) b2.
Proof.
intros.
revert b1 H0.
induction H; simpl; intros.
eexists; eauto.
inv H0. simpl in *.
case_eq (exprEval' e w); intros.
rewrite H0 in H2.
assert (exprEval G e w v). split; auto.
destruct (IHexpr_erase v H3) as [b2 [? ?]].
exists (unopDenote op b2).
split; eauto.
simpl; rewrite H5; auto.
rewrite H0 in H2; inv H2.
inv H1; simpl in *.
case_eq (exprEval' e1 w); case_eq (exprEval' e2 w); intros.
rewrite H1 in *; rewrite H4 in *.
destruct H2.
destruct (IHexpr_erase1 v0). split; auto.
destruct (IHexpr_erase2 v). split; auto.
destruct H6; destruct H7.
exists (binopDenote op x x0); split; auto.
simpl. split; auto.
simpl. rewrite H9; rewrite H8. auto.
rewrite H4 in H3; rewrite H1 in H3; congruence.
rewrite H4 in H3; congruence.
rewrite H4 in H3; congruence.
eapply primexpr_safety; eauto.
Qed.
End ExpressionErasure.
Arguments expr_erase [W S'] _ _ _.


(* Here we define the syntax and operational semantics of generic semantics. *)
Section GenericSemanticsElaboration.
Context {W V G} `{GS : GenericSemantics W V G}.

Inductive stmt : Type :=
| Sprimcom: forall (u: relation W), stmt
| Sskip
| Sseq: forall (s1 s2: stmt), stmt
| Sifte: forall (e: expr W) (s1 s2: stmt), stmt
| Swhile: forall (e: expr W) (s: stmt), stmt.

Inductive ctl : Type := Kstop | Kseq: forall (s: stmt) (k: ctl), ctl.

Inductive step : W -> ctl -> W -> ctl -> Prop :=
| step_Sprimcom: forall v (w w': W) (k: ctl),
     V v
     -> v w w'
     -> step w (Kseq (Sprimcom v) k) w' k
| step_Sskip: forall w (k: ctl),
     step w (Kseq Sskip k) w k
| step_Sseq: forall (s1 s2: stmt) w (k: ctl),
     step w (Kseq (Sseq s1 s2) k) w (Kseq s1 (Kseq s2 k))
| step_Sifte_true: forall (e: expr W) (v: val) (s1 s2: stmt) (w: W) (k: ctl),
     exprEval G e w v
     -> is_true v
     -> step w (Kseq (Sifte e s1 s2) k) w (Kseq s1 k)
| step_Sifte_false: forall (e: expr W) (v: val) (s1 s2: stmt) (w: W) (k: ctl),
     exprEval G e w v
     -> ~is_true v
     -> step w (Kseq (Sifte e s1 s2) k) w (Kseq s2 k)
| step_Swhile: forall (s: stmt) e w (k: ctl),
     step w (Kseq (Swhile e s) k)
          w (Kseq (Sifte e (Sseq s (Swhile e s)) Sskip) k).

(* The usual closures and definition of safety *)
Inductive step_star : W -> ctl -> W -> ctl -> Prop :=
| step_star0: forall w k, step_star w k w k
| step_starN: forall w k w'' k'' w' k', step w k w'' k'' -> step_star w'' k'' w' k'
     -> step_star w k w' k'.

Inductive stepN : nat -> W -> ctl -> W -> ctl -> Prop :=
| stepN_0: forall w k, stepN O w k w k
| stepN_S: forall n w k w' k' w'' k'',
     step w k w' k'
     -> stepN n w' k' w'' k''
     -> stepN (S n) w k w'' k''.

Inductive immed_safe : W -> ctl -> Prop :=
| immed_safe0: forall w,
     immed_safe w Kstop
| immed_safe1: forall w k w' k',
     step w k w' k'
     -> immed_safe w k.

Definition safe w k := forall w'' k'', step_star w k w'' k'' -> immed_safe w'' k''.

(* Step Lemmas *)
Lemma step_step_star : forall w k w' k',
  step w k w' k'
  -> step_star w k w' k'.
Proof.
intros; repeat econstructor; eauto.
Qed.

Lemma step_star_trans : forall w k w'' k'' w' k',
  step_star w k w'' k''
  -> step_star w'' k'' w' k'
  -> step_star w k w' k'.
Proof.
intros; induction H; auto.
generalize (IHstep_star H0); intro.
econstructor; eauto.
Qed.

Lemma step_star_stepN : forall w k w'' k'',
  step_star w k w'' k'' <-> exists n, stepN n w k w'' k''.
Proof.
intros; split; intros.
match goal with [H : step_star _ _ _ _ |- _] => induction H end.
eexists; econstructor.
destruct IHstep_star as [n ?]. exists (S n). econstructor; eauto.
destruct H as [n ?].
induction H.
econstructor.
econstructor; eauto.
Qed.

Lemma step_nprimcom_det : forall w k w' k' w'' k'',
  (forall u k', k <> Kseq (Sprimcom u) k')
  -> step w k w' k'
  -> step w k w'' k''
  -> w'=w'' /\ k'=k''.
Proof.
intros.
destruct k. inv H0.
destruct s; try solve
  [elimtype False; apply (H u k); auto
  |inv H0; inv H1; split; auto].
inv H0; inv H1; split;
destruct H8; destruct H9; congruence.
Qed.

Lemma step_safe : forall w k w' k', safe w k -> step w k w' k' -> safe w' k'.
Proof.
unfold safe.
let H := fresh "H" in intros ? ? ? ? H; intros;
  apply H; eapply step_starN; eauto.
Qed.

Definition config_det w k := forall w' k' w'' k'',
  step w k w' k' -> step w k w'' k'' -> w'=w'' /\ k'=k''.

Lemma step_safe' : forall w k w' k',
  safe w' k' -> step w k w' k' -> config_det w k -> safe w k.
Proof.
unfold safe, config_det; intros.
inv H2.
eapply immed_safe1; eauto.
destruct (H1 w' k' w''0 k''0 H0 H3); subst.
apply H; eauto.
Qed.

Lemma safe_seq_assoc: forall w k c1 c2,
  safe w (Kseq c1 (Kseq c2 k)) -> safe w (Kseq (Sseq c1 c2) k).
Proof.
unfold safe; intros.
remember (Kseq (Sseq c1 c2) k).
inv H0; subst.
repeat econstructor; eauto.
inv H1.
auto.
Qed.

Lemma step_compatible : forall c w w' k,
  step w (Kseq c Kstop) w' Kstop -> step w (Kseq c k) w' k.
Proof.
intros. inv H; econstructor; eauto.
Qed.
End GenericSemanticsElaboration.

(* Stratified Semantics -- the "product" of two generic semantics. *)
(* We use S' instead of S to avoid problems with Datatypes.S. *)
Class StratifiedSemantics {W V G S' U F}
                          `{WVG : GenericSemantics W V G}
                           (* The abstract semantics *)
                          `{S'UF : GenericSemantics S' U F}
                           (* The concrete semantics *)
                           (world_erase : W -> S')
                           (* An erasure function mapping worlds to states *)
                           (VU : relation W -> relation S' -> Prop)
                           (* Acceptable primitive command pairs *)
                           (GF : pfunc W val -> pfunc S' val -> Prop)
                           (* Acceptable primitive expression pairs *)
                           : Type := mkStratifiedSemantics {

  (* These axioms just enforce that VU and GF are subsets of the products
     V x U and G x F. *)
  ss_VU_wellformed : forall v u,
    VU v u
    -> V v /\ U u;

  ss_GF_wellformed : forall g f,
    GF g f
    -> G g /\ F f;

  (* Erasure and safety of primitive commands *)
  ss_primcom_erasure : forall v u w w' s s',
    VU v u
    -> world_erase w = s
    -> v w w'
    -> u s s'
    -> world_erase w' = s';

  ss_primcom_safety : forall v u w w' s,
    VU v u
    -> world_erase w = s
    -> v w w'
    -> exists s', u s s';

  (* Ditto for primitive expressions *)
  ss_primexpr_erasure : forall g f b1 b2 w s (Hgf : GF g f),
    world_erase w = s
    -> exprEval G (EPrim g) w b1
    -> exprEval F (EPrim f) s b2
    -> b1=b2;

  ss_primexpr_saftey : forall g f b1 w s,
    GF g f
    -> world_erase w = s
    -> exprEval G (EPrim g) w b1
    -> exists b2, exprEval F (EPrim f) s b2
}.

Section UnpackStratifiedSemantics.
Context {W V G S' U F world_erase VU GF}
        `{SS : StratifiedSemantics W V G S' U F world_erase VU GF}.

Lemma VU_wellformed : forall v u,
    VU v u
    -> V v /\ U u.
Proof. inversion SS; auto. Qed.

Lemma GF_wellformed : forall g f,
    GF g f
    -> G g /\ F f.
Proof. inversion SS; auto. Qed.

Lemma primcom_erasure : forall v u w w' s s',
    VU v u
    -> world_erase w = s
    -> v w w'
    -> u s s'
    -> world_erase w' = s'.
Proof. inversion SS; auto. Qed.

Lemma primcom_safety : forall v u w w' s,
    VU v u
    -> world_erase w = s
    -> v w w'
    -> exists s', u s s'.
Proof. inversion SS; auto. Qed.

Lemma primexpr_erasure : forall g f b1 b2 w s,
    GF g f
    -> world_erase w = s
    -> exprEval G (EPrim g) w b1
    -> exprEval F (EPrim f) s b2
    -> b1=b2.
Proof. inversion SS; auto. Qed.

Lemma primexpr_safety : forall g f b1 w s,
    GF g f
    -> world_erase w = s
    -> exprEval G (EPrim g) w b1
    -> exists b2, exprEval F (EPrim f) s b2.
Proof. inversion SS; auto. Qed.
End UnpackStratifiedSemantics.


(* Corollaries of primitive erasure in the context of a stratified semantics (WVG, S'UF) *)
Section ErasureCorollaries.
Context
  {W V G S' U F world_erase VU GF}
  `{SS : StratifiedSemantics W V G S' U F world_erase VU GF}.

(* Syntax erasure *)
Inductive stmt_erase : @stmt W -> @stmt S' -> Prop :=
| erase_SPrimcom: forall v u,
     VU v u
     -> stmt_erase (Sprimcom v) (Sprimcom u)
| erase_SSkip: stmt_erase Sskip Sskip
| erase_SSeq: forall c1 c1' c2 c2',
     stmt_erase c1 c1'
     -> stmt_erase c2 c2'
     -> stmt_erase (Sseq c1 c2) (Sseq c1' c2')
| erase_SIfte: forall e e' c1 c2 c1' c2',
     expr_erase GF e e'
     -> stmt_erase c1 c1'
     -> stmt_erase c2 c2'
     -> stmt_erase (Sifte e c1 c2) (Sifte e' c1' c2')
| erase_SWhile: forall e e' c c',
     expr_erase GF e e'
     -> stmt_erase c c'
     -> stmt_erase (Swhile e c) (Swhile e' c').

Inductive ctl_erase : @ctl W -> @ctl S' -> Prop :=
| erase_KStop: ctl_erase Kstop Kstop
| erase_KSeq: forall c c' k k',
     stmt_erase c c'
     -> ctl_erase k k'
     -> ctl_erase (Kseq c k) (Kseq c' k').

(* Corollaries of primitive command erasure and safety *)
Lemma stratified_expr_erasure : forall e e' w b1 b2,
  expr_erase GF e e'
  -> exprEval G e w b1
  -> exprEval F e' (world_erase w) b2
  -> b1=b2.
Proof.
intros.
generalize primexpr_erasure; intros.
eapply expr_erasure; eauto.
Qed.

Lemma stratified_expr_safety : forall e e' w b1,
  expr_erase GF e e'
  -> exprEval G e w b1
  -> exists b2, exprEval F e' (world_erase w) b2.
Proof.
intros.
generalize primexpr_safety; intro.
eapply expr_safety; eauto.
Qed.

Lemma step_erasure : forall (w w': W) (s s': S') k_w k_w' k_s k_s',
  world_erase w = s
  -> ctl_erase k_w k_s
  -> @step _ V G w k_w w' k_w'
  -> @step _ U F s k_s s' k_s'
  -> world_erase w' = s' /\ ctl_erase k_w' k_s'.
Proof.
intros; split; intros.
inv H0; inv H1; inv H2; inv H3; auto; eapply primcom_erasure; eauto.
inv H0; inv H1; inv H2; inv H3; repeat constructor; auto.
assert (v = v0) by (eapply stratified_expr_erasure; eauto); subst; contradiction.
assert (v = v0) by (eapply stratified_expr_erasure; eauto); subst; contradiction.
Qed.

Lemma step_safety : forall w w' s k_w k_w' k_s,
  world_erase w = s
  -> ctl_erase k_w k_s
  -> @step _ V G w k_w w' k_w'
  -> exists s', exists k_s', @step _ U F s k_s s' k_s'.
Proof.
intros.
destruct H0. inv H1.
inv H1. inv H0.
destruct (primcom_safety _ _ _ _ _ H1 (refl_equal _) H9).
destruct (VU_wellformed _ _ H1).
repeat eexists; econstructor; eauto.
inv H0; repeat eexists; econstructor.
inv H0; repeat eexists; econstructor.
inv H0.
assert (exprEval F e' (world_erase w') v).
  destruct (stratified_expr_safety _ _ _ _ H4 H6).
  generalize (stratified_expr_erasure _ _ _ _ _ H4 H6 H); intro.
  rewrite H0; auto.
repeat eexists; econstructor; eauto.
inversion H0; subst.
assert (exprEval F e' (world_erase w') v).
  destruct (stratified_expr_safety _ _ _ _ H4 H6).
  generalize (stratified_expr_erasure _ _ _ _ _ H4 H6 H); intro.
  rewrite H1; auto.
exists (world_erase w'); exists (Kseq c2' k'); econstructor; eauto.
inv H0; repeat eexists; econstructor.
Qed.

Lemma step_star_erasure : forall w w' s k_w k_w' k_s,
  world_erase w = s
  -> ctl_erase k_w k_s
  -> @step_star _ V G w k_w w' k_w'
  -> exists s', exists k_s',
        @step_star _ U F s k_s s' k_s'
        /\ world_erase w' = s' /\ ctl_erase k_w' k_s'.
Proof.
intros.
revert s k_s H H0.
induction H1.
repeat eexists; eauto. subst. econstructor; eauto.
intros.
destruct (step_safety _ _ _ _ _ _ H0 H2 H) as [s' [k_s' H5]].
destruct (step_erasure _ _ _ _ _ _ _ _ H0 H2 H H5).
generalize (IHstep_star s' k_s' H3 H4); intros [s'' [k_s'' [? [? ?]]]].
assert (@step_star _ U F s k_s s'' k_s'') by (eapply step_starN; eauto).
exists s''; exists k_s''. split; auto.
Qed.
End ErasureCorollaries.


(* Stratified Semantics with Separation -- this is where put everything together. *)
Class StratifiedSemanticsWithSeparation
  {W V G S' U F world_erase VU GF}
  `{StratifiedSemantics W V G S' U F world_erase VU GF}
  {A}
  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}
   (* NOTE: Perhaps we also want   CA: Canc_alg A   *)
  (projA : W -> A)
  (* Projection function mapping worlds to elements of A *)
  (H : pfunc A val -> Prop)
  (* Set of primitive expressions on A -- we need these in order
     to use [assert_expr]-style predicates in our separation
     logic. *)
  (HG : pfunc A val -> pfunc W val -> Prop)
  (* Acceptable primitive expression pairs on A and W *)
  : Type := {

   sss_HG_wellformed : forall h g,
     HG h g
     -> H h /\ G g;

   sss_primexpr_erasure : forall w a g h b1 b2,
    HG h g
    -> projA w = a
    -> exprEval H (EPrim h) a b1
    -> exprEval G (EPrim g) w b2
    -> b1=b2;

   sss_primexpr_safety : forall w a g h b1,
    HG h g
    -> projA w = a
    -> exprEval H (EPrim h) a b1
    -> exists b2, exprEval G (EPrim g) w b2
}.

Section UnpackStratifiedSemanticsWithSeparation.
Context
{W V G S' U F world_erase VU GF A projA H HG}
`{SSS : StratifiedSemanticsWithSeparation W V G S' U F world_erase VU GF A projA H HG}.

Lemma HG_wellformed : forall h g,
     HG h g
     -> H h /\ G g.
Proof. inversion SSS; auto. Qed.

Lemma sep_primexpr_erasure : forall w a g h b1 b2,
  HG h g
  -> projA w = a
  -> exprEval H (EPrim h) a b1
  -> exprEval G (EPrim g) w b2
  -> b1=b2.
Proof. inversion SSS; auto. Qed.

Lemma sep_primexpr_safety : forall w a g h b1,
  HG h g
  -> projA w = a
  -> exprEval H (EPrim h) a b1
  -> exists b2, exprEval G (EPrim g) w b2.
Proof. inversion SSS; auto. Qed.
End UnpackStratifiedSemanticsWithSeparation.


Section SepErasureCorollaries.
Context
{W V G S' U F world_erase VU GF A projA H HG}
`{SSS : StratifiedSemanticsWithSeparation W V G S' U F world_erase VU GF A projA H HG}.

Lemma sep_expr_erasure : forall e e' w b1 b2,
  expr_erase HG e e'
  -> exprEval H e (projA w) b1
  -> exprEval G e' w b2
  -> b1=b2.
Proof.
intros.
revert b1 b2 H2 H3.
induction H1; intros.
inv H2; inv H3; simpl in *; congruence.
inv H2; inv H3; simpl in *.
case_eq (exprEval' e (projA w)); intros. rewrite H3 in H5; inv H5.
case_eq (exprEval' e' w); intros. rewrite H5 in H6; inv H6.
f_equal. apply IHexpr_erase; auto||split; auto.
rewrite H5 in *; congruence.
rewrite H3 in *; congruence.
destruct H2; destruct H3; simpl in *.
case_eq (exprEval' e1 (projA w)); intros.
case_eq (exprEval' e2 (projA w)); intros.
rewrite H5 in *; rewrite H6 in *; inv H3.
case_eq (exprEval' e1' w); intros.
case_eq (exprEval' e2' w); intros.
rewrite H3 in *; rewrite H9 in *; inv H4.
destruct H1. inv H2.
f_equal. apply IHexpr_erase1; auto||split; auto.
         apply IHexpr_erase2; auto||split; auto.
rewrite H3 in *. rewrite H9 in *. congruence.
rewrite H3 in *. congruence.
rewrite H5 in *. rewrite H6 in *. congruence.
rewrite H5 in *. congruence.
eapply sep_primexpr_erasure; eauto.
Qed.

Lemma sep_expr_safety : forall e e' w b1,
  expr_erase HG e e'
  -> exprEval H e (projA w) b1
  -> exists b2, exprEval G e' w b2.
Proof.
intros.
revert b1 H2.
induction H1; simpl; intros.
eexists; eauto.
inv H2. simpl in *.
case_eq (exprEval' e (projA w)); intros.
rewrite H2 in H4.
assert (exprEval H e (projA w) v). split; auto.
destruct (IHexpr_erase v H5) as [b2 [? ?]].
exists (unopDenote op b2).
split; eauto.
simpl; rewrite H7; auto.
rewrite H2 in H4; inv H4.
inv H2; simpl in *.
case_eq (exprEval' e1 (projA w)); case_eq (exprEval' e2 (projA w)); intros.
rewrite H2 in *; rewrite H4 in *.
destruct H1.
destruct (IHexpr_erase1 v0). split; auto.
destruct (IHexpr_erase2 v). split; auto.
destruct H6; destruct H7.
exists (binopDenote op x x0); split; auto.
simpl. split; auto.
simpl. rewrite H9; rewrite H8. auto.
rewrite H4 in H3; rewrite H2 in H3; congruence.
rewrite H4 in H3; congruence.
rewrite H4 in H3; congruence.
eapply sep_primexpr_safety; eauto.
Qed.
End SepErasureCorollaries.