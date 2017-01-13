Require Import msl.base.

(* Syntax *)

Definition var := nat.
Definition val := nat.

Inductive expr :=
 | Evar: var->expr
 | Econst: val ->expr
 | Eop: (val->val->val) -> expr -> expr -> expr.

Inductive command :=
 | Cskip: command
 | Cassign: var -> expr -> command
 | Cload: var -> expr -> command
 | Cstore: expr -> expr -> command
 | Cseq : command -> command -> command
 | Cif: expr -> command  -> command -> command
 | Cwhile: expr  -> command -> command.

(* Semantics -- stacks, memories, and states *)
Definition stack := var -> option val.
Definition mem := val -> option val.

Definition rho0 : stack := fun _ => None.
Definition m0 : mem := fun _ => None.

Class EqDec (A : Type) : Type := eq_dec : forall a a' : A, {a = a'} + {a <> a'}.
Instance EqDec_nat: EqDec nat.
Proof. intro. induction a; destruct a'; intros; auto.
 destruct (IHa a'); [left|right]; auto.
Qed.
Instance EqDec_var: EqDec var := _.
Instance EqDec_val: EqDec val := _.

Definition upd{A B}{EA: EqDec A} (f: A -> option B) x y z :=
 if eq_dec x z then y else f z.

Inductive state := State: forall (rho: stack) (m: mem) (c: command), state.
Definition stack_of (s: state) := match s with State rho _ _ => rho end.
Definition mem_of (s: state) := match s with State _ m _ => m end.
Definition cmd_of (s: state) := match s with State _ _ c => c end.

(* Operational semantics *)
Inductive eval: expr -> val -> stack -> Prop :=
| Eval_var: forall rho e v, rho e = Some v -> eval (Evar e) v rho
| Eval_const: forall rho v, eval (Econst v) v rho
| Eval_op: forall rho f e1 e2 v1 v2, eval e1 v1 rho -> eval e2 v2 rho ->
                eval (Eop f e1 e2) (f v1 v2) rho.

Inductive step: relation state :=
| Step_skip: forall rho m c, step (State rho m (Cseq Cskip c)) (State rho m c)
| Step_assign: forall rho m x e c v, eval e v rho ->
                          step (State rho m (Cseq (Cassign x e) c)) (State (upd rho x (Some v)) m c)
| Step_load:  forall rho m x e c v v', eval e v rho -> m v = Some v' ->
                          step (State rho m (Cseq (Cload x e) c)) (State (upd rho x (Some v')) m c)
| Step_store: forall rho m e1 e2 c v1 v2,
                          eval e1 v1 rho -> eval e2 v2 rho ->
                          step (State rho m (Cseq (Cstore e1 e2) c)) (State rho (upd m v1 (Some v2)) c)
| Step_seq: forall rho m c1 c2 c,
                          step (State rho m (Cseq (Cseq c1 c2) c)) (State rho m (Cseq c1 (Cseq c2 c)))
| Step_iftrue: forall rho m e c1 c2 c v, eval e v  rho-> v<>0 ->
                           step (State rho m (Cseq (Cif e c1 c2) c)) (State rho m (Cseq c1 c))
| Step_iffalse: forall rho m e c1 c2 c, eval e 0 rho ->
                           step (State rho m (Cseq (Cif e c1 c2) c)) (State rho m (Cseq c2 c))
| Step_whiletrue: forall rho m e c1 c v, eval e v rho -> v<>0 ->
                           step (State rho m (Cseq (Cwhile e c1) c)) (State rho m (Cseq c1 (Cseq (Cwhile e c1) c)))
| Step_whilefalse: forall rho m e c1 c, eval e 0 rho ->
                           step (State rho m (Cseq (Cwhile e c1) c)) (State rho m c).

Definition stepstar := clos_refl_trans_1n _ step.

Definition a : var := 0.

Definition run (c: command) (v: val) : Prop :=
  exists rho, exists m,
   stepstar (State rho0 m0 (Cseq c Cskip)) (State rho m Cskip) /\ rho a = Some v.

Lemma eval_fun: forall {e rho v1}, eval e v1 rho -> forall {v2}, eval e v2 rho -> v1=v2.
Proof.
induction 1; intros;
 match goal with H: eval _ _ _ |- _ => inversion H; clear H; subst; try congruence end.
specialize (IHeval1 _ H7). specialize (IHeval2 _ H8). congruence.
Qed.

Lemma step_fun: forall {s s1 s2}, step s s1 -> step s s2 -> s1=s2.
Proof.
induction 1; intros;
  match goal with H: step _ _ |- _ => inversion H; clear H; subst; repeat f_equal; auto end.
eapply eval_fun; eauto.
pose proof (eval_fun H H8); congruence.
pose proof (eval_fun H H8); pose proof (eval_fun H0 H9); congruence.
pose proof (eval_fun H H8); pose proof (eval_fun H0 H9); congruence.
pose proof (eval_fun H H9); congruence.
pose proof (eval_fun H H8); congruence.
pose proof (eval_fun H H8); congruence.
pose proof (eval_fun H H7); congruence.
Qed.

(* Hoare Logic *)

Definition h_assert := stack -> Prop.

Inductive immed_safe: state -> Prop :=
| IS_stop: forall rho m, immed_safe (State rho m Cskip)
| IS_step: forall s s', step s s' -> immed_safe s.

Definition safe (s: state) : Prop :=
  forall s', stepstar s s' -> immed_safe s'.

Definition guard (P: h_assert) (c: command) :=
  forall rho,   P rho -> safe (State rho m0 c).

Definition Hoare (P: h_assert) (c: command) (Q: h_assert) : Prop :=
   forall k, guard Q k -> guard P (Cseq c k).

Definition subst (x:var) (v: option val) (P: h_assert) : h_assert :=
   fun rho => P (upd rho x v).


Lemma safe_step: forall s s',
   step s s' -> safe s' -> safe s.
Proof.
unfold safe in *; intros.
inversion H1; clear H1; subst.
econstructor 2; eauto.
apply H0.
pose proof (step_fun H H2).
subst.
apply H3 .
Qed.


Lemma upd_same: forall A B {EA: EqDec A} rho (x: A) (v: option B), upd rho x v x = v.
Proof.
intros. unfold upd. destruct (eq_dec x x); auto. congruence.
Qed.

Lemma upd_other: forall A B {EA: EqDec A} rho (x y: A) (v: option B),
  x <> y -> upd rho x v y = rho y.
Proof.
intros. unfold upd. destruct (eq_dec x y); auto. congruence.
Qed.

Lemma floyd_assign:
  forall (P: h_assert) (x: var) (e: expr),
    (forall rho, P rho -> exists v, eval e v rho) ->
    Hoare P (Cassign x e)
    (fun rho => exists v, exists x',
     eval (Evar x) v rho /\ subst x x' (eval e v) rho /\ subst x x' P rho).
Proof.
intros.
hnf; intros.
hnf; intros.
destruct (H _ H1) as [v ?].
eapply safe_step.
constructor. eassumption.
apply H0.
exists v. exists (rho x).
split. constructor.
apply upd_same.
unfold subst.
replace (upd (upd rho x (Some v)) x (rho x)) with rho; auto.
extensionality y.
destruct (eq_dec y x). subst. rewrite upd_same. auto.
rewrite upd_other by auto. symmetry; apply upd_other; auto.
Qed.
