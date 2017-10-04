Add LoadPath "../..".
Require Import Arith.
Require Import List.
Require Import msl.eq_dec.
Import Relations.

Definition table (A B : Type) := list (A*B).

Fixpoint table_get {A B}{H: EqDec A} (rho: table A B) (x: A) : option B :=
  match rho with
  | (y,v)::ys => if eq_dec x y then Some v else table_get ys x
  | nil => None
 end.

Definition table_set {A B}{H: EqDec A} (x: A) (v: B) (rho: table A B)  : table A B := (x,v)::rho.

Lemma table_gss {A B}{H: EqDec A}: forall rho x (v: B), table_get (table_set x v rho) x = Some v.
Proof.
intros.
simpl. destruct (eq_dec x x); auto. contradiction n; auto.
Qed.

Lemma table_gso {A B}{H: EqDec A}: forall rho x y (v:B), x<>y -> table_get (table_set x v rho) y = table_get rho y.
Proof.
intros.
simpl. destruct (eq_dec y x); auto.  contradiction H0; auto.
Qed.


Definition var := nat.
Definition adr := nat.
Definition stack := table var adr.
Definition heap := table adr adr.
Definition state := (stack * heap)%type.

Inductive command :=
| Skip : command
| Assign: var -> var -> command
| Load : var -> var -> command
| Store: var -> var -> command
| Seq: command -> command -> command.

Inductive step: relation (command * state) :=
| stepAssign:
        forall x y v stk hp,
        table_get stk y = Some v ->
        step (Assign x y, (stk,hp)) (Skip, (table_set x v stk, hp))
| stepLoad:
        forall x y v v' stk hp,
         table_get stk y = Some v ->
         table_get hp v = Some v' ->
         step (Load x y, (stk,hp)) (Skip, (table_set x v' stk, hp))
| stepStore:
         forall x y v p stk hp,
          table_get stk y = Some v ->
          table_get stk x = Some p ->
          step (Store x y, (stk,hp)) (Skip, (stk, table_set p v hp))
| stepSeq0:
         forall c2 s,
         step (Seq Skip c2, s) (c2, s)
| stepSeq1:
         forall c1 c1' c2 s s',
         step (c1,s) (c1',s') ->
         step (Seq c1 c2, s) (Seq c1' c2, s').

Inductive step': relation (list command * state)  :=
| step'Skip:
         forall k s,
         step' (Skip :: k, s) (k,s)
| step'Assign:
        forall x y v stk hp k,
        table_get stk y = Some v ->
        step' (Assign x y :: k, (stk,hp)) (k, (table_set x v stk, hp))
| step'Load:
        forall x y v v' stk hp k,
         table_get stk y = Some v ->
         table_get hp v = Some v' ->
         step' (Load x y :: k, (stk,hp)) (k, (table_set x v' stk, hp))
| step'Store:
         forall x y v p stk hp k,
          table_get stk y = Some v ->
          table_get stk x = Some p ->
          step' (Store x y :: k, (stk,hp)) (k, (stk, table_set p v hp))
| step'Seq:
         forall c1 c2 k s cs',
         step' (c1 :: c2 ::k, s) cs' ->
         step' (Seq c1 c2 :: k, s) cs'.

Fixpoint stackit (k: list command) (c: command) : command :=
 match k with
 | nil => c
 | c'::k' => stackit k' (Seq c c')
 end.

Definition stackit' (k: list command) : command :=
 match k with nil => Skip | c::k' => stackit k' c end.

(* Eval compute in stackit' (Skip :: Assign 0 1 :: Assign 0 2 :: Assign 0 3 :: nil). *)

Ltac inv H := inversion H; clear H; subst.

Lemma stackit_step:
  forall s s' k c c',
   step (c,s) (c',s') -> step (stackit k c, s) (stackit k c', s').
Proof.
 induction k; simpl; intros.
 auto.
 apply IHk.
 apply stepSeq1. auto.
Qed.

Lemma step'_equiv:
  forall k s k' s',
  clos_refl_trans _ step' (k,s) (k', s') ->
  clos_refl_trans _ step (stackit' k, s) (stackit' k', s').
Proof.
 intros.
 remember (k,s) as ks.
 remember (k',s') as ks'.
 apply clos_rt1n_rt; apply clos_rt_rt1n in H.
 revert k s Heqks k' s' Heqks'; induction H; intros; subst.
 inv Heqks'.
 apply rt1n_refl.
 destruct y as [k1 s1].
 rename IHclos_refl_trans_1n into IH.
 specialize (IH _ _ (eq_refl _) _ _ (eq_refl _)).
 destruct k; simpl.
 simpl. inv H.
 apply clos_rt_rt1n.
 eapply rt_trans.
 2: apply clos_rt1n_rt; apply IH.
 clear -H.
 revert k k1 H.
 induction c; intros; inv H.
 destruct k1; simpl. apply rt_refl.
 apply rt_step; apply stackit_step; constructor.
 destruct k1; simpl. apply rt_step; econstructor; eauto.
 eapply rt_trans; apply rt_step; apply stackit_step;
    repeat econstructor; eauto.
 destruct k1; simpl. apply rt_step; econstructor; eauto.
 eapply rt_trans; apply rt_step; apply stackit_step;
    repeat econstructor; eauto.
 destruct k1; simpl. apply rt_step; econstructor; eauto.
 eapply rt_trans; apply rt_step; apply stackit_step;
    repeat econstructor; eauto.
 apply IHc1 in H5.
 eapply rt_trans; [ | apply H5].
 replace (stackit k (Seq c1 c2)) with (stackit (c2::k) c1).
 apply rt_refl.
 clear. induction k; simpl; auto.
Qed.

