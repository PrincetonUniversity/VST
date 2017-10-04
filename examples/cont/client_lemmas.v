Require Import language.
Require Import msl.base.
Require Import msl.seplog.
Require Import msl.alg_seplog.
Require Import seplogic.
Require Import lseg.
Require Import msl.Coqlib2.
Require Import msl.log_normalize.

Local Open Scope logic.


Import Semax.

(* PROOF AUTOMATION FOR SEMAX *)

Hint Extern 3 (inlist _ _ = false) => (compute; reflexivity).

Lemma arguments_gss: forall x xl v vl, arguments (x::xl)(v::vl) x = v.
Proof.
  intros.
 Transparent arguments. unfold arguments, locals2env,mk_locals;  simpl.
 Opaque arguments.
  rewrite if_true; auto.
Qed.
Lemma arguments_gso: forall x xl v vl x', x<>x' -> arguments (x::xl)(v::vl)x' = arguments xl vl x'.
Proof.
  intros.
 Transparent arguments. unfold arguments, locals2env,mk_locals;  simpl.
 Opaque arguments.
  rewrite if_false; auto.
Qed.

Ltac compute_neq := solve [let H := fresh in intro H; inversion H].

Hint Rewrite arguments_gss : args.
Hint Rewrite arguments_gso using compute_neq : args.

Ltac call_tac := unfold call; simpl; autorewrite with args; simpl.


Lemma funassert_e:  forall G i f,
      table_get G i = Some f ->
      funassert G |-- cont f i.
Proof.
  intros.
  unfold funassert.
  apply andp_left1.
  apply allp_left with i. apply allp_left with f.
  normalize.
  eapply derives_trans with (TT && (TT --> cont f i)).
  apply andp_right; auto. apply TT_right. apply modus_ponens.
Qed.

Ltac funassert_tac :=
  match goal with
  | |-   ?A && ?B |-- _ =>
      match A with context [funassert _] => apply andp_left1; funassert_tac  end ||
      match B with context [funassert _] => apply andp_left2; funassert_tac  end
  | |- funassert _ |-- _ => apply funassert_e; simpl; reflexivity
 end.

Ltac func_tac :=
   apply semax_func_cons;
    [ compute; reflexivity | compute; reflexivity | compute; reflexivity
    |  (*eapply semax_pre; [intro ; call_tac; apply derives_refl | ] *)
    | ].

Ltac rewrite' H := eapply semax_pre; [ intro; rewrite H; apply derives_refl | ].

(* This tactic works but introduces magic wands, which is undesirable *)
Ltac forward_magic :=
  match goal with |- semax _ ?G ?P (Assign (Mem ?e1) ?e2 ?c) =>
      let v := fresh "v" in
        (evar (v:adr);
       apply semax_pre with (P' := fun s => mapsto (eval e1 s) v * (mapsto (eval e1 s) v -* P s));
               [intro | apply semax_store; auto  ] );
       unfold v; clear v
  end.

Hint Resolve now_later sepcon_derives.

Definition semax_body (G: funspecs) (spec: funspec) (f: list var * control) :=
  semax (fst f) G (fun s => call spec (map s (fst f))) (snd f).


Lemma semax_store_next: forall x y v c vars G (Q P: assert),
    expcheck vars x = true ->
    expcheck vars y = true ->
    Q = (fun s => next (eval x s) v  * P s) ->
    semax vars G (fun s => next (eval x s) (eval y s) * P s) c ->
    semax vars G Q  (Do Mem x  := y ; c).
Proof. intros; subst.
    apply semax_pre with (fun s => mapsto (eval x s) v * (!! (eval x s > 0) && P s)).
    intros. unfold next. rewrite sepcon_andp_prop.
    rewrite sepcon_comm. rewrite sepcon_andp_prop. rewrite sepcon_comm; auto.
    apply semax_store; auto.
    eapply semax_pre; try apply H2.
    intros; unfold next.
    rewrite sepcon_andp_prop.
    rewrite (sepcon_comm (andp _ _)). rewrite sepcon_andp_prop.
   rewrite sepcon_comm; auto.
 Qed.

Lemma semax_load_next: forall x y z c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c ->
    semax vars G (fun s => (next (eval y s) z * TT) && |> subst x z P s)
               (Do x := Mem y ; c).
Proof.
 intros.
  apply semax_pre with (fun s => mapsto (eval y s) z * TT && |> subst x z P s).
 intros. apply andp_derives; auto. apply sepcon_derives; auto. apply andp_left2; auto.
 apply semax_load; auto.
Qed.



Ltac forward :=
 match goal with
 | |- semax _ _ _ (IfThenElse _ _ _) =>
          apply semax_if; [ compute; reflexivity | | ]
 | |- semax _ _ _ (Assign (Mem _) _ _) =>
            (eapply semax_store || eapply semax_store_next);
             [ compute ; reflexivity | compute; reflexivity | reflexivity | ]
 | |- semax _ _ _ (Assign _ (Mem _) _) =>
            (eapply semax_load || eapply semax_load_next);
             [ compute ; reflexivity | ]
 | |- semax _ _ ?P (Go ?x ?ys) =>
  apply semax_G;
  let p := fresh "P" in
   evar (p: funspec);
   eapply semax_pre with (fun s => cont p (eval x s) && call p (eval_list ys s));
       [ intro; apply andp_right
       | apply semax_go; [ compute; reflexivity ] ]; unfold p; clear p;
       [ try funassert_tac | call_tac  ]; simpl
 end.

