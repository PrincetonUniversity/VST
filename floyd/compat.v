Require Import VST.veric.SequentialClight.
Require Import VST.floyd.proofauto.

#[export] Unset SsrRewrite.

Notation assert := (@assert (VSTΣ unit)).
Notation funspec := (@funspec (VSTΣ unit)).
Notation funspecs := (@funspecs (VSTΣ unit)).

(* Concrete instance of the Iris typeclasses for no ghost state or external calls *)
#[local] Instance default_pre : VSTGpreS unit (VSTΣ unit) := subG_VSTGpreS _.

#[export] Program Instance VST_default : VSTGS unit (VSTΣ unit) := Build_VSTGS _ _ _ _.
Next Obligation.
Proof.
  split.
  - split; split; try apply _.
    + exact 1%positive.
    + exact 2%positive.
    + exact 3%positive.
    + apply lcGpreS_inG.
    + exact 4%positive.
  - split; try apply _.
    + exact 5%positive.
    + exact 6%positive.
  - split; try apply _.
    exact 7%positive.
Defined.
Next Obligation.
Proof.
  split; try apply _.
  exact 8%positive.
Defined.

Opaque VST_default.
#[export] Arguments VST_heapGS : simpl never.

(* avoid unfolding typeclass instances in simplify_func_tycontext *)
Ltac simplify_func_tycontext' DD ::=
  match DD with context [(func_tycontext ?f ?V ?G ?A)] =>
    let D1 := fresh "D1" in let Delta := fresh "Delta" in
    pose (D1 := (func_tycontext f V G A));
    pose (Delta := @abbreviate tycontext D1);
    change (func_tycontext f V G A) with Delta;
    unfold func_tycontext, make_tycontext in D1;
    let DS := fresh "Delta_specs" in
    let d := constr:(make_tycontext_s G) in
    let d := make_ground_PTree d in 
    pose (DS := @abbreviate (PTree.t funspec) d);
    change (make_tycontext_s G) with DS in D1;
    cbv beta iota zeta delta - [VSTΣ VST_default DS] in D1;
    subst D1;
    check_ground_Delta
   end.

Notation "P |-- Q" := (P ⊢ Q)
  (at level 99, Q at level 200, right associativity, only parsing) : stdpp_scope.
Notation " 'ENTAIL' d ',' P |-- Q " :=
  (@bi_entails (monPredI environ_index (iPropI _)) (local (tc_environ d) ∧ P%assert) Q%assert) (at level 99, P at level 98, Q at level 98).
Notation "'!!' φ" := (bi_pure φ%type%stdpp) (at level 15) : bi_scope.
Notation "P && Q" := (P ∧ Q)%I (only parsing) : bi_scope.
Notation "P || Q" := (P ∨ Q)%I (only parsing) : bi_scope.
Notation "P --> Q" := (P → Q)%I (only parsing) : bi_scope.
Notation "P * Q" := (P ∗ Q)%I
  (at level 40, left associativity, only parsing) : bi_scope.
Notation "P -* Q" := (P -∗ Q)%I
  (at level 99, Q at level 200, right associativity, only parsing) : bi_scope.

Notation "'ALL' x .. y , P " := (bi_forall (fun x => .. (bi_forall (fun y => P%I)) ..))
  (at level 65, x binder, y binder, right associativity) : bi_scope.
Notation "'EX' x .. y , P " := (bi_exist (fun x => .. (bi_exist (fun y => P%I)) ..))
  (at level 65, x binder, y binder, right associativity) : bi_scope.

Notation "|> P" := (▷ P)%I
  (at level 20, right associativity, only parsing) : bi_scope.

Notation "P <--> Q" := (P ↔ Q)%I
  (at level 95, no associativity, only parsing) : bi_scope.

Notation TT := (True)%I.
Notation FF := (False)%I.

Open Scope bi_scope.

Definition pred_ext := @bi.equiv_entails_2.
Definition andp_right := @bi.and_intro.
Definition prop_right := @bi.pure_intro.
Definition sepcon_derives := @bi.sep_mono.
Definition andp_derives := @bi.and_mono.
Definition sepcon_emp := @bi.sep_emp.
Definition emp_sepcon := @bi.emp_sep.
Definition sepcon_comm := @bi.sep_comm.
Definition sepcon_assoc := @bi.sep_assoc.
Definition allp_right := @bi.forall_intro.

Fixpoint iter_sepcon2 {B1 B2} (p : B1 -> B2 -> mpred) l :=
    match l with
    | nil => fun l2 =>
       match l2 with
       | nil => emp
       | _ => FF
       end
    | x :: xl => fun l' =>
       match l' with
       | nil => FF
       | y :: yl => p x y * iter_sepcon2 p xl yl
       end
    end.

Global Tactic Notation "inv" ident(H):= Coqlib.inv H.
