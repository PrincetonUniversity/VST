Set Warnings "-custom-entry-overridden".
Require Import VST.veric.SequentialClight.
Require Import VST.floyd.proofauto.
Set Warnings "custom-entry-overridden".

#[export] Unset SsrRewrite.

(*Section GFUNCTORS.
Context `{Σ: gFunctors}.
*)
(*
Notation assert := (@assert (VSTΣ unit)).
Notation funspec := (@funspec (VSTΣ unit)).
Notation funspecs := (@funspecs (VSTΣ unit)).
*)

#[export] Arguments VST_heapGS : simpl never.

Module NoOracle.
(* Concrete instance of the Iris typeclasses for no ghost state or external calls *)
Definition default_pre : VSTGpreS unit (VSTΣ unit) := subG_VSTGpreS _.

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


(*#[export] Notation assert := (@assert (VSTΣ unit)).
#[export] Notation funspec := (@funspec (VSTΣ unit)).*)
#[export] Notation funspecs := (@funspecs (VSTΣ unit)).

End NoOracle.

Notation "P |-- Q" := (P ⊢ Q)
  (at level 99, Q at level 200, right associativity, only parsing) : stdpp_scope.
Notation " 'ENTAIL' d ',' P |-- Q " :=
  (@bi_entails (monPredI env_index (iPropI _)) (local (tc_environ d) ∧ P%assert) Q%assert) (at level 99, P at level 98, Q at level 98).
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

Disable Notation "True" : bi_scope.
Disable Notation "False" : bi_scope.


Open Scope bi_scope.

Definition prop_and: ∀ {M : uora} (P Q : Prop),  
  (@bi_pure (ouPredI M) (and P Q))
  = @bi_and (ouPredI M) (@bi_pure (ouPredI M) P) (@bi_pure (ouPredI M) Q)
   := @pure_and.

Lemma wand_sepcon_adjoint  : forall {B : bi} (P Q R: B),
  ((P * Q) |-- R) = (P |-- (Q -* R)).
Proof.
intros.
apply prop_ext; split.
apply bi.wand_intro_r.
apply bi.wand_elim_l'.
Qed.

Definition pred_ext := @bi.equiv_entails_2.
Definition andp_right := @bi.and_intro.
Definition prop_right := @bi.pure_intro.
Definition sepcon_derives := @bi.sep_mono.
Definition andp_derives := @bi.and_mono.
Definition prop_derives := @bi.pure_mono.
Definition orp_left := @bi.or_elim.
Definition sepcon_emp := @sep_emp.
Definition emp_sepcon := @emp_sep.
Definition sepcon_comm := @sep_comm.
Definition sepcon_assoc := @sep_assoc.
Definition andp_comm := @log_normalize.and_comm.
Definition andp_assoc := @log_normalize.and_assoc.
Definition allp_right := @bi.forall_intro.
Definition FF_left := @False_left.

Lemma andp_left1 : forall {B : bi} (P Q R : B), (P ⊢ R) -> P ∧ Q ⊢ R.
Proof. intros; rewrite bi.and_elim_l; auto. Qed.
Lemma andp_left2 : forall {B : bi} (P Q R : B), (Q ⊢ R) -> P ∧ Q ⊢ R.
Proof. intros; rewrite bi.and_elim_r; auto. Qed.

Lemma derives_refl' : forall {B : bi} {P Q : B}, P = Q -> P ⊢ Q.
Proof. intros; subst; auto. Qed.

Section iter_sepcon2.
(* progs/verif_tree relies on this playing well with Fixpoint, so we have to define it
   in this particular way instead of using [∗ list]. *)

Context {A : bi} {B1 B2} (p : B1 -> B2 -> A).

Fixpoint iter_sepcon2 (l : list B1) : list B2 -> A :=
    match l with
    | nil => fun l2 =>
       match l2 with
       | nil => emp
       | _ => FF
       end
    | x :: xl => fun l' =>
       match l' with
       | nil => FF
       | y :: yl => p x y * iter_sepcon2 xl yl
       end
    end.

Lemma iter_sepcon2_spec: forall l1 l2,
  iter_sepcon2 l1 l2 ⊣⊢ EX l: list (B1 * B2), !! (l1 = map fst l /\ l2 = map snd l) && [∗ list] x ∈ l, uncurry p x.
Proof.
  intros.
  apply pred_ext.
  + revert l2; induction l1; intros; destruct l2.
    - rewrite <- (bi.exist_intro nil).
      simpl; auto.
    - simpl.
      apply FF_left.
    - simpl.
      apply FF_left.
    - simpl.
      specialize (IHl1 l2).
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IHl1] | clear IHl1].
      rewrite bi.sep_exist_l; apply bi.exist_elim; intros l.
      rewrite persistent_and_sep_assoc' by apply _; apply bi.pure_elim_l; intros (-> & ->).
      apply (exp_right ((a, b) :: l)).
      simpl.
      apply andp_right; [apply prop_right; subst; auto |].
      apply derives_refl.
  + Intros l.
    subst.
    induction l.
    - simpl. auto.
    - simpl.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IHl] | clear IHl].
      destruct a; apply derives_refl.
Qed.

End iter_sepcon2.

#[export] Tactic Notation "inv" ident(H):= Coqlib.inv H.
