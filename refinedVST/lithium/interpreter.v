From iris.proofmode Require Import coq_tactics reduction.
From lithium Require Import base hooks normalize solvers.
From VST.lithium Require Import definitions simpl_classes proof_state syntax.
From VST.lithium Require Import simpl_instances. (* required for tests *)
Set Default Proof Using "Type".

(** This file contains the main Lithium interpreter. *)

(** * General proof state management tactics  *)
(* The simpl is necessary since li_unfold_lets_in_context might provide new opportunities for simpl *)
Ltac liShow := li_unfold_lets_in_context; simpl; try liToSyntaxGoal.

Ltac liSimpl :=
  (* simpl inserts a cast even if it does not do anything
     (see https://coq.zulipchat.com/#narrow/stream/237656-Coq-devs.20.26.20plugin.20devs/topic/exact_no_check.2C.20repeated.20casts.20in.20proof.20terms/near/259371220 ) *)
  try progress simpl.

Ltac liUnfoldLetGoal :=
  let do_unfold P :=
    let H := get_head P in
    is_var H;
    unfold LET_ID in H;
    liUnfoldLetGoal_hook H;
    (* This unfold inserts a cast but that is not too bad for
       performance since the goal is small at this point. *)
    unfold H;
    try clear H
  in
  lazymatch goal with
  | |- envs_entails _ (∃ₗ _, ?P _ _ _ ∗ _) => do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P _ _ ∗ _) => do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P _ ∗ _) => do_unfold P
  | |- envs_entails _ (?P ∗ _) => do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P _ _ _) => do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P _ _) => do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P _) => do_unfold P
  | |- envs_entails _ ?P => do_unfold P
  end.

Ltac liUnfoldSyntax :=
  lazymatch goal with
  | |- envs_entails _ (li.all _) => liFromSyntax
  | |- envs_entails _ (li.exist _) => liFromSyntax
  | |- envs_entails _ (li.done) => liFromSyntax
  | |- envs_entails _ (li.false) => liFromSyntax
  | |- envs_entails _ (li.and _ _) => liFromSyntax
  | |- envs_entails _ (li.and_map _ _) => liFromSyntax
  | |- envs_entails _ (li.case_if _ _ _) => liFromSyntax
  | |- envs_entails _ (li.ret) => liFromSyntax
  | |- envs_entails _ (li.bind0 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind1 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind2 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind3 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind4 _ _) => liFromSyntax
  | |- envs_entails _ (li.bind5 _ _) => liFromSyntax
  end.

Ltac liEnsureInvariant := try let_bind_envs; try liUnfoldSyntax.

Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_fast_apply {Δ} {P1 P2 : prop} :
    (P1 ⊢ P2) → envs_entails Δ P1 → envs_entails Δ P2.
  Proof. by rewrite envs_entails_unseal => -> HP. Qed.
End coq_tactics.

(** ** [liInst] *)
Section coq_tactics.
  Context {prop : bi}.
  Lemma tac_li_inst {A B} (P : (A *ₗ B) → Prop) Δ (G : _ → prop):
    envs_entails Δ (∃ₗ x, <affine> ⌜P x⌝ ∗ G x) →
    envs_entails Δ (∃ₗ x, G x).
  Proof. apply tac_fast_apply. apply bi.exist_mono => ?. iIntros "[_ $]". Qed.
  Lemma tac_li_inst_subsume {A B} (P : (A *ₗ B) → Prop) Δ P1 P2 (G : _ → prop):
    envs_entails Δ (P1 -∗ ∃ₗ x, <affine> ⌜P x⌝ ∗ P2 x ∗ G x) →
    envs_entails Δ (subsume P1 P2 G).
  Proof.
    apply tac_fast_apply. apply bi.wand_mono; [done|].
    apply bi.exist_mono => ?. iIntros "[_ $]".
  Qed.
End coq_tactics.

Tactic Notation "liInst" open_constr(P) :=
  liFromSyntax;
  lazymatch goal with
  | |- envs_entails _ (∃ₗ _, _) => notypeclasses refine (tac_li_inst P _ _ _)
  | |- envs_entails _ (subsume _ _ _) => notypeclasses refine (tac_li_inst_subsume P _ _ _ _ _)
  end; try liToSyntax.

(** ** [liExInst] *)
Section coq_tactics.
  Context {prop : bi}.
  Lemma tac_li_ex_inst {A B} Δ (P : A → Prop) (Q : A → prop) (f : B → A) :
    (∀ y, P (f y)) →
    envs_entails Δ (∃ y, Q (f y)) →
    envs_entails Δ (∃ x, <affine> ⌜P x⌝ ∗ Q x).
  Proof. move => ?. apply tac_fast_apply. iIntros "[%a ?]". iExists _. iFrame. naive_solver. Qed.
End coq_tactics.

(* TODO: rename? *)
Create HintDb solve_protected_eq_db discriminated.
Global Hint Constants Opaque : solve_protected_eq_db.

Ltac liExInst :=
  let EX := fresh "EX" in
  (* we use simple to not shelve any of the generated goals *)
  simple refine (tac_li_ex_inst _ _ _ _ _ _);
  (* create the function of the form (λ x, (_, .. , _, tt)ₗ) *)
  [| refine (λ EX, _);
     let x := lazymatch goal with | |- ?x => x end in
     let rec go1 t x :=
       lazymatch x with
       | _ *ₗ ?B =>
           let r := go1 t B in
           uconstr:(li_pair _ r)
       | unit => t
       end in
     let t := go1 uconstr:(tt) x in
     refine t| |];
  (* solve the sidecondition and try to instantiate evars *)
  [..| intro EX; red_li_prod;
   intros;
   solve_protected_eq_hook;
   (* TODO: Is the following necessary? If so, what is the best place to do it? *)
   (* li_unfold_lets_in_context; *)
   lazymatch goal with |- ?a = ?b => unify a b with solve_protected_eq_db end;
   exact: eq_refl |];
  (* create new existential quantifers for all evars that were not instantiated *)
  [| let x := type of EX in
     let rec go2 x t :=
       lazymatch x with
       | _ *ₗ ?B =>
           let r := go2 B t in
           uconstr:(r.nextₗ)
       | _ => t
       end in
     let t := go2 x EX in
     refine (t.1ₗ)..|];
  (* Add unit at the end. *)
  [exact unit|];
  (* reduce the li_pair in the goal *)
  red_li_prod.

(** ** liEnsureSepHead *)
Section coq_tactics.
  Context {prop : bi}.
  Lemma tac_ensure_sep_head {A B} Δ (P : prop) (Q : (A *ₗ B → prop)) :
    envs_entails Δ (P ∗ ∃ₗ x, Q x) → envs_entails Δ (∃ₗ x, P ∗ Q x).
  Proof. apply tac_fast_apply. by iIntros "[$ ?]". Qed.
End coq_tactics.

Ltac liEnsureSepHead :=
  lazymatch goal with
  | |- envs_entails ?Δ (bi_sep _ _) => idtac
  | |- envs_entails ?Δ (∃ₗ _, bi_sep ?P _) =>
      notypeclasses refine (tac_ensure_sep_head _ _ _ _)
  end.


(** * Main lithium tactics *)

(** ** [liExtensible] *)
Section coq_tactics.
  Context {prop : bi}.

  (* For some reason, replacing tac_fast_apply with more specialized
  versions gives a 1-2% performance boost, see
  https://coq-speed.mpi-sws.org/d/1QE_dqjiz/coq-compare?orgId=1&var-project=refinedc&var-branch1=master&var-commit1=05a3e8862ae4ab0041af67d1c02c552f99c4f35c&var-config1=build-coq.8.14.0-timing&var-branch2=master&var-commit2=998704f2a571385c65edfdd36332f6c3d014ec59&var-config2=build-coq.8.14.0-timing&var-metric=instructions&var-group=().*
  TODO: investigate this more
*)
  Lemma tac_apply_i2p {Δ} {P : prop} (P' : iProp_to_Prop P) :
    envs_entails Δ P'.(i2p_P) → envs_entails Δ P.
  Proof. apply tac_fast_apply. apply i2p_proof. Qed.
End coq_tactics.

Ltac liExtensible_to_i2p P bind cont :=
  lazymatch P with
  | subsume ?P1 ?P2 ?T =>
      bind T ltac:(fun H => uconstr:(subsume P1 P2 H));
      cont uconstr:(((_ : Subsume _ _) _))
  | _ => liExtensible_to_i2p_hook P bind cont
  end.
Ltac liExtensible :=
  lazymatch goal with
  | |- envs_entails ?Δ ?P =>
      (* assert_succeeds (repeat lazymatch goal with | H := EVAR_ID _ |- _ => clear H end); *)
      liExtensible_to_i2p P
        ltac:(fun T tac => li_let_bind T (fun H => let X := tac H in constr:(envs_entails Δ X)))
        ltac:(fun converted =>
          simple notypeclasses refine (tac_apply_i2p converted _); [solve [refine _] |];
          liExtensible_hook)
  end.

(** ** [liTrue] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_true Δ :
    envs_entails Δ (True%I : prop).
  Proof. rewrite envs_entails_unseal. by iIntros "_". Qed.
End coq_tactics.

Ltac liTrue :=
  lazymatch goal with
  | |- envs_entails _ True => notypeclasses refine (tac_true _)
  end.

(** ** [liFalse] *)
Ltac liFalse :=
  lazymatch goal with
  | |- envs_entails _ False => exfalso; shelve_sidecond
  | |- False => shelve_sidecond
  end.

(** ** [liForall] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_do_forall A Δ (P : A → prop) :
    (∀ x, envs_entails Δ (P x)) → envs_entails Δ (∀ x : A, P x).
  Proof.
    rewrite envs_entails_unseal. intros HP. by apply bi.forall_intro.
  Qed.

  Lemma tac_do_exist_wand A Δ (P : A → prop) Q :
    (∀ x, envs_entails Δ (P x -∗ Q)) → envs_entails Δ ((∃ x : A, P x) -∗ Q).
  Proof.
    rewrite envs_entails_unseal. iIntros (HP) "Henv". iDestruct 1 as (x) "HP".
    by iApply (HP with "Henv HP").
  Qed.
End coq_tactics.

Ltac liForall :=
  (* n tells us how many quantifiers we should introduce with this name *)
  let rec do_intro n name :=
    lazymatch n with
    | S ?n' =>
      lazymatch goal with
      (* relying on the fact that unification variables cannot contain
         dependent variables to distinguish between dependent and non dependent forall *)
      | |- ?P -> ?Q =>
          lazymatch type of P with
          | Prop => fail "implication, not forall"
          | _ => (* just some unused variable, discard *) move => _
          end
      | |- forall _ : ?A, _ =>
        (* When changing this, also change [prepare_initial_coq_context] in automation.v *)
        lazymatch A with
        | (prod _ _) => case; do_intro (S (S O)) name
        | unit => case
        | _ =>
            first [
                (* We match again since having e in the context when
                calling fresh can mess up names. *)
                lazymatch goal with
                | |- forall e : ?A, @?P e =>
                    let sn := open_constr:(_ : nat) in
                    let p := constr:(_ : SimplForall A sn P _) in
                    refine (@simpl_forall_proof _ _ _ _ p _);
                    do_intro sn name
                end
              | let H := fresh name in intro H
              ]
        end
      end;
      do_intro n' name
    | O => idtac
    end
  in
  lazymatch goal with
  | |- envs_entails _ (bi_forall (λ name, _)) =>
      notypeclasses refine (tac_do_forall _ _ _ _); do_intro (S O) name
  | |- envs_entails _ (bi_wand (bi_exist (λ name, _)) _) =>
      notypeclasses refine (tac_do_exist_wand _ _ _ _ _); do_intro (S O) name
  | |- (∃ name, _) → _ =>
      case; do_intro (S O) name
  | |- forall name, _ =>
      do_intro (S O) name
  | _ => fail "liForall: unknown goal"
  end.

(** ** [liExist] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_ex {A} Δ (P : A → prop) :
    envs_entails Δ (∃ (x : A *ₗ unit), P x.1ₗ) →
    envs_entails Δ (∃ x, P x).
  Proof. apply tac_fast_apply. iIntros "[%a ?]". destruct a. iExists _. iFrame. Qed.

  Lemma tac_ex_evar {A} Δ x (P : A → prop) :
    envs_entails Δ (P x) →
    envs_entails Δ (∃ x, P x).
  Proof. apply tac_fast_apply. iIntros "?". iExists _. iFrame. Qed.

  Lemma tac_li_ex_ex {A B C} Δ (P : _ → _ → prop) :
    envs_entails Δ (∃ (x : C *ₗ A *ₗ B), P x.nextₗ x.1ₗ) →
    envs_entails Δ (∃ (x : A *ₗ B), ∃ y : C, P x y).
  Proof. apply tac_fast_apply. iIntros "[%a ?]". destruct a. iExists _, _. iFrame. Qed.

  Lemma tac_li_ex_ex_evar {A B C} Δ y (P : _ → _ → prop) :
    envs_entails Δ (∃ (x : A *ₗ B), P x y) →
    envs_entails Δ (∃ (x : A *ₗ B), ∃ y : C, P x y).
  Proof. apply tac_fast_apply. iIntros "[%a ?]". iExists _, _. iFrame. Qed.

  Lemma tac_li_ex_li_ex {A B C D} Δ (P : _ → _ → prop) :
    envs_entails Δ (∃ (x : C *ₗ A *ₗ B), ∃ y : D, P x.nextₗ (x.1ₗ, y)ₗ) →
    envs_entails Δ (∃ (x : A *ₗ B), ∃ y : (C *ₗ D), P x y).
  Proof. apply tac_fast_apply. iIntros "[%a [%b ?]]". destruct a. iExists _, _. iFrame. Qed.

  Lemma tac_li_ex_ex_unused {A B C} Δ (P : (A *ₗ B) → prop) :
    C →
    envs_entails Δ (∃ₗ x, P x) →
    envs_entails Δ (∃ₗ x, ∃ y : C, P x).
  Proof.
    move => x. apply tac_fast_apply. apply bi.exist_mono => ?.
    iIntros "?". by iExists x.
  Qed.

  Lemma tac_ex_unused {C} Δ (P : prop) :
    C →
    envs_entails Δ (P) →
    envs_entails Δ (∃ y : C, P).
  Proof.
    move => x. apply tac_fast_apply.
    iIntros "?". by iExists x.
  Qed.

  Lemma tac_li_ex_simpl {A B C} Δ (P : (A *ₗ B) → C → prop) Q :
    SimplExist C Q →
    envs_entails Δ (∃ₗ x, Q (P x)) →
    envs_entails Δ (∃ₗ x, ∃ y, P x y).
  Proof.
    unfold SimplExist. move => Hx. apply tac_fast_apply.
    iIntros "[%a HQ]". iDestruct (Hx with "HQ") as (?) "?".
    iExists _, _. iFrame.
  Qed.

  Lemma tac_ex_simpl {A} Δ (P : A → prop) Q :
    SimplExist A Q →
    envs_entails Δ (Q P) →
    envs_entails Δ (∃ y, P y).
  Proof. unfold SimplExist. move => Hx. by apply tac_fast_apply. Qed.
End coq_tactics.

Ltac liExist protect :=
  lazymatch goal with
  | |- envs_entails _ (∃ₗ _, ∃ₗ _, _) => repeat (refine (tac_li_ex_li_ex _ _ _)); red_li_prod
  | |- envs_entails _ (∃ₗ _, ∃ _, ?P) =>
          notypeclasses refine (tac_li_ex_ex_unused _ _ _ _);
            [first [exact inhabitant | assumption | shelve] |]
  | |- envs_entails _ (∃ₗ _, ∃ _, _) =>
      first [
          notypeclasses refine (tac_li_ex_simpl _ _ _ _ _); [solve [refine _] | cbv beta] |
          lazymatch protect with
          | true => refine (tac_li_ex_ex _ _ _)
          | false => refine (tac_li_ex_ex_evar _ _ _ _)
          end
        ]
  | |- envs_entails _ (∃ₗ _, ?P) =>
      (* TODO: Should we split up the (_ *ₗ _) here? *)
      notypeclasses refine (tac_ex_unused _ _ _ _);
        [first [exact inhabitant | assumption | shelve] |]
  | |- envs_entails _ (∃ₗ _, _) => fail "not handled by liExist"
  | |- envs_entails _ (∃ _, ?P) =>
          notypeclasses refine (tac_ex_unused _ _ _ _);
            [first [exact inhabitant | assumption | shelve] |]
  | |- envs_entails _ (∃ _, _) =>
      first [
          notypeclasses refine (tac_ex_simpl _ _ _ _ _); [solve [refine _] | cbv beta] |
          lazymatch protect with
          | true => refine (tac_ex _ _ _)
          | false => refine (tac_ex_evar _ _ _ _)
          end

        ]
  end.

Tactic Notation "liExist" constr(c) := liExist c.
Tactic Notation "liExist" := liExist true.

Module liExist_tests.
  Goal ∀ {prop : bi}, ∀ P : _ → _ → _ → _ → _ → _ → _ → prop,
    ⊢ ∃ (x : Z * Z) (y : nat) (z : unit) (eq : 1 + 1 = 2) (A : Type), ∃ (a : (N *ₗ positive *ₗ positive *ₗ unit)),
        P x y z (a.1ₗ) (a.2ₗ) eq A.
    intros. iStartProof.
    liExist.
    liExist.
    liExist.
    liExist.
    liExist.
    liExist.
    liExist.
    liExist.
    liExist.
    lazymatch goal with
    | |- envs_entails _ (∃ x : positive *ₗ positive *ₗ N *ₗ nat *ₗ Z *ₗ Z *ₗ (),
               P (x.6ₗ, x.5ₗ) x.4ₗ () x.3ₗ x.2ₗ eq_refl _) => idtac
    end.
  Abort.
End liExist_tests.

(** ** [liImpl] *)
Ltac liImpl :=
  (* We pass false since [(∃ name, _) → _] is handled by [liForall]. *)
  normalize_and_simpl_impl false.

(** ** [liSideCond] *)
Section coq_tactics.
  Context {prop : bi}.
  Lemma tac_sep_pure Δ (P : Prop) (Q : prop) :
    P → envs_entails Δ Q → envs_entails Δ (<affine> ⌜P⌝ ∗ Q).
  Proof.
    rewrite envs_entails_unseal => [HP HΔ].
    iIntros "HΔ". iSplit => //. by iApply HΔ.
  Qed.

  Lemma tac_sep_pure_and {A B} Δ (P1 P2 : _ → Prop) (Q : (A *ₗ B) → prop) :
    envs_entails Δ (∃ₗ x, <affine> ⌜P1 x⌝ ∗ <affine> ⌜P2 x⌝ ∗ Q x) → envs_entails Δ (∃ₗ x, <affine> ⌜P1 x ∧ P2 x⌝ ∗ Q x).
  Proof. apply tac_fast_apply. iIntros "[% [% [% ?]]]". iExists _. by iFrame. Qed.
  Lemma tac_sep_pure_exist {A B} {C} Δ (P : _ → C → Prop) (Q : (A *ₗ B) → prop) :
    envs_entails Δ (∃ₗ x, ∃ y, <affine> ⌜P x y⌝ ∗ Q x) → envs_entails Δ (∃ₗ x, <affine> ⌜∃ y, P x y⌝ ∗ Q x).
  Proof. apply tac_fast_apply. iIntros "[%a [% [% ?]]]". iExists _. iFrame. naive_solver. Qed.

  Lemma tac_normalize_goal_and_liex {A B} Δ (P1 P2 : _ → Prop) (Q : (A *ₗ B) → prop):
    (∀ x, P1 x = P2 x) → envs_entails Δ (∃ₗ x, <affine> ⌜P2 x⌝ ∗ Q x) → envs_entails Δ (∃ₗ x, <affine> ⌜P1 x⌝ ∗ Q x).
  Proof. move => HP. apply tac_fast_apply. iIntros "[%a ?]". rewrite -HP. iExists _. iFrame. Qed.

  Lemma tac_simpl_and_unsafe_envs {A B} Δ P1 P2 (Q : (A *ₗ B) → prop)
    `{!∀ x, SimplAndUnsafe (P1 x) (P2 x)}:
    envs_entails Δ (∃ₗ x, <affine> ⌜P2 x⌝ ∗ Q x) → envs_entails Δ (∃ₗ x, <affine> ⌜P1 x⌝ ∗ Q x).
  Proof.
    apply tac_fast_apply. unfold SimplAndUnsafe in *.
    iIntros "[% [% ?]]". iExists _. iFrame. naive_solver.
  Qed.

End coq_tactics.

Ltac liSideCond :=
  try liEnsureSepHead;
  lazymatch goal with
  | |- envs_entails ?Δ (bi_sep (<affine> ⌜?P⌝) ?Q) =>
      (* We use done instead of fast_done here because solving more
         sideconditions here is a bigger performance win than the overhead
         of done. *)
      notypeclasses refine (tac_sep_pure _ _ _ _ _); [ first [ done | shelve_sidecond ] | ]
  | |- envs_entails ?Δ (∃ₗ x, bi_sep (<affine> ⌜@?P x⌝) _) =>
      (* TODO: Can we get something like the old shelve_hint? *)
      (* TODO: figure out best order here *)
      match P with
      | _ => progress (notypeclasses refine (tac_normalize_goal_and_liex _ _ _ _ _ _);
                       (* cbv beta is important to correctly detect progress *)
                       [intros ?; normalize_hook|cbv beta])
      | _ => liExInst
      | (λ _, _ ∧ _)%type => notypeclasses refine (tac_sep_pure_and _ _ _ _ _)
      | (λ _, ∃ _, _)%type => notypeclasses refine (tac_sep_pure_exist _ _ _ _)
      | _ => notypeclasses refine (tac_simpl_and_unsafe_envs _ _ _ _ _); [solve [refine _] |]
      end
  end.

Module liSideCond_tests. Section test.
  Variable REL : Z → Z → Prop.
  Hypothesis (H : ∀ x y, SimplAndUnsafe (REL x y) (x = y)).


  Goal ∀ prop:bi, ∀ P : _ → _ → prop,
      ⊢ ∃ x y, <affine> ⌜1 = 1⌝ ∗ <affine>⌜1 = locked 1⌝ ∗ <affine>⌜x = 1 ∧ REL x y⌝ ∗ P x y.
    intros. iStartProof. repeat liExist.
    liSideCond.
    liSideCond.
    liSideCond.
    liSideCond.
    liSideCond. simpl.
    liSideCond.
    liExist.
    lazymatch goal with
    | |- envs_entails _ (P 1 (Z.of_nat 1)) => idtac
    end.
  Abort.
End test. End liSideCond_tests.

(** ** [liFindInContext] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_sep_true Δ (P : prop) :
    envs_entails Δ P → envs_entails Δ (True ∗ P).
  Proof. rewrite envs_entails_unseal => ->. by apply bi.True_sep_2. Qed.

  Lemma tac_find_hyp_equal key (Q P P' R : prop) Δ `{!FindHypEqual key Q P P'}:
    envs_entails Δ (P' ∗ R) →
    envs_entails Δ (P ∗ R).
  Proof. by revert select (FindHypEqual _ _ _ _) => ->. Qed.

  Lemma tac_find_hyp Δ i p R (P : prop) :
    envs_lookup i Δ = Some (p, P) →
    envs_entails (envs_delete false i p Δ) R → envs_entails Δ (P ∗ R).
  Proof.
    rewrite envs_entails_unseal. intros ? HQ.
    rewrite (envs_lookup_sound' _ false) // bi.intuitionistically_if_elim.
      by apply bi.sep_mono_r.
  Qed.

  Lemma tac_find_in_context {Δ} {fic} {T : _ → prop} key (F : FindInContext fic key) :
    envs_entails Δ (F T).(i2p_P) → envs_entails Δ (find_in_context fic T).
  Proof. rewrite envs_entails_unseal. etrans; [done|]. apply i2p_proof. Qed.

  Lemma tac_ex_find_in_context {Δ A B} fic (T : (A *ₗ B) → _ → prop) :
    envs_entails Δ (find_in_context fic (λ y, ∃ₗ x, T x y)%I) →
    envs_entails Δ (∃ₗ x, find_in_context fic (T x)).
  Proof.
    apply tac_fast_apply. iDestruct 1 as (?) "[?[% ?]]".
    iExists _, _. iFrame.
  Qed.

End coq_tactics.

Ltac liFindHyp key :=
  let rec go P Hs :=
    lazymatch Hs with
    | Esnoc ?Hs2 ?id ?Q => first [
      lazymatch key with
      | FICSyntactic =>
          (* We try to unify using the opaquenes hints of
             typeclass_instances. Directly doing exact: eq_refl
             sometimes takes 30 seconds to fail (e.g. when trying
             to unify GetMemberLoc for the same struct but with
             different names.) TODO: investigate if constr_eq
             could help even more
             https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacn.constr-eq*)
          unify Q P with typeclass_instances
      | _ =>
          notypeclasses refine (tac_find_hyp_equal key Q _ _ _ _ _); [solve [refine _]|];
          lazymatch goal with
          | |- envs_entails _ (?P' ∗ _) =>
              unify Q P' with typeclass_instances
          end
      end;
      notypeclasses refine (tac_find_hyp _ id _ _ _ _ _); [li_pm_reflexivity | li_pm_reduce]
      | go P Hs2 ]
    end in
  lazymatch goal with
  | |- envs_entails _ (?P ∗ _) =>
    let P := li_pm_reduce_val P in
    let run_go P Hs Hi := first [go P Hs | go P Hi] in
    lazymatch goal with
    | |- envs_entails (Envs ?Hi ?Hs _) _ => run_go P Hs Hi
    | H := (Envs ?Hi ?Hs _) |- _ => run_go P Hs Hi
    end
  end.

Ltac liFindHypOrTrue key :=
  first [
      notypeclasses refine (tac_sep_true _ _ _)
    | progress liFindHyp key
  ].

Ltac liFindInContext :=
  lazymatch goal with
  | |- envs_entails _ (∃ₗ _, find_in_context ?fic _) =>
      notypeclasses refine (tac_ex_find_in_context _ _ _)
  | |- _ => idtac
  end;
  lazymatch goal with
  | |- envs_entails _ (find_in_context ?fic ?T) =>
    let key := open_constr:(_) in
    (* We exploit that [typeclasses eauto] is multi-success to enable
    multiple implementations of [FindInContext]. They are tried in the
    order of their priorities.
    See https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Multi-success.20TC.20resolution.20from.20ltac.3F/near/242759123 *)
    once (simple notypeclasses refine (tac_find_in_context key _ _);
      [ shelve | typeclasses eauto | simpl; repeat liExist false; liFindHypOrTrue key ])
  end.


(** ** [liDoneEvar] *)
(** Internal goal to share evars between subgoals of and. Used by the
[□ P ∗ G] goal. *)
(* TODO: Use this more widely, e.g. for general ∧? *)

(** [li_done_evar_type] is an opaque wrapper for the type of the
shared evar since a hypothesis of type [?Goal] gets instantiated
accidentally by various tactics. *)
#[projections(primitive)] Record li_done_evar_type (A : Type) := { li_done_evar_val : A }.
Global Arguments li_done_evar_val {_} _.

Definition li_done_evar {prop:bi} {A X} (x : A) (y : li_done_evar_type X) (f : X → A) : prop :=
  ⌜x = f (li_done_evar_val y)⌝.
Section coq_tactics.
  Context {prop : bi}.
  Lemma tac_li_done_evar_ex {A X} (f : X → A) y Δ :
    envs_entails Δ (∃ x', li_done_evar (prop := prop) (f x') y f).
  Proof. rewrite envs_entails_unseal. iIntros "HΔ". by iExists _. Qed.

  Lemma tac_li_done_evar {A} (x : A) y Δ :
    envs_entails Δ (li_done_evar (prop := prop) x y (λ _ : unit, x)).
  Proof. rewrite envs_entails_unseal. iIntros "HΔ". done. Qed.
End coq_tactics.

Ltac liDoneEvar :=
  lazymatch goal with
  | |- envs_entails ?Δ (∃ₗ x', li_done_evar (@?x x') ?y _) =>
      notypeclasses refine (tac_li_done_evar_ex x y Δ)
  | |- envs_entails ?Δ (li_done_evar ?x ?y _) =>
      notypeclasses refine (tac_li_done_evar x y Δ)
  end.

(** ** [liSep] *)
Section coq_tactics.
  Context {prop : bi}.
  Hypothesis BiPositive_prop : BiPositive prop.
  Hypothesis BiPersistentlyForall_prop : BiPersistentlyForall prop.

  Lemma tac_sep_sep_assoc Δ (P Q R : prop) :
    envs_entails Δ (P ∗ Q ∗ R) → envs_entails Δ ((P ∗ Q) ∗ R).
  Proof. apply tac_fast_apply. iIntros "($&$&$)". Qed.

  Lemma tac_sep_sep_assoc_ex {A B} Δ (P Q R : (A *ₗ B) → prop) :
    envs_entails Δ (∃ₗ x, P x ∗ Q x ∗ R x) → envs_entails Δ (∃ₗ x, (P x ∗ Q x) ∗ R x).
  Proof. apply tac_fast_apply. iIntros "(%a&?&?&?)". iExists _. iFrame. Qed.

  Lemma tac_sep_emp Δ (P : prop) :
    envs_entails Δ P → envs_entails Δ (emp ∗ P).
  Proof. apply tac_fast_apply. by apply bi.emp_sep_1. Qed.

  Lemma tac_sep_exist_assoc {A} Δ (Φ : A → prop) (Q : prop):
    envs_entails Δ (∃ a : A, Φ a ∗ Q) → envs_entails Δ ((∃ a : A, Φ a) ∗ Q).
  Proof. by rewrite bi.sep_exist_r. Qed.

  Lemma tac_sep_exist_assoc_ex {A B C} Δ (Φ : (B *ₗ C) → A → prop) (Q : _ → prop):
    envs_entails Δ (∃ₗ x, ∃ a : A, Φ x a ∗ Q x) → envs_entails Δ (∃ₗ x, (∃ a : A, Φ x a) ∗ Q x).
  Proof. apply tac_fast_apply. apply bi.exist_mono => ?. by rewrite bi.sep_exist_r. Qed.

  Lemma tac_do_intro_intuit_sep Δ (P Q : prop) :
    envs_entails Δ (□ (P ∗ True) ∧ Q) → envs_entails Δ (□ P ∗ Q).
  Proof using BiPersistentlyForall_prop BiPositive_prop. apply tac_fast_apply. iIntros "[#[$ _] $]". Qed.

  Lemma tac_do_intro_intuit_sep_ex {A B X} Δ (P Q : (A *ₗ B) → prop) (f : X → _) :
    (∀ y, envs_entails Δ (□ (∃ₗ x, P x ∗ li_done_evar x y f))) →
    envs_entails Δ (∃ y, Q (f y)) →
    envs_entails Δ (∃ₗ x, □ (P x) ∗ Q x).
  Proof using BiPersistentlyForall_prop BiPositive_prop.
    rewrite envs_entails_unseal /li_done_evar. move => /bi.forall_intro HP HQ.
    iIntros "HΔ". iDestruct (HP with "HΔ") as "#HP".
    iDestruct (HQ with "HΔ") as (y) "HQ".
    iDestruct ("HP" $! {|li_done_evar_val := y|}) as (?) "[#? ->]". simpl.
    iExists _. iFrame "∗#".
  Qed.

  Lemma tac_do_simplify_goal Δ (n : N) (P : prop) T {SG : SimplifyGoal P (Some n)} :
    envs_entails Δ (SG T).(i2p_P) → envs_entails Δ (P ∗ T).
  Proof. apply tac_fast_apply. iIntros "HP". by iApply (i2p_proof with "HP"). Qed.

  Lemma tac_do_simplify_goal_ex {A B} Δ (n : N) (P : (A *ₗ B) → prop) T
    {SG : ∀ x, SimplifyGoal (P x) (Some n)} :
    envs_entails Δ (∃ₗ x, (SG x (T x)).(i2p_P)) → envs_entails Δ (∃ₗ x, P x ∗ T x).
  Proof.
    apply tac_fast_apply. apply bi.exist_mono => ?.
    iIntros "HP". by iApply (i2p_proof with "HP").
  Qed.

  Lemma tac_intro_subsume_related Δ P T {Hrel : RelatedTo (λ _ : unit, P)}:
    envs_entails Δ (find_in_context Hrel.(rt_fic) (λ x,
      @subsume prop unit (Hrel.(rt_fic).(fic_Prop) x) (λ _, P) (λ _, T))) →
    envs_entails Δ (P ∗ T).
  Proof.
    apply tac_fast_apply. iDestruct 1 as (x) "[HP HT]".
    iDestruct ("HT" with "HP") as (?) "$".
  Qed.

  Lemma tac_intro_subsume_related_ex Δ {A B} (P T : (A *ₗ B) → prop) {Hrel : RelatedTo P}:
    envs_entails Δ (find_in_context Hrel.(rt_fic) (λ x,
      @subsume prop _ (Hrel.(rt_fic).(fic_Prop) x) P T)) →
    envs_entails Δ (∃ₗ x, P x ∗ T x).
  Proof. apply tac_fast_apply. iDestruct 1 as (x) "[HP HT]". by iApply "HT". Qed.

End coq_tactics.

Ltac liSep :=
  try liEnsureSepHead;
  lazymatch goal with
  | |- envs_entails ?Δ (bi_sep ?P ?Q) =>
    lazymatch P with
    | bi_sep _ _ => notypeclasses refine (tac_sep_sep_assoc _ _ _ _ _)
    | bi_exist _ => notypeclasses refine (tac_sep_exist_assoc _ _ _ _)
    | bi_emp => notypeclasses refine (tac_sep_emp _ _ _)
    | (⌜_⌝)%I => fail "handled by liSideCond"
    | (□ ?P)%I => notypeclasses refine (tac_do_intro_intuit_sep _ _ _ _ _ _)
    | match ?x with _ => _ end => fail "should not have match in sep"
    | ?P => first [
        progress liFindHyp FICSyntactic
      | simple notypeclasses refine (tac_do_simplify_goal _ 0%N _ _ _); [solve [refine _] |]
      | simple notypeclasses refine (tac_intro_subsume_related _ _ _ _); [solve [refine _] |];
        simpl; liFindInContext
      | simple notypeclasses refine (tac_do_simplify_goal _ _ _ _ _); [| solve [refine _] |]
      | fail "liSep: unknown sidecondition" P
    ]
    end
  | |- envs_entails ?Δ (∃ₗ x, bi_sep (@?P x) _) =>
    lazymatch P with
    | (λ _, bi_sep _ _) => notypeclasses refine (tac_sep_sep_assoc_ex _ _ _ _ _)
    | (λ _, bi_exist _) => notypeclasses refine (tac_sep_exist_assoc_ex _ _ _ _)
    (* bi_emp cannot happen because it is independent of evars *)
    | (λ _, (⌜_⌝)%I) => fail "handled by liSideCond"
    | (λ _, (□ _)%I) => refine (tac_do_intro_intuit_sep_ex _ _ _ _ _ _ _ _)
    (* The following is probably not necessary: *)
    (* | match ?x with _ => _ end => fail "should not have match in sep" *)
    | ?P => first [
        (* We can't (and don't want to) cancel if there is an evar in the goal *)
        (* progress liFindHyp FICSyntactic | *)
        (* We use cbv beta to reduce the beta expansion in
        SimplifyGoal such that we can match on proposition in the
        pattern of Hint Extern. *)
        simple notypeclasses refine (tac_do_simplify_goal_ex _ 0%N _ _ _); [intro; cbv beta; solve [refine _] |]
      | simple notypeclasses refine (tac_intro_subsume_related_ex _ _ _ _); [solve [refine _] |];
        simpl; liFindInContext
      | simple notypeclasses refine (tac_do_simplify_goal_ex _ _ _ _ _); [|intro; cbv beta; solve [refine _] |]
      | fail "liSep: unknown sidecondition" P
    ]
    end
  end.

Module liSep_tests. Section test.
  Context {prop : bi}.
  Hypothesis BiPositive_prop : BiPositive prop.
  Hypothesis BiPersistentlyForall_prop : BiPersistentlyForall prop.

  Variable A1 A2 A3 : Z → prop.

  Hypothesis HA2 : ∀ (n : Z) G, (<affine> ⌜n = 1%Z⌝ ∗ G ⊢ simplify_goal (A2 n) G).
  Definition HA2_inst := [instance HA2 with 0%N].
  Local Existing Instance HA2_inst.

  Definition FindA3 := {| fic_A := Z; fic_Prop := A3; |}.
  Local Typeclasses Opaque FindA3.

  Lemma find_in_context_A3 (T : Z → prop):
    find_in_context (FindA3) T :- pattern: x, A3 x; return T x.
  Proof. done. Qed.
  Definition find_in_context_A3_inst := [instance @find_in_context_A3 with FICSyntactic].
  Local Existing Instance find_in_context_A3_inst | 1.

  Local Instance A3_related A n : RelatedTo (λ x : A, A3 (n x)) :=
    {| rt_fic := FindA3 |}.

  Lemma subsume_A3 A n m G:
    subsume (A3 n) (λ x : A, A3 (m x)) G :- ∃ x, exhale <affine> ⌜n = m x⌝; return G x.
  Proof. liFromSyntax. iDestruct 1 as (? ->) "?". iIntros "?". iExists _. iFrame. Qed.

  Definition subsume_A3_inst := [instance subsume_A3].
  Local Existing Instance subsume_A3_inst.


  Goal ∀ P : Z → Z → prop,
      ⊢ A1 1 -∗ A3 1 -∗ ∃ x y, (A1 1 ∗ ∃ z, A2 x ∗ A3 z ∗ <affine> ⌜z = y⌝) ∗ P x y.
    intros. iStartProof. iIntros. repeat liExist.
    liSep.
    liSep.
    liSep.
    liExist.
    liSep.
    liSep. simpl.
    liSideCond.
    liSep.
    liSep.
    liExtensible. simpl. li_unfold_lets_in_context.
    liSideCond.
    liSideCond.
    liExist.
    lazymatch goal with
    | |- envs_entails _ (P 1%Z 1%Z) => idtac
    end.
  Abort.

  Goal  ∀ P : Z → Z → Z → prop,
      ⊢ ∃ x y z, □ (<affine> ⌜x = 1%Z⌝ ∗ <affine> ⌜y = 2%Z⌝) ∗ <affine> ⌜z = 3%Z⌝ ∗ P x y z.
    intros. iStartProof. iIntros. repeat liExist.
    1: liSep.
    1: liForall.
    1: iModIntro.
    1: liSep.
    1: liSideCond.
    1: liSideCond.
    1: liDoneEvar.
    1: liSideCond.
    1: liExist.
    lazymatch goal with
    | |- envs_entails _ (P 1%Z 2%Z 3%Z) => idtac
    end.
  Abort.

  Goal  ∀ P : Z → Z → Z → prop,
      ⊢ ∃ x y z, □ (<affine> ⌜x = 1%Z⌝ ∗ □ <affine> ⌜y = 2%Z⌝) ∗ <affine> ⌜z = 3%Z⌝ ∗ P x y z.
    intros. iStartProof. iIntros. repeat liExist.
    1: liSep.
    1: liForall.
    1: iModIntro.
    1: liSep.
    1: liSideCond.
    1: liSep.
    1: liForall.
    1: iModIntro.
    1: liSideCond.
    1: liDoneEvar.
    1: liDoneEvar.
    1: liSideCond.
    1: liExist.
    lazymatch goal with
    | |- envs_entails _ (P 1%Z 2%Z 3%Z) => idtac
    end.
  Abort.

  Goal  ∀ P : Z → Z → Z → prop,
      ⊢ ∃ x y z, □ (<affine> ⌜x = 1%Z⌝ ∗ <affine> ⌜y = 2%Z⌝ ∗ <affine> ⌜z = 3%Z⌝) ∗ P x y z.
    intros. iStartProof. iIntros. repeat liExist.
    1: liSep.
    1: liForall.
    1: iModIntro.
    1: liSep.
    1: liSideCond.
    1: liSep.
    1: liSideCond.
    1: liSideCond.
    1: liExist.
    1: liDoneEvar.
    1: liExist.
    1: liSimpl.
    lazymatch goal with
    | |- envs_entails _ (P 1%Z 2%Z 3%Z) => idtac
    end.
  Abort.

  Goal  ∀ P : Z → prop,
      ⊢ ∃ x, □ (const (<affine> True) x) ∗ <affine> ⌜x = 1%Z⌝ ∗ P x.
    intros. iStartProof. iIntros. repeat liExist.
    1: liSep.
    1: liForall.
    1: iModIntro. 1: simpl.
    1: liSideCond.
    1: liDoneEvar.
    1: liSideCond.
    1: liExist.
    lazymatch goal with
    | |- envs_entails _ (P 1%Z) => idtac
    end.
  Abort.

End test. End liSep_tests.


(** ** [liWand] *)
Section coq_tactics.
  Context {prop : bi}.
  Hypothesis BiPositive_prop : BiPositive prop.
  Hypothesis BiPersistentlyForall_prop : BiPersistentlyForall prop.

  Lemma tac_do_intro_pure Δ (P : Prop) (Q : prop) :
    (P → envs_entails Δ Q) → envs_entails Δ (<affine> ⌜P⌝ -∗ Q).
  Proof.
    rewrite envs_entails_unseal => HP. iIntros "HΔ %".  by iApply HP.
  Qed.

  Lemma tac_do_simplify_hyp (P : prop) (SH: SimplifyHyp P (Some 0%N)) Δ T :
    envs_entails Δ (SH T).(i2p_P) →
    envs_entails Δ (P -∗ T).
  Proof.
    rewrite envs_entails_unseal => HP. iIntros "Henv Hl".
    iDestruct (HP with "Henv") as "HP".
    iDestruct (i2p_proof with "HP Hl") as "$".
  Qed.

  Lemma tac_do_intro i n' (P : prop) n Γs Γp T :
    env_lookup i Γs = None →
    env_lookup i Γp = None →
    envs_entails (Envs Γp (Esnoc Γs i P) n') T →
    envs_entails (Envs Γp Γs n) (P -∗ T).
  Proof.
    rewrite envs_entails_unseal => Hs Hp HP. iIntros "Henv Hl".
    rewrite (envs_app_sound (Envs Γp Γs n) (Envs Γp (Esnoc Γs i P) n) false (Esnoc Enil i P)) //; simplify_option_eq => //.
    iApply HP. iApply "Henv". iFrame.
  Qed.

  Lemma tac_do_intro_intuit i n' (P P' : prop) T n Γs Γp (Hpers : IntroPersistent P P') :
    env_lookup i Γs = None →
    env_lookup i Γp = None →
    envs_entails (Envs (Esnoc Γp i P') Γs n') T →
    envs_entails (Envs Γp Γs n) (<affine> P -∗ T).
  Proof.
    rewrite envs_entails_unseal => Hs Hp HP. iIntros "Henv HP".
    iDestruct (@ip_persistent _ _ _ Hpers with "HP") as "#HP'".
    rewrite (envs_app_sound (Envs Γp Γs n) (Envs (Esnoc Γp i P') Γs n) true (Esnoc Enil i P')) //; simplify_option_eq => //.
    iApply HP. iApply "Henv".
    iModIntro. by iSplit.
  Qed.

  Lemma tac_wand_sep_assoc Δ (P Q R : prop) :
    envs_entails Δ (P -∗ Q -∗ R) → envs_entails Δ ((P ∗ Q) -∗ R).
  Proof. by rewrite bi.wand_curry. Qed.

  Lemma tac_wand_emp Δ (P : prop) :
    envs_entails Δ P → envs_entails Δ (emp -∗ P).
  Proof. apply tac_fast_apply. by iIntros. Qed.

  Lemma tac_wand_pers_sep Δ (P : prop) (Q1 Q2 : prop) :
    envs_entails Δ ((□ Q1 ∗ □ Q2) -∗ P) → envs_entails Δ (□ (Q1 ∗ Q2) -∗ P).
  Proof using BiPositive_prop. apply tac_fast_apply. iIntros "Hx #[? ?]". iApply "Hx". iFrame "#". Qed.

  Lemma tac_wand_pers_exist A Δ (P : prop) (Q : A → prop) :
    envs_entails Δ ((∃ x, □ Q x) -∗ P) → envs_entails Δ (□ (∃ x, Q x) -∗ P).
  Proof. apply tac_fast_apply. iIntros "Hx #[% ?]". iApply "Hx". iExists _. iFrame "#". Qed.

  Lemma tac_wand_pers_pure Δ (P : prop) Φ :
    envs_entails Δ (⌜Φ⌝ -∗ P) → envs_entails Δ (□ ⌜Φ⌝ -∗ P).
  Proof. apply tac_fast_apply. iIntros "HP %". by iApply "HP". Qed.
End coq_tactics.

Ltac liWand :=
  let wand_intro P :=
    first [
      let SH := constr:(_ : SimplifyHyp P (Some 0%N)) in
      simple notypeclasses refine (tac_do_simplify_hyp P SH _ _ _)
    | let P' := open_constr:(_) in
      let ip := constr:(_ : IntroPersistent P P') in
      let n := lazymatch goal with | [ H := Envs _ _ ?n |- _ ] => n end in
      let H := constr:(IAnon n) in
      let n' := eval vm_compute in (Pos.succ n) in
      simple notypeclasses refine (tac_do_intro_intuit H n' P P' _ _ _ _ ip _ _ _); [li_pm_reflexivity..|]
    | let n := lazymatch goal with | [ H := Envs _ _ ?n |- _ ] => n end in
      let H := constr:(IAnon n) in
      let n' := eval vm_compute in (Pos.succ n) in
      simple notypeclasses refine (tac_do_intro H n' P _ _ _ _ _ _ _); [li_pm_reflexivity..|]
    ] in
  lazymatch goal with
  | |- envs_entails ?Δ (bi_wand ?P ?T) =>
      lazymatch P with
      | bi_sep _ _ =>
          li_let_bind T (fun H => constr:(envs_entails Δ (bi_wand P H)));
          notypeclasses refine (tac_wand_sep_assoc _ _ _ _ _)
      | bi_exist _ => fail "handled by liForall"
      | bi_emp => notypeclasses refine (tac_wand_emp _ _ _)
      | bi_pure _ => notypeclasses refine (tac_do_intro_pure _ _ _ _)
      | bi_intuitionistically (bi_sep _ _) => notypeclasses refine (tac_wand_pers_sep _ _ _ _ _)
      | bi_intuitionistically (bi_exist _) => notypeclasses refine (tac_wand_pers_exist _ _ _ _ _)
      | bi_intuitionistically (bi_pure _) => notypeclasses refine (tac_wand_pers_pure _ _ _ _)
      | match ?x with _ => _ end => fail "should not have match in wand"
      | _ => wand_intro P
      end
  end.

(** ** [liAnd] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_do_split Δ (P1 P2 : prop):
    envs_entails Δ P1 →
    envs_entails Δ P2 →
    envs_entails Δ (P1 ∧ P2).
  Proof. rewrite envs_entails_unseal => HP1 HP2. by apply bi.and_intro. Qed.

  Lemma tac_big_andM_insert Δ {A B} `{Countable A} (m : gmap A B) i n (Φ : _ → _→ prop) :
    envs_entails Δ (<affine> ⌜m !! i = None⌝ ∗ (Φ i n ∧ [∧ map] k↦v∈m, Φ k v)) →
    envs_entails Δ ([∧ map] k↦v∈<[i:=n]>m, Φ k v).
  Proof. apply tac_fast_apply. iIntros "[% HT]". by rewrite big_andM_insert. Qed.

  Lemma tac_big_andM_empty Δ {A B} `{Countable A} (Φ : _ → _→ prop) :
    envs_entails Δ ([∧ map] k↦v∈(∅ : gmap A B), Φ k v).
  Proof. rewrite envs_entails_unseal. iIntros "?". by rewrite big_andM_empty. Qed.
End coq_tactics.

Ltac liAnd :=
  lazymatch goal with
  | |- envs_entails _ (bi_and ?P _) =>
    notypeclasses refine (tac_do_split _ _ _ _ _)
  | |- envs_entails _ ([∧ map] _↦_∈<[_:=_]>_, _) =>
    notypeclasses refine (tac_big_andM_insert _ _ _ _ _ _)
  | |- envs_entails _ ([∧ map] _↦_∈∅, _) =>
    notypeclasses refine (tac_big_andM_empty _ _)
  end.

(* TODO Ke: is not valid anymore because logic is linear? maybe to a weaker version where spatial context is empty? *)
(* 
(** ** [liPersistent] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_persistent Δ (P : prop) :
    envs_entails (envs_clear_spatial Δ) P → envs_entails Δ (□ P).
  Proof.
    rewrite envs_entails_unseal => HP. iIntros "Henv".
    iDestruct (envs_clear_spatial_sound with "Henv") as "[#Henv _]".
    iModIntro. iApply (HP with "Henv").
  Qed. 
End coq_tactics.

Ltac liPersistent :=
  lazymatch goal with
  | |- envs_entails ?Δ (bi_intuitionistically ?P) =>
      notypeclasses refine (tac_persistent _ _ _); li_pm_reduce
  end.
*)

(** ** [liCase] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_case_if Δ (P : Prop) T1 T2 :
    (P → envs_entails Δ T1) →
    (¬ P → envs_entails Δ T2) →
    envs_entails Δ (@case_if prop P T1 T2).
  Proof.
    rewrite envs_entails_unseal => HT1 HT2.
    iIntros "Henvs". iSplit; iIntros (?).
    - by iApply HT1.
    - by iApply HT2.
  Qed.

  Lemma tac_case_destruct_bool_decide Δ (P : Prop) `{!Decision P} T:
    (P → envs_entails Δ (T true true)) →
    (¬ P → envs_entails Δ (T false true)) →
    envs_entails Δ (@case_destruct prop bool (bool_decide P) T).
  Proof.
    rewrite envs_entails_unseal => HP HnotP.
    iIntros "Henvs". iExists true. case_bool_decide.
    - by iApply HP.
    - by iApply HnotP.
  Qed.

  Lemma tac_case_destruct {A} (b : bool) Δ a T:
    envs_entails Δ (T a b) →
    envs_entails Δ (@case_destruct prop A a T).
  Proof. apply tac_fast_apply. iIntros "?". iExists _. iFrame. Qed.
End coq_tactics.

(* This tactic checks if destructing x would lead to multiple
non-trivial subgoals. The main reason for it is that we don't want to
destruct constructors like true as this would not be useful. *)
Ltac non_trivial_destruct x :=
  first [
      have : (const False x); [ clear; case_eq x; intros => //; (*
      check if there is only one goal remaining *) [ idtac ]; fail 1 "trivial destruct" |]
    | idtac
  ].

Ltac liCase :=
  lazymatch goal with
  | |- @envs_entails ?prop ?Δ (case_if ?P ?T1 ?T2) =>
      notypeclasses refine (tac_case_if _ _ _ _ _ _)
  | |- @envs_entails ?prop ?Δ (case_destruct (@bool_decide ?P ?b) ?T) =>
      notypeclasses refine (tac_case_destruct_bool_decide _ _ _ _ _)
      (* notypeclasses refine (tac_case_destruct true _ _ _ _); *)
      (* let H := fresh "H" in destruct_decide (@bool_decide_reflect P b) as H; revert H *)
  | |- @envs_entails ?prop ?Δ (case_destruct ?x ?T) =>
      tryif (non_trivial_destruct x) then
        notypeclasses refine (tac_case_destruct true _ _ _ _);
        case_eq x
      else (
        notypeclasses refine (tac_case_destruct false _ _ _ _)
      )
  end;
  (* It is important that we prune branches this way because this way
  we don't need to do normalization and simplification of hypothesis
  that we introduce twice, which has a big impact on performance. *)
  repeat (liForall || liImpl); try by [exfalso; can_solve].

(** ** [liTactic] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_li_tactic {A} Δ t (th : LiTactic t) (Q : A → prop):
    envs_entails Δ (th.(li_tactic_P) Q) →
    envs_entails Δ (li_tactic t Q).
  Proof. rewrite envs_entails_unseal => ?. etrans; [done|]. apply li_tactic_proof. Qed.
End coq_tactics.

Ltac liTactic :=
  lazymatch goal with
  | |- envs_entails _ (li_tactic _ _) =>
      simple notypeclasses refine (tac_li_tactic _ _ _ _ _); [ solve [refine _] |]
  end.

(** ** [liAccu] *)
Section coq_tactics.
  Context {prop : bi}.

  Lemma tac_do_accu Δ (f : prop → prop):
    envs_entails (envs_clear_spatial Δ) (f (env_to_prop (env_spatial Δ))) →
    envs_entails Δ (accu f).
  Proof.
    rewrite envs_entails_unseal => Henv. iIntros "Henv".
    iDestruct (envs_clear_spatial_sound with "Henv") as "[#Henv Hs]".
    iExists (env_to_prop (env_spatial Δ)).
    rewrite -env_to_prop_sound. iFrame. iModIntro. by iApply (Henv with "Henv").
  Qed.
End coq_tactics.

Ltac liAccu :=
  lazymatch goal with
  | |- envs_entails _ (accu _) =>
    notypeclasses refine (tac_do_accu _ _ _); li_pm_reduce
  end.

(** ** [liTrace] *)
Ltac liTrace :=
  lazymatch goal with
  | |- @envs_entails ?prop ?Δ (li_trace ?info ?T) =>
    change_no_check (@envs_entails prop Δ T);
    liTrace_hook info
  end.

(** ** [liStep] *)
Ltac liStep :=
  first [
      liExtensible
    | liSep
    | liAnd
    | liWand
    | liExist
    | liImpl
    | liForall
    | liSideCond
    | liFindInContext
    | liCase
    | liTrace
    | liTactic
    (* | liPersistent *)
    | liTrue
    | liFalse
    | liAccu
    | liDoneEvar
    | liUnfoldLetGoal
    ].
