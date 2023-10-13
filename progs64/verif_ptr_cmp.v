Require Import VST.floyd.proofauto.
Require Import VST.progs64.ptr_cmp.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section Spec.

Context  `{!default_VSTGS Σ}.

Definition t_struct_tree := Tstruct _tree noattr.

(** Some useful lemmas about comparing two pointers. 
    Now these lemmas has been defined in VST/floyd/forward.v. *)

Inductive Tree : Type :=
  | E
  | T (k: Z) (lch: Tree) (rch: Tree).

(** Representation of trees in memory. *)
Fixpoint tree_rep (t: Tree) (p p_lch p_rch: val): mpred :=
  match t with
  | T k lch rch   =>
    ∃ (p_lch_l p_lch_r p_rch_l p_rch_r: val),
    data_at Tsh t_struct_tree 
      (Vint (Int.repr k), (p_lch, p_rch)) p
    ∗ tree_rep lch p_lch p_lch_l p_lch_r 
    ∗ tree_rep rch p_rch p_rch_l p_rch_r 
  | E => ⌜p = nullval⌝ ∧ emp 
  end.

(** Representation of the parent-child relationship. *)
Definition fa_rep (d: bool) (t: Tree) (p_ch p_fa: val) : mpred :=
  match d with
  | true    => 
    ∃ p_oppo: val, tree_rep t p_fa p_ch p_oppo
  | false   =>
    ∃ p_oppo: val, tree_rep t p_fa p_oppo p_ch
  end.

(** Some basic lemmas. *)
Lemma tree_rep_saturate_local:
   forall t p p_lch p_rch, tree_rep t p p_lch p_rch ⊢ ⌜is_pointer_or_null p⌝.
Proof.
  destruct t; simpl; intros.
  entailer!.
  Intros p_lch_l p_lch_r p_rch_l p_rch_r. entailer!.
Qed.
Hint Resolve tree_rep_saturate_local: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t p p_lch p_rch, tree_rep t p p_lch p_rch ⊢ valid_pointer p.
Proof.
  intros.
  destruct t. 
  - simpl. entailer!. 
  - simpl; normalize; auto with valid_pointer.
Qed.
Hint Resolve tree_rep_valid_pointer: valid_pointer.

Definition bool2int (d: bool) : Z :=
  match d with
  | true    => 1
  | false   => 0
  end.

(** Define the specification. *)
Definition get_branch_spec :=
 DECLARE _get_branch
  WITH t: Tree, d: bool, p_fa: val, p: val
  PRE  [ tptr t_struct_tree, tptr t_struct_tree ]
    PROP (p_fa <> nullval; p <> nullval) 
    (** It is reasonable to assume that both p and p_fa are not null pointers. *)
    PARAMS (p; p_fa)
    SEP (fa_rep d t p p_fa)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (bool2int d)))
    SEP (fa_rep d t p p_fa).

Definition Gprog : funspecs :=
  ltac:(with_library prog [get_branch_spec]).

(** Now try to prove this program. *)
Theorem body_get_branch_old_fashion: semax_body Vprog Gprog ⊤ f_get_branch get_branch_spec.
Proof.
  start_function. 
  (* first eliminate the possibility that t is empty *)
  destruct t.
  { 
    destruct d; simpl fa_rep; Intros a; apply H in H1; destruct H1.
  } 
  (** A meta-level discussion. Not a good solution. *)
  destruct d.
  {
    (* If p is the left child of p_fa *)
    simpl fa_rep.
    Intros p_oppo p_lch_l p_lch_r p_rch_l p_rch_r.
    forward.
    forward_if.
    {
      (* valid case *)
      forward.                                        (* return 1; *)
      simpl.
      Exists p_oppo p_lch_l p_lch_r p_rch_l p_rch_r.
      entailer!.
    }
    {
      contradiction.
    }
  }
  { 
    (* If p is the right child of p_fa *)
    simpl fa_rep.
    Intros p_oppo p_lch_l p_lch_r p_rch_l p_rch_r.
    forward.
    forward_if.
    { 
      (* invalid case *)
      destruct t1; destruct t2;
        simpl;
        Intros;
        subst;
        try contradiction.
      simpl tree_rep.
      Intros p_lch_l0 p_lch_r0 p_rch_l0 p_rch_r0.
      Intros p_lch_l1 p_lch_r1 p_rch_l1 p_rch_r1.
      (** Now use data_at_conflict to solve it. *)
      pose proof 
      (data_at_conflict Tsh t_struct_tree 
        (Vint (Int.repr k0), (p_lch_l, p_lch_r))
        (Vint (Int.repr k1), (p_rch_l, p_rch_r))
        p_oppo Share.nontrivial).
        unfold POSTCONDITION. unfold abbreviate.
        
        (* sep_apply H1. *)
        (* new_sep_apply H1 sep_apply_evar_tac sep_apply_prop_tac. *)
        (* new_sep_apply_in_semax H1 sep_apply_evar_tac sep_apply_prop_tac. *)
        eapply semax_pre(*_bupd*).
        (* new_sep_apply_in_lifted_entailment H evar_tac prop_tac. *)
        apply SEP_entail'.

  (* go_lower; *)
  clear_Delta_specs;
intros;
match goal with
 | |- local _ ∧ PROPx _ (LOCALx _ (SEPx ?R)) ⊢ _ => check_mpreds R
 | |- ENTAIL _, PROPx _ (LOCALx _ (SEPx ?R)) ⊢ _ => check_mpreds R
 | |- ENTAIL _, _ ⊢ _ => fail 10 "The left-hand-side of your entailment is not in PROP/LOCAL/SEP form"
 | _ => fail 10 "go_lower requires a proof goal in the form of (ENTAIL _ , _ ⊢ _)"
end.
(* clean_LOCAL_canon_mix. *)
eapply_clean_LOCAL_right_spec;
[solve_all_legal_glob_ident | prove_local2ptree | 
(* solve_clean_LOCAL_right *)
 | simpl_app_localdefs_tc].
 let TT1 := fresh "T1" in 
 let TT2 := fresh "T2" in
 let ggv := fresh "GV" in
 match goal with 
 | |- clean_LOCAL_right Delta ?T1 ?T2 ?GV ?ass ?mp =>
 pose T1 as TT1; pose T2 as TT2; pose GV as ggv
 end.

 pose proof (clean_LOCAL_right_sep_lift Delta T1 T2 None).
 unfold T1, T2 in H2.
 Search embed liftx.
 apply H2. 
 (* solve_clean_LOCAL_right. *)




repeat (simple apply derives_extract_PROP; intro_PROP);
let rho := fresh "rho" in
split => rho;
first
[ simple apply quick_finish_lower
|          
 (let TC := fresh "TC" in apply finish_lower; intros TC ||
 match goal with
 | |- (_ ∧ PROPx nil _) _ ⊢ _ => fail 1 "LOCAL part of precondition is not a concrete list (or maybe Delta is not concrete)"
 | |- _ => fail 1 "PROP part of precondition is not a concrete list"
 end);
cbv [fold_right_sepcon];
unfold_for_go_lower;
simpl tc_val;
cbv [typecheck_exprlist typecheck_expr]; simpl tc_andp;
simpl msubst_denote_tc_assert;
try monPred.unseal; unfold monPred_at;
try clear dependent rho;
clear_Delta;
rewrite ?bi.sep_emp
].


  match goal with |- ?R ⊢ ?R2 =>
    let r2 := fresh "R2" in pose (r2 := R2); change (R ⊢ r2);
    new_sep_apply_in_entailment H evar_tac prop_tac; [ .. |
    match goal with |- ?R' ⊢ _ =>
      let R'' := refold_right_sepcon R' in
      replace R' with (fold_right_sepcon R'')
             by (unfold fold_right_sepcon; rewrite ?bi.sep_emp; reflexivity);
          subst r2; apply derives_refl
    end]
  end.


        lazymatch goal with
  | |- ENTAIL _ , _ ⊢ _ => eapply ENTAIL_trans; [new_sep_apply_in_lifted_entailment H1 sep_apply_evar_tac sep_apply_prop_tac | ]
  | |- _ ⊢ _ => new_sep_apply_in_entailment H1 sep_apply_evar_tac sep_apply_prop_tac
  | |- semax _ _ _ _ _ => new_sep_apply_in_semax H1 sep_apply_evar_tac sep_apply_prop_tac
  end.

      
      sep_apply FF_local_facts.
      Intros.
      destruct H2.
    }
    {
      (* valid case *)
      forward.                                        (* return 0; *)
      simpl.
      Exists p_oppo p_lch_l p_lch_r p_rch_l p_rch_r.
      entailer!.
    }
  }
Qed.

(** To make the proof more concise, here we define some tactics to help us. *)

Lemma tree_rep_conflict :
  forall p t1 t2 p_ll p_lr p_rl p_rr, 
  p <> nullval ->
  tree_rep t1 p p_ll p_lr * tree_rep t2 p p_rl p_rr |-- !! False.
Proof.
  intros.
  destruct t1. 
  {
    simpl.
    Intros.
    apply H in H0. destruct H0.
  }
  destruct t2. 
  {
    simpl.
    Intros.
    apply H in H0. destruct H0.
  }
  simpl tree_rep.
  Intros p_lch_l0 p_lch_r0 p_rch_l0 p_rch_r0.
  Intros p_lch_l1 p_lch_r1 p_rch_l1 p_rch_r1.
  data_at_conflict p.
Qed.

Ltac tree_rep_conflict :=
  try (sep_apply tree_rep_conflict; Intros; exfalso; assumption).

Ltac show_the_way d := 
  destruct d; simpl fa_rep; 
  Intros p_oppo p_lch_l p_lch_r p_rch_l p_rch_r; 
  forward; forward_if; 
  subst;
  try tree_rep_conflict. 

Theorem body_get_branch_new_fashion: semax_body Vprog Gprog f_get_branch get_branch_spec.
Proof.

  (** Now prove the theorem again, with the new tactics. *)

  start_function. 
  (* first eliminate the possibility that t is empty *)
  destruct t.
  { 
    destruct d; simpl fa_rep; Intros a; apply H in H1; destruct H1.
  }
  show_the_way d;
  (** The invalid cases are ruled out automatically. *)
  forward; simpl;
  Exists p_oppo p_lch_l p_lch_r p_rch_l p_rch_r;
  entailer!.
Qed.