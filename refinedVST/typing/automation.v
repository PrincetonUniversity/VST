(* refinedC/typing/automation.v *)
From iris.proofmode Require Import coq_tactics reduction.
From lithium Require Import hooks normalize.
From VST.lithium Require Export all.
From VST.typing Require Export type.
From VST.typing.automation Require Export proof_state (* solvers simplification loc_eq. *).
From VST.typing Require Import programs function singleton array (* struct *) bytes own int.
Set Default Proof Using "Type".
Set Nested Proofs Allowed.
(** * Defining extensions *)
(** The [sidecond_hook] and [unsolved_sidecond_hook] hooks that get
called for all sideconditions resp. all sideconditions that are not
automatically solved using the default solver. *)
Ltac sidecond_hook := idtac.
Ltac unsolved_sidecond_hook := idtac.

(** * Registering extensions *)
(** We use autorewrite for the moment. *)
Ltac normalize_hook ::= normalize_autorewrite.
(* Goal ∀ l i (x : Z), *)
(*     0 < length (<[i:=x]> $ <[i:=x]> (<[length (<[i:=x]>l) :=x]> l ++ <[length (<[i:=x]>l) :=x]> l)). *)
(*   move => ???. normalize_goal. *)
(* Abort. *)

Ltac solve_protected_eq_hook ::=
  lazymatch goal with
  (* unfold constants for function types *)
  | |- @eq (_ → fn_params) ?a (λ x, _) =>
    lazymatch a with
    | (λ x, _) => idtac
    | _ =>
      let h := get_head a in
      unfold h;
      (* necessary to reduce after unfolding because of the strict
      opaqueness settings for unification *)
      liSimpl
    end
  (* don't fail if nothing matches *)
  | |- _ => idtac
  end.

Ltac liUnfoldLetGoal_hook H ::=
  unfold RETURN_MARKER in H.

Ltac can_solve_hook ::= solve_goal.

Ltac liTrace_hook info ::= add_case_distinction_info info.

Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | typed_value ?cty ?v ?T =>
      (* One could introduce more let-bindings as follows, but too
      many let-bindings seem to hurt performance. *)
      (* bind T ltac:(fun H => uconstr:(typed_value v H)); *)
      cont uconstr:(((_ : TypedValue _ _) _))
  | typed_bin_op ?ge ?v1 ?ty1 ?v2 ?ty2 ?o ?ot1 ?ot2 ?ot ?T =>
      cont uconstr:(((_ : TypedBinOp _ _ _ _ _ _ _ _ _) _))
  | typed_un_op ?v ?ty ?o ?ot1 ?ot ?T =>
      cont uconstr:(((_ : TypedUnOp _ _ _ _ _) _))
  (*
  | typed_call ?v ?P ?vl ?tys ?T =>
      cont uconstr:(((_ : TypedCall _ _ _ _) _))
  | typed_copy_alloc_id ?v1 ?ty1 ?v2 ?ty2 ?ot ?T =>
      cont uconstr:(((_ : TypedCopyAllocId _ _ _ _ _) _))  *)
  | typed_place ?genv_t ?P ?l1 ?β1 ?ty1 ?T =>
      cont uconstr:(((_ : TypedPlace _ _ _ _ _) _))
  | typed_if ?ot ?v ?P ?F ?T1 ?T2 =>
      cont uconstr:(((_ : TypedIf _ _ _ _) _ _))
  (*
  | typed_switch ?v ?ty ?it ?m ?ss ?def ?fn ?ls ?fr ?Q =>
      cont uconstr:(((_ : TypedSwitch _ _ _) _ _ _ _ _ _ _))
  | typed_assert ?ot ?v ?ty ?s ?fn ?ls ?fr ?Q =>
      cont uconstr:(((_ : TypedAssert _ _ _) _ _ _ _ _))
      *)
  | typed_read_end ?a ?E ?l ?β ?ty ?ly ?T =>
      cont uconstr:(((_ : TypedReadEnd _ _ _ _ _ _) _))
  | typed_write_end ?a ?E ?ot ?v1 ?ty1 ?l2 ?β2 ?ty2 ?T =>
      cont uconstr:(((_ : TypedWriteEnd _ _ _ _ _ _ _ _) _))
  | typed_addr_of_end ?l ?β ?ty ?T =>
      cont uconstr:(((_ : TypedAddrOfEnd _ _ _) _))
  (*
  | typed_cas ?ot ?v1 ?P1 ?v2 ?P2 ?v3 ?P3 ?T =>
      cont uconstr:(((_ : TypedCas _ _ _ _ _ _ _) _))
      *)
  | typed_annot_expr ?n ?a ?v ?P ?T =>
      cont uconstr:(((_ : TypedAnnotExpr _ _ _ _) _) )
  | typed_annot_stmt ?a ?l ?P ?T =>
      cont uconstr:(((_ : TypedAnnotStmt _ _ _) _))
      (*
  | typed_macro_expr ?m ?es ?T =>
      cont uconstr:(((_ : TypedMacroExpr _ _) _))
      *)
  end.

Ltac liToSyntax_hook ::=
  unfold pop_location_info(*, LocInfoE*);
  change (typed_value ?x1 ?x2) with (li.bind1 (typed_value x1 x2));
  change (typed_bin_op ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) with (li.bind2 (typed_bin_op x1 x2 x3 x4 x5 x6 x7 x8));
  change (typed_un_op ?x1 ?x2 ?x3 ?x4 ?x5) with (li.bind2 (typed_un_op x1 x2 x3 x4 x5));
  (* change (typed_call ?x1 ?x2 ?x3 ?x4) with (li.bind2 (typed_call x1 x2 x3 x4)); *)
  (* change (typed_copy_alloc_id ?x1 ?x2 ?x3 ?x4 ?x5) with (li.bind2 (typed_copy_alloc_id x1 x2 x3 x4 x5)); *)
  change (typed_place ?x1 ?x2 ?x3 ?x4 ?x5 ?x6) with (li.bind5 (typed_place x1 x2 x3 x4 x5 x6));
  change (typed_read ?x1 ?x2 ?x3 ?x4) with (li.bind2 (typed_read x1 x2 x3 x4));
  change (typed_read_end ?x1 ?x2 ?x3 ?x4 ?x5 ?x6) with (li.bind3 (typed_read_end x1 x2 x3 x4 x5 x6));
  change (typed_write ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7) with (li.bind0 (typed_write x1 x2 x3 x4 x5 x6 x7));
  change (typed_write_end ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) with (li.bind1 (typed_write_end x1 x2 x3 x4 x5 x6 x7 x8));
  change (typed_addr_of ?x1 ?x2 ?x3) with (li.bind3 (typed_addr_of x1 x2 x3));
  change (typed_addr_of_end ?x1 ?x2 ?x3) with (li.bind3 (typed_addr_of_end x1 x2 x3));
  (* change (typed_cas ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7) with (li.bind2 (typed_cas x1 x2 x3 x4 x5 x6 x7)); *)
  (* change (typed_annot_expr ?x1 ?x2 ?x3 ?x4) with (li.bind0 (typed_cas x1 x2 x3 x4)); *)
  (* change (typed_macro_expr ?x1 ?x2) with (li.bind2 (typed_macro_expr x1 x2)); *)
  change (typed_val_expr ?x1 ?x2 ?x3) with (li.bind2 (typed_val_expr x1 x2 x3))
  (* no typed_if, typed_switch, typed_assert, typed_stmt, typed_annot_stmt *)
.

(* 
(** * Main automation tactics *)
Section automation.
  Context `{!typeG Σ}.

  Lemma tac_simpl_subst xs s fn ls Q R:
    typed_stmt (W.to_stmt (W.subst_stmt xs s)) fn ls R Q
    ⊢ typed_stmt (subst_stmt xs (W.to_stmt s)) fn ls R Q.
  Proof. by rewrite W.to_stmt_subst. Qed.

  Lemma tac_typed_single_block_rec P b Q fn ls R s:
    Q !! b = Some s →
    (P ∗ accu (λ A, typed_block (P ∗ A) b fn ls R Q -∗ P -∗ A -∗ typed_stmt s fn ls R Q))
    ⊢ typed_stmt (Goto b) fn ls R Q.
  Proof.
    iIntros (HQ) "[HP Hs]". iIntros (Hls). unfold accu, typed_block.
    iDestruct "Hs" as (A) "[HA #Hs]". iLöb as "Hl".
    iApply wps_goto =>//. iModIntro. iApply ("Hs" with "[] HP HA") => //.
    iIntros "!# [HP HA]". by iApply ("Hl" with "HP HA").
  Qed.
End automation. *)

Ltac liRIntroduceLetInGoal :=
  lazymatch goal with
  | |- @envs_entails ?prop ?Δ ?P =>
    lazymatch P with
    | @typed_val_expr ?OK_ty ?Σ ?tG ?cs ?ge ?f ?e ?T =>
      li_let_bind T (fun H => constr:(@envs_entails prop Δ (@typed_val_expr OK_ty Σ tG cs ge f e H)))
    | @typed_write ?OK_ty ?Σ ?tG ?cs ?ge ?f ?b ?e ?ot ?v ?ty ?T =>
      li_let_bind T (fun H => constr:(@envs_entails prop Δ (@typed_write OK_ty Σ tG cs ge f b e ot v ty H)))
    | @typed_place ?OK_ty ?Σ ?tG ?cs ?ge ?P ?l1 ?β1 ?ty1 ?T =>
      li_let_bind T (fun H => constr:(@envs_entails prop Δ (@typed_place OK_ty Σ tG cs ge P l1 β1 ty1 H)))
    | @typed_bin_op ?OK_ty ?Σ ?tG ?cs ?ge ?v1 ?P1 ?v2 ?P2 ?op ?ot1 ?ot2 ?ot ?T =>
      li_let_bind T (fun H => constr:(@envs_entails prop Δ (@typed_bin_op OK_ty Σ tG cs ge v1 P1 v2 P2 op ot1 ot2 ot H)))
    end
  end.

Ltac liRStmt :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?Espec ?ge ?s ?f ?T) =>
    lazymatch s with
    (* | LocInfo ?info ?s2 =>
      update_loc_info (Some info);
      change_no_check (envs_entails Δ (typed_stmt s2 fn ls fr Q)) *)
    | _ => update_loc_info (None : option location_info)
    end
  end;
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?Espec ?ge ?s ?f ?T) =>
    lazymatch s with
    (* | subst_stmt ?xs ?s =>
      let s' := W.of_stmt s in
      change (subst_stmt xs s) with (subst_stmt xs (W.to_stmt s'));
      refine (tac_fast_apply (tac_simpl_subst _ _ _ _ _ _) _); simpl; unfold W.to_stmt, W.to_expr *)
    | _ =>
      let s' := s in
      lazymatch s' with
      | Sassign _ _ => notypeclasses refine (tac_fast_apply (type_assign _ _ _ _ _ _ _ _ ) _); [done..|]
      | Sset _ _ => notypeclasses refine (tac_fast_apply (type_set _ _ _ _ _ _ _) _)
      | Ssequence _ _ => notypeclasses refine (tac_fast_apply (type_seq _ _ _ _ _ _) _)
      | Sreturn $ Some _ => notypeclasses refine (tac_fast_apply (type_return_some _ _ _ _ _) _)
      | Sreturn None => notypeclasses refine (tac_fast_apply (type_return_none _ _ _ _ _) _)
      | _ => fail "do_stmt: unknown stmt" s
      end
    end
  end.

(* Ltac liRIntroduceTypedStmt :=
  lazymatch goal with
  | |- @envs_entails ?prop ?Δ (introduce_typed_stmt ?fn ?ls ?R) =>
    iEval (rewrite /introduce_typed_stmt !fmap_insert fmap_empty; simpl_subst);
      lazymatch goal with
      | |- @envs_entails ?prop ?Δ (@typed_stmt ?Σ ?tG ?s ?fn ?ls ?R ?Q) =>
        let HQ := fresh "Q" in
        let HR := fresh "R" in
        pose (HQ := (CODE_MARKER Q));
        pose (HR := (RETURN_MARKER R));
        change_no_check (@envs_entails prop Δ (@typed_stmt Σ tG s fn ls HR HQ));
        iEval (simpl) (* To simplify f_init *)
      end
  end. *)

Ltac liRPopLocationInfo :=
  lazymatch goal with
  (* TODO: don't hardcode this for two arguments *)
  | |- envs_entails ?Δ (pop_location_info ?info ?T ?a1 ?a2) =>
    update_loc_info [info; info];
    change_no_check (envs_entails Δ (T a1 a2))
  end.

Ltac liRExpr :=
  (* lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr ?e ?T) =>
    lazymatch e with
    (* | LocInfo ?info ?e2 =>
      update_loc_info [info];
      change_no_check (envs_entails Δ (typed_val_expr e2 (pop_location_info info T))) *)
    | _ => idtac
    end
  end; *)
  lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr _ _ ?e ?T) =>
    lazymatch e with
    | Ecast _ _ => notypeclasses refine (tac_fast_apply (type_Ecast_same_val _ _ _ _ _) _)
    | Econst_int _ _ => notypeclasses refine (tac_fast_apply (type_const_int _ _ _ _ _) _)
    | Ebinop _ _ _ _ => notypeclasses refine (tac_fast_apply (type_bin_op _ _ _ _ _ _ _) _)
    | Ederef _ _ => notypeclasses refine (tac_fast_apply (type_deref _ _ _ _ _ _) _);[done|]
    | Etempvar _ _ => notypeclasses refine (tac_fast_apply (type_tempvar _ _ _ _ _ _) _)
    | _ => fail "do_expr: unknown expr" e
    end
  | |- envs_entails ?Δ (typed_lvalue _ _ ?β ?e ?T) =>
    lazymatch e with
    | Evar _ _ => notypeclasses refine (tac_fast_apply (type_var_local _ _ _ _ _ _ _ _) _)
    | _ => fail "do_expr: unknown expr" e
    end
  end.

Ltac liRJudgement :=
  lazymatch goal with
    | |- envs_entails _ (typed_write _ _ _ ?e _ _ _ _) =>
      lazymatch e with
      | (Ederef _ _) => notypeclasses refine (tac_fast_apply (type_write_deref _ _ _ _ _ _ _ _ _ _) _); [ solve [refine _ ] |]
      | _ => notypeclasses refine (tac_fast_apply (type_write_simple _ _ _ _ _ _ _ _ _) _)
      end
    | |- envs_entails _ (typed_read _ _ _ _ _ _) =>
      notypeclasses refine (tac_fast_apply (type_read _ _ _ _ _ _ _) _); [ solve [refine _ ] |]
    | |- envs_entails _ (typed_addr_of _ _ _ _) =>
      fail "liRJudgement: type_addr_of not implemented yet"
      (* notypeclasses refine (tac_fast_apply (type_addr_of_place _ _ _ _) _); [solve [refine _] |] *)
  end.

(* deal with objective modalities. This is ad-hoc for now *)
Ltac liObj :=
  match goal with
  | |- envs_entails _ (<obj> _) =>
    iModIntro
  end.

(* This does everything *)
Ltac liRStep :=
 liEnsureInvariant;
 try liRIntroduceLetInGoal;
 first [
   liRPopLocationInfo
 | liRStmt
 (* | liRIntroduceTypedStmt *)
 | liRExpr
 | liRJudgement
 | liObj
 | liStep
]; liSimpl.

Tactic Notation "liRStepUntil" open_constr(id) :=
  repeat lazymatch goal with
         | |- @environments.envs_entails _ _ ?P =>
           lazymatch P with
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ => fail
           | id _ _ _ _ _ => fail
           | id _ _ _ _ => fail
           | id _ _ => fail
           | id _ => fail
           | id => fail
           | _  => liRStep
           end
         | _ => liRStep
  end; liShow.


(** * Tactics for starting a function *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_split_big_sepM {K A} `{!EqDecision K} `{!Countable K} (m : gmap K A) i x Φ (P : iProp Σ):
    m !! i = None →
    (Φ i x -∗ ([∗ map] k↦x∈m, Φ k x) -∗ P) ⊢
    ([∗ map] k↦x∈<[i := x]>m, Φ k x) -∗ P.
  Proof.
    move => Hin. rewrite big_sepM_insert //.
    iIntros "HP [? Hm]". by iApply ("HP" with "[$]").
  Qed.
End coq_tactics.

(* IMPORTANT: We need to make sure to never call simpl while the code
(Q) is part of the goal, because simpl seems to take exponential time
in the number of blocks! *)
(* TODO: don't use i... tactics here *)
(* FIXME for now the intropattern is just x for the entire array of arguments. *)
(* was start_function in refinedc; name conflict with the floyd tactic *)
Tactic Notation "type_function" constr(fnname) "(" simple_intropattern(x) ")" :=
  intros;
  repeat iIntros "#?";
  rewrite /typed_function;
  iIntros ( x );
  (* computes the ofe_car in introduced arguments *)
  match goal with | H: ofe_car _ |- _ => hnf in H; destruct H end;
  iSplit; [iPureIntro; simpl; by [repeat constructor] || fail "in" fnname "argument types don't match layout of arguments" |];
  let lsa := fresh "lsa" in let lsb := fresh "lsb" in
  iIntros "!#" (lsa lsb); inv_vec lsb; inv_vec lsa;
  iPureIntro;
  iIntros "(?&?&?&?)";
  cbn.

Tactic Notation "prepare_parameters" "(" ident_list(i) ")" :=
  revert i; repeat liForall.

Ltac liRSplitBlocksIntro :=
  repeat (
      liEnsureInvariant;
      first [
          liSep
        | liWand
        | liImpl
        | liForall
        | liExist
        | liUnfoldLetGoal]; liSimpl);
        li_unfold_lets_in_context.
(*
(* TODO: don't use i... tactics here *)
Ltac split_blocks Pfull Ps :=
  (* cbn in *|- is important here to simplify the types of local
  variables, otherwise unification gets confused later *)
  cbn -[union] in * |-;
  let rec pose_Ps Ps :=
      lazymatch Ps with
      | ?P::?m =>
        let Hhint := fresh "Hhint" in
        pose proof (I : P) as Hhint;
        pose_Ps m
      | nil => idtac
      end
  in
  pose_Ps Ps;
  let Hfull := fresh "Hfull" in
  (* We must do this pose first since do_split_block_intro might call
  subst and we want to subst in Ps as well. *)
  pose (Hfull := Pfull);
  liRSplitBlocksIntro;
  liRIntroduceTypedStmt;
  iApply (typed_block_rec Hfull); unfold Hfull; clear Hfull; last first; [|
  repeat (iApply big_sepM_insert; [reflexivity|]; iSplitL); last by [iApply big_sepM_empty];
  iExists _; (iSplitR; [iPureIntro; unfold_code_marker_and_compute_map_lookup|]); iModIntro ];
  repeat (iApply tac_split_big_sepM; [reflexivity|]; iIntros "?"); iIntros "_".
*)

Ltac repeat' tac :=
  let rec aux n :=
    tryif tac
    then (idtac "Step" n; aux (S n))
    else idtac "Repeated" n "times"
  in aux 0%nat.

Import env.
Section automation_tests.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (* to programs.v *)
  Definition normal_type_assert R := {| T_normal := R; T_break := False; T_continue := False; T_return := λ _ _, False |}.

  Goal forall Espec ge f (_x:ident) (x:val),
  temp _x x
  ⊢ typed_stmt Espec ge (Sset _x (Ebinop Oadd (Econst_int (Int.repr 41) tint)
                                              (Econst_int (Int.repr 1) tint) tint)) f
                        (normal_type_assert (temp _x (Vint (Int.repr 42))
                                ∗ ⎡ Vint (Int.repr 42) ◁ᵥₐₗ|tint| 42 @ int tint ⎤)).
  Proof.
    iIntros.
    repeat liRStep.
    liShow; try done.
    (* FIXME add these Integer facts to Lithium automation *)
    rewrite -Int.add_signed add_repr /= Int.signed_repr; last rep_lia.
    repeat liRStep.
    rewrite Int.signed_repr; last rep_lia.
    done.
  Qed.

  Goal forall Espec ge f (_x:ident) b (l:address) ty,
  TCDone (ty_has_op_type ty tint MCNone) ->
  ⊢ lvar _x tint b -∗
    ⎡ (b, Ptrofs.unsigned Ptrofs.zero) ◁ₗ int tint ⎤ -∗
    typed_stmt Espec ge (Sassign (Evar _x tint) (Econst_int (Int.repr 1) tint)) f
               (normal_type_assert (⎡ (b, Ptrofs.unsigned Ptrofs.zero) ◁ₗ Int.signed (Int.repr 1) @ int tint ⎤ ∗ True)).
  Proof.
    iIntros.
    repeat liRStep.
  Qed.

End automation_tests.

  Open Scope printing_sugar.
  Arguments find_in_context: simpl never.
  Arguments subsume: simpl never.
  Arguments FindVal: simpl never.
  (* for triggering related_to_val_rep_v *)
  Arguments repinject: simpl never.
  Arguments sep_list: simpl never.
  Transparent Archi.ptr64.

(* TODO move these to programs.v *)
Section additional_instances.

  Context `{!typeG OK_ty Σ} {cs : compspecs}.
  Global Instance related_to_val_embed A v cty ty : RelatedTo (λ x : A, (⎡v ◁ᵥₐₗ|cty| ty x⎤))%I | 100
  := {| rt_fic := FindVal cty v |}.
  Global Instance related_to_val_embed2 A v cty ty : RelatedTo (λ x : A, (⎡v ◁ᵥₐₗ|cty| ty⎤))%I | 100
  := {| rt_fic := FindVal cty v |}.
  Global Instance related_to_val_rep_v A cty v_rep ty :  RelatedTo (λ x : A, ⎡ v_rep ◁ᵥ|cty| ty x⎤:assert)%I | 100
  := {| rt_fic := FindValP (repinject cty v_rep) |}.
  
  Lemma find_in_context_type_val_P_id  cty v (T:assert->assert):
    (∃ ty , ⎡v ◁ᵥ|cty| ty⎤ ∗ T (⎡v ◁ᵥ|cty| ty⎤))
    ⊢ find_in_context (FindValP (repinject cty v)) T.
  Proof. intros. iDestruct 1 as "(% & ? & ?)". iExists ⎡ty_own_val ty _ _⎤ => /=. iFrame. Qed.
  Definition find_in_context_type_val_P_id_inst :=
    [instance find_in_context_type_val_P_id with FICSyntactic].
  Global Existing Instance find_in_context_type_val_P_id_inst | 1.

  Lemma simple_subsume_val_to_subsume_embed_inject (A:Type) (v : val) cty (ty1 : type) (ty2 : A → type) (P:A->mpred)
    `{!∀ (x:A), SimpleSubsumeVal cty ty1 (ty2 x) (P x)} (T: A-> assert) :
    (∃ x, (@embed mpred assert _ $ P x) ∗ T x) ⊢@{assert} subsume (⎡v ◁ᵥₐₗ|cty| ty1⎤) (λ x : A, ⎡v ◁ᵥₐₗ|cty| ty2 x⎤) T.
  Proof.
    iIntros "H".
    iDestruct "H" as (x) "[HP HT]".
    unfold subsume. iIntros. iExists x. iFrame.
    iApply (@simple_subsume_val with "[$HP] [$]").
  Qed.
  Definition simple_subsume_val_to_subsume_embed_inject_inst := [instance simple_subsume_val_to_subsume_embed_inject].
  Global Existing Instance simple_subsume_val_to_subsume_embed_inject_inst.

  Lemma simple_subsume_val_to_subsume_embed (A:Type) cty (v : reptype cty)  (ty1 : type) (ty2 : A → type) (P:A->mpred)
    `{!∀ (x:A), SimpleSubsumeVal cty ty1 (ty2 x) (P x)} (T: A-> assert) :
    (∃ x, (@embed mpred assert _ $ P x) ∗ T x) ⊢@{assert} subsume (⎡v ◁ᵥ|cty| ty1⎤) (λ x : A, ⎡v ◁ᵥ|cty| ty2 x⎤) T.
  Proof.
    iIntros "H".
    iDestruct "H" as (x) "[HP HT]".
    unfold subsume. iIntros. iExists x. iFrame.
    iApply (@simple_subsume_val with "[$HP] [$]").
  Qed.
  Definition simple_subsume_val_to_subsume_embed_inst := [instance simple_subsume_val_to_subsume_embed].
  Global Existing Instance simple_subsume_val_to_subsume_embed_inst.
  
End additional_instances.

Section automation_tests.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

  Definition _ar : ident := $"ar".
  Definition _i : ident := $"i".
  Definition _j : ident := $"j".
  Definition _k : ident := $"k".
  Definition _main : ident := $"main".
  Definition _permute : ident := $"permute".
  Definition _t'1 : ident := 128%positive.

  Definition f_permute := {|
    fn_return := tvoid;
    fn_callconv := cc_default;
    fn_params := ((_ar, (tptr tint)) :: (_i, tint) :: (_j, tint) :: nil);
    fn_vars := nil;
    fn_temps := ((_k, tint) :: (_t'1, tint) :: nil);
    fn_body :=
  (Ssequence
    (Sset _k
      (Ederef
        (Ebinop Oadd (Etempvar _ar (tptr tint)) (Etempvar _i tint) (tptr tint))
        tint))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _ar (tptr tint)) (Etempvar _j tint)
              (tptr tint)) tint))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _ar (tptr tint)) (Etempvar _i tint)
              (tptr tint)) tint) (Etempvar _t'1 tint)))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _ar (tptr tint)) (Etempvar _j tint)
            (tptr tint)) tint) (Etempvar _k tint))))
  |}.

  Context `{!typeG OK_ty Σ} {cs : compspecs} `{BiPositive mpred}.
 
  Lemma subsume_array A cty_arr tys1 tys2 l β T:
    (∀ id,
       subsume (sep_list id type [] tys1 (λ i ty, ⎡(l arr_ofs{cty_arr}ₗ i) ◁ₗ{β} ty⎤:assert))
         (λ x, sep_list id type [] (tys2 x) (λ i ty, ⎡(l arr_ofs{cty_arr}ₗ i) ◁ₗ{β} ty⎤)) T)
    ⊢ subsume (⎡l ◁ₗ{β} array cty_arr tys1⎤) (λ x : A, ⎡l ◁ₗ{β} array cty_arr (tys2 x)⎤) T.
  Admitted.
    Definition subsume_array_inst := [instance subsume_array].
  Global Existing Instance subsume_array_inst.

  Goal forall Espec genv_t (v_k t'1: val) (v_ar v_i v_j:address) (i j: nat)  (elts:list Z) v1 v2 f,
    ⊢ ⎡ v_i ◁ᵥ| tint | i @ int tint ⎤ -∗
      ⎡ v_j ◁ᵥ| tint | j @ int tint⎤ -∗
      <affine> ⌜elts !! i = Some v1⌝ -∗
      <affine> ⌜elts !! j = Some v2⌝ -∗
      <affine> ⌜i ≠ j⌝ -∗
      temp _j v_j -∗
      temp _ar v_ar -∗
      temp _i v_i -∗
      temp _k v_k -∗
      temp _t'1 t'1 -∗
      ⎡v_ar ◁ₗ  (array tint (elts `at_type` int tint))⎤ -∗
    typed_stmt Espec genv_t (fn_body f_permute) f (normal_type_assert (⎡(v_ar ◁ₗ (array tint (<[j:=v1]>(<[i:=v2]>elts) `at_type` int tint)))⎤ ∗ True)).
  Proof.
    intros.
    iStartProof.
    iIntros "#? #?".
    repeat liRStep.
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "permute".
    (* We admit Some pure sideconditions *)
  Admitted.

End automation_tests.

From VST.typing Require Import automation_test.


Require Import VST.veric.make_compspecs.

  Section f_test1.
    Context `{!typeG OK_ty Σ} {cs : compspecs}.

    Definition spec_f_ret_expr :=
      fn(∀ () : (); emp) → ∃ z : Z, (z @ ( int tint )); ⌜z = 3⌝.
    Instance CompSpecs : compspecs. make_compspecs prog. Defined.

    Goal forall Espec ge, ⊢ typed_function(A := ConstType _) Espec ge f_f_ret_expr spec_f_ret_expr.
    Proof.
      type_function "f_ret_expr" ( x ).
      repeat liRStep.
    Qed.
  End f_test1.

  Section f_test2.
    Context `{!typeG OK_ty Σ} {cs : compspecs}.

    Definition spec_f_temps :=
      fn(∀ () : (); emp) → ∃ z : Z, (z @ (int tint)) ; ⌜z=42⌝.

    Local Instance CompSpecs : compspecs. make_compspecs prog. Defined.

    Goal forall Espec ge, ⊢ typed_function(A := ConstType _) Espec ge f_f_temps spec_f_temps.
    Proof.
      type_function "f_ret_expr" ( x ).
      repeat liRStep.
  Qed.

End f_test2.
