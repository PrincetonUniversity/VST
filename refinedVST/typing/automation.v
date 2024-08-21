(* refinedC/typing/automation.v *)
From iris.proofmode Require Import coq_tactics reduction.
From lithium Require Import hooks normalize.
From VST.lithium Require Export all.
From VST.typing Require Export type.
From VST.typing.automation Require Export proof_state (* solvers simplification  loc_eq. *).
From VST.typing Require Import programs (* function singleton own struct bytes *) int.
Set Default Proof Using "Type".

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
  | typed_value ?v ?T =>
      (* One could introduce more let-bindings as follows, but too
      many let-bindings seem to hurt performance. *)
      (* bind T ltac:(fun H => uconstr:(typed_value v H)); *)
      cont uconstr:(((_ : TypedValue _) _))
  | typed_bin_op ?v1 ?ty1 ?v2 ?ty2 ?o ?ot1 ?ot2 ?T =>
      cont uconstr:(((_ : TypedBinOp _ _ _ _ _ _ _) _))
  | typed_un_op ?v ?ty ?o ?ot ?T =>
      cont uconstr:(((_ : TypedUnOp _ _ _ _) _))
  (*
  | typed_call ?v ?P ?vl ?tys ?T =>
      cont uconstr:(((_ : TypedCall _ _ _ _) _))
  | typed_copy_alloc_id ?v1 ?ty1 ?v2 ?ty2 ?ot ?T =>
      cont uconstr:(((_ : TypedCopyAllocId _ _ _ _ _) _))
  | typed_place ?P ?l1 ?β1 ?ty1 ?T =>
      cont uconstr:(((_ : TypedPlace _ _ _ _) _))
  *)    
  | typed_if ?ot ?v ?P ?T1 ?T2 =>
      cont uconstr:(((_ : TypedIf _ _ _) _ _))
  (*
  | typed_switch ?v ?ty ?it ?m ?ss ?def ?fn ?ls ?fr ?Q =>
      cont uconstr:(((_ : TypedSwitch _ _ _) _ _ _ _ _ _ _))
  | typed_assert ?ot ?v ?ty ?s ?fn ?ls ?fr ?Q =>
      cont uconstr:(((_ : TypedAssert _ _ _) _ _ _ _ _))
      *)
  | typed_read_end ?a ?E ?l ?β ?ty ?ly ?mc ?T =>
      cont uconstr:(((_ : TypedReadEnd _ _ _ _ _ _ _) _))
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
  change (typed_bin_op ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7) with (li.bind2 (typed_bin_op x1 x2 x3 x4 x5 x6 x7));
  change (typed_un_op ?x1 ?x2 ?x3 ?x4) with (li.bind2 (typed_un_op x1 x2 x3 x4));
  (* change (typed_call ?x1 ?x2 ?x3 ?x4) with (li.bind2 (typed_call x1 x2 x3 x4)); *)
  (* change (typed_copy_alloc_id ?x1 ?x2 ?x3 ?x4 ?x5) with (li.bind2 (typed_copy_alloc_id x1 x2 x3 x4 x5)); *)
  (* change (typed_place ?x1 ?x2 ?x3 ?x4) with (li.bind5 (typed_place x1 x2 x3 x4)); *)
  change (typed_read ?x1 ?x2 ?x3 ?x4) with (li.bind2 (typed_read x1 x2 x3 x4));
  change (typed_read_end ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7) with (li.bind3 (typed_read_end x1 x2 x3 x4 x5 x6 x7));
  change (typed_write ?x1 ?x2 ?x3 ?x4 ?x5) with (li.bind0 (typed_write x1 x2 x3 x4 x5));
  change (typed_write_end ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) with (li.bind1 (typed_write_end x1 x2 x3 x4 x5 x6 x7 x8));
  change (typed_addr_of ?x1) with (li.bind3 (typed_addr_of x1));
  change (typed_addr_of_end ?x1 ?x2 ?x3) with (li.bind3 (typed_addr_of_end x1 x2 x3));
  (* change (typed_cas ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7) with (li.bind2 (typed_cas x1 x2 x3 x4 x5 x6 x7)); *)
  (* change (typed_annot_expr ?x1 ?x2 ?x3 ?x4) with (li.bind0 (typed_cas x1 x2 x3 x4)); *)
  (* change (typed_macro_expr ?x1 ?x2) with (li.bind2 (typed_macro_expr x1 x2)); *)
  change (typed_val_expr ?x1) with (li.bind2 (typed_val_expr x1))
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
    | @typed_val_expr ?Σ ?tG ?cs ?e ?T =>
      li_let_bind T (fun H => constr:(@envs_entails prop Δ (@typed_val_expr Σ tG cs e H)))
    | @typed_write ?Σ ?tG ?cs ?b ?e ?ot ?v ?ty ?T =>
      li_let_bind T (fun H => constr:(@envs_entails prop Δ (@typed_write Σ tG cs b e ot v ty H)))
    (* | @typed_place ?Σ ?tG ?P ?l1 ?β1 ?ty1 ?T =>
      li_let_bind T (fun H => constr:(@envs_entails prop Δ (@typed_place Σ tG P l1 β1 ty1 H))) *)
    | @typed_bin_op ?Σ ?tG ?cs ?v1 ?P1 ?v2 ?P2 ?op ?ot1 ?ot2 ?T =>
      li_let_bind T (fun H => constr:(@envs_entails prop Δ (@typed_bin_op Σ tG cs v1 P1 v2 P2 op ot1 ot2 H)))
    end
  end.

Ltac liRStmt :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?Espec ?Delta ?s ?T) =>
    lazymatch s with
    (* | LocInfo ?info ?s2 =>
      update_loc_info (Some info);
      change_no_check (envs_entails Δ (typed_stmt s2 fn ls fr Q)) *)
    | _ => update_loc_info (None : option location_info)
    end
  end;
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?Espec ?Delta ?s ?T) =>
    lazymatch s with
    (* | subst_stmt ?xs ?s =>
      let s' := W.of_stmt s in
      change (subst_stmt xs s) with (subst_stmt xs (W.to_stmt s'));
      refine (tac_fast_apply (tac_simpl_subst _ _ _ _ _ _) _); simpl; unfold W.to_stmt, W.to_expr *)
    | _ =>
      let s' := s in
      lazymatch s' with
      | Sassign _ _ => notypeclasses refine (tac_fast_apply (type_assign _ _ _ _ _) _)
      | Sset _ _ => notypeclasses refine (tac_fast_apply (type_set _ _ _ _ _ _) _)
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
  lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr ?e ?T) =>
    lazymatch e with
    (* | LocInfo ?info ?e2 =>
      update_loc_info [info];
      change_no_check (envs_entails Δ (typed_val_expr e2 (pop_location_info info T))) *)
    | _ => idtac
    end
  end;
  lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr ?e ?T) =>
    lazymatch e with
    | Ecast _ _ => notypeclasses refine (tac_fast_apply (type_Ecast_same_val _ _ _) _)
    | Econst_int _ _ => notypeclasses refine (tac_fast_apply (type_const_int _ _ _) _)
    | Ebinop _ _ _ _ => notypeclasses refine (tac_fast_apply (type_bin_op _ _ _ _ _) _)
    | _ => fail "do_expr: unknown expr" e
    end
  end.

Ltac liRJudgement :=
  lazymatch goal with
    | |- envs_entails _ (typed_write _ _ _ _ _ _) => 
      notypeclasses refine (tac_fast_apply (type_write_simple _ _ _ _ _ _) _)
    | |- envs_entails _ (typed_read _ _ _ _ _) =>
      fail "liRJudgement: type_read not implemented yet"
      (* notypeclasses refine (tac_fast_apply (type_read _ _ _ _ _ _ _) _); [ solve [refine _ ] |] *)
    | |- envs_entails _ (typed_addr_of _ _) =>
      fail "liRJudgement: type_addr_of not implemented yet"
      (* notypeclasses refine (tac_fast_apply (type_addr_of_place _ _ _ _) _); [solve [refine _] |] *)
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
Tactic Notation "start_function" constr(fnname) "(" simple_intropattern(x) ")" :=
  intros;
  repeat iIntros "#?";
  (* rewrite /typed_function; *)
  iIntros ( x );
  iSplit; [iPureIntro; simpl; by [repeat constructor] || fail "in" fnname "argument types don't match layout of arguments" |];
  let lsa := fresh "lsa" in let lsv := fresh "lsv" in
  iIntros "!#" (lsa lsv); inv_vec lsv; inv_vec lsa.

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

From VST.typing Require Import int.
Section automation_tests.
  Context `{!typeG Σ} {cs : compspecs} `{!externalGS OK_ty Σ}.
 
   Opaque local locald_denote.

  Goal forall Espec Delta (_x:ident) (x:val),
  <affine> (local $ locald_denote $ temp _x x)
  ⊢ typed_stmt Espec Delta (Sset _x (Ebinop Oadd (Econst_int (Int.repr 41) tint) (Econst_int (Int.repr 1) tint) tint)) 
                           (λ v t, local (locald_denote (temp _x (Vint (Int.repr 42))))).
  Proof.
    iIntros.
    Info 0 liRStep. (* type_set *)
    Info 0 liRStep. (* frame temp _x *)
    Info 0 liRStep. (* type_bin_op *)
    
    Info 0 liRStep. (* type first const expr *)
    liRStep.
    liRStep.
    liRStep.

    Info 0 liRStep.  (* type second const expr *)
    liRStep.
    liRStep.
    liRStep.
    liRStep.
    repeat liRStep; liShow.
    done. (* Ke: we shouldn't need this; *)
    Unshelve. (* TODO write solvers for side conditions, register to sidecond_hook or some other hook *)
  Admitted.


  Goal forall Espec Delta (_x:ident) (x: address),
  (local $ locald_denote $ temp _x x) ∗
  ⎡data_at_ Tsh tint x ⎤ ∗
  ⎡ ty_own_val (0 @ int tint) (Vint (Int.repr 0))  ⎤
  ⊢ typed_stmt Espec Delta (Sassign (Evar _x tint) (Econst_int (Int.repr 0) tint)) (λ v t, True).
  Proof.
  iIntros.
  (* usually Info level 0 is able to see the tactic applied *)
  Info 0 liRStep. (* type_assign *)
  Info 0 liRStep. (* type_Ecast_same_val *)
  Info 0 liRStep. (* type_const_int *)
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  
  (** Ke: TODO need typed_val_expr (Evar _x tint)  *)
  Abort.
End automation_tests.