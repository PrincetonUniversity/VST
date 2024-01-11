Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import LiftNotation.
Import -(notations) compcert.lib.Maps.

(*
Definition NDfunspec_sub (f1 f2 : funspec) :=
let Delta2 := rettype_tycontext (snd (typesig_of_funspec f2)) in
match f1 with
| mk_funspec tpsig1 cc1 (ConstType A1) P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 (ConstType As) P2 Q2 _ _ =>
        (tpsig1=tpsig2 /\ cc1=cc2) /\
        forall x2 (rho:argsEnviron),
        ((!! (tc_argsenv Delta2 (fst tpsig2)) rho) ∧ P2 nil x2 rho)
         ⊢ (∃ x1:_, ∃ F:_, 
                           (F ∗ (P1 nil x1 rho)) ∧
                               (!! (forall rho',
                                           ((!! (tc_environ (rettype_tycontext (snd tpsig1)) rho') ∧
                                                 (F ∗ (Q1 nil x1 rho')))
                                         ⊢ (Q2 nil x2 rho')))))
 | _ => False end
 | _ => False end.*)

Section mpred.

Context `{!heapGS Σ}.

Definition NDfunspec_sub (f1 f2 : @funspec Σ) :=
let Delta2 := rettype_tycontext (snd (typesig_of_funspec f2)) in
match f1 with
| mk_funspec tpsig1 cc1 E1 (ConstType A1) P1 Q1 =>
    match f2 with
    | mk_funspec tpsig2 cc2 E2 (ConstType As) P2 Q2 =>
        (tpsig1=tpsig2 /\ cc1=cc2 /\ E1 ⊆ E2) /\
        forall x2 (gargs:argsEnviron),
        (⌜argsHaveTyps(snd gargs)(fst tpsig1)⌝ ∧ P2 x2 gargs)
         ⊢ |={E2}=> (∃ x1:_, ∃ F:_,
                           (F ∗ (P1 x1 gargs)) ∧
                               (⌜forall rho',
                                           (⌜ve_of rho' = Map.empty (block * type)⌝ ∧
                                                 (F ∗ (Q1 x1 rho')))
                                         ⊢ (Q2 x2 rho')⌝))
 | _ => False%type end
 | _ => False%type end.

(*Definition is_NDfunspec (fs: funspec) :=
 match fs with
 | mk_funspec _ _ (ConstType A) P Q =>
    (forall ts, P ts = P nil /\ Q ts = Q nil)
 | _ => False
 end.*)

Lemma NDsubsume_subsume:
  forall f1 f2,
(*   is_NDfunspec f2 ->*)
   NDfunspec_sub f1 f2 ->
   funspec_sub f1 f2.
Proof.
intros.
destruct f1, f2; hnf in H.
destruct A; try contradiction. destruct A0; try contradiction.
destruct H as [[? ?] ?]; split; auto.
Qed.

(*
Definition funspec_sub' (f1 f2 : funspec):Prop :=
let Delta := rettype_tycontext (snd (typesig_of_funspec f1)) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        fsig1 = fsig2 /\ cc1=cc2 /\
        forall (ts2 : list Type) x2,
               ENTAIL Delta, P2 ts2 x2
           ⊢
               |==> (∃ ts1:_,  ∃ x1:_, ∃ F:_, 
                           (`F ∗ (P1 ts1 x1)) ∧
                               (!! ENTAIL (ret0_tycon Delta),
                                                 (`F ∗ (Q1 ts1 x1))
                                         ⊢
                                           |==> (Q2 ts2 x2)))
    end
end.

Lemma subsume_subsume:
  forall f1 f2,
   funspec_sub' f1 f2 ->
   funspec_sub f1 f2.
Proof.
  unfold funspec_sub', funspec_sub.
  rewrite <- derives_eq; auto.
Qed.
 *)

Inductive empty_type : Type := .

Definition withtype_of_NDfunspec (fs : @funspec Σ) := match fs with
  mk_funspec _ _ _ (ConstType A) _ _ => A | _ => empty_type end.
 

Definition withtype_of_funspec (fs : @funspec Σ) := match fs with
  mk_funspec _ _ _ A _ _ => A end.

Lemma sepcon_ENTAIL:
 forall Delta (P Q P' Q' : @assert Σ),
  (ENTAIL Delta, P ⊢ P') ->
  (ENTAIL Delta, Q ⊢ Q') ->
  (ENTAIL Delta, (P ∗ Q) ⊢ (P' ∗ Q')).
Proof.
  intros; apply sepcon_ENTAIL; done.
Qed.

Lemma NDfunspec_sub_refl:
  forall fsig cc A P Q,
   NDfunspec_sub (NDmk_funspec fsig cc A P Q) (NDmk_funspec fsig cc A P Q).
Proof.
  intros.
  simpl.
  split; auto.
  intros.
  iIntros "(% & ?) !>".
  iExists x2, emp; iFrame.
  iSplit; iPureIntro; first done.
  intros; iIntros "(_ & ? & $)".
Qed.

Lemma NDfunspec_sub_trans:
  forall fsig1 cc1 A1 P1 Q1 fsig2 cc2 A2 P2 Q2 fsig3 cc3 A3 P3 Q3, 
   NDfunspec_sub (NDmk_funspec fsig1 cc1 A1 P1 Q1) (NDmk_funspec fsig2 cc2 A2 P2 Q2) ->
   NDfunspec_sub (NDmk_funspec fsig2 cc2 A2 P2 Q2) (NDmk_funspec fsig3 cc3 A3 P3 Q3) ->
   NDfunspec_sub (NDmk_funspec fsig1 cc1 A1 P1 Q1) (NDmk_funspec fsig3 cc3 A3 P3 Q3).
Proof.
  intros.
  destruct H as [(?E & ?E' & ?) H].
  destruct H0 as [(?F & ?F'& ?) H0].
  subst.
  split; auto.
  intro x3; simpl in x3. simpl in H, H0. simpl. intros.
  specialize (H0 x3 gargs).
  iIntros "(% & ?)".
  iMod (H0 with "[-]") as (??) "((F & H) & %Hpost)".
  { iFrame; iFrame "%". }
  iMod (H with "[H]") as (??) "((F1 & H1) & %Hpost1)".
  { iFrame; iFrame "%". }
  iExists _, (F ∗ F0); iFrame.
  iModIntro; iSplit; iPureIntro; first done.
  intros; iIntros "(% & (? & ?) & ?)".
  rewrite -Hpost; iFrame; iFrame "%".
  rewrite -Hpost1; iFrame; iFrame "%".
Qed.

Context {Espec: OracleKind} `{!externalGS OK_ty Σ} {CS: compspecs}.

Lemma semax_call_subsume:
  forall E (fs1: funspec) A P Q argsig retsig cc,
    funspec_sub fs1 (mk_funspec  (argsig,retsig) cc E A P Q)  ->
  forall Delta x F ret a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc  ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax E Delta
       (((tc_expr Delta a ∧ tc_exprlist Delta argsig bl))  ∧
           (assert_of (fun rho => func_ptr fs1 (eval_expr a rho)) ∗
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (assert_of (Q x)) retsig ret)).
Proof.
  intros.
  eapply semax_pre, semax_call; [|done..].
  rewrite bi.and_elim_r; apply bi.and_mono; first done.
  apply bi.sep_mono; last done.
  split => rho; simpl.
  by apply func_ptr_mono.
Qed.

Lemma semax_call_subsume_si:
  forall E (fs1: funspec) A P Q argsig retsig cc,
   forall Delta  x F ret a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc  ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax E Delta
       ((tc_expr Delta a ∧ tc_exprlist Delta argsig bl) ∧
           ((assert_of (fun rho => func_ptr_si fs1 (eval_expr a rho)) ∧ ⎡funspec_sub_si fs1 (mk_funspec  (argsig,retsig) cc E A P Q)⎤) ∗
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (assert_of (Q x)) retsig ret)).
Proof.
  intros.
  eapply semax_pre, semax_call; [|done..].
  rewrite bi.and_elim_r; apply bi.and_mono; first done.
  apply bi.sep_mono; last done.
  monPred.unseal; split => rho; simpl.
  rewrite comm; apply func_ptr_si_mono.
Qed.

(* For now, NDmk_funspec defaults to ⊤ mask, so functions can only be called at ⊤. *)
Lemma semax_call_NDsubsume :
  forall (fs1: funspec) A P Q argsig retsig cc,
    NDfunspec_sub fs1
        (NDmk_funspec  (argsig,retsig) cc A P Q)  ->
    forall  Delta  x F ret a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax ⊤ Delta
       (((tc_expr Delta a ∧ tc_exprlist Delta argsig bl))  ∧
           (assert_of (fun rho => func_ptr fs1 (eval_expr a rho)) ∗
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (assert_of (Q x)) retsig ret)).
Proof.
  intros.
  apply (semax_call_subsume ⊤ fs1 (ConstType A) (λne (a : leibnizO A), (P a) : _ -d> iProp Σ) (λne (a : leibnizO A), (Q a) : _ -d> iProp Σ) argsig retsig cc); auto.
  apply NDsubsume_subsume. simpl; auto.
Qed.

End mpred.
