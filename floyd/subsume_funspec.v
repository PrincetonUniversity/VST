Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import LiftNotation.
Local Open Scope logic.
(*
Definition NDfunspec_sub (f1 f2 : funspec) :=
let Delta2 := rettype_tycontext (snd (typesig_of_funspec f2)) in
match f1 with
| mk_funspec tpsig1 cc1 (rmaps.ConstType A1) P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 (rmaps.ConstType As) P2 Q2 _ _ =>
        (tpsig1=tpsig2 /\ cc1=cc2) /\
        forall x2 (rho:argsEnviron),
        ((!! (tc_argsenv Delta2 (fst tpsig2)) rho) && P2 nil x2 rho)
         |-- (EX x1:_, EX F:_, 
                           (F * (P1 nil x1 rho)) &&
                               (!! (forall rho',
                                           ((!! (tc_environ (rettype_tycontext (snd tpsig1)) rho') &&
                                                 (F * (Q1 nil x1 rho')))
                                         |-- (Q2 nil x2 rho')))))
 | _ => False end
 | _ => False end.*)

Definition NDfunspec_sub (f1 f2 : funspec) :=
let Delta2 := rettype_tycontext (snd (typesig_of_funspec f2)) in
match f1 with
| mk_funspec tpsig1 cc1 (rmaps.ConstType A1) P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 (rmaps.ConstType As) P2 Q2 _ _ =>
        (tpsig1=tpsig2 /\ cc1=cc2) /\
        forall x2 (gargs:argsEnviron),
        ((!! (argsHaveTyps(snd gargs)(fst tpsig1)) && P2 nil x2 gargs)
         |-- (EX x1:_, EX F:_, 
                           (F * (P1 nil x1 gargs)) &&
                               (!! (forall rho',
                                           ((!! (ve_of rho' = Map.empty (block * type))) &&
                                                 (F * (Q1 nil x1 rho')))
                                         |-- (Q2 nil x2 rho')))))
 | _ => False end
 | _ => False end.

Definition is_NDfunspec (fs: funspec) :=
 match fs with
 | mk_funspec _ _ (rmaps.ConstType A) P Q _ _ =>
    (forall ts, P ts = P nil /\ Q ts = Q nil)
 | _ => False
 end.

Lemma NDsubsume_subsume:
  forall f1 f2, 
   is_NDfunspec f2 ->
   NDfunspec_sub f1 f2 ->
   funspec_sub f1 f2.
Proof.
intros f1 f2. pose proof I. intros H0 H1.
destruct f1, f2; hnf in H1.
destruct A; try contradiction. destruct A0; try contradiction.
destruct H1 as [[? ?] ?]; split; auto.
subst t0 c0.
intros ts1 x1 rho.
specialize (H3 x1).
simpl in H0.
specialize (H0 ts1). destruct H0 as [H0 H0'].
rewrite H0.
eapply derives_trans; [apply H3 | clear H3 ].
apply (exp_right (@nil Type)). simpl.
apply exp_derives; intros x2.
apply exp_derives; intros F.
apply andp_derives; trivial. simpl. apply prop_derives. intros.
rewrite H0'. eapply derives_trans. 2: apply H1. clear H1. apply andp_derives; trivial; try apply derives_refl.
Qed.

Inductive empty_type : Type := .

Definition withtype_of_NDfunspec fs := match fs with
  mk_funspec _ _ (rmaps.ConstType A) _ _ _ _ => A | _ => empty_type end.
 

Definition withtype_of_funspec fs := match fs with
  mk_funspec _ _ A _ _ _ _ => A end.

Lemma sepcon_ENTAIL:
 forall Delta P Q P' Q',
  ENTAIL Delta, P |-- P' ->
  ENTAIL Delta, Q |-- Q' ->
  ENTAIL Delta, P * Q |-- P' * Q'.
Proof.
intros.
intro rho; specialize (H rho); specialize (H0 rho); simpl in *.
unfold local, lift1 in *.
normalize.
rewrite prop_true_andp in H,H0 by auto.
apply sepcon_derives; auto.
Qed.

Lemma NDfunspec_sub_refl:
  forall fsig cc A P Q, 
   NDfunspec_sub (NDmk_funspec fsig cc A P Q) (NDmk_funspec fsig cc A P Q).
Proof.
intros.
simpl.
split; auto.
intros.
Exists x2. Exists emp.
unfold_lift.
rewrite !emp_sepcon.
apply andp_right.
apply andp_left2; auto.
apply prop_right.
intros rho'.
rewrite emp_sepcon.
apply andp_left2; auto.
Qed.

Lemma NDfunspec_sub_trans:
  forall fsig1 cc1 A1 P1 Q1 fsig2 cc2 A2 P2 Q2 fsig3 cc3 A3 P3 Q3, 
   NDfunspec_sub (NDmk_funspec fsig1 cc1 A1 P1 Q1) (NDmk_funspec fsig2 cc2 A2 P2 Q2) ->
   NDfunspec_sub (NDmk_funspec fsig2 cc2 A2 P2 Q2) (NDmk_funspec fsig3 cc3 A3 P3 Q3) ->
   NDfunspec_sub (NDmk_funspec fsig1 cc1 A1 P1 Q1) (NDmk_funspec fsig3 cc3 A3 P3 Q3).
Proof.
intros.
destruct H as [[?E ?E'] H]. 
destruct H0 as [[?F ?F'] H0].
subst.
split; auto.
intro x3; simpl in x3. simpl in H, H0. simpl. intros.
specialize (H0 x3 gargs).
eapply derives_trans. apply andp_right. apply andp_left1. apply derives_refl. apply H0. clear H0.
(*eapply ENTAIL_trans; [apply H0 | ].
clear H0.*)
normalize. rename x1 into x2.
specialize (H x2 gargs).
eapply derives_trans.
(*apply sepcon_ENTAIL.*) apply sepcon_derives.
(*apply ENTAIL_refl.*) apply derives_refl.
apply andp_right. apply prop_right. apply H0. apply derives_refl. 
eapply derives_trans. apply sepcon_derives. apply derives_refl.  apply H. 
clear H.
Intros x1.
Intros F1.
Exists x1 (F*F1). rewrite sepcon_assoc. apply andp_right; trivial.
apply prop_right.
intro tau.
eapply derives_trans. 2: apply H1. clear H1. normalize.
rewrite sepcon_assoc. apply sepcon_derives; trivial.
eapply derives_trans. 2: apply H. clear H. normalize.
Qed.

Lemma later_exp'' (A: Type) (ND: NatDed A)(Indir: Indir A):
      forall T : Type,
       (exists x: T, True) ->
       forall F : T -> A,
       |> (EX x : _, F x) = EX x : T, |> F x.
Proof.
intros.
destruct H as [x _].
apply later_exp'; auto.
Qed.

Lemma semax_call_subsume:
  forall (fs1: funspec) A P Q NEP NEQ argsig retsig cc,
    funspec_sub fs1 (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)  ->
   forall {CS: compspecs} {Espec: OracleKind} Delta  ts x (F: environ -> mpred) ret  a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->   
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          (((*|>*)((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  &&
         (`(func_ptr fs1) (eval_expr a) &&
          |>(F * (fun rho => P ts x (ge_of rho, eval_exprlist argsig bl rho)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Proof. intros.
eapply semax_pre. 2: apply semax_call with (P0:=P)(NEP0:=NEP)(NEQ0:=NEQ); trivial; eassumption.
apply andp_left2. apply andp_derives; trivial. apply andp_derives; trivial.
unfold liftx, lift. simpl. intros rho. clear - H.
remember (mk_funspec (argsig, retsig) cc A P Q NEP NEQ) as gs.
remember (eval_expr a rho) as v.
unfold func_ptr.
apply func_ptr_mono; trivial.
apply derives_refl.
Qed.

Lemma semax_call_subsume_si:
  forall (fs1: funspec) A P Q NEP NEQ argsig retsig cc,
   forall {CS: compspecs} {Espec: OracleKind} Delta  ts x (F: environ -> mpred) ret  a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc  ->
           (retsig = Tvoid -> ret = None) ->   
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          (((*|>*)((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  && 
          
         (`(func_ptr fs1) (eval_expr a) && `(funspec_sub_si fs1 (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) &&
          |>(F * (fun rho => P ts x (ge_of rho, eval_exprlist argsig bl rho)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Proof. intros.
eapply semax_pre. 2: apply semax_call with (P0:=P)(NEP0:=NEP)(NEQ0:=NEQ); trivial; eassumption.
apply andp_left2. apply andp_derives; trivial. apply andp_derives; trivial.
unfold liftx, lift. simpl. clear. intros rho.
rewrite andp_comm. apply func_ptr_si_mono.
apply derives_refl.
Qed.

Lemma semax_call_NDsubsume :
  forall (fs1: funspec) A P Q argsig retsig cc,
    NDfunspec_sub fs1 
        (NDmk_funspec  (argsig,retsig) cc A P Q)  ->
     forall {CS: compspecs} {Espec: OracleKind},
    forall  Delta  x (F: environ -> mpred) ret a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          (((*|>*)((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  &&
         (`(func_ptr fs1) (eval_expr a) &&
          |>(F * (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q x) retsig ret)).
Proof.
intros.
apply (semax_call_subsume fs1 (rmaps.ConstType A) (fun _ => P) (fun _ => Q)
   (args_const_super_non_expansive A _) (const_super_non_expansive A _)
    argsig retsig cc); auto.
clear - H.
apply NDsubsume_subsume. simpl; auto. apply H. apply nil.
Qed.