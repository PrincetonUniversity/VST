Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import LiftNotation.
Local Open Scope logic.
(*NOW in veric/seplog.v
Definition NDfunspec_sub (f1 f2 : funspec) :=
let Delta1 := funsig_tycontext (funsig_of_funspec f1) in
let Delta2 := funsig_tycontext (funsig_of_funspec f2) in
 match f1 with
 | mk_funspec fsig1 cc1 (rmaps.ConstType A1) P1 Q1 _ _ =>
 match f2 with
 | mk_funspec fsig2 cc2 (rmaps.ConstType A2) P2 Q2 _ _ =>
   funsigs_match fsig1 fsig2 = true /\ cc1 = cc2 /\ 
   let ids1 := map fst (fst fsig1) in
   let ids2 := map fst (fst fsig2) in
   forall x2,
        ENTAIL Delta2, (port ids2 ids2) (P2 nil x2) |-- EX x1:_, EX F:mpred,
                             ((local (tc_environ Delta1)) && (`F * (port ids1 ids2) (P1 nil x1)) &&
                              (!! (ENTAIL (ret0_tycon Delta1), `F * Q1 nil x1 
                                      |-- ((local (tc_environ (ret0_tycon Delta2))) && Q2 nil x2))))
 | _ => False end
 | _ => False end.*)

(*
Definition NDfunspec_sub (f1 f2 : funspec) :=
let Delta1 := funsig_tycontext (funsig_of_funspec f1) in
let Delta2 := funsig_tycontext (funsig_of_funspec f2) in
 match f1 with
 | mk_funspec fsig1 cc1 (rmaps.ConstType A1) P1 Q1 _ _ =>
 match f2 with
 | mk_funspec fsig2 cc2 (rmaps.ConstType A2) P2 Q2 _ _ =>
   funsigs_match fsig1 fsig2 = true /\ cc1 = cc2 /\ 
   let ids1 := map fst (fst fsig1) in
   let ids2 := map fst (fst fsig2) in
   forall x2,
        ENTAIL Delta2, (port ids2 ids2) (P2 nil x2) |-- EX x1:_, EX F:mpred,
                             ((*(local (tc_environ Delta1)) &&*) (`F * (port ids1 ids2) (P1 nil x1)) &&
                              (!! (forall rho', 
                                        ((local (tc_environ (ret0_tycon Delta1)) rho') && (F * (Q1 nil x1 rho')))
                                           |-- ((local (tc_environ (ret0_tycon Delta2)) rho') && Q2 nil x2 rho'))))
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
destruct f1 as [f1 c1 A1 P1 Q1 NEP1 NEQ1].
destruct f2 as [f2 c2 A2 P2 Q2 NEP2 NEQ2].
destruct A1; try contradiction. destruct A2; try contradiction.
destruct H1 as [? [? ?]]. split3; trivial.
destruct f1 as [params1 retty1]. destruct f2 as [params2 retty2].
simpl fst in *; simpl snd in *. (*subst c2*)
intros ts2 x2 rho. simpl funsig_of_funspec in *.
unfold port, restrict in *.
simpl in H0.
specialize (H0 ts2). destruct H0 as [H0 H0'].
specialize (H3 x2).
rewrite H0 in *. rewrite H0' in *. 
eapply predicates_hered.derives_trans; [apply H3 | clear H3 ].
apply (predicates_hered.exp_right (@nil Type)).
apply predicates_hered.exp_derives; intros x.
apply predicates_hered.exp_derives; intros F.
apply predicates_hered.andp_derives; trivial.
hnf; intros ? [TC X]. simpl in *. split; trivial. clear X. subst.
destruct TC as [? [? ?]]; split3; trivial. simpl in *. clear - H2. 
red; intros. destruct (H2 _ _ H) as [u [Hu TCu]]; clear H2.
Abort.
*)
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
   NDfunspec_sub (NDmk_Newfunspec fsig cc A P Q) (NDmk_Newfunspec fsig cc A P Q).
Proof.
intros.
apply isNDfunspec_sub_refl; simpl; intros; split; trivial.
Qed.

Lemma NDfunspec_sub_trans:
  forall fsig1 cc1 A1 P1 Q1 fsig2 cc2 A2 P2 Q2 fsig3 cc3 A3 P3 Q3, 
   NDfunspec_sub (NDmk_Newfunspec fsig1 cc1 A1 P1 Q1) (NDmk_Newfunspec fsig2 cc2 A2 P2 Q2) ->
   NDfunspec_sub (NDmk_Newfunspec fsig2 cc2 A2 P2 Q2) (NDmk_Newfunspec fsig3 cc3 A3 P3 Q3) ->
   NDfunspec_sub (NDmk_Newfunspec fsig1 cc1 A1 P1 Q1) (NDmk_Newfunspec fsig3 cc3 A3 P3 Q3).
Proof. intros.
eapply isNDfunspec_sub_trans. 4: eassumption.
all: simpl; trivial.
all: intros; split; trivial.
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
  forall fs1 A P Q NEP NEQ argsig retsig cc,
    funspec_sub fs1 (mk_Newfunspec  (argsig,retsig) cc A P Q NEP NEQ)  ->
   forall {CS: compspecs} {Espec: OracleKind} Delta ts x (F: environ -> mpred) ret  a bl,
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
remember (mk_Newfunspec (argsig, retsig) cc A P Q NEP NEQ) as gs.
remember (eval_expr a rho) as v.
unfold func_ptr.
apply func_ptr_mono; trivial.
Qed.

Lemma semax_call_subsume_si:
  forall fs1 A P Q NEP NEQ argsig retsig cc,
   forall {CS: compspecs} {Espec: OracleKind} Delta ts x (F: environ -> mpred) ret  a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->   
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          (((*|>*)((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  && 
          
         (`(func_ptr fs1) (eval_expr a) && `(funspec_sub_si fs1 (mk_Newfunspec  (argsig,retsig) cc A P Q NEP NEQ)) &&
          |>(F * (fun rho => P ts x (ge_of rho, eval_exprlist argsig bl rho)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Proof. intros.
eapply semax_pre. 2: apply semax_call with (P0:=P)(NEP0:=NEP)(NEQ0:=NEQ); trivial; eassumption.
apply andp_left2. apply andp_derives; trivial. apply andp_derives; trivial.
unfold liftx, lift. simpl. clear. intros rho.
rewrite andp_comm. apply func_ptr_si_mono.
Qed.

Lemma semax_call_NDsubsume :
  forall fs1 A P Q argsig retsig cc,
    NDfunspec_sub fs1 
        (NDmk_Newfunspec  (argsig,retsig) cc A P Q)  ->
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
   (const_args_super_non_expansive A _) (const_args_super_non_expansive A _)
    argsig retsig cc); auto.
+ clear - H.
  apply NDsubsume_subsume.
  - simpl; auto.
  - apply H.
+ apply nil.
Qed.
