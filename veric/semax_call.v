Require Import Coq.Logic.FunctionalExtensionality.
Require Import VST.veric.juicy_base.
Require Import VST.msl.normalize.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.expr_lemmas4.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.
Import LiftNotation.
Local Open Scope pred.

Lemma age_later {A} {agA : ageable A}: forall {w w1 w2} (AGE: age w w1) (L: laterR w w2), w1=w2 \/ laterR w1 w2.
Proof. intros. induction L.
+ unfold age in *. rewrite AGE in H. left; inv H; trivial.
+ right. destruct (IHL1 AGE); subst. apply L2. eapply t_trans; eassumption.
Qed.

Lemma tc_val_sem_cast':
  forall {cs: compspecs} t2 e2 rho Delta,
      @typecheck_environ Delta rho ->
      @denote_tc_assert cs (@typecheck_expr cs Delta e2) rho
     &&  @denote_tc_assert cs (@isCastResultType cs (typeof e2) t2  e2) rho 
     |-- !! @tc_val t2 (force_val (sem_cast (typeof e2) t2 (eval_expr e2 rho))).
Proof.
intros.
intro phi.
intros [? ?].
eapply expr_lemmas.tc_val_sem_cast; eauto.
Qed.

Lemma typecheck_expr_sound' {cs: compspecs} :
  forall Delta rho e,
    @typecheck_environ Delta rho ->
    @tc_expr cs Delta e rho |-- !! @tc_val (typeof e) (eval_expr e rho).
Proof.
intros.
intros ? ?.
simpl.
eapply expr_lemmas4.typecheck_expr_sound; eauto.
Qed.

Lemma tc_environ_make_args':
 forall {CS: compspecs} argsig retsig bl rho Delta,
   tc_environ Delta rho ->
  tc_exprlist Delta (snd (split argsig)) bl rho
  |-- !! tc_environ (funsig_tycontext (argsig, retsig)) (make_args (map fst argsig)
         (eval_exprlist (snd (split argsig)) bl rho) rho).
Proof.
intros. rename H into H2.
unfold tc_environ.
simpl.
unfold tc_exprlist.
revert bl; induction argsig; destruct bl as [ | b bl]; simpl; intros; unfold_lift.
* hnf; intros. clear H.
  split3; hnf; intros; try (simpl in *; rewrite PTree.gempty in H; inv H).
  rewrite PTree.gempty. split; intro. inv H. destruct H. inv H.
* apply prop_derives; intros. inv H.
* destruct a as [i ti]; simpl.
  destruct (split argsig) eqn:?.
  simpl.
  unfold_lift; apply prop_derives; intros; inv H.
* destruct a as [i ti]; simpl.
  destruct (split argsig) eqn:?.
  specialize (IHargsig bl).
  simpl denote_tc_assert.
  rewrite !denote_tc_assert_andp.
  simpl andp.
  unfold_lift.
  apply derives_trans with
   (denote_tc_assert (typecheck_expr Delta b) rho &&
   denote_tc_assert (isCastResultType (typeof b) ti b) rho &&
   (!! typecheck_environ (funsig_tycontext (argsig, retsig))
                    (make_args (map fst argsig)
                       (eval_exprlist l0 bl rho) rho))).
  apply andp_derives; auto.
  clear IHargsig.
  simpl. unfold_lift.
  normalize.
  destruct H as [? [? ?]].
  unfold typecheck_environ; simpl.
  match goal with |- ?A |-- ?B => apply derives_trans with
      (!! tc_val' ti (force_val (sem_cast (typeof b) ti (eval_expr b rho))) && A)
  end.
  + apply andp_right; auto.
    clear - H2.
    apply derives_trans with (!! (tc_val (typeof b) (eval_expr b rho)) &&
     !! (tc_val ti (force_val (sem_cast (typeof b) ti (eval_expr b rho))))).
    - apply andp_right.
      eapply derives_trans; [ | eapply typecheck_expr_sound']; eauto.
      apply andp_left1. apply derives_refl.
      pose proof expr_lemmas.tc_val_sem_cast.
      apply tc_val_sem_cast'; auto.
    - apply andp_left2.
      apply prop_derives.
      unfold tc_val'.
      intros; auto.
  + normalize. rename H3 into H8.
    hnf; intros. simpl.
    split3; auto.
    unfold typecheck_temp_environ; intros.
    destruct (ident_eq i id).
    - subst.
      rewrite PTree.gss in H4. inv H4.
      rewrite Map.gss.
      eexists; split; eauto.
    - rewrite Map.gso by auto.
      apply (H id ty).
      rewrite PTree.gso in H4 by auto.
      simpl. auto.
Qed.

(* Scall *)

Lemma age_twin' {A B} `{HA: ageable A} `{HB: ageable B}:
  forall (x: A) (y: B) (x': A),
       level x = level y -> age x x' ->
       exists y', level x' = level y' /\ age y y'.
Proof.
intros x y x' H0 H1.
unfold fashionR in *.
destruct (age1_levelS _ _ H1) as [n ?].
rewrite H0 in H.
destruct (levelS_age1 _ _ H) as [y' ?].
exists y'; split.
apply age_level in H2.
apply age_level in H1.
congruence.
auto.
Qed.

Lemma later_twin' {A B} `{HA: ageable A} `{HB: ageable B}:
  forall (x: A) (y: B) (x': A),
       level x = level y -> laterR x x' ->
       exists y', level x' = level y' /\ laterR y y'.
Proof.
intros x y x' H0 H1.
revert y H0; induction H1; intros.
destruct (age_twin' _ _ _ H0 H) as [y' [? ?]].
exists y'; split; auto.
specialize (IHclos_trans1 _ H0).
destruct IHclos_trans1 as [y2 [? ?]].
specialize (IHclos_trans2 _ H).
destruct IHclos_trans2 as [u [? ?]].
exists u; split; auto.
apply t_trans with y2; auto.
Qed.

Lemma later_twin {A} `{ageable A}:
   forall phi1 phi2 phi1',
     level phi1 = level phi2 ->
     laterR phi1 phi1' ->
     exists phi2', level phi1' = level phi2' /\ laterR phi2 phi2'.
Proof.
intros.
eapply later_twin'; eauto.
Qed.

Lemma someP_inj:  forall A P Q, SomeP A P = SomeP A Q -> P=Q.
Proof. intros. injection H; intro. apply inj_pair2 in H0. auto. Qed.

Lemma function_pointer_aux:
  forall A P P' Q Q' (w: rmap),
    super_non_expansive P ->
    super_non_expansive Q ->
    super_non_expansive P' ->
    super_non_expansive Q' ->
   SomeP (SpecTT A) (fmap (fpi _) (approx (level w)) (approx (level w)) (packPQ P Q)) =
   SomeP (SpecTT A) (fmap (fpi _) (approx (level w)) (approx (level w)) (packPQ P' Q')) ->
   ( (forall ts x vl, (! |> (P' ts x vl <=> P ts x vl)) w) /\
     (forall ts x vl, (! |> (Q' ts x vl <=> Q ts x vl)) w)).
Proof.
  intros ? ? ? ? ? ? NEP NEQ NEP' NEQ' H.
  apply someP_inj in H.
  unfold packPQ in H; simpl in H.
  split; intros.
  + apply equal_f_dep with ts in H.
    apply equal_f with x in H.
    apply equal_f with true in H.
    apply equal_f with vl in H.
    simpl in H.
    rewrite @later_fash; auto with typeclass_instances.
    intros ? ? m' ?.
    assert (forall m'', necR m' m'' -> (level m'' < level w)%nat).
    {
      intros.
      clear - H0 H1 H2; hnf in H1.
      apply laterR_level in H1.
      apply necR_level in H2; simpl in *.
      omega.
    }
    split; intros m'' ? ?.
    - apply f_equal with (f:= fun x => app_pred x m'') in H.
      apply prop_unext in H.
      apply approx_p with (level w).
      rewrite NEP.
      apply H.
      rewrite <- NEP'.
      apply approx_lt; auto.
    - apply f_equal with (f:= fun x => app_pred x m'') in H.
      apply prop_unext in H.
      apply approx_p with (level w).
      rewrite NEP'.
      apply H.
      rewrite <- NEP.
      apply approx_lt; auto.
  + apply equal_f_dep with ts in H.
    apply equal_f with x in H.
    apply equal_f with false in H.
    apply equal_f with vl in H.
    simpl in H.
    rewrite @later_fash; auto with typeclass_instances; intros ? ? m' ?.
    assert (forall m'', necR m' m'' -> (level m'' < level w)%nat).
    {
      intros.
      clear - H0 H1 H2; hnf in H1.
      apply laterR_level in H1.
      apply necR_level in H2; simpl in *.
      omega.
    }
    split; intros m'' ? ?.
    - apply f_equal with (f:= fun x => app_pred x m'') in H.
      apply prop_unext in H.
      apply approx_p with (level w).
      rewrite NEQ.
      apply H.
      rewrite <- NEQ'.
     apply approx_lt; auto.
    - apply f_equal with (f:= fun x => app_pred x m'') in H.
      apply prop_unext in H.
      apply approx_p with (level w).
      rewrite NEQ'.
      apply H.
      rewrite <- NEQ.
     apply approx_lt; auto.
Qed.

Import JuicyMemOps.

Fixpoint alloc_juicy_variables (ge: genv) (rho: env) (jm: juicy_mem) (vl: list (ident*type)) : env * juicy_mem :=
 match vl with
 | nil => (rho,jm)
 | (id,ty)::vars => match JuicyMemOps.juicy_mem_alloc jm 0 (@sizeof ge ty) with
                              (m1,b1) => alloc_juicy_variables ge (PTree.set id (b1,ty) rho) m1 vars
                           end
 end.

Lemma juicy_mem_alloc_core:
  forall jm lo hi jm' b, JuicyMemOps.juicy_mem_alloc jm lo hi = (jm', b) ->
    core (m_phi jm) = core (m_phi jm').
Proof.
 unfold JuicyMemOps.juicy_mem_alloc, after_alloc; intros.
 inv H.
 simpl.
 apply rmap_ext.
 repeat rewrite level_core. rewrite level_make_rmap. auto.
 intro loc.
 repeat rewrite <- core_resource_at.
 rewrite resource_at_make_rmap.
 unfold after_alloc'.
 if_tac; auto.
 destruct loc as [b z].
 simpl in H.
 rewrite core_YES.
 rewrite juicy_mem_alloc_cohere. rewrite core_NO; auto.
 simpl. destruct H.
 revert H; case_eq (alloc (m_dry jm) lo hi); intros.
 simpl in *. subst b0. apply alloc_result in H. subst b; xomega.
 rewrite <- (core_ghost_of (proj1_sig _)), ghost_of_make_rmap, core_ghost_of; auto.
Qed.

Lemma alloc_juicy_variables_e:
  forall ge rho jm vl rho' jm',
    alloc_juicy_variables ge rho jm vl = (rho', jm') ->
  Clight.alloc_variables ge rho (m_dry jm) vl rho' (m_dry jm')
   /\ level jm = level jm'
   /\ core (m_phi jm) = core (m_phi jm').
Proof.
 intros.
 revert rho jm H; induction vl; intros.
 inv H. split; auto. constructor.
 unfold alloc_juicy_variables in H; fold alloc_juicy_variables in H.
 destruct a as [id ty].
 revert H; case_eq (JuicyMemOps.juicy_mem_alloc jm 0 (@sizeof ge ty)); intros jm1 b1 ? ?.
 specialize (IHvl (PTree.set id (b1,ty) rho) jm1 H0).
 destruct IHvl as [? [? ?]]; split3; auto.
 apply alloc_variables_cons  with  (m_dry jm1) b1; auto.
 apply JuicyMemOps.juicy_mem_alloc_succeeds in H. auto.
 apply JuicyMemOps.juicy_mem_alloc_level in H.
 congruence.
 rewrite <- H3.
 eapply  juicy_mem_alloc_core; eauto.
Qed.


Lemma alloc_juicy_variables_match_venv:
  forall ge jm vl ve' jm',
     alloc_juicy_variables ge empty_env jm vl = (ve',jm') ->
     match_venv (make_venv ve') vl.
Proof.
intros.
  intro i.
 unfold make_venv.
  destruct (ve' ! i) as [[? ?] | ] eqn:?; auto.
  assert (H0: (exists b, empty_env ! i = Some (b,t)) \/ In (i,t) vl).
2: destruct H0; auto; destruct H0; rewrite PTree.gempty in H0; inv H0.
 forget empty_env as e.
  revert jm e H; induction vl; simpl; intros.
  inv H.
  left; eexists; eauto.
  destruct a.
  apply IHvl in H; clear IHvl.
 destruct (ident_eq i0 i). subst i0.
 destruct H; auto. destruct H as [b' ?].
 rewrite PTree.gss in H. inv H. right. auto.
 destruct H; auto. left. destruct H as [b' ?].
 rewrite PTree.gso in H by auto. eauto.
Qed.

Lemma build_call_temp_env:
  forall f vl,
     length (fn_params f) = length vl ->
  exists te,  bind_parameter_temps (fn_params f) vl
                     (create_undef_temps (fn_temps f)) = Some te.
Proof.
 intros.
 forget (create_undef_temps (fn_temps f)) as rho.
 revert rho vl H; induction (fn_params f); destruct vl; intros; inv H; try congruence.
 exists rho; reflexivity.
 destruct a; simpl.
 apply IHl. auto.
Qed.

Lemma resource_decay_funassert:
  forall G rho b w w',
         necR (core w) (core w') ->
         resource_decay b w w' ->
         app_pred (funassert G rho) w ->
         app_pred (funassert G rho) w'.
Proof.
unfold resource_decay, funassert; intros until w'; intro CORE; intros.
destruct H. 
destruct H0.
split; [clear H2 | clear H0].
+ intros id fs w2 Hw2 H3.
  specialize (H0 id fs). cbv beta in H0.
  specialize (H0 _ (necR_refl _) H3).
  destruct H0 as [loc [? ?]].
  exists loc; split; auto.
  destruct fs as [f cc A a a0].
  simpl in H2|-*.
  pose proof (necR_resource_at (core w) (core w') (loc,0)
         (PURE (FUN f cc) (SomeP (SpecTT A) (packPQ a a0))) CORE).
  pose proof (necR_resource_at _ _ (loc,0)
         (PURE (FUN f cc) (SomeP (SpecTT A) (packPQ a a0))) Hw2).
  apply H5.
  clear - H4 H2.
  repeat rewrite <- core_resource_at in *.
  spec H4. rewrite H2.  rewrite core_PURE.  simpl.  rewrite level_core; reflexivity.
  destruct (w' @ (loc,0)).
  rewrite core_NO in H4; inv H4.
  rewrite core_YES in H4; inv H4.
  rewrite core_PURE in H4; inv H4. rewrite level_core; reflexivity.
+
intros loc sig cc w2 Hw2 H6.
specialize (H2 loc sig cc _ (necR_refl _)).
spec H2.
{ clear - Hw2 CORE H6. simpl in *.
  destruct H6 as [pp H6].
  rewrite <- resource_at_approx.
  case_eq (w @ (loc,0)); intros.
  + assert (core w @ (loc,0) = resource_fmap (approx (level (core w))) (approx (level (core w))) (NO _ bot_unreadable)).
     - rewrite <- core_resource_at.
       simpl; erewrite <- core_NO; f_equal; eassumption.
     - pose proof (necR_resource_at _ _ _ _ CORE H0).
       pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
       rewrite <- core_resource_at in H2; rewrite H6 in H2;
       rewrite core_PURE in H2; inv H2.
  + assert (core w @ (loc,0) = resource_fmap (approx (level (core w))) (approx (level (core w))) (NO _ bot_unreadable)).
    - rewrite <- core_resource_at.
      simpl; erewrite <- core_YES; f_equal; eassumption.
    - pose proof (necR_resource_at _ _ _ _ CORE H0).
      pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
      rewrite <- core_resource_at in H2; rewrite H6 in H2;
      rewrite core_PURE in H2; inv H2.
  + pose proof (resource_at_approx w (loc,0)).
    pattern (w @ (loc,0)) at 1 in H0; rewrite H in H0.
    symmetry in H0.
    assert (core (w @ (loc,0)) = core (resource_fmap (approx (level w)) (approx (level w))
       (PURE k p))) by (f_equal; auto).
    rewrite core_resource_at in H1.
    assert (core w @ (loc,0) =
        resource_fmap (approx (level (core w))) (approx (level (core w)))
         (PURE k p)).
    - rewrite H1.  simpl. rewrite level_core; rewrite core_PURE; auto.
    - pose proof (necR_resource_at _ _ _ _ CORE H2).
      assert (w' @ (loc,0) = resource_fmap
         (approx (level w')) (approx (level w')) (PURE k p)).
      * rewrite <- core_resource_at in H3. rewrite level_core in H3.
        destruct (w' @ (loc,0)).
        ++ rewrite core_NO in H3; inv H3.
        ++ rewrite core_YES in H3; inv H3.
        ++ rewrite core_PURE in H3; inv H3.
           reflexivity.
      * pose proof (necR_resource_at _ _ _ _ Hw2 H4).
        inversion2 H6 H5.
        exists p. reflexivity. }
destruct H2 as [id [? ?]].
exists id. split; auto.
Qed. 

Definition substopt {A} (ret: option ident) (v: val) (P: environ -> A)  : environ -> A :=
   match ret with
   | Some id => subst id v P
   | None => P
   end.

Lemma fst_split {T1 T2}: forall vl: list (T1*T2), fst (split vl) = map fst vl.
Proof. induction vl; try destruct a; simpl; auto.
  rewrite <- IHvl; clear IHvl.
 destruct (split vl); simpl in *; auto.
Qed.

Lemma snd_split {T1 T2}: forall vl: list (T1*T2), snd (split vl) = map snd vl.
Proof. induction vl; try destruct a; simpl; auto.
  rewrite <- IHvl; clear IHvl.
 destruct (split vl); simpl in *; auto.
Qed.

Lemma bind_parameter_temps_excludes :
forall l1 l2 t id t1,
~In id (map fst l1) ->
(bind_parameter_temps l1 l2 t) = Some t1 ->
t1 ! id = t ! id.
Proof.
induction l1;
intros.
simpl in *. destruct l2; inv H0. auto.
simpl in H0. destruct a. destruct l2; inv H0.
specialize (IHl1 l2 (PTree.set i v t) id t1).
simpl in H. intuition. rewrite PTree.gsspec in H3.
destruct (peq id i). subst; intuition. auto.
Qed.

Lemma pass_params_ni :
  forall  l2
     (te' : temp_env) (id : positive) te l,
   bind_parameter_temps l2 l (te) = Some te' ->
   (In id (map fst l2) -> False) ->
   Map.get (make_tenv te') id = te ! id.
Proof.
intros. eapply bind_parameter_temps_excludes in H.
unfold make_tenv, Map.get.
apply H. intuition.
Qed.

Lemma bind_exists_te : forall l1 l2 t1 t2 te,
bind_parameter_temps l1 l2 t1 = Some te ->
exists te2, bind_parameter_temps l1 l2 t2 = Some te2.
Proof.
induction l1; intros.
+ simpl in H. destruct l2; inv H. simpl. eauto.

+ destruct a. simpl in *. destruct l2; inv H. eapply IHl1.
apply H1.
Qed.


Lemma smaller_temps_exists2 : forall l1 l2 t1 t2 te te2 i,
bind_parameter_temps l1 l2 t1 = Some te ->
bind_parameter_temps l1 l2 t2 = Some te2 ->
t1 ! i = t2 ! i ->
te ! i = te2 ! i.
Proof.
induction l1; intros; simpl in *; try destruct a; destruct l2; inv H; inv H0.
apply H1.
eapply IHl1. apply H3. apply H2.
repeat rewrite PTree.gsspec. destruct (peq i i0); auto.
Qed.


Lemma smaller_temps_exists' : forall l l1 te te' id i t,
bind_parameter_temps l l1 (PTree.set id Vundef t)=  Some te ->
i <> id ->
(bind_parameter_temps l l1 t = Some te') -> te' ! i = te ! i.
Proof.
induction l; intros.
simpl in *. destruct l1; inv H. inv H1. rewrite PTree.gso; auto.

simpl in *. destruct a. destruct l1; inv H.
eapply smaller_temps_exists2. apply H1. apply H3.
intros. repeat rewrite PTree.gsspec. destruct (peq i i0); auto.
destruct (peq i id). subst. intuition. auto.
Qed.

Lemma smaller_temps_exists'' : forall l l1 te id i t,
bind_parameter_temps l l1 (PTree.set id Vundef t)=  Some te ->
i <> id ->
exists te', (bind_parameter_temps l l1 t = Some te').
Proof.
intros.
eapply bind_exists_te; eauto.
Qed.

Lemma smaller_temps_exists : forall l l1 te id i t,
bind_parameter_temps l l1 (PTree.set id Vundef t)=  Some te ->
i <> id ->
exists te', (bind_parameter_temps l l1 t = Some te' /\ te' ! i = te ! i).
Proof.
intros. copy H. eapply smaller_temps_exists'' in H; eauto.
destruct H. exists x. split. auto.
eapply smaller_temps_exists'; eauto.
Qed.


Lemma alloc_vars_lookup :
forall ge id m1 l ve m2 e ,
list_norepet (map fst l) ->
(forall i, In i (map fst l) -> e ! i = None) ->
Clight.alloc_variables ge (e) m1 l ve m2 ->
(exists v, e ! id = Some v) ->
ve ! id = e ! id.
Proof.
intros.
generalize dependent e.
revert ve m1 m2.

induction l; intros.
inv H1. auto.

inv H1. simpl in *. inv H.
destruct H2.
assert (id <> id0).
intro. subst.  specialize (H0 id0). spec H0. auto. congruence.
eapply IHl in H10.
rewrite PTree.gso in H10; auto.
auto. intros. rewrite PTree.gsspec. if_tac. subst. intuition.
apply H0. auto.
rewrite PTree.gso; auto. eauto.
Qed.

Lemma alloc_vars_lemma : forall ge id l m1 m2 ve ve'
(SD : forall i, In i (map fst l) -> ve ! i = None),
list_norepet (map fst l) ->

Clight.alloc_variables ge ve m1 l ve' m2 ->
(In id (map fst l) ->
exists v, ve' ! id = Some v).
Proof.
intros.
generalize dependent ve.
revert m1 m2.
induction l; intros. inv H1.
simpl in *. destruct a; simpl in *.
destruct H1. subst. inv H0. inv H.  apply alloc_vars_lookup with (id := id) in H9; auto.
rewrite H9. rewrite PTree.gss. eauto. intros.
destruct (peq i id). subst. intuition. rewrite PTree.gso; auto.
rewrite PTree.gss; eauto.

inv H0. apply IHl in H10; auto. inv H; auto.
intros. rewrite PTree.gsspec. if_tac. subst. inv H. intuition.
auto.
Qed.

Lemma semax_call_typecheck_environ:
  forall (Delta : tycontext) (args: list val) (psi : genv) (vx : env) (tx : temp_env)
           (jm : juicy_mem) (b : block) (f : function)
     (H17 : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
     (H17' : list_norepet (map fst (fn_vars f)))
     (H16 : Genv.find_funct_ptr psi b = Some (Internal f))
     (ve' : env) (jm' : juicy_mem) (te' : temp_env)
     (H15 : alloc_variables psi empty_env (m_dry jm) (fn_vars f) ve' (m_dry jm'))
    (TC3 : typecheck_temp_environ (make_tenv tx) (temp_types Delta))
    (TC4 : typecheck_var_environ (make_venv vx) (var_types Delta))
    (TC5 : typecheck_glob_environ (filter_genv psi) (glob_types Delta))
   (H : forall (b : ident) (b0 : funspec) (a' : rmap),
    necR (m_phi jm') a' ->
    (glob_specs Delta) ! b = Some b0 ->
    exists b1 : block,
        filter_genv psi b = Some b1 /\
        func_at b0 (b1,0) a')
   (TC8 : tc_vals (snd (split (fn_params f))) args)
   (H21 : bind_parameter_temps (fn_params f) args
              (create_undef_temps (fn_temps f)) = Some te'),
   typecheck_environ
    (mk_tycontext
      (make_tycontext_t (fn_params f) (fn_temps f))
      (make_tycontext_v (fn_vars f))
      (fn_return f)  (glob_types Delta) (glob_specs Delta) (annotations Delta))
     (mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).
Proof. assert (H1:= True).
 intros.
 pose (rho3 := mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).

unfold typecheck_environ. repeat rewrite andb_true_iff.
split3.
*
clear H H1 H15.
unfold typecheck_temp_environ in *. intros. simpl.
unfold temp_types in *. simpl in *.
apply func_tycontext_t_sound in H; auto.
 clear - H21 H TC8 TC3 H17.

destruct H. (*in params*)
forget (create_undef_temps (fn_temps f)) as temps.
rewrite snd_split in TC8.
generalize dependent temps.
generalize dependent args. generalize dependent te'.
{  induction (fn_params f); intros.
   + inv H.
   + destruct args. inv TC8. destruct a. simpl in *.
       destruct TC8 as [TC8' TC8].
       destruct H.
      - clear IHl. 
        inv H.
        rewrite (pass_params_ni _ _ id _ _ H21)
           by (inv H17; contradict H1; apply in_app; auto).
        rewrite PTree.gss.
        eexists.  split. reflexivity. apply tc_val_tc_val'.
        auto.
      - inv H17.
        assert (i <> id). intro. subst.
        apply H2. apply in_or_app. left. apply in_map with (f := fst) in H. apply H.
        eapply IHl; eauto.
}

(*In temps*)
apply list_norepet_app in H17. destruct H17 as [? [? ?]].
generalize dependent (fn_params f). generalize dependent args.
generalize dependent te'.

induction (fn_temps f); intros.
inv H.

simpl in *. destruct H. destruct a. inv H. simpl in *.
clear IHl. exists Vundef. simpl in *. split; [| hnf; congruence]. inv H1.
eapply pass_params_ni with (id := id) in H21; auto.
rewrite PTree.gss in *. auto.
intros.
unfold list_disjoint in *. eapply H2. eauto. left. auto. auto.

destruct a.
destruct (peq id i). subst.
apply pass_params_ni with (id := i) in H21.
rewrite PTree.gss in *. exists Vundef. split; [auto | hnf; congruence].
intros. unfold list_disjoint in *. intuition.
eapply H2. eauto. left. auto. auto.

apply smaller_temps_exists with (i := id) in H21.
destruct H21.  destruct H3.
eapply IHl in H3; auto.
destruct H3. destruct H3.
exists x0. split. unfold Map.get in *.
unfold make_tenv in *. rewrite <- H4. auto. auto.
inv H1; auto. unfold list_disjoint in *. intros.
apply H2. auto. right. auto. auto.
*

simpl in *.
unfold typecheck_var_environ in *. intros.
clear TC3 TC5.
simpl in *. unfold typecheck_var_environ in *.
unfold func_tycontext' in *. unfold var_types in *.
simpl in *.
rewrite (func_tycontext_v_sound (fn_vars f) id ty); auto.
transitivity ((exists b, empty_env ! id = Some (b,ty) )\/ In (id,ty) (fn_vars f)).
clear; intuition. destruct H0. unfold empty_env in H.
rewrite PTree.gempty in H; inv H.
generalize dependent (m_dry jm).
clear - H17'.
assert (forall id, empty_env ! id <> None -> ~ In id (map fst (fn_vars f))).
intros. unfold empty_env in H. rewrite PTree.gempty in H. contradiction H; auto.
generalize dependent empty_env.
unfold Map.get, make_venv.
induction (fn_vars f); intros.
inv H15.
destruct (ve' ! id); intuition.
inv H15.
inv H17'.
specialize (IHl H3); clear H3.
specialize (IHl (PTree.set id0 (b1,ty0) e)).
spec IHl.
intros id' H8; specialize (H id').
destruct (ident_eq id0 id'). subst. auto.
rewrite PTree.gso  in H8 by auto.
specialize (H H8). contradict H.
right; auto.
specialize (IHl _ H7).
clear - H H2 IHl.
destruct (ident_eq id0 id). subst id0.
rewrite PTree.gss in IHl.
split; intro.
destruct H0.
destruct H0. specialize (H id).
destruct (e!id); try discriminate.
inv H0.
spec H; [congruence | ].
contradiction H. left; auto.
destruct H0. inv H0.
apply IHl. left; eauto.
contradiction H2. apply in_map with (f:=fst) in H0. apply H0.
rewrite <- IHl in H0.
destruct H0.
destruct H0. inv H0. right; left; auto.
contradiction H2.
apply in_map with (f:=fst) in H0. auto.
rewrite PTree.gso in IHl by auto.
rewrite <- IHl.
intuition. inv H5. inv H0. intuition.
apply H4 in H0. apply H1; auto.
*
unfold ge_of in *. simpl in *. auto.
Qed.

Lemma free_juicy_mem_level:
  forall jm m b lo hi H, level (free_juicy_mem jm m b lo hi H) = level jm.
Proof.
 intros;  simpl;  unfold inflate_free; simpl.
 rewrite level_make_rmap. auto.
Qed.

Lemma free_juicy_mem_ghost:
  forall jm m b lo hi H,
    ghost_of (m_phi (free_juicy_mem jm m b lo hi H)) = ghost_of (m_phi jm).
Proof.
 intros;  simpl;  unfold inflate_free; simpl.
 rewrite ghost_of_make_rmap. auto.
Qed.

Lemma free_list_free:
  forall m b lo hi l' m',
       free_list m ((b,lo,hi)::l') = Some m' ->
         {m2 | free m b lo hi = Some m2 /\ free_list m2 l' = Some m'}.
Proof.
simpl; intros.
 destruct (free m b lo hi). eauto. inv H.
Qed.

Definition freeable_blocks: list (block * BinInt.Z * BinInt.Z) -> mpred :=
  fold_right (fun (bb: block*BinInt.Z * BinInt.Z) a => 
                        match bb with (b,lo,hi) => 
                                          sepcon (VALspec_range (hi-lo) Share.top (b,lo)) a
                        end)
                    emp.

Inductive free_list_juicy_mem:
      forall  (jm: juicy_mem) (bl: list (block * BinInt.Z * BinInt.Z))
                                         (jm': juicy_mem), Prop :=
| FLJM_nil: forall jm, free_list_juicy_mem jm nil jm
| FLJM_cons: forall jm b lo hi bl jm2 jm'
                          (H: free (m_dry jm) b lo hi = Some (m_dry jm2))
                          (H0 : forall ofs : Z,
                        lo <= ofs < hi ->
                        perm_of_res (m_phi jm @ (b, ofs)) = Some Freeable),
                          free_juicy_mem jm (m_dry jm2) b lo hi H = jm2 ->
                          free_list_juicy_mem jm2 bl jm' ->
                          free_list_juicy_mem jm ((b,lo,hi)::bl) jm'.

Lemma perm_of_res_val : forall r, perm_of_res r = Some Freeable ->
  exists v pp, r = YES Share.top readable_share_top (VAL v) pp.
Proof.
  destruct r; simpl; try if_tac; try discriminate.
  destruct k; try discriminate.
  unfold perm_of_sh.
  repeat if_tac; try discriminate.
  subst; intro; do 2 eexists; f_equal.
  apply proof_irr.
Qed.

Lemma free_list_juicy_mem_i:
  forall jm bl m' F,
   free_list (m_dry jm) bl = Some m' ->
   app_pred (freeable_blocks bl * F) (m_phi jm) ->
   exists jm', free_list_juicy_mem jm bl jm'
                  /\ m_dry jm' = m'
                  /\ level jm = level jm'.
Proof.
intros jm bl; revert jm; induction bl; intros.
*
 inv H; exists jm; split3; auto. constructor.
*
 simpl freeable_blocks in H0. destruct a as [[b lo] hi].
 rewrite sepcon_assoc in H0.
 destruct (free_list_free _ _ _ _ _ _ H) as [m2 [? ?]].
 generalize H0; intro H0'.
 destruct H0 as [phi1 [phi2 [? [? H6]]]].

 assert (H10:= @juicy_free_lemma' jm b lo hi m2 phi1 _ _ H1 H0' H3 H0).
 match type of H10 with m_phi ?A = _ => set (jm2:=A) in H10 end; subst.

 specialize (IHbl  jm2 m' F H2 H6).
 destruct IHbl as [jm' [? [? ?]]].
 exists jm'; split3; auto.
 apply (FLJM_cons jm b lo hi bl jm2 jm' H1
   (juicy_free_aux_lemma (m_phi jm) b lo hi (freeable_blocks bl * F) H0') (eq_refl _) H4).
 rewrite <- H7.
 unfold jm2.
 symmetry; apply free_juicy_mem_level.
Qed.

Lemma free_juicy_mem_ext:
  forall jm1 jm2 b lo hi m1 m2 H1 H2,
      jm1=jm2 -> m1=m2 ->
     free_juicy_mem jm1 m1 b lo hi H1 = free_juicy_mem jm2 m2 b lo hi H2.
Proof.
intros. subst. proof_irr. auto.
Qed.


Lemma free_list_juicy_mem_lem:
  forall P jm bl jm',
     free_list_juicy_mem jm bl jm' ->
     app_pred (freeable_blocks bl * P) (m_phi jm) ->
     app_pred P (m_phi jm').
Proof.
 intros.
 revert H0; induction H; simpl freeable_blocks.
 intros.  rewrite emp_sepcon in H0; auto.
 rename H0 into H99. rename H1 into H0; rename H2 into H1.
 intro.
 rewrite sepcon_assoc in H2.
 generalize H2; intro H2'.
 destruct H2 as [phi1 [phi2 [? [? ?]]]].
 apply IHfree_list_juicy_mem.
 pose proof  (@juicy_free_lemma' jm b lo hi _ phi1 _ _ H H2' H3 H2).
 match type of H5 with m_phi ?A = _ => set (jm3 := A) in H5 end.
 replace jm2 with jm3 by (subst jm3; rewrite <- H0; apply free_juicy_mem_ext; auto).
 subst; auto.
Qed.

Lemma xelements_app:
 forall A (rho: PTree.t A) i al bl,
    PTree.xelements rho i al ++ bl = PTree.xelements rho i (al++bl).
Proof.
 induction rho; simpl; intros; auto.
 destruct o; simpl.
 rewrite IHrho1. simpl. rewrite IHrho2; auto.
 rewrite IHrho1. simpl. rewrite IHrho2; auto.
Qed.

Lemma PTree_elements_remove: forall {A} (T: PTree.tree A) i e,
  In e (PTree.elements (PTree.remove i T)) ->
  In e (PTree.elements T) /\ fst e <> i.
Proof.
  intros.
  destruct e as [i0 v0].
  apply PTree.elements_complete in H.
  destruct (peq i0 i).
  + subst.
    rewrite PTree.grs in H.
    inversion H.
  + rewrite PTree.gro in H by auto.
    split; [| simpl; auto].
    apply PTree.elements_correct.
    auto.
Qed.

Lemma stackframe_of_freeable_blocks {CS}:
  forall Delta f rho ge ve,
      cenv_sub (@cenv_cs CS) (genv_cenv ge) ->
      Forall (fun it => complete_type cenv_cs (snd it) = true) (fn_vars f) ->
      list_norepet (map fst (fn_vars f)) ->
      ve_of rho = make_venv ve ->
      guard_environ (func_tycontext' f Delta) f rho ->
       stackframe_of f rho |-- freeable_blocks (blocks_of_env ge ve).
Proof.
  intros until ve.
  intros HGG COMPLETE.
 intros.
 destruct H1. destruct H2 as [H7 _].
 unfold stackframe_of.
 unfold func_tycontext' in H1.
 unfold typecheck_environ in H1.
 destruct H1 as [_ [?  _]].
 rewrite H0 in H1.
 unfold make_venv in H1.
 unfold var_types in H1.
 simpl in H1. unfold make_tycontext_v in H1.
 unfold blocks_of_env.
match goal with |- ?A |-- _ =>
 replace A
  with (fold_right (@sepcon _ _ _ _ _) emp
            (map (fun idt : ident * type => var_block Share.top idt rho)
            (fn_vars f)))
end.
 2: clear; induction (fn_vars f); simpl; f_equal; auto.
 unfold var_block. unfold eval_lvar. simpl.
  rewrite H0. unfold make_venv. forget (ge_of rho) as ZZ. rewrite H0 in H7; clear rho H0.
 revert ve H1 H7; induction (fn_vars f); simpl; intros.
 case_eq (PTree.elements ve); simpl; intros; auto.
 destruct p as [id ?].
 pose proof (PTree.elements_complete ve id p). rewrite H0 in H2. simpl in H2.
 specialize (H7 id). unfold make_venv in H7. rewrite H2 in H7; auto.
 destruct p; inv H7.
 inv H.
 destruct a as [id ty]. simpl in *.
 simpl in COMPLETE. inversion COMPLETE; subst.
 clear COMPLETE; rename H5 into COMPLETE; rename H2 into COMPLETE_HD.
 specialize (IHl COMPLETE H4 (PTree.remove id ve)).
 assert (exists b, ve ! id = Some (b,ty)). {
  specialize (H1 id ty).
  rewrite PTree.gss in H1. destruct H1 as [[b ?] _]; auto. exists b; apply H.
 }
 destruct H as [b H].
 destruct (@PTree.elements_remove _ id (b,ty) ve H) as [l1 [l2 [? ?]]].
 rewrite H0.
 rewrite map_app. simpl map.
 apply derives_trans with (freeable_blocks ((b,0,@sizeof ge ty) ::  (map (block_of_binding ge) (l1 ++ l2)))).
 2:{
   clear.
   induction l1; simpl; try auto.
   destruct a as [id' [hi lo]]. simpl. rewrite <- sepcon_assoc. 
   rewrite (sepcon_comm (VALspec_range (@sizeof ge ty - 0) Share.top (b, 0))).
   rewrite sepcon_assoc. apply sepcon_derives; auto.
 }
 unfold freeable_blocks; simpl. rewrite <- H2.
 apply sepcon_derives.
 unfold Map.get. rewrite H. rewrite eqb_type_refl.
 unfold memory_block. normalize. {
  rename H6 into H99.
 normalize. (* don't know why we cannot do normalize at first *)
 rewrite memory_block'_eq.
 2: rewrite Ptrofs.unsigned_zero; omega.
 2:{
 rewrite Ptrofs.unsigned_zero. rewrite Zplus_0_r.
 rewrite Z2Nat.id.
 change (Ptrofs.unsigned Ptrofs.zero) with 0 in H99.
 omega.
 pose proof (sizeof_pos ty); omega.
}
 rewrite Z.sub_0_r.
 unfold memory_block'_alt.
 rewrite if_true by apply readable_share_top.
 rewrite Z2Nat.id.
 + rewrite (cenv_sub_sizeof HGG); auto.
 + pose proof (sizeof_pos ty); omega.
}
 eapply derives_trans; [ | apply IHl]; clear IHl.
 clear - H3.
 induction l; simpl; auto.
 destruct a as [id' ty']. simpl in *.
 apply sepcon_derives; auto.
 replace (Map.get (fun id0 : positive => (PTree.remove id ve) ! id0) id')
   with (Map.get (fun id0 : positive => ve ! id0) id'); auto.
 unfold Map.get.
 rewrite PTree.gro; auto.
 intros id' ty'; specialize (H1 id' ty').
 {split; intro.
 - destruct H1 as [H1 _].
   assert (id<>id').
   intro; subst id'.
   clear - H3 H5; induction l; simpl in *. rewrite PTree.gempty in H5; inv H5.
   destruct a; simpl in *.
   rewrite PTree.gso in H5. auto. auto.
   destruct H1 as [v ?].
   rewrite PTree.gso; auto.
   exists v. unfold Map.get. rewrite PTree.gro; auto.
 - unfold Map.get in H1,H5.
   assert (id<>id').
     clear - H5; destruct H5. intro; subst. rewrite PTree.grs in H. inv H.
   rewrite PTree.gro in H5 by auto.
   rewrite <- H1 in H5. rewrite PTree.gso in H5 by auto. auto.
 }
 hnf; intros.
 destruct (make_venv (PTree.remove id ve) id0) eqn:H5; auto.
 destruct p.
 unfold make_venv in H5.
 destruct (peq id id0).
 subst.  rewrite PTree.grs in H5. inv H5.
 rewrite PTree.gro in H5 by auto.
 specialize (H7 id0). unfold make_venv in H7. rewrite H5 in H7.
 destruct H7; auto. inv H6; congruence.
Qed.

Definition maybe_retval (Q: environ -> mpred) retty ret :=
 match ret with
 | Some id => fun rho => Q (get_result1 id rho)
 | None =>
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => EX v: val, Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end.

Lemma VALspec_range_free:
  forall n b phi1 jm,
  app_pred (VALspec_range n Share.top (b, 0)) phi1 ->
  join_sub phi1 (m_phi jm) ->
  {m' | free (m_dry jm) b 0 n = Some m' }.
Proof.
intros.
apply range_perm_free.
destruct H0 as [phi2 H0].
hnf; intros.
pose proof (juicy_mem_access jm (b,ofs)).
hnf. unfold access_at in H2. simpl in H2.
destruct H as [H _]; specialize (H (b,ofs)).
hnf in H.
rewrite if_true in H by (split; auto; omega).
destruct H as [v ?].
apply (resource_at_join _ _ _ (b,ofs)) in  H0.
destruct H.
hnf in H.
rewrite H in H0.
rewrite H2.
inv H0; simpl; apply join_top in RJ; subst sh3; rewrite perm_of_freeable; constructor.
Qed.

Lemma Forall_filter: forall {A} P (l: list A) f, Forall P l -> Forall P (filter f l).
Proof.
  intros.
  induction l.
  + constructor.
  + inversion H; subst.
    apply IHl in H3.
    simpl.
    simple_if_tac.
    - constructor; auto.
    - auto.
Qed.

Lemma can_free_list {CS}:
  forall Delta F f jm ge ve te
  (NOREP: list_norepet (map (@fst _ _) (fn_vars f)))
  (COMPLETE: Forall (fun it => complete_type cenv_cs (snd it) = true) (fn_vars f))
  (HGG: cenv_sub (@cenv_cs CS) (genv_cenv ge)),
   guard_environ (func_tycontext' f Delta) f
        (construct_rho (filter_genv ge) ve te) ->
    (F * stackframe_of f (construct_rho (filter_genv ge)ve te))%pred (m_phi jm) ->
   exists m2, free_list (m_dry jm) (blocks_of_env ge ve) = Some m2.
Proof.
  intros.
  destruct H0 as [? [? [? [_ ?]]]].
  unfold stackframe_of in H1.
  unfold blocks_of_env in *.
  destruct H as [_ [H _]]; clear - NOREP COMPLETE HGG H H0 H1. simpl in H.
  pose (F vl := (fold_right
          (fun (P Q : environ -> pred rmap) (rho : environ) => P rho * Q rho)
          (fun _ : environ => emp)
          (map (fun idt : ident * type => var_block Share.top idt) vl))).
  change ((F (fn_vars f)  (construct_rho (filter_genv ge) ve te)) x0) in H1.
  assert (forall id b t, In (id,(b,t)) (PTree.elements ve) ->
                In (id,t) (fn_vars f)). {
   intros.
    apply PTree.elements_complete in  H2.
    specialize (H id); unfold make_venv in H; rewrite H2 in H.
     apply H.
  }
  clear H.
  assert (Hve: forall i bt, In (i,bt) (PTree.elements ve) -> ve ! i = Some bt)
    by apply PTree.elements_complete.
  assert (NOREPe: list_norepet (map (@fst _ _) (PTree.elements ve)))
    by apply PTree.elements_keys_norepet.
  forget (PTree.elements ve) as el.
  rename x0 into phi.
  assert (join_sub phi (m_phi jm)).
  econstructor; eauto.
  clear H0.
  forget (fn_vars f) as vl.
  revert vl phi jm H H1 H2 Hve NOREP NOREPe COMPLETE; induction el; intros;
    [ solve [simpl; eauto] | ].
  simpl in H2.
  destruct a as [id [b t]]. simpl in NOREPe,H2|-*.
  assert (H2': In (id,t) vl) by (apply H2 with b; auto).
  specialize (IHel (filter (fun idt => negb (eqb_ident (fst idt) id)) vl)).
  replace (F vl (construct_rho (filter_genv ge) ve te))
    with  (var_block Share.top (id,t) (construct_rho (filter_genv ge) ve te)
    * F (filter (fun idt => negb (eqb_ident (fst idt) id)) vl) (construct_rho (filter_genv ge) ve te)) in H1.
  2:{
    clear - H2' NOREP.
    induction vl; inv H2'.
    simpl in NOREP.
    inv NOREP.
    unfold F; simpl fold_right.
    f_equal.
    f_equal.
    f_equal.
    replace (eqb_ident id id) with true
      by (symmetry; apply (eqb_ident_spec id id); auto).
    simpl.
    clear - H1.
    induction vl; simpl; auto.
    replace (negb (eqb_ident (fst a) id)) with true.
    f_equal.
    apply IHvl.
    contradict H1. right; auto.
    pose proof (eqb_ident_spec (fst a) id).
    destruct (eqb_ident (fst a) id) eqn:?; auto.
    elimtype False; apply H1. left. rewrite <- H; auto.
    transitivity
     (var_block Share.top a (construct_rho (filter_genv ge) ve te) *
         F vl (construct_rho (filter_genv ge) ve te)); [ | reflexivity].
    inv NOREP.
    rewrite <- IHvl; auto.
    repeat rewrite <- sepcon_assoc.
    simpl filter.
    replace (eqb_ident (fst a) id) with false.
    simpl.
    unfold F at 1.
    simpl.
    symmetry;
    rewrite (sepcon_comm (var_block _ _ _ )).
    repeat rewrite sepcon_assoc.
    reflexivity.
    pose proof (eqb_ident_spec (fst a) id).
    destruct (eqb_ident (fst a) id); auto.
    assert (fst a = id) by (apply H0; auto).
    subst id.
    contradiction H2.
    replace (fst a) with (fst (fst a, t)) by reflexivity.
    apply in_map; auto.
  }
  pose (H0:=True).
  destruct H1 as [phi1 [phi2 [? [? ?]]]].
  unfold var_block in H3.
  normalize in H3.
  simpl in H3.
  assert (0 <= sizeof t) by (pose proof (sizeof_pos t); omega).
  simpl in H5.
  unfold eval_lvar, Map.get in H3. simpl in H3.
  unfold make_venv in H3.
  rewrite (Hve id (b,t)) in H3 by (left; auto).
  rewrite eqb_type_refl in H3.
  simpl in H3; destruct H3 as [H99 H3].
  rewrite memory_block'_eq in H3;
  try rewrite Ptrofs.unsigned_zero; try omega.
  2:{
   rewrite Z.add_0_r; rewrite Z2Nat.id by omega. change (Ptrofs.unsigned Ptrofs.zero) with 0 in H99; omega.
  }
  unfold memory_block'_alt in H3.
  rewrite Ptrofs.unsigned_zero in H3.
  rewrite Z2Nat.id in H3 by omega.
  rewrite if_true in H3 by apply readable_share_top.
  assert (join_sub phi1 (m_phi jm)) as H7
   by ( apply join_sub_trans with phi; auto; eexists; eauto).
  destruct (VALspec_range_free _ _ _ _ H3 H7)
   as [m3 ?H].
  assert (VR: app_pred (VALspec_range (sizeof t-0) Share.top (b, 0) * TT) (m_phi jm)).
    clear - H3 H7. destruct H7.
  rewrite Z.sub_0_r; exists phi1; exists x; split3; auto.
  pose (jm3 := free_juicy_mem _ _ _ _ _ H8 ).
  destruct H as [phix H].
  destruct (join_assoc H1 H) as [phi3 []].
  assert (phi3 = m_phi jm3).
  { subst jm3; symmetry; eapply juicy_free_lemma'; eauto.
    rewrite Z.sub_0_r; auto.
  }
  subst phi3.  assert (join_sub phi2 (m_phi jm3)) as Hphi2 by (eexists; eauto).
  destruct (IHel phi2 jm3 Hphi2) as [m4 ?]; auto; clear IHel.
  + intros.
    specialize (H2 id0 b0 t0).
    spec H2; [ auto |].
    assert (id0 <> id).
    {
      clear - NOREPe H11.
      inv NOREPe. intro; subst.
      apply H1. change id with (fst (id,(b0,t0))); apply in_map; auto.
    }
    clear - H2 H12.
    induction vl; simpl in *; auto.
    destruct H2. subst a. simpl.
    replace (eqb_ident id0 id) with false; simpl; auto.
    pose proof (eqb_ident_spec id0 id); destruct (eqb_ident id0 id); simpl in *; auto.
    contradiction H12; apply H; auto.
    pose proof (eqb_ident_spec (fst a) id); destruct (eqb_ident (fst a) id); simpl in *; auto.
  + intros; eapply Hve; eauto.
    right; auto.
  + clear - NOREP.
    induction vl; simpl; auto.
    pose proof (eqb_ident_spec (fst a) id); destruct (eqb_ident (fst a) id); simpl in *; auto.
    assert (fst a = id) by ( apply H; auto); subst.
    apply IHvl; inv NOREP; auto.
    inv NOREP.
    constructor; auto.
    clear - H2.
    contradict H2.
    induction vl; simpl in *; auto.
    destruct (eqb_ident (fst a0) id); simpl in *; auto.
    destruct H2; auto.
  + inv NOREPe; auto.
  + apply Forall_filter; auto.
  + pose proof (proj1 (Forall_forall _ _) COMPLETE (id, t) H2').
    simpl in H11.
    exists m4.
    rewrite (cenv_sub_sizeof HGG), H8; auto.
Qed.

Lemma age_juicy_mem_i:
  forall jm jm', m_dry jm = m_dry jm' ->
        age (m_phi jm) (m_phi jm') ->
       age jm jm'.
Proof.
intros.
hnf in H0 |-*.
unfold age1; simpl.
apply age1_juicy_mem_unpack'; auto.
Qed.

Lemma free_juicy_mem_resource_decay:
  forall jm b lo hi m' jm'
     (H : free (m_dry jm) b lo hi = Some m')
     (H0 : forall ofs : Z,  lo <= ofs < hi ->
             perm_of_res (m_phi jm @ (b, ofs)) = Some Freeable),
    free_juicy_mem jm m' b lo hi H = jm' ->
    resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
intros.
 subst jm'. simpl.
 apply (inflate_free_resource_decay _ _ _ _ _ H H0).
Qed.

Lemma free_list_resource_decay:
  forall bl jm jm',
  free_list_juicy_mem jm bl jm' ->
  resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
induction 1; intros.
apply resource_decay_refl; intros.
apply (juicy_mem_alloc_cohere jm l H).
apply resource_decay_trans with (nextblock (m_dry jm)) (m_phi jm2).
apply Pos.le_refl.
eapply free_juicy_mem_resource_decay; eauto.
rewrite <- (nextblock_free _ _ _ _ _ H).
apply IHfree_list_juicy_mem.
Qed.

Definition tc_fn_return (Delta: tycontext) (ret: option ident) (t: type) :=
 match ret with
 | None => True
 | Some i => match (temp_types Delta) ! i with Some t' => t=t' | _ => False end
 end.

Lemma derives_refl' {A: Type}  `{ageable A}:
    forall P Q: pred A, P=Q -> P |-- Q.
Proof.  intros; subst; apply derives_refl. Qed.

 Lemma free_juicy_mem_core:
  forall jm m b lo hi H
   (H0 : forall ofs : Z,
     lo <= ofs < hi -> perm_of_res (m_phi jm @ (b, ofs)) = Some Freeable),
   core (m_phi (free_juicy_mem jm m b lo hi H)) = core (m_phi jm).
Proof.
 intros.
 apply rmap_ext.
 do 2  rewrite level_core.
 apply free_juicy_mem_level.
 intros.
 repeat rewrite <- core_resource_at.
 simpl. unfold inflate_free; simpl;  rewrite resource_at_make_rmap.
 destruct (m_phi jm @ l) eqn:?; auto.
 if_tac; rewrite !core_NO; auto.
 if_tac. rewrite core_YES, core_NO; auto. rewrite !core_YES; auto.
 if_tac; auto.
 destruct l; destruct H1; subst. specialize (H0 z).
 spec H0; [omega | ]. rewrite Heqr in H0. inv H0.
 rewrite !ghost_of_core, free_juicy_mem_ghost; auto.
Qed.

Lemma same_glob_funassert':
  forall Delta1 Delta2 rho rho',
     (forall id, (glob_specs Delta1) ! id = (glob_specs Delta2) ! id) ->
      ge_of rho = ge_of rho' ->
              funassert Delta1 rho = funassert Delta2 rho'.
Proof.
assert (forall Delta Delta' rho rho',
             (forall id, (glob_specs Delta) ! id = (glob_specs Delta') ! id) ->
             ge_of rho = ge_of rho' ->
             funassert Delta rho |-- funassert Delta' rho').
+ intros.
  unfold funassert.
  intros w [? ?]; split.
  - clear H2; intro id. rewrite <- (H id), <- H0; auto.
  - intros loc sig cc w' Hw' H4; destruct (H2 loc sig cc w' Hw' H4)  as [id H3].
    exists id; rewrite <- (H id), <- H0; auto.
+ intros.
  apply pred_ext; apply H; intros; auto.
Qed.

Definition thisvar (ret: option ident) (i : ident) : Prop :=
 match ret with None => False | Some x => x=i end.

Lemma closed_wrt_modvars_Scall:
  forall ret a bl, closed_wrt_modvars (Scall ret a bl) = closed_wrt_vars (thisvar ret).
Proof.
intros.
unfold closed_wrt_modvars.
extensionality F.
f_equal.
 extensionality i; unfold modifiedvars; simpl.
 unfold isSome, idset0, insert_idset; destruct ret; simpl; auto.
 destruct (ident_eq i0 i).
 subst. rewrite PTree.gss. apply prop_ext; split; auto.
 rewrite PTree.gso by auto. rewrite PTree.gempty.
 apply prop_ext; split ;intro; try contradiction.
 rewrite PTree.gempty. auto.
Qed.

Lemma semax_call_external: forall 
 (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
 (A : TypeTree) 
 (P Q : forall ts : list Type,  (dependent_type_functor_rec ts (AssertTT A)) mpred)
 (NEP : super_non_expansive P) (NEQ' : super_non_expansive Q)
 (ts : list Type)
 (x : (dependent_type_functor_rec ts A) mpred)
 (F : environ -> pred rmap) (F0 : assert)
 (ret : option ident) (curf : function) (fsig : funsig) (cc : calling_convention)
 (R : ret_assert) (psi : genv) (vx : env) (tx : temp_env) 
 (k : cont) (rho : environ) (ora : OK_ty) (b : block) (jm : juicy_mem)
 (Hora : (ext_compat ora) (m_phi jm)) 
 (TCret : tc_fn_return Delta ret (snd fsig)) 
 (TC3 : guard_environ Delta curf rho)
 (TC5 : snd fsig = Tvoid -> ret = None)
 (H : closed_wrt_vars (thisvar ret) F0)
 (HGG : cenv_sub cenv_cs psi) 
 (H0 : rho = construct_rho (filter_genv psi) vx tx) 
 (H1 : (rguard Espec psi Delta curf (frame_ret_assert R F0) k) (level (m_phi jm)))
 (H4 : (funassert Delta rho) (m_phi jm)) 
 (Prog_OK : (believe Espec Delta psi Delta) (level jm)) 
 (args : list val) 
 (H14 : (F0 rho * F rho *
              P ts x (make_args (map fst (fst fsig)) args rho))%pred
              (m_phi jm))
 (H5 : (believe_external Espec psi (Vptr b Ptrofs.zero) fsig cc A P Q) (S (level jm)))
 (ff : fundef)
 (H16 : Genv.find_funct psi (Vptr b Ptrofs.zero) = Some ff)
 (H16' : type_of_fundef ff =
       Tfunction (type_of_params (fst fsig)) (snd fsig) cc)
 (TC8 : tc_vals (snd (split (fst fsig))) args)
 (Hargs : Datatypes.length (fst fsig) = Datatypes.length args),
 let ctl := Kcall ret curf vx tx k : cont in
 forall (HR : (ALL rho' : environ,
      |> ! ((EX old : val,
             substopt ret old F rho' *
             maybe_retval (Q ts x) (snd fsig) ret rho') >=>
            RA_normal R rho')) (m_phi jm)),
 jsafeN OK_spec psi (level jm) ora (Callstate ff args ctl) jm.
Proof.
intros.
destruct TC3 as [TC3 TC3'].
rename H5 into H15.
unfold believe_external in H15.
rewrite H16 in H15.
destruct ff; try contradiction H15.

destruct H15 as [[H5 H15] Hretty]. hnf in H5.
destruct H5 as [H5 [H5' [Eef Hlen]]]. subst c.
inversion H5. destruct fsig0 as [params retty].
injection H2; clear H2; intros H8 H7. subst t0.
rename t into tys. subst rho.
destruct (age1 jm) as  [jm' |] eqn:Hage.
2:{ Search age1 None level. rewrite (proj1 (age1_level0 jm) Hage). constructor. }
specialize (H15 psi ts x (level jm)).
spec H15. apply age_laterR. constructor. 
specialize (H15
  (F0 (construct_rho (filter_genv psi) vx tx) *
          F (construct_rho (filter_genv psi) vx tx))
   (typlist_of_typelist tys) args jm).
spec H15; [ clear; omega | ].
specialize (H15 _ (necR_refl _)).
spec H15. { clear H15.
assert (app_pred ((P ts x
      (make_args (map fst params) args (tycontext.empty_environ psi)) *
    (F0 (construct_rho (filter_genv psi) vx tx) *
     F (construct_rho (filter_genv psi) vx tx)))) (m_phi jm)). {
rewrite sepcon_comm.
eapply sepcon_derives; try apply H14; auto.
apply derives_refl'. f_equal.
simpl.
clear - H7 Hlen Hargs.
simpl in Hlen, Hargs.
rewrite fst_split in H7,Hlen.
revert args tys H7 Hlen Hargs; induction params; destruct args, tys; simpl; intros; auto; try discriminate.
f_equal.
eapply IHparams; eauto.
injection H7; auto.
}
simpl.
rewrite fst_split.
split.
{ (* typechecking arguments *)
  rewrite Eef; simpl.
  clear - TC8. simpl in TC8. rewrite snd_split in TC8.
  revert args TC8; induction params; destruct args; intros; try discriminate; auto.
  inv TC8.
  simpl in TC8. destruct TC8.
  destruct a. simpl in *. split; auto.
  apply tc_val_has_type; auto.
}
apply H0.
}
clear H14.
destruct H15 as [x' H15].
clear H5.
destruct H15 as [H5 H15].
specialize (H15 (opttyp_of_type retty)).
do 3 red in H15.

assert (Hty: type_of_params params = tys).
{ clear -H7 Hlen.
  rewrite H7. clear H7. revert tys Hlen. induction params.
  simpl. destruct tys; auto. inversion 1.
  intros; simpl. destruct a. case_eq (split params). intros l1 l2 Heq. simpl.
  destruct tys; auto. simpl. rewrite Heq in IHparams. rewrite IHparams; auto.
  simpl in Hlen|-*. rewrite Heq in Hlen. inv Hlen. rewrite Heq. auto. }
rewrite (age_level _ _ Hage).
eapply jsafeN_external with (x0 := x'); eauto.
reflexivity.
rewrite Eef. subst tys. apply H5; auto.
assert (H2 := I). assert (H3 := I).
intros.
specialize (H15 ret0 z').
change ((ext_spec_post' Espec e x' (genv_symb_injective psi) (opttyp_of_type retty) ret0 z' >=>
        juicy_mem_op
          (Q ts x (make_ext_rval  (filter_genv psi) ret0) *
              (F0 (construct_rho (filter_genv psi) vx tx) *
               F (construct_rho (filter_genv psi) vx tx)))) (level jm)) in H15.
apply (pred_nec_hereditary _ _ (level m')) in H15.
 2:{ clear - H6. destruct H6 as [? [? ?]]. apply nec_nat. omega. }
apply (pred_nec_hereditary _ _ (level m')) in H15;
 [ | apply nec_nat; omega].
rewrite Eef in *.
specialize (H15 m' (le_refl _) _ (necR_refl _) H8).

pose (tx' := match ret,ret0 with
                   | Some id, Some v => PTree.set id v tx
                   | _, _ => tx
                   end). 
assert (LAT: laterM (level (m_phi jm)) (level jm')). { simpl; apply laterR_level'. constructor. apply age_jm_phi. apply Hage. }
apply (pred_nec_hereditary _ _ _ (laterR_necR LAT)) in H1.

specialize (H1 EK_normal None tx' vx (m_phi m')).
assert (LATER: laterM (m_phi jm) (m_phi jm')). { clear - Hage. apply age_laterR. apply age1_juicy_mem_Some in Hage; trivial. }

spec H1.
{ clear - Hage H6.
  destruct H6 as [? [? ?]]. apply age_level in Hage.
  rewrite <- level_juice_level_phi. omega.
}
rewrite proj_frame_ret_assert in H1.
simpl proj_ret_assert in H1. hnf in H1. 

assert (H1' : forall a' : rmap,
     necR (m_phi m') a' ->
     (!! guard_environ Delta curf (construct_rho (filter_genv psi) vx tx') &&
      seplog.sepcon (fun rho0 => EX old:val, substopt ret old F rho0 * maybe_retval (Q ts x) retty ret rho0) F0 (construct_rho (filter_genv psi) vx tx') &&
      funassert Delta (construct_rho (filter_genv psi) vx tx')) a' ->
     (assert_safe Espec psi curf vx tx' (exit_cont EK_normal None k) (construct_rho (filter_genv psi) vx tx')) a').
{ intros a' NEC Ha'. apply (H1 _ NEC); clear H1.
  destruct Ha' as [HX HY].
  split; trivial. clear HY. destruct HX as [HA HB]. split; trivial. clear HA.
  destruct HB as [a1 [a2 [J [A1 A2]]]]. exists a1, a2; split; [trivial | split ;[| trivial]].
  destruct (nec_join4 _ _ _ _ J NEC) as [a1' [a2' [J' [NA1 NA2]]]].
  eapply HR; try eassumption.
  apply join_level in J'; destruct J' as [J' _]; rewrite J'.
  rewrite <- 2 level_juice_level_phi. destruct H6 as [? [? ?]]; subst. omega. } 
clear H1; rename H1' into H1. clear R HR.

simpl exit_cont in H1.
do 3 red in H5.
specialize (H1 _ (necR_refl _)).

assert (Htc: tc_option_val retty ret0).
{clear - TCret TC3 H0 TC5 H15 Hretty Hretty0 H6 Hage.
 destruct H15 as [phi1 [phi2 [Ha [Hb Hc]]]].
 specialize (Hretty ts x ret0 phi1).
 spec Hretty.
 { apply join_level in Ha. destruct Ha as [? ?].
   rewrite H. cut ((level jm > level jm')%nat). intros.
   simpl. unfold natLevel. do 2 rewrite <-level_juice_level_phi.
   destruct H6 as [? [? ?]].  omega.
   apply age_level in Hage. omega.
 }
 specialize (Hretty phi1).
 spec Hretty. apply rt_refl.
 spec Hretty. split. apply Hb. apply Hretty0.
 simpl in Hretty. auto.
}
spec H1. { clear H1.
split; [split; [split |] |].
*
 split.
 2:{
 clear - TC3.
 destruct TC3; simpl in *.
 destruct ret; try apply H0.
 }
 simpl.
 destruct TC3 as [TC3 _].
 destruct ret; try apply TC3. {
 clear - TCret TC3 H0 TC5 H15 Hretty Hretty0 H6 H8 Hage.
 simpl in TCret.
 destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
 subst retty.
 unfold tx' in *; clear tx'. simpl in TC3.
 assert (Hu: exists u, opttyp_of_type t = Some u).
 { clear - TC5; destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   try (eexists; reflexivity).
   spec TC5; [auto | congruence].
 }
 destruct Hu as [u Hu]. (*rewrite Hu in *.*) clear TC5.
 destruct H15 as [phi1 [phi2 [Ha [Hb Hc]]]].
 specialize (Hretty ts x ret0 phi1).
 spec Hretty.
 { apply join_level in Ha. destruct Ha as [? ?].
   rewrite H. cut ((level jm > level jm')%nat). intros.
   simpl. unfold natLevel. do 2 rewrite <-level_juice_level_phi. destruct H6; omega.
   apply age_level in Hage. omega.
 }
 specialize (Hretty phi1).
 spec Hretty. apply rt_refl. spec Hretty. split. apply Hb. apply Hretty0. simpl in Hretty.
 unfold typecheck_temp_environ. intros id ty Hty.
 destruct (ident_eq i id).
 + subst i.
 rewrite Heqo in Hty.
 destruct ret0; auto.
 inversion Hty. subst t. simpl.
 exists v. split. rewrite <-map_ptree_rel, Map.gss; auto.
 assert (ty <> Tvoid). { destruct ty; try inv Hu; intros C; congruence. }
 assert (tc_val ty v). { destruct ty; auto. }
 apply tc_val_tc_val'; auto.
 inversion Hty. subst t. simpl.
 assert (ty = Tvoid). { destruct ty; auto; inv Hretty. } subst ty.
 simpl in Hu. inv Hu.
 + destruct ret0.
 rewrite <-map_ptree_rel, Map.gso; auto.
 assert (t = Tvoid). { destruct t; auto; inv Hretty. } subst t.
 simpl in Hu. inv Hu.
}
*
 auto.
*
do 3 red in H15.
rewrite (sepcon_comm (F0 _)) in H15.
rewrite <- sepcon_assoc in H15.
assert (H15': ((!!tc_option_val retty ret0 && Q ts x (make_ext_rval (filter_genv psi) ret0)) *
       F (construct_rho (filter_genv psi) vx tx) *
       F0 (construct_rho (filter_genv psi) vx tx))%pred (m_phi m')). {
rewrite sepcon_assoc in H15|-*.
destruct H15 as [w1 [w2 [H1 [H10 H12]]]]; exists w1; exists w2; split3; auto.
clear - H1 H6 H10  Hage Hretty Hretty0.
specialize (Hretty ts x ret0 w1).
spec Hretty. {
 destruct H6 as [? [? ?]].
 repeat rewrite <- level_juice_level_phi.
 apply age_level in Hage. rewrite Hage.
 apply join_level in H1. destruct H1.
 rewrite H1.
 change (S (S (level jm')) >= level m')%nat.
 omega.
}
split.
apply Hretty; auto. split; auto.
auto.
}
clear H15.
revert Htc.
normalize in H15'.
do 2 red in H1.
intros Htc.
rewrite (sepcon_comm (Q _ _ _)) in H15'.
unfold seplog.sepcon, seplog.LiftSepLog .
rewrite <- exp_sepcon1.
eapply sepcon_derives; [apply sepcon_derives | | apply H15']; clear H15'.
+ (* F *)
  destruct TC3 as [TC3 _].
  hnf in TC3; simpl in TC3.
 hnf in TCret.
apply exp_right with
  match ret with
       | Some id =>
           match tx ! id with
           | Some old => old
           | None => Vundef
           end
       | None => Vundef
       end.
unfold substopt.
unfold tx' in *; clear tx'.
destruct ret; auto.
destruct ((temp_types Delta) ! i) as [ti|] eqn:H29; try contradiction.
specialize (TC3 _ _ H29).
destruct TC3 as [v [? ?]].
unfold subst.
apply derives_refl'.
f_equal.
unfold env_set, construct_rho.
simpl. f_equal.
unfold Map.set,Map.get, make_tenv in H9 |- *; rewrite H9.
destruct (type_eq retty Tvoid).
spec TC5; auto. inv TC5.
extensionality j.
if_tac. subst j. auto.
destruct ret0; auto.
rewrite PTree.gso; auto.
+ (* Q *)
destruct (type_eq retty Tvoid).
subst retty. unfold maybe_retval.
hnf in H1.
destruct ret0; try contradiction.
simpl make_ext_rval.
spec TC5; auto. unfold tx' in *; subst ret.
apply derives_refl.
destruct ret0; hnf in H1; simpl in H1.
assert (tc_val retty v).
destruct retty; try congruence; auto.
clear H1.
unfold maybe_retval.
destruct ret.
 apply derives_refl'; f_equal.
unfold tx'.
unfold make_ext_rval, get_result1; simpl.
unfold ret_temp, eval_id, env_set; simpl.
f_equal.
unfold Map.get, make_tenv; simpl.
rewrite PTree.gss; reflexivity.
apply derives_trans with
  (EX  v0 : val, Q ts x (make_args (ret_temp :: nil) (v0 :: nil) (construct_rho (filter_genv psi) vx tx'))).
apply exp_right with v.
unfold make_args, make_ext_rval; simpl.
unfold env_set, globals_only; simpl.
apply derives_refl.
destruct retty; try congruence.
repeat match goal with
| _ => destruct retty; try contradiction
| _ => congruence (* 8.5 *)
end.
+
clear - H.
apply derives_refl'; apply H; intros.
unfold tx'; clear.
unfold thisvar; simpl.
destruct ret; simpl; auto.
destruct (ident_eq i0 i).
subst; auto.
right.
unfold Map.get, make_tenv.
destruct ret0; auto.
rewrite PTree.gso by auto.
auto. 
*
assert (H4': (funassert Delta (construct_rho (filter_genv psi) vx tx)) (m_phi m')).
{ clear - H6 H4.
  destruct H6 as (?&?&?).
  destruct H4.
  split.
  * intros id fs ???.
    specialize (H2 id fs (m_phi jm) (necR_refl _)).    spec H2; auto.
    destruct H2 as [b [? ?]].
    destruct H1 as [H1 H1'].
    specialize (H1 (b,0)).
    unfold func_at in H6. destruct fs; simpl in *.
    rewrite H6 in H1.
    apply (necR_PURE (m_phi m') a') in H1; eauto.
    exists b. split; auto. rewrite H1. simpl.
    f_equal. f_equal.
    assert (Hlev1: (level (m_phi m') >= level a')%nat).
    { apply necR_level in H4; auto. }
    extensionality ts x.
    extensionality b0 rho.
    rewrite !fmap_app.
    match goal with
    | |- ?A (?B (?C ?D)) = _ => change (A (B (C D))) with ((A oo B oo C) D)
    end.
    rewrite approx_oo_approx' by omega.
    rewrite approx_oo_approx' by omega.
    rewrite approx'_oo_approx by omega.
    rewrite approx'_oo_approx by omega.
    auto.
  * intros b sig cc ???.
    specialize (H3 b sig cc (m_phi jm)).
    specialize (H3 (necR_refl _)); spec H3; auto.
    destruct H1 as [H1 H1'].
    specialize (H1' (b,0)).
    simpl in *.
    destruct H5 as [b0 ?].
    destruct (m_phi m' @ (b,0)) eqn:?.
    eapply necR_NOx in Heqr; try apply H4. inversion2 H5 Heqr.
    eapply necR_YES in Heqr; try apply H4. inversion2 H5 Heqr.
    destruct H1' as [pp ?].
    rewrite H6.
    exists pp.
    assert (H9 := necR_PURE _ _ _ _ _ H4 Heqr).
    rewrite H5 in H9. inv H9.
    f_equal.
    pose proof (resource_at_approx (m_phi jm) (b,0)).
    rewrite H6 in H; simpl in H.
    injection H; intro. symmetry in H7. apply H7.
  }
match type of H4' with ?A => match goal with |- ?B => replace B with A; auto end end.
}

exists (Returnstate (force_val ret0) (Kcall ret curf vx tx k)).
split.
unfold cl_after_external.
revert Htc TC5.
destruct (type_eq retty Tvoid).
+ subst retty. simpl. destruct ret0; try solve[inversion 1].
  intros _. intros X; spec X; auto.
+ intros Hret0.
  assert (Hv: exists v, ret0 = Some v).
  { revert Hret0.
    destruct retty; destruct ret0; simpl;
      try solve[intros _; eexists; eauto]; try inversion 1.
    exfalso; auto. }
  revert TCret.
  unfold tc_fn_return.
  destruct Hv as [v Hv]. rewrite Hv.
  destruct ret; auto.
+
destruct H6 as (?&?&?).
subst n'.
rewrite level_juice_level_phi.
change (jm_bupd z'
  (jsafeN OK_spec psi (level m') z'
     (Returnstate (force_val ret0) (Kcall ret curf vx tx k))) m').
replace tx' with (set_opttemp ret (force_val ret0) tx) in H1.
2:{ subst tx'.
  clear - Htc TCret TC5. hnf in Htc, TCret.
 destruct ret0, ret; simpl; auto.
 destruct ((temp_types Delta) ! i); try contradiction.
 destruct retty; try contradiction. spec TC5; auto. inv TC5.
}
clear tx'.
(* this proof is like assert_safe_jsafe *)
clear - H1.
repeat intro.
destruct (H1 _ H0) as (? & ? & ? & Hl & Hr & ? & Hsafe); subst.
simpl in Hsafe.
destruct (juicy_mem_resource _ _ Hr) as (jm' & ? & ?); subst.
exists jm'; repeat split; auto.
rewrite level_juice_level_phi, <- Hl.
hnf in Hsafe.
specialize (Hsafe z' jm').
spec Hsafe. {
    eapply joins_comm, join_sub_joins_trans, joins_comm, H2.
    destruct H.
    change (Some (ghost_PCM.ext_ref z', NoneP) :: nil) with
      (own.ghost_approx (m_phi m') (Some (ghost_PCM.ext_ref z', NoneP) :: nil)).
    eexists; apply ghost_fmap_join; eauto.
  }
  do 2 (spec Hsafe; [auto|]).
  destruct (gt_dec (level (m_phi jm')) O).
2:   replace (level (m_phi jm')) with O by omega; constructor.
  spec Hsafe; [auto |].
  destruct k; try contradiction.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
Qed.

Lemma alloc_juicy_variables_age:
  forall {ge rho jm jm1 vl rho' jm' jm1'},
   age jm jm1 -> age jm' jm1' ->
   alloc_juicy_variables ge rho jm vl = (rho', jm') ->
   alloc_juicy_variables ge rho jm1 vl = (rho', jm1').
Proof.
  intros.
  revert jm jm1 H rho H1.
  induction vl; intros.
  {
    simpl in *; inv H1.
    hnf in H0,H. congruence.
  }
  destruct a.
  simpl in H1|-*.
  eapply IHvl; [| rewrite <- (age_jm_dry H); eassumption].
  apply age_juicy_mem_i; [simpl; rewrite (age_jm_dry H); auto |].
  simpl.
  apply rmap_age_i.
  {
    unfold after_alloc; simpl. repeat rewrite level_make_rmap.
    apply age_level. apply age_jm_phi; auto.
  }
  intro. unfold resource_fmap; simpl.
  unfold after_alloc; simpl.
  do 2  rewrite resource_at_make_rmap.
  unfold after_alloc'.
  if_tac; [rewrite if_true | rewrite if_false].
  + f_equal.
  + rewrite <- (age_jm_dry H); assumption.
  + clear H1.
    destruct (m_phi jm @ l) eqn:?.
    - symmetry;  eapply necR_NOx; try apply Heqr.
      constructor 1. apply age_jm_phi; auto.
    - symmetry.
      rewrite level_make_rmap.
      eapply necR_YES. constructor 1. eapply age_jm_phi. eassumption.
      auto.
    - rewrite level_make_rmap.
      symmetry.
      eapply necR_PURE. constructor 1. eapply age_jm_phi. eassumption.  auto.
  + rewrite <- (age_jm_dry H); assumption.
  + unfold after_alloc; rewrite !ghost_of_make_rmap, level_make_rmap.
    symmetry; apply age1_ghost_of, age_jm_phi; auto.
Qed.

Lemma alloc_juicy_variables_resource_decay:
  forall ge rho jm vl rho' jm',
    alloc_juicy_variables ge rho jm vl = (rho', jm') ->
    resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
    (nextblock (m_dry jm) <= nextblock (m_dry jm'))%positive.
Proof.
 intros.
 revert rho jm H; induction vl; intros.
 inv H. split. apply resource_decay_refl.
   apply juicy_mem_alloc_cohere. apply Pos.le_refl.
 destruct a as [id ty].
 unfold alloc_juicy_variables in H; fold alloc_juicy_variables in H.
 revert H; case_eq (juicy_mem_alloc jm 0 (@sizeof ge ty)); intros jm1 b1 ? ?.
 pose proof (juicy_mem_alloc_succeeds _ _ _ _ _ H).
 specialize (IHvl _ _ H0).
 symmetry in H1; pose proof (nextblock_alloc _ _ _ _ _ H1).
 destruct IHvl.
 split; [ |  rewrite H2 in H4; xomega].
 eapply resource_decay_trans; try eassumption.
 rewrite H2; xomega.
 clear - H H1.
 pose proof (juicy_mem_alloc_level _ _ _ _ _ H).
 unfold resource_decay.
 split. repeat rewrite <- level_juice_level_phi; rewrite H0; auto.
 intro loc.
 split.
 apply juicy_mem_alloc_cohere.
 rewrite (juicy_mem_alloc_at _ _ _ _ _ H).
 rewrite Z.sub_0_r.
 destruct loc as [b z]. simpl in *.
 if_tac. destruct H2; subst b1.
 right. right. left. split. apply alloc_result in H1; subst b; xomega.
 eauto.
 rewrite <- H0. left. apply resource_at_approx.
Qed.

(*
bind_parameter_temps params args (create_undef_temps (fn_temps f)) = Some te' ->
alloc_juicy_variables psi empty_env jmx (fn_vars f) = (ve', jm'') ->
P ts x
  (make_args (map fst (fst fsig)) args (construct_rho (filter_genv psi) vx tx))
|-- close_precondition (map fst (fst fsig)) (map fst params) 
      (P ts x) (construct_rho (filter_genv psi) ve' te')
*)

Lemma ge_of_make_args:  
    forall s a rho, ge_of (make_args s a rho) = ge_of rho.
Proof.
induction s; intros.
 destruct a; auto.
 simpl in *. destruct a0; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

Lemma ve_of_make_args:  
    forall s a rho, length s = length a -> ve_of (make_args s a rho) = (Map.empty (block * type)).
Proof.
induction s; intros.
 destruct a; inv H; auto.
 simpl in *. destruct a0; inv H; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

Definition globals_only (rho: environ) : environ := (mkEnviron (ge_of rho) (Map.empty _) (Map.empty _)).

Fixpoint make_args' (il: list ident) (vl: list val)  : tenviron :=
  match il, vl with
  | i::il', v::vl' => Map.set i v (make_args' il' vl') 
  | _, _ => Map.empty _
  end.

Lemma make_args_eq:  forall il vl, length il = length vl ->
    forall rho,
    make_args il vl rho = mkEnviron (ge_of rho) (Map.empty _) (make_args' il vl).
Proof.
induction il; destruct vl; intros; inv H; simpl.
auto.
unfold env_set.
rewrite IHil; auto.
Qed.

Lemma make_args_close_precondition:
  forall specparams bodyparams args ge ve te m tx ve' te' m' P vars,
    length specparams = length bodyparams ->
    list_norepet specparams ->
    list_norepet (map fst bodyparams) ->
    bind_parameter_temps bodyparams args tx = Some te' ->
    alloc_juicy_variables ge empty_env m vars = (ve', m') ->
    P (make_args specparams args (construct_rho (filter_genv ge) ve te))
   |-- close_precondition specparams (map fst bodyparams) P
           (construct_rho (filter_genv ge) ve' te').
Proof.
intros *. intros Hlen Hno. intros.
intros phi ?.
exists (Map.empty (block * type)).
pose (f := fix f (s b: list ident) :=
          match s,b with
          | s1::sr, b1::br => PTree.set s1 (force_val (te' ! b1)) (f sr br)
          | _, _ => empty_tenv
           end).
pose (e := f specparams (map fst bodyparams) : temp_env).
exists (fun i => e!i).
split; intros.
*
unfold Map.get.
simpl.
unfold make_tenv.
subst e.
clear - Hno H0 H3 H4.
rename specparams into s.
forget bodyparams as b.
revert args tx s b Hno H0 H3 H4; induction n; intros.
destruct s; inv H3. destruct b; inv H4. simpl in H0. destruct p, args. inv H0.
simpl. rewrite PTree.gss.
clear - H0. {
  assert ((PTree.set i0 v tx) ! i0 <> None).
  rewrite PTree.gss. congruence.
  forget (PTree.set i0 v tx) as te.
  revert args te te' H H0; induction b as [|[??]]; intros; destruct args; inv H0; auto.
  destruct (te' ! i0); try contradiction; auto.
   apply IHb in H2; auto.
  destruct (ident_eq i0 i). subst. rewrite PTree.gss. clear; congruence.
  rewrite PTree.gso; auto.
}
destruct s; inv H3. destruct b; inv H4.
inv Hno.
simpl.
destruct p.
destruct args; inv H0.
simpl.
rewrite PTree.gso.
eapply IHn; eauto.
contradict H4.
subst i0.
clear - H1.
eapply nth_error_In; eauto.
*
 simpl.
 replace (mkEnviron (filter_genv ge) (Map.empty (block * type)) (fun i : positive => e ! i))
   with  (make_args specparams args (construct_rho (filter_genv ge) ve te)); auto.
 clear - Hlen Hno H H0.
 rewrite make_args_eq.
2:{ rewrite Hlen. clear - H0.
    revert args tx H0; induction bodyparams as [|[??]]; intros; destruct args; inv H0; simpl; auto.
    f_equal; eauto.
 }
  f_equal.
  subst e.  
  assert (length bodyparams = length args). {
   clear - H0.
   revert tx te' args H0; induction bodyparams as [|[??]]; intros; destruct args;inv H0; simpl; f_equal; eauto.
  }
  revert bodyparams args tx H0 H H1 Hno Hlen; induction specparams; intros.
  destruct bodyparams; inv Hlen.
  destruct args; inv H1.
  extensionality j.
  simpl. unfold empty_tenv.
  rewrite PTree.gempty.
  reflexivity.
  destruct bodyparams as [|[? ?]]; inv Hlen.
  destruct args; inv H1.
  inv Hno. inv H.
  simpl. 
  simpl in H0.
   rewrite (IHspecparams bodyparams args (PTree.set i v tx)) by auto.
  extensionality j.
  unfold Map.set. if_tac. subst a. rewrite PTree.gss.
   clear - H0 H7.
  assert ((PTree.set i v tx) ! i = Some v).
  apply PTree.gss.
  forget (PTree.set i v tx) as te.
  revert args te H H0 H7; induction bodyparams as [|[??]]; intros; destruct args; inv H0.
  rewrite H. auto.
  apply IHbodyparams in H2; auto.
  rewrite PTree.gso; auto.
   contradict H7. left; auto.
  contradict H7. right; auto.
  rewrite PTree.gso; auto.
Qed.

Lemma juicy_mem_alloc_block:
 forall jm n jm2 b F,
   juicy_mem_alloc jm 0 n = (jm2, b) ->
   app_pred F (m_phi jm)  ->
   0 <= n < Ptrofs.modulus ->
   app_pred (F * memory_block Share.top n (Vptr b Ptrofs.zero)) (m_phi jm2).
Proof.
intros. rename H1 into Hn.
inv H.
unfold after_alloc; simpl m_phi.
match goal with |- context [proj1_sig ?A] => destruct A; simpl proj1_sig end.
rename x into phi2.
destruct a as (? & ? & Hg).
unfold after_alloc' in H1.
destruct (allocate (m_phi jm)
    (fun loc : address =>
      if adr_range_dec (snd (alloc (m_dry jm) 0 n), 0) (n - 0) loc
      then YES Share.top readable_share_top (VAL Undef) NoneP
      else core (m_phi jm @ loc)) (core (ghost_of phi2)))
  as [phi3 [phi4  [? [? Hg']]]].
* extensionality loc; unfold compose.
  if_tac. unfold resource_fmap. rewrite preds_fmap_NoneP. reflexivity.
  repeat rewrite core_resource_at.
  rewrite <- level_core.
  apply resource_at_approx.
*
 intros.
 simpl; if_tac.
 exists (YES Share.top readable_share_top (VAL Undef) NoneP).
 destruct l as [b ofs]; destruct H2.
 rewrite juicy_mem_alloc_cohere. constructor.
 apply join_unit1; auto.
 destruct (alloc (m_dry jm) 0 n) eqn:?H.
 apply alloc_result in H4. subst. simpl.
 xomega.
 exists (m_phi jm @ l).
 apply join_comm.
 apply core_unit.
*
rewrite ghost_core; auto.
*
rewrite <- Hg; eexists; apply join_comm, core_unit.
*
assert (phi4 = phi2). {
 apply rmap_ext. apply join_level in H2. destruct H2; omega.
 intro loc; apply (resource_at_join _ _ _ loc) in H2.
 rewrite H3 in H2; rewrite H1.
 if_tac.
 inv H2; apply YES_ext; apply (join_top _ _ (join_comm RJ)).
 apply join_comm in H2.
 apply core_identity in H2. auto.
 apply ghost_of_join in H2.
 rewrite Hg' in H2.
 apply join_comm, core_identity in H2; congruence.
}
subst phi4.
exists (m_phi jm), phi3; split3; auto.
split.
do 3 red.
rewrite Ptrofs.unsigned_zero.
omega.
rewrite Ptrofs.unsigned_zero.
rewrite memory_block'_eq; try omega.
2: rewrite Z2Nat.id; omega.
unfold memory_block'_alt.
rewrite if_true by apply readable_share_top.
split.
intro loc. hnf.
rewrite Z2Nat.id by omega.
if_tac.
exists Undef.
exists readable_share_top.
hnf.
rewrite H3.
rewrite Z.sub_0_r.
rewrite if_true by auto.
rewrite preds_fmap_NoneP.
f_equal.
unfold noat. simpl.
rewrite H3.
rewrite Z.sub_0_r.
rewrite if_false by auto.
apply core_identity.
simpl; rewrite Hg'; apply core_identity.
Qed.

Lemma alloc_juicy_variables_lem2 {CS}:
  forall jm f (ge: genv) ve te jm' (F: pred rmap)
      (HGG: cenv_sub (@cenv_cs CS) (genv_cenv ge))
      (COMPLETE: Forall (fun it => complete_type cenv_cs (snd it) = true) (fn_vars f))
      (Hsize: Forall (fun var => @sizeof ge (snd var) <= Ptrofs.max_unsigned) (fn_vars f)),
      list_norepet (map fst (fn_vars f)) ->
      alloc_juicy_variables ge empty_env jm (fn_vars f) = (ve, jm') ->
      app_pred F (m_phi jm) ->
      app_pred (F * stackframe_of f (construct_rho (filter_genv ge) ve te)) (m_phi jm').
Proof.
intros.
unfold stackframe_of.
forget (fn_vars f) as vars. clear f.
forget empty_env as ve0.
revert F ve0 jm Hsize H0 H1; induction vars; intros.
simpl in H0. inv H0.
simpl fold_right. rewrite sepcon_emp; auto.
inv Hsize. rename H4 into Hsize'; rename H5 into Hsize.
simpl fold_right.
unfold alloc_juicy_variables in H0; fold alloc_juicy_variables in H0.
destruct a as [id ty].
destruct (juicy_mem_alloc jm 0 (@sizeof ge ty)) eqn:?H.
rewrite <- sepcon_assoc.
inv H.
simpl in COMPLETE; inversion COMPLETE; subst.
rename H7 into COMPLETE'.
rename H4 into COMPLETE_HD.
eapply IHvars; eauto. clear IHvars.
pose proof I.
unfold var_block, eval_lvar.
simpl sizeof; simpl typeof.
simpl Map.get. simpl ge_of.
assert (Map.get (make_venv ve) id = Some (b,ty)). {
 clear - H0 H5.
 unfold Map.get, make_venv.
 assert ((PTree.set id (b,ty) ve0) ! id = Some (b,ty)) by (apply PTree.gss).
 forget (PTree.set id (b, ty) ve0) as ve1.
 rewrite <- H; clear H.
 revert ve1 j H0 H5; induction vars; intros.
 inv H0; auto.
 unfold alloc_juicy_variables in H0; fold alloc_juicy_variables in H0.
 destruct a as [id' ty'].
 destruct (juicy_mem_alloc j 0 (@sizeof ge ty')) eqn:?H.
 rewrite (IHvars _ _ H0).
 rewrite PTree.gso; auto. contradict H5. subst; left; auto.
 contradict H5; right; auto.
}
rewrite H3. rewrite eqb_type_refl.
simpl in Hsize'.
rewrite <- (cenv_sub_sizeof HGG); auto.
rewrite prop_true_andp by auto.
assert (0 <= @sizeof ge ty <= Ptrofs.max_unsigned) by (pose proof (@sizeof_pos ge ty); omega).
simpl.
forget (@sizeof ge ty) as n.
clear - H2 H1 H4.
eapply juicy_mem_alloc_block; eauto.
unfold Ptrofs.max_unsigned in H4; omega.
Qed.

Lemma free_list_juicy_mem_ghost: forall m l m', free_list_juicy_mem m l m' ->
  ghost_of (m_phi m') = ghost_of (m_phi m).
Proof.
  induction 1; auto.
  rewrite IHfree_list_juicy_mem, <- H1.
  apply free_juicy_mem_ghost.
Qed.

Lemma alloc_juicy_variables_ghost: forall l ge rho jm,
  ghost_of (m_phi (snd (alloc_juicy_variables ge rho jm l))) = ghost_of (m_phi jm).
Proof.
  induction l; auto; simpl; intros.
  destruct a; simpl.
  rewrite IHl; simpl.
  apply ghost_of_make_rmap.
Qed.

Lemma map_snd_typeof_params:
  forall al bl, map snd al = map snd bl -> type_of_params al = type_of_params bl.
Proof.
induction al as [|[? ?]]; destruct bl as [|[? ?]]; intros; inv H; simpl; f_equal; auto.
Qed.

Lemma jsafeN_local_step':
  forall {Espec: OracleKind} ge ora s1 m s2 m2,
  cl_step  ge s1 (m_dry m) s2 (m_dry m2) ->
  resource_decay (nextblock (m_dry m)) (m_phi m) (m_phi m2) ->
  level m = S (level m2) /\
   ghost_of (m_phi m2) =ghost_fmap (approx (level m2)) (approx (level m2)) (ghost_of (m_phi m)) ->
  jsafeN (@OK_spec Espec) ge (level m2) ora s2 m2 ->
  jsafeN (@OK_spec Espec) ge (level m) ora s1 m.
Proof.
intros.
  rename H into Hstep.
  remember (level m) as N.
  destruct N; [constructor|].
  eapply jsafeN_step with
    (m' := m2).
  split3.
  apply Hstep.
  auto.
  rewrite HeqN in H1; auto.
  apply jm_bupd_intro.
  destruct H1. inv H.
  apply H2.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Proof.
induction k; intros; simpl; auto.
Qed.

Lemma semax_call_aux2: 
 forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
  (A : TypeTree) 
  (P Q : forall ts : list Type,
     _functor (dependent_type_functor_rec ts (AssertTT A)) mpred)
  (ts : list Type)
  (x : _functor (dependent_type_functor_rec ts A) mpred) 
  (F : environ -> pred rmap)
  (F0 : assert)
  (ret : option ident)
  (curf : function)
  (fsig : funsig)
  (cc : calling_convention)
  (a : expr) (bl : list expr) (R : ret_assert) 
  (psi : genv) 
  (ora : OK_ty) (jm jmx : juicy_mem)
  (f : function)
  (NEP : super_non_expansive P)
  (NEQ : super_non_expansive Q)
  (Hora : app_pred (juicy_mem_op (ext_compat ora)) jm) 
  (TCret : tc_fn_return Delta ret (snd fsig))
  (TC5 : snd fsig = Tvoid -> ret = None)
  (H : closed_wrt_modvars (Scall ret a bl) F0)
  (HR : app_pred
       (ALL rho' : environ,
        |> ! ((EX old : val,
               substopt ret old F rho' *
               maybe_retval (Q ts x) (snd fsig) ret rho') >=> 
              RA_normal R rho')) (m_phi jm))
  (HGG : cenv_sub cenv_cs (genv_cenv psi))
  (H13 : age1 jm = Some jmx)
  (COMPLETE : Forall
             (fun it : ident * type => complete_type cenv_cs (snd it) = true)
             (fn_vars f))
  (H17 : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
  (H17' : list_norepet (map fst (fn_vars f)))
  (H18 : map snd (fst fsig) = map snd (fst (fn_funsig f)) /\
      snd fsig = snd (fn_funsig f) /\ list_norepet (map fst (fst fsig))),
forall vx tx k rho
  (H0 : rho = construct_rho (filter_genv psi) vx tx)
  (H1 : app_pred (|> rguard Espec psi Delta curf (frame_ret_assert R F0) k)
       (level (m_phi jm)))
  (TC3 : guard_environ Delta curf rho),
app_pred
  (!! closed_wrt_modvars (fn_body f) (fun _ : environ => F0 rho * F rho) &&
   rguard Espec psi (func_tycontext' f Delta) f
     (frame_ret_assert
        (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x))
           (stackframe_of' cenv_cs f)) (fun _ : environ => F0 rho * F rho))
     (Kcall ret curf vx tx k)) (level jmx).
Proof.
intros.
pose proof I.
assert (LATER : laterR (level (m_phi jm)) (level (m_phi jmx))). {
  apply laterR_level'. apply age_laterR. apply age_jm_phi. auto.
}
rename fsig0 into fsig.
set (ctl := Kcall ret curf vx tx k) in *.
do 2 pose proof I.
 split.
 repeat intro; f_equal.
 intros ek vl te ve.
 rewrite !proj_frame_ret_assert.
 unfold seplog.sepcon, seplog.LiftSepLog .
 remember ((construct_rho (filter_genv psi) ve te)) as rho'.
 simpl seplog.sepcon.
 rewrite <- (sepcon_comm (stackframe_of' cenv_cs f rho')).
 unfold function_body_ret_assert.
 destruct ek; simpl proj_ret_assert; try solve [normalize].
 rewrite andp_assoc.
 apply prop_andp_subp; intro. simpl in H5.
 repeat rewrite andp_assoc.
 pose proof I.
 pose proof I.
 rewrite <- (sepcon_comm (F0 rho * F rho)).
 change (stackframe_of' cenv_cs f rho') with (stackframe_of f rho').

 intros wx ? w' ? ?.
 assert (level jmx >= level w')%nat.
 apply necR_level in H9.
 apply le_trans with (level wx); auto.
 clear wx H8 H9.
 apply own.bupd_intro; simpl.
 intros ora' jm' Hora' VR ?.
 subst w'.
 intro.
 case_eq (@level rmap ag_rmap (m_phi jm')); [intros; omega | intros n0 H21; clear LW ].
 rewrite <- level_juice_level_phi in H21.
 destruct (levelS_age1 jm' _ H21) as [jm'' H24].
 rewrite -> level_juice_level_phi in H21.
 assert (FL: exists m2, free_list (m_dry jm'')  (Clight.blocks_of_env psi ve) = Some m2). {
    rewrite <- (age_jm_dry H24).
    subst rho'.
    rewrite (sepcon_comm (stackframe_of f _)) in H10.
    repeat rewrite <- sepcon_assoc in H10.
    destruct H10 as [H10 _].
    eapply can_free_list; try eassumption.
    }

 clear Hora ora NEP P.
 fold ctl.
 destruct FL as [m2 FL2].
 assert (H25: ve_of rho' = make_venv ve) by (subst rho'; reflexivity).
 assert (SFFB := stackframe_of_freeable_blocks Delta _ rho' _ ve HGG COMPLETE H17' H25 H5);
   clear HGG COMPLETE.
 clear H25.
 destruct (free_list_juicy_mem_i _ _ _ (F0 rho * F rho * bind_ret vl (fn_return f) (Q ts x) rho') FL2)
 as [jm2 [FL [H21' FL3]]].
 eapply sepcon_derives. apply SFFB. apply derives_refl.
 forget (F0 rho * F rho) as F0F.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (stackframe_of _ _)). rewrite sepcon_assoc.
 destruct H10 as [H22 _].
 eapply pred_nec_hereditary; try apply H22.
 apply laterR_necR. apply age_laterR. apply age_jm_phi; auto.
 subst m2.
 pose (rval := force_val vl).
 assert (jsafeN OK_spec psi (level jm2) ora'
             (Returnstate rval (call_cont ctl)) jm2). {
   assert (LATER2': (level jmx > level (m_phi jm2))%nat). {
     apply age_level in H24.
     repeat rewrite <- level_juice_level_phi in *. omega.
    } 
   assert (HH1 : forall a' : rmap,
     necR (m_phi jm2) a' ->
     (!! guard_environ Delta curf (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) &&
      seplog.sepcon (fun rho0 : environ => EX old : val, substopt ret old F rho0 * maybe_retval (Q ts x) (snd fsig) ret rho0) F0
        (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) && funassert Delta (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx))) a' ->
     (assert_safe Espec psi curf vx (set_opttemp ret rval tx) (exit_cont EK_normal None k) (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx))) a').
   { intros. hnf in H1.
     assert (Help0: laterM (level (m_phi jm)) (level (m_phi jm2))). { 
       clear - LATER2' LATER.
       eapply necR_laterR. apply laterR_necR; eassumption.
       apply later_nat. rewrite <- !level_juice_level_phi in *. omega. }
     specialize (H1 _ Help0 EK_normal None (set_opttemp ret rval tx) vx); hnf in H1.
     assert (Help1: (level (m_phi jm2) >= level (m_phi jm2))%nat) by omega. 
     apply (H1 _ Help1 _ H8).
     rewrite proj_frame_ret_assert in H1.
     simpl proj_ret_assert in H1.
     rewrite proj_frame_ret_assert.
     simpl proj_ret_assert.
     destruct H9 as [[XX1 XX2] XX3]. split; trivial. split; trivial. clear XX1 XX3.
     destruct XX2 as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [LevU1 _].
     exists u1, u2; split. trivial. split; [clear U2| trivial].
     assert (JMX: laterM (m_phi jm) (m_phi jmx)). { constructor. apply age_jm_phi. apply H13. }
     assert (JMX_u1: (level (m_phi jmx) >= level u1)%nat).
     { rewrite LevU1; clear -H8 LATER2' H2 H13. apply necR_level in H8. apply age_level in H13.
        rewrite <- !level_juice_level_phi in *. omega. }
     apply (HR (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) _ JMX _ JMX_u1 _ (necR_refl _) U1). 
   }
   clear H1.
   specialize (HH1 _ (necR_refl _)). simpl in H5.
   spec HH1; [clear HH1 | ].
   - split; [split |].
    + destruct H10 as [H22 _].
        destruct H18 as [H18 [H18b Hnor]].
        simpl. 
        destruct ret; unfold rval; [destruct vl | ].
        *
         assert (tc_val' (fn_return f) v).
           apply tc_val_tc_val'.
           clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
         unfold construct_rho. unfold set_opttemp. rewrite <- map_ptree_rel.
         apply guard_environ_put_te'. subst rho; auto.
         intros.
         cut (t = fn_return f). intros. rewrite H9; auto.
         hnf in TCret; rewrite H8 in TCret. subst; auto.
        *
         assert (f.(fn_return)=Tvoid).
         clear - H22; unfold bind_ret in H22; destruct (f.(fn_return)); normalize in H22; try contradiction; auto.
         unfold fn_funsig in H18b. rewrite H1 in H18b. rewrite H18b in TC5. simpl in TC5.
         specialize (TC5 (eq_refl _)); congruence.
        * unfold set_opttemp. rewrite <- H0. auto.
    +
       destruct H10 as [H22a H22b].
       simpl seplog.sepcon.
       rewrite sepcon_comm in H22a|-*.
       rewrite sepcon_assoc in H22a.
       assert (bind_ret vl (fn_return f) (Q ts x) rho' * (F0 rho * F rho)
            |-- (maybe_retval (Q ts x) (snd fsig) ret (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) *
                   (F0 (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) *
                    EX old: val, substopt ret old F (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx))))). {
        apply sepcon_derives.
        *
         clear dependent a.
         clear Hora' H6 H7 ora'.
         destruct fsig as [f_params f_ret]. 
         simpl in H18; destruct H18 as [H18 [H18b Hnor]]; subst rho' f_ret.
         clear H22b VR. clear LATER2' jm2 FL FL2 FL3.
         unfold rval; clear rval.
         unfold bind_ret.
         unfold get_result1. simpl.
         unfold bind_ret.
         destruct vl.
         +apply derives_extract_prop; intro.
            unfold maybe_retval.
           destruct ret.
           unfold get_result1. simpl.
           apply derives_refl'. f_equal.
           unfold env_set; simpl.
           f_equal. unfold eval_id; simpl.
           f_equal. unfold Map.get. unfold make_tenv. rewrite PTree.gss. reflexivity.
           destruct (fn_return f); try contradiction H;
           apply exp_right with v;    apply derives_refl.
         +
           unfold fn_funsig in TC5. simpl in TC5.
           destruct (fn_return f) eqn:?; try apply FF_derives.
           specialize (TC5 (eq_refl _)). subst ret.
           unfold maybe_retval. apply derives_refl.
        *
          subst rho.
         destruct ret; apply sepcon_derives; auto.
         +
          clear - H.
          apply derives_refl'.
          apply H. intros. destruct (ident_eq i i0).
          subst; left; hnf; simpl. unfold insert_idset. rewrite PTree.gss; auto.
          right; unfold Map.get; simpl; unfold make_tenv; simpl.
          rewrite PTree.gso; auto.
        +
          simpl in TCret.
          destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
          subst t.
          destruct TC3 as [[TC3 _] _].
          hnf in TC3; simpl in TC3.
          specialize (TC3 _ _ Heqo).
          destruct TC3 as [old [? _]].
          apply exp_right with old. unfold substopt, subst.
          apply derives_refl'. f_equal.
          unfold env_set, construct_rho.
           f_equal. unfold make_tenv. extensionality j.
          simpl. unfold Map.set. if_tac. subst.
          apply H0. rewrite PTree.gso; auto.
        +
          apply exp_right with Vundef; simpl; auto.
       } 
      eapply derives_trans. 3: apply H1. apply derives_refl.
      normalize. intros v. exists v. rewrite <- sepcon_assoc. rewrite sepcon_comm in H8. apply H8.
      eapply free_list_juicy_mem_lem. eauto.
      eapply pred_nec_hereditary.
      apply laterR_necR. apply age_jm_phi in H24. apply age_laterR; eauto.
      eapply sepcon_derives; try apply H22a; auto.
   +
     destruct H10 as [H22a H22b].
     eapply pred_nec_hereditary in H22b.
     2:{  apply laterR_necR. apply age_jm_phi in H24. apply age_laterR; eauto. }
     rewrite VR in H22b; clear - FL H22b. {
      rewrite corable_funassert in H22b.
      rewrite corable_funassert.
      replace (core (m_phi jm2)) with (core (m_phi jm'')).
      apply H22b.
      clear - FL.
      induction FL; auto.
      rewrite <-IHFL.
      rewrite <- H1.
      rewrite free_juicy_mem_core; auto.
     }
  -
    clear - HH1.
    destruct (level jm2) eqn:H26; try solve [constructor];
    destruct (levelS_age _ _ (eq_sym H26)) as [jm2' [H27 ?]].
    subst n;
    apply jsafeN_step with (c' := State curf Sskip k vx (set_opttemp ret rval tx)) (m' := jm2');
    simpl.
    split; [ rewrite <- (age_jm_dry H27); constructor | ].
    split3;
    [ apply age1_resource_decay; auto | auto
    | apply age1_ghost_of; apply age_jm_phi; auto].
    eapply pred_nec_hereditary in HH1;
     [ | apply laterR_necR; apply age_jm_phi in H27; apply age_laterR; eauto];
    apply assert_safe_jsafe'; auto.
 }
   clear H1.
    destruct H18 as [H18 [H18b Hnor]].
    simpl.
    rewrite <- H21; clear n0 H21.
    destruct vl; intros; 
    (eapply jsafeN_local_step' with (m2 := jm2);
     [econstructor; eauto |  .. ]).
    1,5: rewrite (age_jm_dry H24); auto.
    1,4:
    eapply resource_decay_trans;
    [ | | eapply free_list_resource_decay; eauto];
    [ rewrite (age_jm_dry H24); apply Pos.le_refl |
      apply age1_resource_decay ].
    1,2: auto.
    1,3: split; [change (level (m_phi ?a)) with (level a); rewrite <- FL3; apply age_level in H24; omega |].
    1,2:rewrite (free_list_juicy_mem_ghost _ _ _ FL);
      erewrite age1_ghost_of by (eapply age_jm_phi; eauto);
      change (level (m_phi jm'')) with (level jm'');
      rewrite FL3; auto.
      change v with rval; auto.
      change Vundef with rval; auto.
Qed.

Lemma tc_eval_exprlist:
  forall {CS: compspecs} Delta tys bl rho m,
    typecheck_environ Delta rho ->
    (tc_exprlist Delta tys bl rho) m ->
    tc_vals tys (eval_exprlist tys bl rho).
Proof.
induction tys; destruct bl; simpl; intros; auto.
unfold tc_exprlist in H0. simpl in H0.
rewrite !denote_tc_assert_andp in H0.
destruct H0 as [[? ?] ?].
split.
unfold_lift.
eapply tc_val_sem_cast; eauto.
apply IHtys with m; auto.
Qed.

Lemma tc_vals_length: forall tys vs, tc_vals tys vs -> length tys = length vs.
Proof.
induction tys; destruct vs; simpl; intros; auto; try contradiction.
destruct H; auto.
Qed.

Lemma eval_exprlist_relate {CS}:
  forall (Delta : tycontext) (tys: typelist)
     (bl : list expr) (psi : genv) (vx : env) (tx : temp_env)
     (rho : environ) m,
   @denote_tc_assert CS (typecheck_exprlist Delta (typelist2list tys) bl) rho (m_phi m) ->
   typecheck_environ Delta rho ->
   cenv_sub cenv_cs (genv_cenv psi) ->
   rho = construct_rho (filter_genv psi) vx tx ->
   Clight.eval_exprlist psi vx tx (m_dry m) bl
     tys
     (eval_exprlist (typelist2list tys) bl rho).
Proof.
  intros.
  revert bl H; induction tys; destruct bl; simpl; intros; try contradiction H.
  constructor.
 rewrite !denote_tc_assert_andp in H.
 super_unfold_lift.
 destruct H as [[? ?] ?].
 specialize (IHtys bl H4).
 constructor 2 with (eval_expr e (construct_rho (filter_genv psi) vx tx)); auto.
 subst.
 eapply eval_expr_relate; eauto.
 pose proof (cast_exists Delta e t rho (m_phi m) H0 H H3).
 rewrite <- H5; clear H5.
 subst. 
 apply cop2_sem_cast'; try eassumption.
 eapply typecheck_expr_sound; eassumption.
Qed.

Lemma semax_call_aux {CS Espec}:
 forall (Delta : tycontext)
  (A : TypeTree)
  (P Q Q' : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: super_non_expansive P) (NEQ': super_non_expansive Q')
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
  (F : environ -> pred rmap)
  (F0 : assert) (ret : option ident) (curf: function) (fsig0 : funsig) cc (a : expr)
  (bl : list expr) (R : ret_assert) (psi : genv) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)
  (ora : OK_ty) (jm : juicy_mem) (b : block) (id : ident)
  (Hora : juicy_mem_op (ext_compat ora) jm),
   Cop.classify_fun (typeof a) =
   Cop.fun_case_f (type_of_params (fst fsig0)) (snd fsig0) cc ->
   tc_fn_return Delta ret (snd fsig0) ->
   (|>tc_expr Delta a rho) (m_phi jm) ->
   (|>tc_exprlist Delta (snd (split (fst fsig0))) bl rho) (m_phi jm) ->
    guard_environ Delta curf rho ->
    (snd fsig0 =Tvoid -> ret=None) ->
    closed_wrt_modvars (Scall ret a bl) F0 ->
    ( ( ALL rho' : environ , |>
       !((EX old:val, substopt ret old F rho' * maybe_retval (Q ts x) (snd fsig0) ret rho') >=> (RA_normal R rho') )) (m_phi jm)) ->
    cenv_sub (@cenv_cs CS) (genv_cenv psi) ->
    rho = construct_rho (filter_genv psi) vx tx ->
    eval_expr a rho = Vptr b Ptrofs.zero ->
    (funassert Delta rho) (m_phi jm) ->
    (|> rguard Espec psi Delta curf (frame_ret_assert R F0) k) (level (m_phi jm)) ->
    (believe Espec Delta psi Delta) (level (m_phi jm)) ->
    (glob_specs Delta)!id = Some (mk_funspec fsig0 cc A P Q' NEP NEQ') ->
    Genv.find_symbol psi id = Some b ->
    (forall vl : environ, (!|>(Q' ts x vl <=> Q ts x vl)) (m_phi jm)) ->
    (|>(F0 rho * F rho *
           P ts x (make_args (map (@fst  _ _) (fst fsig0))
             (eval_exprlist (snd (split (fst fsig0))) bl rho) rho)
            )) (m_phi jm) ->
   jsafeN (@OK_spec Espec) psi (level (m_phi jm)) ora
     (State curf (Scall ret a bl) k vx tx) jm.
Proof.
intros Delta A P Q Q' NEP NEQ' ts x F F0 ret curf fsig cc a bl R psi vx tx k rho ora jm b id Hora.
intros TC0 TCret TC1 TC2 TC3 TC5 H HR HGG H0 H3 H4 H1 Prog_OK H8 H7 H11 H14.
(*************************************************)
assert (Prog_OK' := Prog_OK).
specialize (Prog_OK' (Vptr b Ptrofs.zero) fsig cc A P Q' _ (necR_refl _)). 
(*************************************************)
spec Prog_OK'.
{ hnf. exists id, NEP, NEQ'; split; auto.
  exists b; split; auto.
}
clear H8 H7 id.

assert (H16: exists ff, Genv.find_funct psi (Vptr b Ptrofs.zero) = Some ff /\
                   type_of_fundef ff = Tfunction (type_of_params (fst fsig)) (snd fsig) cc). {
 clear - Prog_OK'.
 destruct Prog_OK'.
-
 destruct fsig as [params res]. simpl fst; simpl snd.
 unfold believe_external in H.
 destruct (Genv.find_funct psi (Vptr b Ptrofs.zero)) eqn:?H; try contradiction.
 exists f; split; auto.
 destruct f; try contradiction; simpl.
 destruct H as [[? _] _].
 destruct H as [? [? [? ?]]]. inv H.
 f_equal.
 simpl in H3.
 clear - H5 H3.
 rewrite fst_split in *. rewrite <- H5.
 revert t H5 H3; induction params; destruct t; simpl; intros; auto.
 inv H3. inv H5. destruct a. simpl in H5. inv H5. f_equal.
 rewrite <- H1. apply IHparams; auto.
-
 destruct H as [b' [f [[? [? ?]] _]]]; inv H; eauto.
 exists (Internal f); auto.
 simpl. rewrite if_true by auto.
 split; auto.
 destruct H1 as [_ [_ [_ [_ [[?[? _]]?]]]]].
 unfold type_of_function; f_equal; auto.
 apply map_snd_typeof_params; auto.
}
destruct H16 as [ff [H16 H16']].

case_eq (level (m_phi jm)); [solve [simpl; constructor] | intros n H2].
simpl.
rewrite <- level_juice_level_phi in H2.
destruct (levelS_age1 _ _ H2) as [jmx H13].
specialize (TC1 _ (age_laterR (age_jm_phi H13))).
specialize (TC2 _ (age_laterR (age_jm_phi H13))).
specialize (H14 _ (age_laterR (age_jm_phi H13))).
specialize (H1 _ (laterR_level' (age_laterR (age_jm_phi H13)))).
apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H13)))) in H4.
apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H13)))) in Hora.
assert (LATER: laterR (level (m_phi jm)) n) by (constructor 1; rewrite <- level_juice_level_phi, H2; reflexivity).
apply (pred_nec_hereditary _ _ n (laterR_necR LATER)) in Prog_OK.
rewrite <- H2.

apply jsafeN_local_step
 with (s2 :=  Callstate ff (eval_exprlist (snd (split (fst fsig))) bl rho)
                                     (Kcall ret curf vx tx k)). {
 eapply step_call with (vargs:=eval_exprlist (snd (split (fst fsig))) bl rho); try eassumption.
 rewrite <- H3.
 erewrite age_jm_dry by eauto.
 eapply eval_expr_relate; try solve[rewrite H0; auto]; auto. destruct TC3; eassumption. eauto.
 destruct (fsig). unfold fn_funsig in *.
 erewrite age_jm_dry by eauto.

 simpl.
 simpl in TC2. revert TC2.
 replace (snd (split l)) with (typelist2list (type_of_params l))
  by (clear; rewrite snd_split; induction l; try destruct a; simpl; f_equal; auto).
 simpl.
 intro TC2.
 eapply eval_exprlist_relate; try eassumption; auto.
 destruct TC3 ; auto.
}
intros jm2 H22.
assert (jmx = jm2). {clear - H13 H22. red in H22. congruence. }
subst jmx.

apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H13)))) in HR.
(*apply (pred_nec_hereditary _ _ n (laterR_necR LATER)) in Prog_OK'.*)
assert (H11': forall vl : environ, (! |> (Q' ts x vl <=> Q ts x vl)) (m_phi jm2)). {
  intro vl.  
 apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H13)))); auto.
}
clear H11; rename H11' into H11.
apply age_level in H13.
assert (n = level jm2) by congruence.
subst n.
change (level (m_phi jm)) with (level jm) in Prog_OK'.
rewrite H2 in Prog_OK'.
clear jm LATER H22 H2 H13.
rename jm2 into jm.

assert (TC8 := tc_eval_exprlist _ _ _ _ _ (proj1 TC3) TC2).
assert (Hargs: Datatypes.length (fst fsig) = 
                 Datatypes.length (eval_exprlist (snd (split (fst fsig))) bl rho)). {
 clear - TC2.
 rewrite snd_split in *.
 revert bl TC2; induction (fst fsig); destruct bl; intros; try contradiction.
 reflexivity.
 unfold tc_exprlist in TC2. simpl in TC2. rewrite !denote_tc_assert_andp in TC2.
 destruct TC2 as [[? ?] ?].
 simpl. f_equal; auto.
}
set (ctl := Kcall ret curf vx tx k).
set (args := eval_exprlist (snd (split (fst fsig))) bl rho) in *.
clearbody args.
clear TC2.
clear TC1 H3. pose proof I.
assert (HR':  (ALL rho' : environ,
      |> ! ((EX old : val,
             substopt ret old F rho' *
             maybe_retval (Q' ts x) (snd fsig) ret rho') >=> 
            RA_normal R rho')) (m_phi jm)). {
 clear - HR H11.
 intros rho'; specialize (HR rho').
 intros ? ? ? ? ? ? [old ?].
 apply (HR a' H y H0 a'0 H1); clear HR.
 exists old.
 revert a'0 H1 H2.
 eapply sepcon_subp'; try apply H0.
 apply derives_subp; apply derives_refl.
 intros ? ?.
 unfold maybe_retval; destruct ret.
 apply (H11 _ (level a')); auto; apply (laterR_level' H).
 destruct (snd fsig);
 [apply (H11 _ (level a')); auto; apply (laterR_level' H) 
 |  intros ? ?  [v ?]; exists v; revert a'0 H2 H3;
  apply (H11 _ (level a')); auto; apply (laterR_level' H)  .. ].
}

rewrite closed_wrt_modvars_Scall in H.
clear a bl TC0.

clear Q HR H11; rename HR' into HR; rename Q' into Q; assert (H11 := I).


destruct Prog_OK' as [H5|H5].
 eapply semax_call_external with (P:=P)(Q:=Q); try eassumption.

apply (pred_nec_hereditary _ _ (level jm)) in H5.
2: apply laterR_necR; apply age_laterR; constructor.

red in TC3.
(*(*TEST*)clear HR *)
destruct H5 as [b' [f [[H3a [H3b ?]] H19]]].
injection H3a; intro; subst b'; clear H3a.
change (Genv.find_funct psi (Vptr b Ptrofs.zero) = Some (Internal f)) in H3b.
rewrite H16 in H3b. injection H3b; clear H3b; intros; subst ff.
destruct H3 as [COMPLETE [H17 [H17' [Hvars [H18 H18']]]]].
pose proof I.

assert (HDelta: forall f : function, tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta))
   by (intro; apply tycontext_sub_refl).
specialize (H19 Delta CS (level (m_phi jm)) (necR_refl _) HDelta _ (necR_refl _) (cenv_sub_refl) ts x).
red in H19.
clear HDelta.
clear H2. destruct (level jm) eqn:H2; [constructor |].
destruct (levelS_age1 _ _ H2) as [jm2 H13]. change (age jm jm2) in H13.
rewrite <- H2 in *. clear H2. pose proof I.
specialize (H19 _ (laterR_level' (age_laterR H13))).
rewrite semax_fold_unfold in H19.
specialize (H19 _ _ _ _ (necR_refl _) (conj (tycontext_sub_refl _) (conj cenv_sub_refl HGG))  _ (necR_refl _) 
      (pred_nec_hereditary  _ _ _ (necR_level' (laterR_necR (age_laterR H13))) Prog_OK)
                      ctl (fun _: environ => F0 rho * F rho) f _ (necR_refl _)).
clear Prog_OK.
spec H19; [eapply semax_call_aux2 with (P:=P)(Q:=Q); eauto | ].
red. red. red. eauto.
instantiate (1:=nil).
instantiate (1 := Econst_int Int.zero tint).
rewrite closed_wrt_modvars_Scall. auto.
apply now_later; auto.
remember (alloc_juicy_variables psi empty_env jm (fn_vars f)) eqn:AJV.
destruct p as [ve' jm']; symmetry in AJV.
destruct (alloc_juicy_variables_e _ _ _ _ _ _ AJV) as [H15 [H20' CORE]].
assert (MATCH := alloc_juicy_variables_match_venv _ _ _ _ _ AJV).
assert (H20 := alloc_juicy_variables_resource_decay _ _ _ _ _ _ AJV).
destruct (build_call_temp_env f args)
as [te' H21]; auto. 
  { clear - H16' Hargs.
    simpl in H16'. unfold type_of_function in H16'. inv H16'. rewrite <- Hargs.
    clear - H0.  
    forget (fst fsig) as al.
   revert al H0; induction (fn_params f) as [|[? ?]]; destruct al as [|[? ?]]; simpl; intros; try discriminate; auto.
   inv H0; f_equal; auto.
}
pose proof (age_twin' _ _ _ H20' H13) as [jm'' [_ H20x]].
rewrite (age_level _ _ H13).
apply jsafeN_step
  with (c' := State f (f.(fn_body)) ctl ve' te')
       (m' := jm''); auto.
split; auto.
apply step_internal_function.
apply list_norepet_append_inv in H17; destruct H17 as [H17 [H22 H23]]; constructor; auto.
rewrite <- (age_jm_dry H20x); auto.
split.
 destruct H20;  apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm'); auto.
 apply age1_resource_decay; auto.
 split.
 rewrite H20'; apply age_level; auto.
 erewrite <- (alloc_juicy_variables_ghost _ _ _ jm), AJV; simpl.
 apply age1_ghost_of, age_jm_phi; auto.

assert (H22: (level jm2 >= level jm'')%nat)
  by (apply age_level in H13; apply age_level in H20x; omega).
pose (rho3 := mkEnviron (ge_of rho) (make_venv ve') (make_tenv te')).
assert (H23: app_pred (funassert Delta rho3) (m_phi jm'')). {
  apply (resource_decay_funassert _ _ (nextblock (m_dry jm)) _ (m_phi jm'')) in H4.
  2: apply laterR_necR; apply age_laterR; auto.
  unfold rho3; clear rho3.
  apply H4.
  rewrite CORE. apply age_core. apply age_jm_phi; auto.
  destruct H20;  apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm'); auto.
   apply age1_resource_decay; auto.
}
specialize (H19 te' ve' _ H22 _ (necR_refl _)).
spec H19; [clear H19|]. {
 split; [split |]; auto.
 3:{ unfold rho3 in H23. unfold construct_rho. rewrite H0 in H23.
     simpl ge_of in H23. auto.
  }
 split; [ | simpl; split; [ | reflexivity]; apply MATCH ].
 -
  rewrite (age_jm_dry H20x) in H15.
  unfold func_tycontext'.
  unfold construct_rho.
  clear - H0 TC3 TC8 H18 H16 H21 H15 H23 H17 H17' H13.
  unfold rho3 in *. simpl in *. destruct H23.
  destruct rho. inv H0. simpl in *.
  remember (split (fn_params f)). destruct p.
  simpl in *. if_tac in H16; try congruence.
  destruct TC3 as [TC3 TC3'].
  destruct TC3 as [TC3 [TC4 TC5]].
  eapply semax_call_typecheck_environ with (jm := jm2); try eassumption.
  erewrite <- age_jm_dry by apply H13; auto.
  clear - TC8 H18. destruct H18 as [H18 _]. rewrite snd_split in *. rewrite <- H18; auto.
-
 normalize.
 split; auto. unfold rho3 in H23. unfold construct_rho. rewrite H0 in H23.
 simpl ge_of in H23. auto.
 unfold bind_args.
 unfold tc_formals.
 normalize.
 rewrite <- sepcon_assoc.
 normalize.
 split.
 +
 hnf.
 destruct H18 as [H18 [H18b Hnor]]. rewrite H18b in *. clear H18b.
 rewrite (map_snd_typeof_params _ _ H18) in *.
 rewrite <- snd_split in H18; rewrite H18 in *.
 clear - TC8 H21 H17.
 simpl in *.
 match goal with H: tc_vals _ ?A |- tc_vals _ ?B => replace B with A; auto end.
 rewrite list_norepet_app in H17. destruct H17 as [H17 [_ _]].
 clear - H17 H21.
 forget (create_undef_temps (fn_temps f)) as te.
 revert  args te te' H21 H17.
 induction (fn_params f); destruct args; intros; auto; try discriminate.
 destruct a; inv H21.
 destruct a. simpl in H21. inv H17.
 simpl. f_equal. unfold eval_id, construct_rho; simpl.
  inv H21.
 erewrite pass_params_ni; try eassumption.
  rewrite PTree.gss. reflexivity.
 eapply IHl; try eassumption.
+
 forget (F0 rho * F rho) as Frame.
 destruct H18 as [H18 [H18b Hnor]]. rewrite H18b in *. clear H18b.
 rewrite (map_snd_typeof_params _ _ H18) in *.
 rewrite <- snd_split in H18; rewrite H18 in *.
 rewrite @snd_split in *.
 simpl @fst in *.
 apply (alloc_juicy_variables_age H13 H20x) in AJV.
 forget (fn_params f) as params.
 clear - Hnor H18 H21 H14 AJV H17 H17' H0 Hvars HGG COMPLETE H13.
 assert (app_pred (Frame * close_precondition (map fst (fst fsig)) (map fst params)  (P ts x)
                               (construct_rho (filter_genv psi) ve' te')) (m_phi jm2)). {
 eapply pred_nec_hereditary. apply laterR_necR. apply age_laterR. eapply age_jm_phi. apply H13.
  eapply sepcon_derives; try apply H14; auto.
  subst rho.
  eapply make_args_close_precondition; eauto.
  clear - H18. rewrite !map_length.
  rewrite <- (map_length snd). rewrite H18. rewrite map_length; auto.
  apply list_norepet_app in H17; intuition.
 }
  clear H14.
  forget (Frame *
     close_precondition (map fst (fst fsig)) (map fst params)  (P ts x)
       (construct_rho (filter_genv psi) ve' te')) as Frame2.
 clear - H17' H21 AJV H Hvars HGG COMPLETE.
 change (stackframe_of' cenv_cs) with stackframe_of.
 eapply alloc_juicy_variables_lem2; eauto.
 unfold var_sizes_ok in Hvars;
 rewrite Forall_forall in Hvars, COMPLETE |- *.
 intros.
 specialize (COMPLETE x H0).
 specialize (Hvars x H0).
 rewrite (cenv_sub_sizeof HGG); auto.
}
replace (level jm2) with (level jm'') 
  by (clear - H13 H20x H20'; apply age_level in H13; apply age_level in H20x; omega).
eapply assert_safe_jsafe, own.bupd_mono, H19.
intros ? Hsafe ?? Hora0 ??.
subst; specialize (Hsafe ora0 _ Hora0 eq_refl eq_refl).
clear - Hsafe.
intros.
specialize (Hsafe LW).
simpl in Hsafe.
case_eq (@level rmap ag_rmap (m_phi jm0)); intros; [omega | clear LW ].
rewrite H in Hsafe.
auto.
Qed.

Lemma semax_call_aux' {CS Espec}:
 forall (Delta : tycontext)
  (A : TypeTree)
  (P Q Q' : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: super_non_expansive P) (NEQ': super_non_expansive Q')
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
  (F : environ -> pred rmap)
  (F0 : assert) (ret : option ident) (curf : function) (fsig0 : funsig) cc (a : expr)
  (bl : list expr) (R : ret_assert) (psi : genv) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)
  (ora : OK_ty) (jm : juicy_mem) (b : block) (id : ident)
  (Hora : juicy_mem_op (ext_compat ora) jm),
   Cop.classify_fun (typeof a) =
   Cop.fun_case_f (type_of_params (fst fsig0)) (snd fsig0) cc ->
   tc_fn_return Delta ret (snd fsig0) ->
   (|>tc_expr Delta a rho) (m_phi jm) ->
   (|>tc_exprlist Delta (snd (split (fst fsig0))) bl rho) (m_phi jm) ->
    guard_environ Delta curf rho ->
    (snd fsig0 =Tvoid -> ret=None) ->
    closed_wrt_modvars (Scall ret a bl) F0 ->

    ( (ALL rho' : environ ,
       !((EX old:val, substopt ret old F rho' * maybe_retval (Q ts x) (snd fsig0) ret rho') >=> (RA_normal R rho') )) (m_phi jm)) ->

    cenv_sub (@cenv_cs CS) (genv_cenv psi) ->
    rho = construct_rho (filter_genv psi) vx tx ->
   eval_expr a rho = Vptr b Ptrofs.zero ->
    (funassert Delta rho) (m_phi jm) ->
    (rguard Espec psi Delta curf (frame_ret_assert R F0) k) (level (m_phi jm)) ->
    (believe Espec Delta psi Delta) (level (m_phi jm)) ->
    (glob_specs Delta)!id = Some (mk_funspec fsig0 cc A P Q' NEP NEQ') ->
    Genv.find_symbol psi id = Some b ->
    (forall vl : environ, (!|>(Q' ts x vl <=> Q ts x vl)) (m_phi jm)) ->
    (|>(F0 rho * F rho *
           P ts x (make_args (map (@fst  _ _) (fst fsig0))
             (eval_exprlist (snd (split (fst fsig0))) bl rho) rho)
            )) (m_phi jm) ->
   jsafeN (@OK_spec Espec) psi (level (m_phi jm)) ora
     (State curf (Scall ret a bl) k vx tx) jm.
Proof. intros. apply now_later in H6. apply now_later in H11. rewrite box_all in H6.
eapply semax_call_aux; eassumption. 
Qed.

Lemma semax_call {CS Espec}:
  forall Delta (A: TypeTree)
  (P Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: super_non_expansive P) (NEQ: super_non_expansive Q)
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
   F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
       (fun rho => (|>(tc_expr Delta a rho && tc_exprlist Delta (snd (split argsig)) bl rho))  &&
           (func_ptr (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (make_args (map (@fst  _ _) argsig)
                (eval_exprlist (snd (split argsig)) bl rho) rho )))))
         (Scall ret a bl)
         (normal_ret_assert
          (fun rho => (EX old:val, substopt ret old F rho * maybe_retval (Q ts x) retsig ret rho))).
Proof.
rewrite semax_unfold. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TCF TC5 TC7.
intros. 
rename H into Closed; rename H0 into RGUARD.
intros tx vx.
intros ? ? ? NecR_ya' [[TC3 ?] funassertDelta'].

assert (NecR_wa': necR w (level a')).
{ apply nec_nat. apply necR_level in NecR_ya'. apply le_trans with (level y); auto. }
eapply pred_nec_hereditary in RGUARD; [ | apply NecR_wa'].
eapply pred_nec_hereditary in Prog_OK; [ | apply NecR_wa'].
clear w NecR_wa' NecR_ya' y H.
rename a' into w.


assert (TC7': tc_fn_return Delta' ret retsig).
{
  clear - TC7 TS.
  hnf in TC7|-*. destruct ret; auto.
  destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
  destruct TS.
  specialize (H i); rewrite Heqo in H. subst t.
  destruct ((temp_types Delta') ! i ).
  destruct H; auto.
  auto.
} clear TC7.
rewrite !later_andp in H0.
apply extend_sepcon_andp in H0; auto.
destruct H0 as [[TC1 TC2] pre].

normalize in pre. unfold func_ptr in *. hnf in pre.
destruct pre as [preA preB]. destruct preA as [b [EvalA funcatb]].
destruct preB as [z1 [z2 [JZ [HF0 pre]]]].
destruct (level w) eqn: Hl.
{ apply own.bupd_intro; repeat intro.
  rewrite Hl; constructor. }
rewrite <- Hl in *.
destruct (levelS_age w n) as (w' & Hage & Hw'); auto.

hnf in funcatb. 

destruct funcatb as [gs [GS funcatb]]. simpl in GS.
unfold func_at, pureat in funcatb.

assert (Hpsi: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)) by reflexivity.
unfold filter_genv in Hpsi.
remember (construct_rho (filter_genv psi) vx tx) as rho.

set (args := @eval_exprlist CS (snd (split argsig)) bl rho).
set (args' := @eval_exprlist CS' (snd (split argsig)) bl rho).

assert (MYPROP: exists id fs, Map.get (ge_of rho) id = Some b /\ 
         (glob_specs Delta') ! id = Some fs /\ func_at fs (b, 0) w).
{ clear - funcatb funassertDelta' GS JZ.
  assert (XX: exists id:ident, (Map.get (ge_of rho) id = Some b)
                               /\ exists fs, (glob_specs Delta')!id = Some fs).
  { destruct funassertDelta' as [_ FD]. 
    apply (FD b (argsig, retsig) cc _ (necR_refl _)); clear FD.
    simpl. destruct gs. hnf in funcatb. destruct GS as [? [? ?]]; subst.
    eexists; eauto. }
  destruct XX as [id [Hb [fs specID]]]; simpl in Hb.

  assert (exists v, Map.get (ge_of rho) id = Some v /\ func_at fs (v, 0) w).
  { destruct funassertDelta' as [funassertDeltaA _].
    destruct (funassertDeltaA id fs _ (necR_refl _) specID) as [v [Hv funcatv]]; simpl in Hv.
    exists v; split; trivial. }
  destruct H as [v [Hv funcatv]].
  assert (VB: b=v); [inversion2 Hb Hv; trivial | subst; clear Hb].
  exists id, fs; auto. }
destruct MYPROP as [id [fs [RhoID [SpecOfID funcatv]]]].
destruct fs as [fsig' cc' A' P' Q' NEP' NEQ'].
unfold func_at in funcatv, funcatb. destruct gs.
hnf in funcatb, funcatv. inversion2 funcatv funcatb.
assert (PREPOST: (forall ts x vl, (! |> (P' ts x vl <=> P0 ts x vl)) w) /\
                 (forall ts x vl, (! |> (Q' ts x vl <=> Q0 ts x vl)) w)).
{ apply inj_pair2 in H3; 
  apply (function_pointer_aux); trivial. f_equal; apply H3. }
clear H3; destruct PREPOST as [Hpre Hpost]. 

fold args in pre. clear Hpsi. remember (construct_rho (filter_genv psi) vx tx) as rho; clear Heqrho.
destruct GS as [? [? GS]]; subst fsig' cc'.

  assert (typecheck_environ Delta rho) as TC4.
{ clear - TC3 TS.
  destruct TC3 as [TC3 TC4].
  eapply typecheck_environ_sub in TC3; [| eauto].
  auto.
}

assert (HARGS: args = args').
{ clear - Hage HGG TC4 TC2.
  assert (ARGSEQ: (|> (!! (args = args'))) w).
  { hnf; intros. specialize (TC2 _ H). subst args args'.
    simpl. destruct HGG as [CSUB HGG].
     apply (typecheck_exprlist_sound_cenv_sub CSUB Delta rho TC4 a'); apply TC2. }
  eapply (ARGSEQ w'). apply age_laterR; trivial. }

eapply later_derives in TC2; [|apply (tc_exprlist_sub _ _ _ TS); auto].
eapply later_derives in TC1; [|apply (tc_expr_sub _ _ _ TS); auto].

assert (HPP: (|> (F0 rho * F rho * P ts x (make_args (map fst argsig) args rho)))%pred w).
{ clear - pre JZ HF0 HGG TC1 TC2.
  rewrite sepcon_assoc. rewrite later_sepcon. exists z1, z2; split; trivial. 
  split. apply now_later; trivial. trivial. }
simpl in EvalA.  clear pre JZ HF0 z1 z2.
rewrite later_sepcon in HPP.
destruct HPP as [w1 [w2 [J [W1 W2]]]]; destruct (join_level _ _ _ J) as [LevW1 LevW2].
destruct (age1_join2 _ J Hage) as [w1' [w2' [J' [Age1 Age2]]]].

assert (TRIV: (forall rho, typecheck_temp_environ rho (PTree.empty type)) /\
              (typecheck_var_environ (Map.empty (block * type)) (PTree.empty type)) /\ 
              (forall rho, typecheck_glob_environ rho (PTree.empty type))).
{ clear. split.
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } split. 
  { intros; hnf; intros. split; intros. rewrite PTree.gempty in H; congruence. 
    destruct H. unfold Map.empty, Map.get in H; congruence. } 
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } }

assert (TCD': tc_environ Delta' rho) by eapply TC3.

assert (LA2: laterM w2 w2'). { constructor; trivial. }
assert (TCARGS: tc_environ (funsig_tycontext (argsig, retsig)) (make_args (map fst argsig) args rho)).
{ assert (LaterW': laterR w w'). constructor; trivial.
  specialize (TC2 _ LaterW'). subst args.
  apply (tc_environ_make_args' argsig retsig bl rho Delta' TCD' _ TC2).  }
 
specialize (GS ts x (make_args (map fst argsig) args rho)).
destruct (GS w2') as [ts1 [x1 [G [HG1 HG2]]]].
{ simpl; split; trivial. clear - W2 Age2. apply W2. apply age_laterR; trivial. }

specialize (Hpre ts1 x1 (make_args (map fst argsig) args rho)).

assert (ArgsW: app_pred (|> (F0 rho * (F rho * G) * P' ts1 x1 (make_args (map (@fst  _ _) argsig)
  (eval_exprlist (snd (split argsig)) bl rho) rho) )) w).
{ clear Hpost HG2 funcatv SpecOfID Prog_OK RhoID TC7' RGUARD. rewrite HARGS in *.
  assert (XX: (|> (F0 rho * F rho * G * P' ts1 x1 (make_args (map (@fst  _ _) argsig)
     (eval_exprlist (snd (split argsig)) bl rho) rho) )) w). 
  { rewrite sepcon_assoc. rewrite sepcon_assoc. rewrite <- sepcon_assoc.
    rewrite later_sepcon.
    exists w1, w2; split. trivial. split. trivial. hnf; intros.
    destruct (age_later Age2 H); [ subst a' |].
    - destruct HG1 as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [LevU1 LevU2]. 
      exists u1, u2; split; trivial. split; trivial. 
      assert (LatWU2: laterM (level w) (level u2)). { rewrite LevU2, <- LevW2 . apply laterR_level'; trivial. } 
      eapply (Hpre (level u2) LatWU2); [| apply necR_refl | trivial]. omega.
    - apply now_later in HG1. specialize (HG1 _ H0).
      destruct HG1 as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [LevU1 LevU2]. 
      exists u1, u2; split; trivial. split; trivial. 
      assert (LatWU2: laterM (level w) (level u2)). { rewrite LevU2, <- LevW2 . apply laterR_level'; trivial. }
      eapply (Hpre (level u2) LatWU2); [| apply necR_refl | trivial]; omega.  }
  clear - XX. rewrite 2 sepcon_assoc. rewrite 2 sepcon_assoc in XX.
  intros u U. destruct (XX _ U) as [u1 [u2 [J [U1 U2]]]]; clear XX.
  exists u1, u2; split; trivial. split; trivial.
}

clear Hpre GS.
specialize (Hpost ts1 x1).
apply own.bupd_intro; repeat intro; subst.
assert (CSUBpsi:cenv_sub (@cenv_cs CS) psi).
{ destruct HGG as [CSUB' HGG]. apply (cenv_sub_trans CSUB' HGG). }
destruct HGG as [CSUB HGG].

rewrite (typecheck_expr_sound_cenv_sub CSUB Delta' _ TCD' w' a) in EvalA by (apply (TC1 w' (age_laterR  Hage))).
eapply (@semax_call_aux' CS') with (F := fun rho => F rho * G)(P:=P')(F0:=F0)(rho:=construct_rho (filter_genv psi) vx tx)
 (ts:=ts1)(x:=x1)(fsig0:=(argsig, retsig)); try eassumption; try trivial.
{ clear - TC1 CSUB; intros w W. apply (tc_expr_cenv_sub CSUB _ _ _ _ (TC1 _ W)) . }
{ clear - Espec TC2 CSUB. intros w W. specialize (TC2 _ W).
  apply (tc_exprlist_cenv_sub CSUB). apply TC2. }
simpl RA_normal; auto. clear - TRIV TC7' HG2. change (snd (argsig, retsig)) with retsig.
intros rho' u U m NEC [v V]. exists v.
hnf in TC7'.
destruct ret. 
+ remember ((temp_types Delta') ! i) as rr; destruct rr; try contradiction; subst t.
  assert (TCR: tc_environ (ret0_tycon (funsig_tycontext (argsig, retsig))) (get_result1 i rho')).
  { hnf; simpl. intuition. }
  simpl in V; simpl. destruct V as [m1 [m2 [JM [[u1 [u2 [JU [U1 U2]]]] M2]]]].
  destruct (join_assoc JU JM) as [q1 [Q2 Q1]].
  exists u1, q1; split; trivial. split. apply U1.
  hnf in HG2. apply HG2. simpl. split. trivial.
  exists u2, m2; auto.
+ destruct V as [m1 [m2 [JM [[u1 [u2 [JU [U1 U2]]]] M2]]]].
  destruct (join_assoc JU JM) as [q1 [Q2 Q1]]. simpl in M2. simpl.
  exists u1, q1; split; trivial. split. apply U1.
  hnf in HG2.
  destruct retsig. 
  - apply HG2. simpl. split. hnf; simpl; intuition. exists u2, m2; auto.
  - destruct M2 as [z M2]; exists z. apply HG2. simpl. split; [ hnf; simpl; intuition | exists u2, m2; auto].
  - destruct M2 as [z M2]; exists z. apply HG2. simpl. split; [ hnf; simpl; intuition | exists u2, m2; auto].
  - destruct M2 as [z M2]; exists z. apply HG2. simpl. split; [ hnf; simpl; intuition | exists u2, m2; auto].
  - destruct M2 as [z M2]; exists z. apply HG2. simpl. split; [ hnf; simpl; intuition | exists u2, m2; auto].
  - destruct M2 as [zz M2]; exists zz. apply HG2. simpl. split; [ hnf; simpl; intuition | exists u2, m2; auto].
  - destruct M2 as [z M2]; exists z. apply HG2. simpl. split; [ hnf; simpl; intuition | exists u2, m2; auto].
  - destruct M2 as [z M2]; exists z. apply HG2. simpl. split; [ hnf; simpl; intuition | exists u2, m2; auto].
  - destruct M2 as [z M2]; exists z. apply HG2. simpl. split; [ hnf; simpl; intuition | exists u2, m2; auto].
Qed.

Lemma semax_call_si {CS Espec}:
  forall Delta (A: TypeTree)
  (P Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: super_non_expansive P) (NEQ: super_non_expansive Q)
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
   F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
       (fun rho => (|>(tc_expr Delta a rho && tc_exprlist Delta (snd (split argsig)) bl rho))  &&
           (func_ptr_si (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (make_args (map (@fst  _ _) argsig)
                (eval_exprlist (snd (split argsig)) bl rho) rho )))))
         (Scall ret a bl)
         (normal_ret_assert
          (fun rho => (EX old:val, substopt ret old F rho * maybe_retval (Q ts x) retsig ret rho))).
Proof.
rewrite semax_unfold. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TCF TC5 TC7.
intros.
rename H into Closed; rename H0 into RGUARD.
intros tx vx.
intros ? ? ? NecR_ya' [[TC3 ?] funassertDelta'].

assert (NecR_wa': necR w (level a')).
{ apply nec_nat. apply necR_level in NecR_ya'. apply le_trans with (level y); auto. }
eapply pred_nec_hereditary in RGUARD; [ | apply NecR_wa'].
eapply pred_nec_hereditary in Prog_OK; [ | apply NecR_wa'].
clear w NecR_wa' NecR_ya' y H.
rename a' into w.


assert (TC7': tc_fn_return Delta' ret retsig).
{
  clear - TC7 TS.
  hnf in TC7|-*. destruct ret; auto.
  destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
  destruct TS.
  specialize (H i); rewrite Heqo in H. subst t.
  destruct ((temp_types Delta') ! i ).
  destruct H; auto.
  auto.
} 
rewrite !later_andp in H0.
apply extend_sepcon_andp in H0; auto.
destruct H0 as [[TC1 TC2] pre].

normalize in pre. unfold func_ptr_si in *.
destruct pre as [[b [EvalA funcatb]] HP].
destruct (level w) eqn: Hl.
{ apply own.bupd_intro; repeat intro.
  rewrite Hl; constructor. }
rewrite <- Hl in *.
destruct (levelS_age w n) as (w' & Hage & Hw'); auto.

hnf in funcatb. 

destruct funcatb as [gs [GS funcatb]].

assert (Hpsi: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)) by reflexivity.
unfold filter_genv in Hpsi.
remember (construct_rho (filter_genv psi) vx tx) as rho.

set (args := @eval_exprlist CS (snd (split argsig)) bl rho).
set (args' := @eval_exprlist CS' (snd (split argsig)) bl rho).

assert (MYPROP: exists id fs, Map.get (ge_of rho) id = Some b /\ 
         (glob_specs Delta') ! id = Some fs /\ func_at fs (b, 0) w).
{ clear - funcatb funassertDelta' GS.
  assert (XX: exists id:ident, (Map.get (ge_of rho) id = Some b)
                               /\ exists fs, (glob_specs Delta')!id = Some fs).
  { destruct funassertDelta' as [_ FD]. 
    apply (FD b (argsig, retsig) cc _ (necR_refl _)); clear FD.
    simpl. destruct gs. hnf in funcatb. destruct GS as [[? ?] _]; subst. (* destruct GS as [? [? ?]]; subst.*)
    eexists. eapply funcatb. }
  destruct XX as [id [Hb [fs specID]]]; simpl in Hb.

  assert (exists v, Map.get (ge_of rho) id = Some v /\ func_at fs (v, 0) w).
  { destruct funassertDelta' as [funassertDeltaA _].
    destruct (funassertDeltaA id fs _ (necR_refl _) specID) as [v [Hv funcatv]]; simpl in Hv.
    exists v; split; trivial. }
  destruct H as [v [Hv funcatv]].
  assert (VB: b=v); [inversion2 Hb Hv; trivial | subst; clear Hb].
  exists id, fs; auto. }
destruct MYPROP as [id [fs [RhoID [SpecOfID funcatv]]]].
destruct fs as [fsig' cc' A' P' Q' NEP' NEQ'].
unfold func_at in funcatv, funcatb. destruct gs.
hnf in funcatb, funcatv. inversion2 funcatv funcatb.
assert (PREPOST: (forall ts x vl, (! |> (P' ts x vl <=> P0 ts x vl)) w) /\
                 (forall ts x vl, (! |> (Q' ts x vl <=> Q0 ts x vl)) w)).
{ apply inj_pair2 in H3; 
  apply (function_pointer_aux); trivial. f_equal; apply H3. }
clear H3; destruct PREPOST as [Hpre Hpost]. 

fold args in HP. clear Hpsi. remember (construct_rho (filter_genv psi) vx tx) as rho.

assert (typecheck_environ Delta rho) as TC4.
{ clear - TC3 TS.
  destruct TC3 as [TC3 TC4].
  eapply typecheck_environ_sub in TC3; [| eauto].
  auto.
} 

assert (HARGS: args = args').
{ clear - Hage HGG TC4 TC2.
  assert (ARGSEQ: (|> (!! (args = args'))) w).
  { hnf; intros. specialize (TC2 _ H). subst args args'.
    simpl. destruct HGG as [CSUB HGG].
    apply (typecheck_exprlist_sound_cenv_sub CSUB Delta rho TC4 a'). apply TC2. }
  eapply (ARGSEQ w'). apply age_laterR; trivial. }

eapply later_derives in TC2; [|apply (tc_exprlist_sub _ _ _ TS); auto].
eapply later_derives in TC1; [|apply (tc_expr_sub _ _ _ TS); auto].

clear TC4.

assert (TCD': tc_environ Delta' rho) by eapply TC3.

assert (TCARGS: tc_environ (funsig_tycontext (argsig, retsig)) (make_args (map fst argsig) args rho)).
{ assert (LaterW': laterR w w'). constructor; trivial.
  specialize (TC2 _ LaterW'). subst args.
  apply (tc_environ_make_args' argsig retsig bl rho Delta' TCD' _ TC2).  }

clear Heqrho.
destruct GS as [[? ?] GS] ; subst fsig' cc'.

rewrite later_sepcon, <- sepcon_assoc in HP.

assert (HPP: (|> (F0 rho * F rho * P ts x (make_args (map fst argsig) args rho)))%pred w).
{ clear - HP. rewrite 2 later_sepcon. rewrite sepcon_assoc.  rewrite sepcon_assoc in HP. 
  eapply sepcon_derives. 3: apply HP. apply now_later. trivial. } clear HP.
rewrite later_sepcon in HPP.
destruct HPP as [w1 [w2 [J [W1 W2]]]]; destruct (join_level _ _ _ J) as [LevW1 LevW2].
destruct (age1_join2 _ J Hage) as [w1' [w2' [J' [Age1 Age2]]]]; destruct (join_level _ _ _ J') as [Lw1' Lw2'].

assert (LA2: laterM w2 w2'). { constructor; trivial. }
specialize (GS ts). hnf in GS.
fold (@dependent_type_functor_rec ts) in *.
specialize (W2 _ LA2). 

specialize (GS x (make_args (map fst argsig) args rho)). hnf in GS.
assert (LW2': (level w >= level w2')%nat). { apply age_level in Age2. destruct (join_level _ _ _ J); omega. }
destruct (GS _ LW2' _ (necR_refl _)) as [ts1 [x1 [G [AA BB]]]]; clear GS.
{ split; trivial. } 

specialize (Hpre ts1 x1 (make_args (map fst argsig) args rho)).
fold (@dependent_type_functor_rec ts1) in *.
rewrite <- later_unfash in Hpre.
specialize (Hpre _ (age_laterR Hage)).
(****)


destruct AA as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [Lu1 Lu2].
hnf in Hpre. destruct (Hpre u2) as [_ HP']; clear Hpre. omega. specialize (HP' _ (necR_refl _) U2).

assert (ArgsW: app_pred (|> (F0 rho * (F rho * G) * P' ts1 x1 (make_args (map (@fst  _ _) argsig)
  (eval_exprlist (snd (split argsig)) bl rho) rho) )) w).
{ clear Hpost funcatv SpecOfID Prog_OK RhoID TC7' RGUARD. rewrite HARGS in *.
  assert (XX: (|> (F0 rho * F rho * G * P' ts1 x1 (make_args (map (@fst  _ _) argsig)
     (eval_exprlist (snd (split argsig)) bl rho) rho) )) w). 
  { rewrite sepcon_assoc. rewrite sepcon_assoc. rewrite <- sepcon_assoc.
    rewrite later_sepcon.
    exists w1, w2; split. trivial. split. trivial. hnf; intros. specialize (age_later_nec _ _ _ Age2 H). intros.
    destruct (nec_join2  JU H0) as [a1' [a2' [JA [A1 A2]]]]; destruct (join_level _ _ _ JA) as [La1 La2].
    exists a1', a2'; split. trivial. split.
    + destruct (nec_refl_or_later _ _ A1); subst. trivial. eapply now_later. apply U1. trivial. 
    + destruct (nec_refl_or_later _ _ A2); subst. trivial. eapply now_later. apply HP'. trivial. }
  clear - XX. rewrite 2 sepcon_assoc. rewrite 2 sepcon_assoc in XX.
  intros u U. destruct (XX _ U) as [u1 [u2 [J [U1 U2]]]]; clear XX.
  exists u1, u2; split; trivial. split; trivial. 
}
apply now_later in  RGUARD.
apply own.bupd_intro; repeat intro; subst. rename H into ORA.

specialize (Hpost ts1 x1).

assert (CSUBpsi:cenv_sub (@cenv_cs CS) psi).
{ destruct HGG as [CSUB' HGG]. apply (cenv_sub_trans CSUB' HGG). }
destruct HGG as [CSUB HGG].

rewrite (typecheck_expr_sound_cenv_sub CSUB Delta' _ TCD' w' a) in EvalA by (apply (TC1 w' (age_laterR  Hage))).
eapply (@semax_call_aux CS') with (F := fun rho => F rho * G)(P:=P')(F0:=F0)(rho:=construct_rho (filter_genv psi) vx tx)
 (ts:=ts1)(x:=x1)(fsig0:=(argsig, retsig)); try eassumption; try trivial.
{ clear - TC1 CSUB; intros w W. apply (tc_expr_cenv_sub CSUB _ _ _ _ (TC1 _ W)) . }
{ clear - Espec TC2 CSUB. intros w W. specialize (TC2 _ W).
  apply (tc_exprlist_cenv_sub CSUB). apply TC2. }
simpl RA_normal; auto.  clear ArgsW Hpost RGUARD. 
intros rho' l L y Y z YZ [v Z]. exists v.
assert (TRIV: (forall rho, typecheck_temp_environ rho (PTree.empty type)) /\
              (typecheck_var_environ (Map.empty (block * type)) (PTree.empty type)) /\ 
              (forall rho, typecheck_glob_environ rho (PTree.empty type))).
{ clear. split.
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } split. 
  { intros; hnf; intros. split; intros. rewrite PTree.gempty in H; congruence. 
    destruct H. unfold Map.empty, Map.get in H; congruence. } 
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } }
assert (LEV2': (level w2' >= level w2')%nat) by omega. 
assert (LEVz: (level w2' >= level z)%nat). 
{ rewrite Lw2'. apply necR_level in YZ.
  destruct (age_later Hage L).
  + subst l; omega. + apply laterR_level in H; omega. }
destruct ret; simpl.
+ destruct Z as [z1 [z2 [JZ [Z1 Z2]]]]; destruct (join_level _ _ _ JZ) as [Levz1 Levz2]. simpl in Z1, Z2.
  destruct Z1 as [z1_1 [z1_2 [JZ1 [Z11 Z12]]]]; destruct (join_level _ _ _ JZ1) as [Levz11 Levz12].
  destruct (join_assoc JZ1 JZ) as [y11 [JY1 JY2]]; destruct (join_level _ _ _ JY2) as [_ Levy11].
  assert (LL: (level w2' >= level y11)%nat) by omega. 
  exists z1_1, y11; split; trivial. split; trivial.
  apply (BB (get_result1 i rho') _ LL _ (necR_refl _)).
  simpl; split. { hnf; simpl; intuition. }
  exists z1_2, z2; auto.
+ destruct Z as [z1 [z2 [JZ [Z1 Z2]]]]; destruct (join_level _ _ _ JZ) as [Levz1 Levz2]. simpl in Z1, Z2.
  destruct Z1 as [z1_1 [z1_2 [JZ1 [Z11 Z12]]]]; destruct (join_level _ _ _ JZ1) as [Levz11 Levz12].
  destruct (join_assoc JZ1 JZ) as [y11 [JY1 JY2]]; destruct (join_level _ _ _ JY2) as [_ Levy11].
  assert (LL: (level w2' >= level y11)%nat) by omega. 
  exists z1_1, y11; split; trivial. split; trivial. 
  destruct (type_eq retsig Tvoid).
  - subst retsig. 
    apply (BB (globals_only rho') _ LL _ (necR_refl _)).
    simpl; split. hnf; simpl; intuition.
    exists z1_2, z2; auto.
  - assert (Z22: ((fun rho : environ => EX v : val, Q0 ts1 x1 (env_set (globals_only rho) ret_temp v)) rho') z2).
    destruct retsig; trivial.  congruence.
    clear Z2; destruct Z22 as [vv Z2]. 
    specialize (BB (env_set (globals_only rho') ret_temp vv) _ LL _ (necR_refl _)); spec BB.
    * simpl; split. hnf; simpl; intuition.
      exists z1_2, z2; auto.
    *  destruct retsig; try solve [ congruence]; exists vv; trivial.
Qed.

Lemma semax_call_early {CS Espec}:
  forall Delta (A: TypeTree)
  (P Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: super_non_expansive P) (NEQ: super_non_expansive Q)
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
   F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
       (fun rho => (|>(tc_expr Delta a rho && tc_exprlist Delta (snd (split argsig)) bl rho))  &&
           (func_ptr_early (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (make_args (map (@fst  _ _) argsig)
                (eval_exprlist (snd (split argsig)) bl rho) rho )))))
         (Scall ret a bl)
         (normal_ret_assert
          (fun rho => (EX old:val, substopt ret old F rho * maybe_retval (Q ts x) retsig ret rho))).
Proof.
rewrite semax_unfold. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TCF TC5 TC7.
intros.
rename H into Cloased; rename H0 into RGUARD. Locate guard.
intros tx vx.
intros ? ? ? NecR_ya' [[TC3 ?] funassertDelta'].

assert (NecR_wa': necR w (level a')).
{ apply nec_nat. apply necR_level in NecR_ya'. apply le_trans with (level y); auto. }
eapply pred_nec_hereditary in RGUARD; [ | apply NecR_wa'].
eapply pred_nec_hereditary in Prog_OK; [ | apply NecR_wa'].
clear w NecR_wa' NecR_ya' y H.
rename a' into w.


assert (TC7': tc_fn_return Delta' ret retsig).
{
  clear - TC7 TS.
  hnf in TC7|-*. destruct ret; auto.
  destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
  destruct TS.
  specialize (H i); rewrite Heqo in H. subst t.
  destruct ((temp_types Delta') ! i ).
  destruct H; auto.
  auto.
} 
rewrite !later_andp in H0.
apply extend_sepcon_andp in H0; auto.
destruct H0 as [[TC1 TC2] pre].

normalize in pre. unfold func_ptr_early in *.
destruct pre as [preA preB]. destruct preA as [b [EvalA funcatb]].
destruct preB as [z1 [z2 [JZ [HF0 pre]]]].
destruct (level w) eqn: Hl.
{ apply own.bupd_intro; repeat intro.
  rewrite Hl; constructor. }
rewrite <- Hl in *.
destruct (levelS_age w n) as (w' & Hage & Hw'); auto.

destruct funcatb as [gs [GS funcatb]]; simpl in GS.
unfold func_at, pureat in funcatb. 

assert (Hpsi: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)) by reflexivity.
unfold filter_genv in Hpsi.
remember (construct_rho (filter_genv psi) vx tx) as rho.

set (args := @eval_exprlist CS (snd (split argsig)) bl rho).
set (args' := @eval_exprlist CS' (snd (split argsig)) bl rho).

assert (MYPROP: exists id fs, Map.get (ge_of rho) id = Some b /\ 
         (glob_specs Delta') ! id = Some fs /\ func_at fs (b, 0) w).
{ clear - funcatb funassertDelta' GS.
  assert (XX: exists id:ident, (Map.get (ge_of rho) id = Some b)
                               /\ exists fs, (glob_specs Delta')!id = Some fs).
  { destruct funassertDelta' as [_ FD]. 
    apply (FD b (argsig, retsig) cc _ (necR_refl _)); clear FD.
    simpl. destruct gs. hnf in funcatb. destruct GS as [[? ?] _]; subst. (* destruct GS as [? [? ?]]; subst.*)
    eexists. eapply funcatb. }
  destruct XX as [id [Hb [fs specID]]]; simpl in Hb.

  assert (exists v, Map.get (ge_of rho) id = Some v /\ func_at fs (v, 0) w).
  { destruct funassertDelta' as [funassertDeltaA _].
    destruct (funassertDeltaA id fs _ (necR_refl _) specID) as [v [Hv funcatv]]; simpl in Hv.
    exists v; split; trivial. }
  destruct H as [v [Hv funcatv]].
  assert (VB: b=v); [inversion2 Hb Hv; trivial | subst; clear Hb].
  exists id, fs; auto. }
destruct MYPROP as [id [fs [RhoID [SpecOfID funcatv]]]].
destruct fs as [fsig' cc' A' P' Q' NEP' NEQ'].
unfold func_at in funcatv, funcatb. destruct gs.
hnf in funcatb, funcatv. inversion2 funcatv funcatb.
assert (PREPOST: (forall ts x vl, (! |> (P' ts x vl <=> P0 ts x vl)) w) /\
                 (forall ts x vl, (! |> (Q' ts x vl <=> Q0 ts x vl)) w)).
{ apply inj_pair2 in H3; 
  apply (function_pointer_aux); trivial. f_equal; apply H3. }
clear H3; destruct PREPOST as [Hpre Hpost]. 

fold args in pre. clear Hpsi. remember (construct_rho (filter_genv psi) vx tx) as rho.

assert (typecheck_environ Delta rho) as TC4.
{ clear - TC3 TS.
  destruct TC3 as [TC3 TC4].
  eapply typecheck_environ_sub in TC3; [| eauto].
  auto.
} 
assert (HARGS: args = args').
{ clear - Hage HGG TC4 TC2.
  assert (ARGSEQ: (|> (!! (args = args'))) w).
  { hnf; intros. specialize (TC2 _ H). subst args args'.
    simpl. destruct HGG as [CSUB HGG].
    apply (typecheck_exprlist_sound_cenv_sub CSUB Delta rho TC4 a'). apply TC2. }
  eapply (ARGSEQ w'). apply age_laterR; trivial. }

eapply later_derives in TC2; [|apply (tc_exprlist_sub _ _ _ TS); auto].
eapply later_derives in TC1; [|apply (tc_expr_sub _ _ _ TS); auto].
clear TC4.

assert (TCD': tc_environ Delta' rho) by eapply TC3.

assert (TCARGS: tc_environ (funsig_tycontext (argsig, retsig)) (make_args (map fst argsig) args rho)).
{ assert (LaterW': laterR w w'). constructor; trivial.
  specialize (TC2 _ LaterW'). subst args.
  apply (tc_environ_make_args' argsig retsig bl rho Delta' TCD' _ TC2).  }

clear Heqrho.
destruct GS as [[? ?] GS]; subst fsig' cc'.


assert (HPP: (|> (F0 rho * F rho * P ts x (make_args (map fst argsig) args rho)))%pred w).
{ clear - HF0 pre JZ. rewrite sepcon_assoc, later_sepcon. apply now_later in HF0.
  exists z1, z2;  auto. } clear pre.
rewrite later_sepcon in HPP.
destruct HPP as [w1 [w2 [J [W1 W2]]]]; destruct (join_level _ _ _ J) as [LevW1 LevW2].
destruct (age1_join2 _ J Hage) as [w1' [w2' [J' [Age1 Age2]]]]; destruct (join_level _ _ _ J') as [Lw1' Lw2'].

assert (LA2: laterM w2 w2'). { constructor; trivial. }
specialize (GS ts). hnf in GS.
fold (@dependent_type_functor_rec ts) in *.
specialize (W2 _ LA2). 

specialize (GS x (make_args (map fst argsig) args rho)). hnf in GS.
assert (LW2': (level w >= level w2')%nat). { apply age_level in Age2. destruct (join_level _ _ _ J); omega. }
destruct (join_level _ _ _ JZ) as [Lev_z1 Lev_z2].

destruct GS as [ts1 [x1 [G TSX1]]]. hnf in TSX1. 
destruct (TSX1 _ LW2' _ (necR_refl _)) as [AA BB].
{ split; trivial. }

specialize (Hpre ts1 x1 (make_args (map fst argsig) args rho)).
fold (@dependent_type_functor_rec ts1) in *.
rewrite <- later_unfash in Hpre.
specialize (Hpre _ (age_laterR Hage)).


destruct AA as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [Lu1 Lu2].
hnf in Hpre. destruct (Hpre u2) as [_ HP']; clear Hpre. omega. specialize (HP' _ (necR_refl _) U2).

assert (ArgsW: app_pred (|> (F0 rho * (F rho * G) * P' ts1 x1 (make_args (map (@fst  _ _) argsig)
  (eval_exprlist (snd (split argsig)) bl rho) rho) )) w).
{ clear Hpost funcatv SpecOfID Prog_OK RhoID TC7' RGUARD. rewrite HARGS in *.
  assert (XX: (|> (F0 rho * F rho * G * P' ts1 x1 (make_args (map (@fst  _ _) argsig)
     (eval_exprlist (snd (split argsig)) bl rho) rho) )) w). 
  { rewrite sepcon_assoc. rewrite sepcon_assoc. rewrite <- sepcon_assoc.
    rewrite later_sepcon.
    exists w1, w2; split. trivial. split. trivial. hnf; intros. specialize (age_later_nec _ _ _ Age2 H). intros.
    destruct (nec_join2  JU H0) as [a1' [a2' [JA [A1 A2]]]]; destruct (join_level _ _ _ JA) as [La1 La2].
    exists a1', a2'; split. trivial. split.
    + destruct (nec_refl_or_later _ _ A1); subst. trivial. eapply now_later. apply U1. trivial. 
    + destruct (nec_refl_or_later _ _ A2); subst. trivial. eapply now_later. apply HP'. trivial. }
  clear - XX. rewrite 2 sepcon_assoc. rewrite 2 sepcon_assoc in XX.
  intros u U. destruct (XX _ U) as [u1 [u2 [J [U1 U2]]]]; clear XX.
  exists u1, u2; split; trivial. split; trivial. 
}
apply now_later in  RGUARD.
apply own.bupd_intro; repeat intro; subst. rename H into ORA.
specialize (Hpost ts1 x1).

assert (CSUBpsi:cenv_sub (@cenv_cs CS) psi).
{ destruct HGG as [CSUB' HGG]. apply (cenv_sub_trans CSUB' HGG). }
destruct HGG as [CSUB HGG].

rewrite (typecheck_expr_sound_cenv_sub CSUB Delta' _ TCD' w' a) in EvalA by (apply (TC1 w' (age_laterR  Hage))).
eapply (@semax_call_aux CS') with (F := fun rho => F rho * G)(P:=P')(F0:=F0)(rho:=construct_rho (filter_genv psi) vx tx)
 (ts:=ts1)(x:=x1)(fsig0:=(argsig, retsig));  try eassumption; try trivial.
{ clear - TC1 CSUB; intros w W. apply (tc_expr_cenv_sub CSUB _ _ _ _ (TC1 _ W)) . }
{ clear - Espec TC2 CSUB. intros w W. specialize (TC2 _ W).
  apply (tc_exprlist_cenv_sub CSUB). apply TC2. }

simpl RA_normal; auto. clear ArgsW Hpost RGUARD.
intros rho' l L y Y z YZ [v Z]. exists v.
assert (TRIV: (forall rho, typecheck_temp_environ rho (PTree.empty type)) /\
              (typecheck_var_environ (Map.empty (block * type)) (PTree.empty type)) /\ 
              (forall rho, typecheck_glob_environ rho (PTree.empty type))).
{ clear. split.
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } split. 
  { intros; hnf; intros. split; intros. rewrite PTree.gempty in H; congruence. 
    destruct H. unfold Map.empty, Map.get in H; congruence. } 
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } }
assert (LEV2': (level w2' >= level w2')%nat) by omega. 
assert (LEVz: (level w2' >= level z)%nat). 
{ rewrite Lw2'. apply necR_level in YZ.
  destruct (age_later Hage L).
  + subst l; omega. + apply laterR_level in H; omega. }
destruct ret; simpl.
+ destruct Z as [zz1 [zz2 [JZZ [Z1 Z2]]]]; destruct (join_level _ _ _ JZ) as [Levz1 Levz2]. simpl in Z1, Z2.
  destruct Z1 as [z1_1 [z1_2 [JZ1 [Z11 Z12]]]]; destruct (join_level _ _ _ JZ1) as [Levz11 Levz12].
  destruct (join_assoc JZ1 JZZ) as [y11 [JY1 JY2]]; destruct (join_level _ _ _ JY2) as [_ Levy11].
  assert (LL: (level w2' >= level y11)%nat) by omega. 
  exists z1_1, y11; split; trivial. split; trivial.
  apply (BB (get_result1 i rho') _ LL _ (necR_refl _)).
  simpl; split. { hnf; simpl; intuition. }
  exists z1_2, zz2; auto.
+ destruct Z as [zz1 [zz2 [JZZ [Z1 Z2]]]]; destruct (join_level _ _ _ JZ) as [Levz1 Levz2]. simpl in Z1, Z2.
  destruct Z1 as [z1_1 [z1_2 [JZ1 [Z11 Z12]]]]; destruct (join_level _ _ _ JZ1) as [Levz11 Levz12].
  destruct (join_assoc JZ1 JZZ) as [y11 [JY1 JY2]]; destruct (join_level _ _ _ JY2) as [_ Levy11].
  assert (LL: (level w2' >= level y11)%nat) by omega. 
  exists z1_1, y11; split; trivial. split; trivial. 
  destruct (type_eq retsig Tvoid).
  - subst retsig. 
    apply (BB (globals_only rho') _ LL _ (necR_refl _)).
    simpl; split. hnf; simpl; intuition.
    exists z1_2, zz2; auto.
  - assert (Z22: ((fun rho : environ => EX v : val, Q0 ts1 x1 (env_set (globals_only rho) ret_temp v)) rho') zz2).
    destruct retsig; trivial.  congruence.
    clear Z2; destruct Z22 as [vv Z2]. 
    specialize (BB (env_set (globals_only rho') ret_temp vv) _ LL _ (necR_refl _)); spec BB.
    * simpl; split. hnf; simpl; intuition.
      exists z1_2, zz2; auto.
    *  destruct retsig; try solve [ congruence]; exists vv; trivial.
Qed.

Lemma semax_call_alt {CS Espec}:
 forall Delta (A: TypeTree)
   (P Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
   (NEP: super_non_expansive P) (NEQ: super_non_expansive Q)
     ts x F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
       (fun rho => (|> (tc_expr Delta a rho && tc_exprlist Delta (snd (split argsig)) bl rho))  &&
           (func_ptr_si (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (make_args (map (@fst  _ _) argsig)
                (eval_exprlist (snd (split argsig)) bl rho) rho )))))
         (Scall ret a bl)
         (normal_ret_assert
          (fun rho => (EX old:val, substopt ret old F rho * maybe_retval (Q ts x) retsig ret rho))).
Proof. exact semax_call_si. Qed.

Lemma semax_call_ext {CS Espec}:
   forall (IF_ONLY: False),
     forall Delta P Q ret a tl bl a' bl',
      typeof a = typeof a' ->
      map typeof bl = map typeof bl' ->
      (forall rho,
          !! (typecheck_environ Delta rho) && P rho |--
            tc_expr Delta a rho && tc_exprlist Delta tl bl rho &&
            tc_expr Delta a' rho && tc_exprlist Delta tl bl' rho &&
            !! (eval_expr a rho = eval_expr a' rho /\
                eval_exprlist tl bl rho = eval_exprlist tl bl' rho)) ->
  semax Espec Delta P (Scall ret a bl) Q ->
  @semax CS Espec Delta P (Scall ret a' bl') Q.
Proof.
intros until 2. intro Hbl. intros.
rewrite semax_unfold in H1|-*.
rename H1 into H2. pose proof I.
intros.
assert (HGpsi: cenv_sub (@cenv_cs CS)  psi).
{ destruct HGG as [CSUB HGG]. apply (cenv_sub_trans CSUB HGG). }
specialize (H2 psi Delta' CS' w TS HGG Prog_OK k F f H3 H4).
intros tx vx; specialize (H2 tx vx).
intros ? ? ? ? ?.
specialize (H2 y H5 a'0 H6 H7).
destruct H7 as[[? ?] _].
hnf in H7.
pose proof I.
intros ? J; destruct (H2 _ J) as (? & J' & m' & Hl & Hr & ? & Hsafe); subst.
eexists; split; eauto; exists m'; repeat split; auto.
hnf in Hsafe|-*; intros ?? Hora ??.
specialize (Hsafe ora jm Hora H10).
intros.
spec Hsafe; auto.
spec Hsafe; auto.
simpl in Hsafe.
eapply convergent_controls_jsafe; try apply Hsafe.
reflexivity.
simpl; intros ? ?. unfold cl_after_external. destruct ret0; auto.
reflexivity.
intros.
destruct H8 as [w1 [w2 [H8' [_ ?]]]]. subst m'.
assert (H8'': extendM w2 a'0) by (eexists; eauto). clear H8'.
remember (construct_rho (filter_genv psi) vx tx) as rho.
assert (H7': typecheck_environ Delta rho).
destruct H7; eapply typecheck_environ_sub; eauto.
destruct H7 as [H7 _].
specialize (H0 rho w2 (conj H7' H8)).
destruct H0 as [[[[TCa TCbl] TCa'] TCbl'] [? ?]].
apply (boxy_e _ _ (extend_tc_expr _ _ _) _ _ H8'') in TCa.
apply (boxy_e _ _ (extend_tc_exprlist _ _ _ _) _ _ H8'') in TCbl.
apply (boxy_e _ _ (extend_tc_expr _ _ _) _ _ H8'') in TCa'.
apply (boxy_e _ _ (extend_tc_exprlist _ _ _ _) _ _ H8'') in TCbl'.
eapply denote_tc_resource with (a'1 := m_phi jm) in TCa; auto.
eapply denote_tc_resource with (a'1 := m_phi jm) in TCa'; auto.
eapply denote_tc_resource with (a'1 := m_phi jm) in TCbl; auto.
eapply denote_tc_resource with (a'1 := m_phi jm) in TCbl'; auto.
assert (forall vf, Clight.eval_expr psi vx tx (m_dry jm) a vf
               -> Clight.eval_expr psi vx tx (m_dry jm) a' vf). {
clear - TCa TCa' H7 H7' H0 Heqrho HGG TS HGpsi.
intros.
eapply tc_expr_sub in TCa; [| eauto | eauto].
pose proof (eval_expr_relate _ _ _ _ _ _ jm HGpsi Heqrho H7 TCa).
pose proof (eval_expr_fun H H1). subst vf.
rewrite H0.
eapply eval_expr_relate; eauto.
}
assert (forall tyargs vargs,
             Clight.eval_exprlist psi vx tx (m_dry jm) bl tyargs vargs ->
             Clight.eval_exprlist psi vx tx (m_dry jm) bl' tyargs vargs). {
clear - IF_ONLY TCbl TCbl' H11 Hbl H7' Heqrho HGpsi.
revert bl bl' H11 Hbl TCbl TCbl'; induction tl; destruct bl, bl'; simpl; intros; auto;
 try (clear IF_ONLY; contradiction).
 unfold tc_exprlist in TCbl,TCbl'. simpl in TCbl, TCbl'.
repeat rewrite denote_tc_assert_andp in TCbl, TCbl'.
destruct TCbl as [[TCe ?] ?].
destruct TCbl' as [[TCe0 ?] ?].
inversion H; clear H. subst bl0 tyargs vargs.
inversion Hbl; clear Hbl. rewrite <- H5 in *.
pose proof (eval_expr_relate _ _ _ _ _ _ _ HGpsi Heqrho H7' TCe).
pose proof (eval_expr_fun H H6).
repeat rewrite <- cop2_sem_cast in *.
unfold force_val in H1.
rewrite H9 in *.
subst.
clear H.
unfold_lift in H11.
inv H11.
specialize (IHtl _ _ H9 H8); clear H9 H8.
assert (exists v1, Clight.eval_expr psi vx tx (m_dry jm) e0 v1 /\
                             Cop.sem_cast v1 (typeof e0) ty (m_dry jm) = Some v2). {
 clear - IF_ONLY H4 H6 H7 TCe H0 TCe0 H2 HGpsi H7'.
   contradiction IF_ONLY.  (* still some work to do here *)
}
destruct H as [v1 [? ?]]; 
econstructor; try eassumption.
eapply IHtl; eauto.
}
destruct H12; split; auto.
inv H12.
eapply step_call; eauto.
rewrite <- H; auto.
destruct H24 as [H24 | H24]; inv H24.
destruct H24 as [H24 | H24]; inv H24.
Qed.

Definition cast_expropt {CS} (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (@eval_expr CS (Ecast e' t))  | None => `None end.

(*
Lemma call_cont_current_function:
  forall {k i f e t l}, call_cont k = Kcall i f e t :: l -> current_function k = Some f.
Proof. intros. induction k; try destruct a; simpl in *; inv H; auto.
Qed.
*)

Definition tc_expropt {CS} Delta (e: option expr) (t: type) : environ -> mpred :=
   match e with None => `!!(t=Tvoid)
                     | Some e' => @denote_tc_assert CS (typecheck_expr Delta (Ecast e' t))
   end.

Lemma tc_expropt_char {CS} Delta e t: @tc_expropt CS Delta e t =
                                      match e with None => `!!(t=Tvoid)
                                              | Some e' => @tc_expr CS Delta (Ecast e' t)
                                      end.
Proof. reflexivity. Qed.

Lemma RA_return_castexpropt_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta rho (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- !!(@cast_expropt CS ret t rho = @cast_expropt CS' ret t rho).
Proof.
  intros w W. simpl. unfold tc_expropt in W. destruct ret. 
  + simpl in W. simpl.
    unfold force_val1, liftx, lift; simpl. rewrite denote_tc_assert_andp in W. destruct W.
    rewrite <- (typecheck_expr_sound_cenv_sub CSUB Delta rho D w); trivial.
  + simpl in W; subst. simpl; trivial.
Qed.

Lemma tc_expropt_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta rho (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- @tc_expropt CS' Delta ret t rho.
Proof.
  intros w W. simpl. rewrite  tc_expropt_char in W; rewrite tc_expropt_char.
  specialize (tc_expr_cenv_sub CSUB); intros.
  destruct ret; trivial; auto.
Qed.

Lemma tc_expropt_cspecs_sub {CS CS'} (CSUB: cspecs_sub CS CS') Delta rho (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- @tc_expropt CS' Delta ret t rho.
Proof.
  destruct CSUB as [CSUB _].
  apply (@tc_expropt_cenv_sub _ _ CSUB _ _ D).     
Qed.

Lemma tc_expropt_sub {CS} Delta Delta' rho (TS:tycontext_sub Delta Delta') (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- @tc_expropt CS Delta' ret t rho.
Proof.
  intros w W. rewrite  tc_expropt_char in W; rewrite tc_expropt_char.
  specialize (tc_expr_sub _ _ _ TS); intros.
  destruct ret; [ eapply H; assumption | trivial]. 
Qed.

Lemma  semax_return {CS Espec}:
   forall Delta R ret,
      @semax CS Espec Delta
                (fun rho => tc_expropt Delta ret (ret_type Delta) rho &&
                             RA_return R (cast_expropt ret (ret_type Delta) rho) rho)
                (Sreturn ret)
                R.
Proof.
  intros.
  hnf; intros.
  rewrite semax_fold_unfold.
  intros psi Delta' CS'.
  apply prop_imp_i. intros [TS [CSUB HGG]].
  replace (ret_type Delta) with (ret_type Delta')
    by (destruct TS as [_ [_ [? _]]]; auto).
  apply derives_imp.
  clear n.
  intros w ? k F f.
  intros w' ? ?. 
  clear H.
  clear w H0.
  rename w' into w.
  destruct H1.
  do 3 red in H.
  intros te ve.
  intros n ? w' ? ?.
  assert (necR w (level w')).
  {
    apply nec_nat.
    apply necR_level in H2.
    apply le_trans with (level n); auto.
  }
  apply (pred_nec_hereditary _ _ _ H4) in H0.
  clear w n H2 H1 H4.
  destruct H3 as [[H3 ?] ?].
  pose proof I.
  remember ((construct_rho (filter_genv psi) ve te)) as rho.
  assert (H1': ((F rho * proj_ret_assert R EK_return (cast_expropt ret (ret_type Delta') rho) rho))%pred w').
  { 
    eapply sepcon_derives; try apply H1; auto. (*apply andp_left2. simpl. destrforget (ret_type Delta') as t.*)
    intros w [W1 W2]. simpl in H3; destruct H3 as [TCD' _].
    assert (TCD: typecheck_environ Delta rho) by (eapply typecheck_environ_sub; eauto). 
    apply (tc_expropt_sub _ _ _ TS) in W1; trivial.
(*    apply (tc_expropt_cenv_sub CSUB _ _ TCD) in W1. *)
    rewrite <- (RA_return_castexpropt_cenv_sub CSUB Delta' rho TCD' _ _ _ W1); trivial.
  }
  assert (TC: (tc_expropt Delta ret (ret_type Delta') rho) w').
  {
    simpl in H3; destruct H3 as [TCD' _].
    clear - H1 TCD' TS CSUB Espec. 
    assert (TCD: typecheck_environ Delta rho) by (eapply typecheck_environ_sub; eauto); clear TS.
    destruct H1 as [w1 [w2 [? [? [? ?]]]]].
    apply (tc_expropt_cenv_sub CSUB) in H1; trivial.
    rewrite tc_expropt_char; rewrite tc_expropt_char in H1. destruct ret; [ |trivial].
    apply (boxy_e _ _ (extend_tc_expr _ _ _) w2); auto.
    exists w1; auto.
  }
  clear H1; rename H1' into H1.
  specialize (H0 EK_return (cast_expropt ret (ret_type Delta') rho) te ve).
  specialize (H0 _ (le_refl _) _ (necR_refl _)).
  spec H0.
  {
    rewrite <- Heqrho.
    rewrite proj_frame_ret_assert.
    split; auto.
    split; auto.
    rewrite seplog.sepcon_comm; auto.
  }
  unfold tc_expropt in TC; destruct ret; simpl in TC.
  + eapply own.bupd_mono, bupd_denote_tc, H0; eauto.
    clear TC; intros ? [TC Hsafe] ?? Hora ??.
    specialize (Hsafe ora jm Hora (eq_refl _) H6).
    intros. subst a.
    specialize (Hsafe LW e (eval_expr e rho)).
    destruct H3 as [H3a [H3b H3c]].
    rewrite H3c in Hsafe,TC.
    rewrite denote_tc_assert_andp in TC; destruct TC as [?TC ?TC].
    spec Hsafe.
    eapply eval_expr_relate; eauto.
    eapply tc_expr_sub; try eassumption.
    eapply typecheck_environ_sub; try eassumption.
    spec Hsafe. {
    rewrite cop2_sem_cast'; auto.
    2:{ eapply typecheck_expr_sound; eauto.
    eapply tc_expr_sub; try eassumption.
    eapply typecheck_environ_sub; try eassumption.
    }
    eapply cast_exists; eauto.
    eapply tc_expr_sub; try eassumption.
    eapply typecheck_environ_sub; try eassumption.
   }
    clear - Hsafe.
    eapply convergent_controls_jsafe; try apply Hsafe; auto.
    intros ? ? [? ?]; split; auto.
    inv H.
    1,3: destruct H9; discriminate.
    rewrite call_cont_idem.
    econstructor; eauto.
  + eapply own.bupd_mono, H0; eauto.
    intros ? Hsafe ?? Hora ???.
    specialize (Hsafe ora jm Hora (eq_refl _) H6 LW).
     simpl in Hsafe.
    eapply convergent_controls_jsafe; try apply Hsafe; auto.
    intros.
    destruct H7; split; auto.
    inv H7.
    1,3: destruct H17; discriminate.
    rewrite call_cont_idem.
    econstructor; eauto.
Qed.
