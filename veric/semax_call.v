Require Import Coq.Logic.FunctionalExtensionality.
Require Import VST.veric.juicy_base.
Require Import VST.msl.normalize.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_new.
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

Local Open Scope pred.
Section extensions.
Context {CS: compspecs} {Espec: OracleKind}.

(* Scall *)

Lemma opt2list_inj: forall A (a b: option A), opt2list a = opt2list b -> a=b.
Proof.
destruct a; destruct b; intros; inv H; auto.
Qed.

Lemma unlater_writable:
  forall m m', laterR m m' ->
            forall loc, writable loc m' -> writable loc m.
Proof.
induction 1; intros; auto.
hnf in *.
simpl in H0.
assert (match y @ loc with
     | YES sh rsh k _ => writable_share sh /\ isVAL k
     | _ => False
     end) by (destruct (y @ loc); eauto).
clear H0.
revert H1; case_eq (y @ loc); intros; try contradiction.
destruct H1; subst.
destruct (rmap_unage_YES _ _ _ _ _ _ _ H H0).
rewrite H3; simpl; auto.
Qed.

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

(*Lenb: moved alloc_juicy_variables, juicy_mem_alloc_core, and 
  alloc_juicy_variables_e here from to veric/juicy_mem_ops.v*)

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
intros id fs w2 Hw2 H3.
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

intros loc fs w2 Hw2 H6.
specialize (H2 loc fs _ (necR_refl _)).
spec H2.
clear - Hw2 CORE H6.
destruct fs; simpl in *.
destruct H6 as [pp H6].
 rewrite <- resource_at_approx.
case_eq (w @ (loc,0)); intros.
assert (core w @ (loc,0) = resource_fmap (approx (level (core w))) (approx (level (core w))) (NO _ bot_unreadable)).
 rewrite <- core_resource_at.
simpl; erewrite <- core_NO; f_equal; eassumption.
pose proof (necR_resource_at _ _ _ _ CORE H0).
pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
rewrite <- core_resource_at in H2; rewrite H6 in H2;
 rewrite core_PURE in H2; inv H2.
assert (core w @ (loc,0) = resource_fmap (approx (level (core w))) (approx (level (core w))) (NO _ bot_unreadable)).
 rewrite <- core_resource_at.
simpl; erewrite <- core_YES; f_equal; eassumption.
pose proof (necR_resource_at _ _ _ _ CORE H0).
pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
rewrite <- core_resource_at in H2; rewrite H6 in H2;
 rewrite core_PURE in H2; inv H2.
pose proof (resource_at_approx w (loc,0)).
pattern (w @ (loc,0)) at 1 in H0; rewrite H in H0.
symmetry in H0.
assert (core (w @ (loc,0)) = core (resource_fmap (approx (level w)) (approx (level w))
       (PURE k p))) by (f_equal; auto).
rewrite core_resource_at in H1.
assert (core w @ (loc,0) =
        resource_fmap (approx (level (core w))) (approx (level (core w)))
         (PURE k p)).
 rewrite H1.  simpl. rewrite level_core; rewrite core_PURE; auto.
pose proof (necR_resource_at _ _ _ _ CORE H2).
 assert (w' @ (loc,0) = resource_fmap
       (approx (level w')) (approx (level w')) (PURE k p)).
 rewrite <- core_resource_at in H3. rewrite level_core in H3.
 destruct (w' @ (loc,0)).
  rewrite core_NO in H3; inv H3.
  rewrite core_YES in H3; inv H3.
  rewrite core_PURE in H3; inv H3.
 reflexivity.
 pose proof (necR_resource_at _ _ _ _ Hw2 H4).
 inversion2 H6 H5.
 exists p. reflexivity.
 
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

Lemma eval_exprlist_relate:
  forall (Delta : tycontext) (fsig0 : funsig)
     (bl : list expr) (psi : genv) (vx : env) (tx : temp_env)
     (rho : environ) m,
   denote_tc_assert (typecheck_exprlist Delta (snd (split (fst fsig0))) bl) rho (m_phi m) ->
   typecheck_environ Delta rho ->
   genv_cenv psi = cenv_cs ->
   rho = construct_rho (filter_genv psi) vx tx ->
   forall f : function,
   fsig0 = fn_funsig f ->
   Clight.eval_exprlist psi vx tx (m_dry m) bl
     (type_of_params (fn_params f))
     (eval_exprlist (snd (split (fst fsig0))) bl rho).
Proof.
  intros.
  destruct fsig0. unfold fn_funsig in *. inversion H3; clear H3; subst l t. simpl in *.
  forget (fn_params f) as vl.
  forget (fn_temps f) as tl.
  clear f.
  clear - H0 H1 H2 H.

 rewrite snd_split. rewrite snd_split in H.
 assert (length (map snd vl) = length bl).
 apply tc_exprlist_length in H; auto.
 revert vl H H3; induction bl; destruct vl; intros; inv H3; simpl.
 constructor.
 destruct p. simpl in *; subst.
 rewrite !denote_tc_assert_andp in H.
 super_unfold_lift.
 destruct H as [[? ?] ?].
 specialize (IHbl _ H3 H5).
 clear - IHbl H3 H H0 H1 H2.
 constructor 2 with (eval_expr a (construct_rho (filter_genv psi) vx tx)); auto.
 eapply eval_expr_relate; eauto.
 pose proof (cast_exists Delta a _ _ _ H0 H H2).
 forget (force_val
          (sem_cast (typeof a) t
             (eval_expr a
                (construct_rho (filter_genv psi) vx tx)))) as v.
 rewrite cop2_sem_cast'; try eassumption.
 eapply typecheck_expr_sound; eassumption.
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
  forall (Delta : tycontext) (bl : list expr) (psi : genv) (vx : env) (tx : temp_env)
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
(*    (glob_types Delta) ! b = Some (type_of_funspec b0) -> *)
    exists b1 : block,
        filter_genv psi b = Some b1 /\
        func_at b0 (b1,0) a')
    (H1: forall (b : block) (b0 : funspec) (a' : rmap),
     necR (m_phi jm') a' ->
     (func_at' b0 (b, 0)) a' ->
     exists (b1 : ident),
       filter_genv psi b1 = Some b /\
       (exists fs : funspec, (glob_specs Delta) ! b1 = Some fs))
   (l : list ident) (l0 : list type)
    (Heqp : (l, l0) = split (fn_params f))
   (TC2 : denote_tc_assert (typecheck_exprlist Delta l0 bl)
        (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)) (m_phi jm)) (**)
   (H21 : bind_parameter_temps (fn_params f)
        (eval_exprlist l0 bl
           (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)))
        (create_undef_temps (fn_temps f)) = Some te')
   (TE : typecheck_environ
        Delta (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx))),
   typecheck_environ
    (mk_tycontext
      (make_tycontext_t (fn_params f) (fn_temps f))
      (make_tycontext_v (fn_vars f))
      (fn_return f)  (glob_types Delta) (glob_specs Delta) (annotations Delta))
     (mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).
Proof.
 intros.
 pose (rho3 := mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).

unfold typecheck_environ. repeat rewrite andb_true_iff.
split3.
*
clear H H1 H15.
unfold typecheck_temp_environ in *. intros. simpl.
unfold temp_types in *. simpl in *.
apply func_tycontext_t_sound in H; auto.
 clear - H21 H TC2 TC3 Heqp H17 TE.

destruct H. (*in params*)
forget (create_undef_temps (fn_temps f)) as temps.
generalize dependent temps.
generalize dependent l. generalize dependent l0.
generalize dependent bl. generalize dependent te'.
{  induction (fn_params f); intros.
   + inv H.
   + simpl in *.
     destruct a. simpl in *. remember (split l). destruct p.
     simpl in *. destruct H.
      - clear IHl. destruct bl. inv H.  inv Heqp. inv TC2.
        inv H. inv Heqp. simpl in *.
        rewrite !denote_tc_assert_andp in TC2.
        simpl in *; super_unfold_lift.
        destruct TC2 as [[? ?] ?].
        rewrite (pass_params_ni _ _ id _ _ H21) by (inv H17; contradict H4; apply in_app; auto).
        rewrite PTree.gss.
        eexists.  split. reflexivity. apply tc_val_tc_val'.
        eapply tc_val_sem_cast; eauto.
      - inv Heqp. destruct bl. inv TC2. inv H17. simpl in TC2.
        repeat (rewrite tc_andp_sound in TC2; simpl in TC2; super_unfold_lift).
        destruct TC2 as [[? ?] ?]. assert (i <> id). intro. subst.
        apply H2. apply in_or_app. left. apply in_map with (f := fst) in H. apply H.
        remember (eval_exprlist (t :: l3) (e :: bl)
            (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx))).
        destruct l0; inv H21. simpl in Heql0.
        super_unfold_lift. inv Heql0.
        eapply IHl; eauto.
}

(*In temps*)
apply list_norepet_app in H17. destruct H17 as [? [? ?]].
generalize dependent (fn_params f). generalize dependent bl.
generalize dependent l0. generalize dependent l. generalize dependent te'.

induction (fn_temps f); intros.
inv H.

simpl in *. destruct H. destruct a. inv H. simpl in *.
clear IHl. exists Vundef. simpl in *. split; [| hnf; congruence]. inv H1.
assert (In id (map fst (l2)) -> False).
intros.
unfold list_disjoint in *. eapply H2. eauto. left. auto. auto.
eapply pass_params_ni with (id := id) in H21; auto.  rewrite PTree.gss in *. auto.


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
apply H2. auto. right. auto. apply Heqp. auto.
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

Lemma stackframe_of_freeable_blocks:
  forall Delta f rho ge ve,
      genv_cenv ge = cenv_cs ->
      Forall (fun it => complete_type cenv_cs (snd it) = true) (fn_vars f) ->
      list_norepet (map fst (fn_vars f)) ->
      ve_of rho = make_venv ve ->
      guard_environ (func_tycontext' f Delta) (Some f) rho ->
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
(* case_eq (type_is_volatile ty); intros; simpl negb; cbv iota; *)
 unfold memory_block. normalize. {
(* rewrite andp_assoc; apply derives_extract_prop; intros. *)
(* apply derives_extract_prop; intros. *)
  rename H6 into H99.
 normalize. (* don't know why we cannot do normalize at first *)
 rewrite memory_block'_eq.
 2: rewrite Ptrofs.unsigned_zero; omega.
 2:{
 rewrite Ptrofs.unsigned_zero. rewrite Zplus_0_r.
 rewrite Coqlib.nat_of_Z_eq.
 change (Ptrofs.unsigned Ptrofs.zero) with 0 in H99.
 omega.
 pose proof (sizeof_pos ty); omega.
}
 rewrite Z.sub_0_r.
 unfold memory_block'_alt.
 rewrite if_true by apply readable_share_top.
 rewrite Coqlib.nat_of_Z_eq.
 + rewrite HGG. auto.
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

Lemma can_free_list:
  forall Delta F f jm ge ve te
  (NOREP: list_norepet (map (@fst _ _) (fn_vars f)))
  (COMPLETE: Forall (fun it => complete_type cenv_cs (snd it) = true) (fn_vars f))
  (HGG:  genv_cenv ge = cenv_cs),
   guard_environ (func_tycontext' f Delta) (Some f)
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
  (*destruct (type_is_volatile t) eqn:?; try (simpl in H3; tauto).*)
  simpl in H3; destruct H3 as [H99 H3].
  change nat_of_Z with Z.to_nat in H3.
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
    rewrite HGG.
    rewrite H8. auto.
Qed.

Lemma necR_m_dry':
  forall jm jm', m_dry jm = m_dry jm' ->
                (necR (m_phi jm) (m_phi jm')) ->
            necR jm jm'.
Proof.
intros.
remember (m_phi jm) as phi.
remember (m_phi jm') as phi'.
unfold necR in *.
rewrite clos_rt_rt1n_iff in *.
revert jm jm' Heqphi Heqphi' H; induction H0; intros; subst.
replace jm' with jm. constructor 1.
apply juicy_mem_ext; auto.
destruct (can_age_jm jm) as [jm1 ?].
destruct (age1 (m_phi jm)) eqn:?; congruence.
constructor 2 with jm1; auto.
apply age1_juicy_mem_unpack in H2. destruct H2.
apply IHclos_refl_trans_1n.
hnf in H,H2. congruence.
congruence.
congruence.
Qed. (* maybe don't need this? *)

Lemma age_juicy_mem_i:
  forall jm jm', m_dry jm = m_dry jm' ->
        age (m_phi jm) (m_phi jm') ->
       age jm jm'.
Proof.
intros.
hnf in H0 |-*.
unfold age1; simpl.
apply age1_juicy_mem_unpack'; auto.
Qed. (* maybe don't need this? *)

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
intros.
unfold funassert.
intros w [? ?]; split.
clear H2; intro id. rewrite <- (H id), <- H0; auto.
intros loc fs w' Hw' H4; destruct (H2 loc fs w' Hw' H4)  as [id H3].
exists id; rewrite <- (H id), <- H0; auto.
intros.
apply pred_ext; apply H; intros; auto.
Qed.

Lemma semax_call_external:
forall (Delta : tycontext) (A : TypeTree)
  (P Q Q' : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
  (F : environ -> pred rmap) (F0 : assert)
  (ret : option ident) (params : list (ident * type)) (retty : type) cc
  (a : expr) (bl : list expr) (R : ret_assert) (psi : genv) (vx : env)
  (tx : temp_env) (k : cont) (rho : environ) (ora : OK_ty) (jm : juicy_mem)
  (b : block)
 (TC0 : Cop.classify_fun (typeof a) =
      Cop.fun_case_f (type_of_params params) retty cc)
 (TCret : tc_fn_return Delta ret retty)
 (TC1 : (|> tc_expr Delta a rho) (m_phi jm))
 (TC2 : (|> tc_exprlist Delta (map snd params) bl rho) (m_phi jm))
 (TC3 : guard_environ Delta (current_function k) rho)
 (TC5 : retty = Tvoid -> ret = None)
 (H : closed_wrt_modvars (Scall ret a bl) F0)
 (HR : RA_normal R =
     (fun rho0 : environ =>
      EX  old : val,
      substopt ret old F rho0 * maybe_retval (Q ts x) retty ret rho0))
 (HGG:  genv_cenv psi = cenv_cs)
 (H0 : rho = construct_rho (filter_genv psi) vx tx)
 (H3 : eval_expr a rho = Vptr b Ptrofs.zero)
 (H4 : (funassert Delta rho) (m_phi jm))
 (H1 : (rguard Espec psi Delta
        (frame_ret_assert R F0) k) (level (m_phi jm)))
 (H11 : forall vl : environ, (!|>(Q' ts x vl <=> Q ts x vl)) (m_phi jm))
 (H14 : (|>(F0 rho * F rho *
          P ts x
            (make_args (map fst params)
               (eval_exprlist (map snd params) bl rho) rho))) (m_phi jm))
 (n : nat)
 (H2 : level (m_phi jm) = S n)
 (H15 : (believe_external Espec psi (Vptr b Ptrofs.zero) (params, retty) cc A P Q')
        (level (m_phi jm))),
 exists (c' : corestate) (m' : juicy_mem),
  jstep (cl_core_sem psi) (State vx tx (Kseq (Scall ret a bl) :: k)) jm c' m' /\
  jm_bupd ora (jsafeN OK_spec psi n ora c') m'.
Proof.
intros.
destruct TC3 as [TC3 TC3'].
rewrite <- snd_split in TC2.
rewrite <- level_juice_level_phi in H2.
destruct (levelS_age1 _ _ H2) as [jm' Hage].
specialize (TC1 (m_phi jm') (t_step _ _ _ _ (age_jm_phi Hage))).
specialize (TC2 (m_phi jm') (t_step _ _ _ _ (age_jm_phi Hage))).
assert (H21 := eval_exprlist_relate Delta (params,retty) bl psi vx tx _
      jm' TC2 TC3 HGG H0
      (mkfunction retty cc params nil nil Sskip)
      (eq_refl _)). simpl in H21.
rewrite snd_split in TC2.

unfold believe_external in H15.
destruct (Genv.find_funct psi (Vptr b Ptrofs.zero)) eqn:H22; try (contradiction H15).
destruct f eqn:Ef; try (contradiction H15).

destruct H15 as [[H5 H15] Hretty]. hnf in H5.
destruct H5 as [H5 [H5' [Eef Hlen]]]. subst c.
inversion H5. subst t0. rename t into tys. subst rho.
specialize (H15 psi ts x n).
spec H15; [constructor 1; rewrite <- level_juice_level_phi, H2; constructor | ].
specialize (H15
  (F0 (construct_rho (filter_genv psi) vx tx) *
          F (construct_rho (filter_genv psi) vx tx))
   (typlist_of_typelist tys)
  (eval_exprlist (snd (split params)) bl
                  (construct_rho (filter_genv psi) vx tx))
   jm').
spec H15; [ apply age_level in Hage; omega | ].
specialize (H15 _ (necR_refl _)).
spec H15. { clear H15.
assert ((|> (P ts x
      (make_ext_args (filter_genv psi) (map fst params)
         (eval_exprlist (snd (split params)) bl
            (construct_rho (filter_genv psi) vx tx))) *
    (F0 (construct_rho (filter_genv psi) vx tx) *
     F (construct_rho (filter_genv psi) vx tx)))) (m_phi jm)). {
eapply later_derives; try apply H14.
rewrite sepcon_comm.
apply sepcon_derives; auto.
apply derives_refl'. f_equal.
rewrite H7 in TC2.
clear - TC2 H7 Hlen.
revert bl tys TC2 H7 Hlen; induction params; destruct bl; simpl; intros; auto.
{ destruct tys; try congruence.
simpl in Hlen. destruct a. destruct (split params). inv Hlen.
destruct a. revert TC2. case_eq (split params). intros l1 l2 Heq. simpl.
  intros; inv TC2.
}
destruct tys.
simpl in Hlen. destruct a. destruct (split params). inv Hlen.
destruct a. revert TC2. case_eq (split params). intros l1 l2 Heq.
  simpl in *. intros TC2.
unfold tc_exprlist in TC2; simpl in TC2.
repeat rewrite denote_tc_assert_andp in TC2.
destruct TC2 as [[? ?] ?].
inversion H7.
rewrite Heq in *. simpl in *.
specialize (IHparams _ _ H1). spec IHparams. inv H3; auto.
rewrite IHparams; auto.
}
simpl.
rewrite fst_split.
split.
{ (* typechecking arguments *)
  rewrite Eef; simpl.
  clear -TC2 TC3.
  revert bl TC2.
  induction params. now auto.
  destruct a as (id, ty).
  intros [ | b bl] TC2.
  - rewrite snd_split in *.
    simpl in *.
    inversion TC2.
  - rewrite snd_split.
    simpl in *.
    unfold tc_exprlist in *.
    simpl in TC2.
    repeat rewrite denote_tc_assert_andp in TC2.
    destruct TC2 as ((tcb & tcb') & tcbl).
    split.
    + pose proof tc_val_sem_cast _ _ _ _ _ TC3 tcb tcb' as tc.
      apply tc_val_has_type.
      auto.
    + rewrite <-snd_split.
      apply (IHparams bl).
      apply tcbl.
}
apply H0.
constructor 1.
apply age_jm_phi; auto.
}
clear H14 TC2.
destruct H15 as [x' H15].
specialize (H15 ora).
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
eexists; exists jm'.
split.
econstructor.
rewrite (age_jm_dry Hage).
eapply step_call_external; try eassumption.
eapply eval_expr_relate; try eassumption.
reflexivity.
rewrite H3.
rewrite H22.
rewrite Hty. reflexivity.
split.
apply age1_resource_decay; auto.
split; [apply age_level; auto|].
apply age1_ghost_of, age_jm_phi; auto.
apply jm_bupd_intro.
destruct n as [ | n ].
constructor.
eapply jsafeN_external with (x0 := x'); eauto.
reflexivity.
rewrite Eef. subst tys. assumption.
intros.
specialize (H15 ret0 z').
change ((ext_spec_post' Espec e x' (genv_symb_injective psi) (opttyp_of_type retty) ret0 z' >=>
        juicy_mem_op
          (Q' ts x (make_ext_rval  (filter_genv psi) ret0) *
              (F0 (construct_rho (filter_genv psi) vx tx) *
               F (construct_rho (filter_genv psi) vx tx)))) (level jm')) in H15.
assert (level jm' > level m')%nat.
{
 destruct H6 as (?&?&?); auto.
}
apply (pred_nec_hereditary _ _ (level m')) in H15;
 [ | apply nec_nat; omega].
rewrite Eef in *.
specialize (H15 m' (le_refl _) _ (necR_refl _) H8).

pose (tx' := match ret,ret0 with
                   | Some id, Some v => PTree.set id v tx
                   | _, _ => tx
                   end).

specialize (H1 EK_normal None tx' vx (m_phi m')).
spec H1.
{ clear - Hage H9.
  change (level jm >= level m')%nat.
  apply age_level in Hage. omega.
}
rewrite proj_frame_ret_assert in H1.
simpl proj_ret_assert in H1.
rewrite HR in H1; clear R HR.
simpl exit_cont in H1.
do 3 red in H5.
specialize (H1 _ (necR_refl _)).

assert (Htc: tc_option_val retty ret0).
{clear - TCret TC3 H0 TC5 H15 Hretty Hretty0 H6 H9 Hage.
 destruct H15 as [phi1 [phi2 [Ha [Hb Hc]]]].
 specialize (Hretty ts x ret0 phi1).
 spec Hretty.
 { apply join_level in Ha. destruct Ha as [? ?].
   rewrite H. cut ((level jm > level jm')%nat). intros.
   simpl. unfold natLevel. do 2 rewrite <-level_juice_level_phi. omega.
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
 destruct (current_function k); auto.
*
do 3 red in H15.
rewrite (sepcon_comm (F0 _)) in H15.
rewrite <- sepcon_assoc in H15.
assert (H15': ((!!tc_option_val retty ret0 && Q ts x (make_ext_rval (filter_genv psi) ret0)) *
       F (construct_rho (filter_genv psi) vx tx) *
       F0 (construct_rho (filter_genv psi) vx tx))%pred (m_phi m')). {
rewrite sepcon_assoc in H15|-*.
destruct H15 as [w1 [w2 [? [? ?]]]]; exists w1; exists w2; split3; auto.
clear - H1 H9 H10 H11 Hage Hretty Hretty0.
specialize (H11 (make_ext_rval (filter_genv psi) ret0) (level (m_phi jm'))).
specialize (Hretty ts x ret0 w1).
spec H11.
constructor 1.
repeat rewrite <- level_juice_level_phi.
apply age_level in Hage. rewrite Hage.
reflexivity.
spec Hretty.
repeat rewrite <- level_juice_level_phi.
apply age_level in Hage. rewrite Hage.
apply join_level in H1. destruct H1.
rewrite H. change (S (level jm') >= level m')%nat.
omega.
split.
apply Hretty; auto. split; auto.
destruct (H11 w1) as [? _].
apply join_level in H1. destruct H1.
rewrite <- level_juice_level_phi in *.
omega.
apply H; auto.
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
unfold Map.set,Map.get, make_tenv in H10 |- *; rewrite H10.
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
unfold modifiedvars; simpl.
destruct ret; simpl; auto.
destruct (ident_eq i0 i).
subst.
left. unfold insert_idset. rewrite PTree.gss; apply I.
right.
unfold Map.get, make_tenv.
destruct ret0; auto.
rewrite PTree.gso by auto.
auto.
*
assert (H4': (funassert Delta (construct_rho (filter_genv psi) vx tx)) (m_phi m')).
{ clear - Hage H6 H4.
destruct H6 as (?&?&?).
destruct H4.
assert (Hnec: necR (m_phi jm) (m_phi jm')). {
  cut (age jm jm'). intro Hx.
  constructor. apply age_jm_phi in Hx; auto. eauto.
}
split.
* intros id fs ???.
specialize (H2 id fs (m_phi jm')).
specialize (H2 Hnec); spec H2; auto.
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
* intros b fs ???.
specialize (H3 b fs (m_phi jm')).
specialize (H3 Hnec); spec H3; auto.
destruct H1 as [H1 H1'].
specialize (H1' (b,0)).
destruct fs; simpl in *.
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
pose proof (resource_at_approx (m_phi jm') (b,0)).
rewrite H6 in H; simpl in H.
injection H; intro. symmetry in H7. apply H7.
}
match type of H4' with ?A => match goal with |- ?B => replace B with A; auto end end.
}
exists
match ret0 with
| Some v =>
    match ret with
    | Some id => (State vx (PTree.set id v tx) k)
    | None => (State vx tx k) (* bogus *)
    end
| None => match ret with
          | Some _ => (State vx tx k) (* bogus *)
          | None => (State vx tx k)
          end
end.
split.
unfold cl_after_external.
revert Htc TC5.
destruct (type_eq retty Tvoid).
+ subst retty. simpl. destruct ret0; try solve[inversion 1].
  intros _. intros X; spec X; auto. rewrite X; auto.
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
destruct ret; destruct ret0; apply assert_safe_jsafe; auto.
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
(*  rewrite (juicy_mem_alloc_core _ _ _ _ _ H) in H1. *)
(*  rewrite H2 in H1. *)
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

Lemma make_args_close_precondition:
  forall params args ge ve te m tx ve' te' m' P vars,
    list_norepet (map fst params) ->
    bind_parameter_temps params args tx = Some te' ->
    alloc_juicy_variables ge empty_env m vars = (ve', m') ->
    P (make_args (map fst params) args (construct_rho (filter_genv ge) ve te))
   |-- close_precondition params vars P (construct_rho (filter_genv ge) ve' te').
Proof.
intros.
intros phi ?.
exists (Map.empty (block * type)).
assert (exists e : temp_env,
    forall i, e ! i = if in_dec ident_eq i (map fst params) then te' ! i else None). {
 clear - H H0.
 revert args tx H H0; induction params as [ | [? ?]]; destruct args; intros; simpl in *; inv H0.
 exists empty_tenv; intros; apply PTree.gempty.
 inv H.
 destruct (IHparams _ _ H4 H2) as [e ?]; clear IHparams.
 exists (PTree.set i v e); intro j; specialize (H j).
 destruct (ident_eq i j). subst.
 symmetry.
 rewrite PTree.gss.
 assert ((PTree.set j v tx) ! j = Some v) by (apply PTree.gss).
 forget (PTree.set j v tx) as tz.
 clear - H0 H2 H3; revert args tz H0 H2; induction params as [ | [? ? ]]; destruct args; intros; simpl in *; inv H2; auto.
 apply IHparams with args (PTree.set i v0 tz); auto.
 rewrite PTree.gso; auto.
 rewrite PTree.gso by auto.
 destruct (in_dec ident_eq j (map fst params)); auto.
}
destruct H3 as [e ?].
exists (fun i => e!i).
split3; intros.
*
unfold Map.get.
simpl. specialize (H3 i). rewrite if_true in H3 by auto. auto.
*
simpl.
 destruct (in_dec ident_eq i (map fst vars)).
 auto.
 right.
 unfold Map.get, Map.empty.
 symmetry.
 clear - H1 n.
 unfold make_venv.
 assert (empty_env ! i = None) by apply PTree.gempty.
 forget empty_env as ve.
 revert ve m H H1; induction vars as [ | [? ?]]; intros. inv H1; auto.
 spec IHvars. contradict n. right; auto.
 unfold alloc_juicy_variables in H1; fold alloc_juicy_variables in H1.
 destruct (juicy_mem_alloc m 0 (@sizeof ge t)).
 eapply IHvars; try apply H1.
 rewrite PTree.gso; auto.
 contradict n. left. auto.
*
 simpl.
 replace (mkEnviron (filter_genv ge) (Map.empty (block * type)) (fun i : positive => e ! i))
   with  (make_args (map fst params) args (construct_rho (filter_genv ge) ve te)); auto.
 replace (fun i : positive => e ! i)
  with (fun i => if in_dec ident_eq i (map fst params) then te' ! i else None)
   by (extensionality j; auto).
 clear - H H0.
 change (filter_genv ge) with (ge_of (construct_rho (filter_genv ge) ve te)) at 2.
 forget (construct_rho (filter_genv ge) ve te) as rho. clear - H H0.
 revert args tx rho H H0; induction params as [ | [? ? ]]; destruct args; intros; inv H0.
 reflexivity.
 simpl.
 inv H.
 rewrite (IHparams args (PTree.set i v tx) rho); auto.
 unfold env_set. simpl.
 f_equal. unfold Map.set; extensionality j.
 destruct (ident_eq j i). subst.
 rewrite if_true by auto.
 clear - H2 H3.
 symmetry.
 replace (Some v) with ((PTree.set i v tx) ! i) by (rewrite PTree.gss; auto).
 forget (PTree.set i v tx) as tz.
 revert args tz H2 H3; induction params as [ | [? ? ]]; destruct args; intros; inv H2; auto.
 rewrite (IHparams args (PTree.set i0 v0 tz)); auto. apply PTree.gso; auto.
 contradict H3; left; auto. contradict H3; right; auto.
 destruct (ident_eq i j); try congruence.
 destruct (in_dec ident_eq j (map fst params)); auto.
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
2: rewrite Coqlib.nat_of_Z_eq; omega.
unfold memory_block'_alt.
rewrite if_true by apply readable_share_top.
split.
intro loc. hnf.
rewrite Coqlib.nat_of_Z_eq by omega.
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

Lemma alloc_juicy_variables_lem2:
  forall jm f (ge: genv) ve te jm' (F: pred rmap)
      (HGG:  genv_cenv ge = cenv_cs)
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
(*assert (Hmatch := alloc_juicy_variables_match_venv _ _ _ _ H0). *)
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
(* pose proof (juicy_mem_alloc_succeeds _ _ _ _ _ H2). *)
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
rewrite <- HGG.
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

Lemma semax_call_aux:
 forall (Delta : tycontext)
  (A : TypeTree)
  (P Q Q' : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: super_non_expansive P) (NEQ': super_non_expansive Q')
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
  (F : environ -> pred rmap)
  (F0 : assert) (ret : option ident) (fsig0 : funsig) cc (a : expr)
  (bl : list expr) (R : ret_assert) (psi : genv) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)
  (ora : OK_ty) (jm : juicy_mem) (b : block) (id : ident),
   Cop.classify_fun (typeof a) =
   Cop.fun_case_f (type_of_params (fst fsig0)) (snd fsig0) cc ->
   tc_fn_return Delta ret (snd fsig0) ->
   (|>tc_expr Delta a rho) (m_phi jm) ->
   (|>tc_exprlist Delta (snd (split (fst fsig0))) bl rho) (m_phi jm) ->
    (*map typeof bl = map (@snd _ _) (fst fsig) ->*)
    guard_environ Delta (current_function k) rho ->
    (snd fsig0 =Tvoid -> ret=None) ->
    closed_wrt_modvars (Scall ret a bl) F0 ->
    RA_normal R = (fun rho0 : environ => EX old:val, substopt ret old F rho0 * maybe_retval (Q ts x) (snd fsig0) ret rho0) ->
(*    Forall (fun it => complete_type (composite_types Delta) (snd it) = true) (fn_vars (snd fsig)) ->*)
    genv_cenv psi = cenv_cs ->
    rho = construct_rho (filter_genv psi) vx tx ->
    (*filter_genv psi = ge_of rho ->*)
    eval_expr a rho = Vptr b Ptrofs.zero ->
    (funassert Delta rho) (m_phi jm) ->
    (rguard Espec psi Delta (frame_ret_assert R F0) k) (level (m_phi jm)) ->
    (believe Espec Delta psi Delta) (level (m_phi jm)) ->
    (glob_specs Delta)!id = Some (mk_funspec fsig0 cc A P Q' NEP NEQ') ->
    Genv.find_symbol psi id = Some b ->
    (forall vl : environ, (!|>(Q' ts x vl <=> Q ts x vl)) (m_phi jm)) ->
    (|>(F0 rho * F rho *
           P ts x (make_args (map (@fst  _ _) (fst fsig0))
             (eval_exprlist (snd (split (fst fsig0))) bl rho) rho)
            )) (m_phi jm) ->
   jsafeN (@OK_spec Espec) psi (level (m_phi jm)) ora
     (State (vx) (tx) (Kseq (Scall ret a bl) :: k)) jm.
Proof.
intros Delta A P Q Q' NEP NEQ' ts x F F0 ret fsig cc a bl R psi vx tx k rho ora jm b id.
intros TC0 TCret TC1 TC2 TC3 TC5 H HR HGG H0 H3 H4 H1 Prog_OK H8 H7 H11 H14.
pose (H6:=True); pose (H9 := True); pose (H16:=True);
pose (H12:=True); pose (H10 := True); pose (H5:=True).
(*************************************************)
assert (Prog_OK' := Prog_OK).
specialize (Prog_OK' (Vptr b Ptrofs.zero) fsig cc A P Q' _ (necR_refl _)).
(*************************************************)
case_eq (level (m_phi jm)); [solve [simpl; constructor] | intros n H2].
simpl.
rewrite <- level_juice_level_phi in H2.
destruct (levelS_age1 _ _ H2) as [jmx H13].
assert (LATER: laterR (level (m_phi jm)) n) by (constructor 1; rewrite <- level_juice_level_phi, H2; reflexivity).
spec Prog_OK'.
hnf. exists id, NEP, NEQ'; split; auto.
exists b; split; auto.
clear H16.
clear H10 H6 H5 H8.
do 4 (pose proof I).
destruct Prog_OK'. {
clear H5 H6 H8 H10 H9 H12.
destruct fsig as [params retty].
simpl @fst in *; simpl @snd in *.
rewrite @snd_split in *.
clear LATER.
clear id H7.
clear jmx H13.
clear Prog_OK.
edestruct semax_call_external; eauto.
destruct H5 as [? [? ?]].
inv H5.
econstructor; eauto.
simpl. constructor; auto.
}
specialize (TC1 _ (age_laterR (age_jm_phi H13))).
specialize (TC2 _ (age_laterR (age_jm_phi H13))).
specialize (H14 _ (age_laterR (age_jm_phi H13))).
destruct H15 as [b' [f [[? [? [COMPLETE [? ?]]]] ?]]].
destruct H18 as [H17' [Hvars [H18 H18']]].
inversion H15; clear H15; subst b'.
specialize (H19 ts x n LATER).
rewrite semax_fold_unfold in H19.
apply (pred_nec_hereditary _ _ n (laterR_necR LATER)) in Prog_OK.
pose (F0F := fun _: environ => F0 rho * F rho).
specialize (H19 _ _ _ (necR_refl _) (conj (tycontext_sub_refl _) HGG)  _ (necR_refl _) (Prog_OK)
                      ((*Kseq (Sreturn None) ::*) Kcall ret f (vx) (tx) :: k)
                       F0F _ (necR_refl _)).
unfold F0F in *; clear F0F.
spec H19 ; [clear H19 |]. {
 split.
 repeat intro; f_equal.
 intros ek vl te ve.
 rewrite !proj_frame_ret_assert.
 unfold seplog.sepcon, seplog.LiftSepLog .
 remember ((construct_rho (filter_genv psi) ve te)) as rho'.
 replace (stackframe_of' psi f rho') with (stackframe_of f rho')
   by (rewrite HGG; auto).
 simpl seplog.sepcon.
 rewrite <- (sepcon_comm (stackframe_of f rho')).
 unfold function_body_ret_assert.
 destruct ek; simpl proj_ret_assert; try solve [normalize].
(* apply prop_andp_subp; intros _.*)
 rewrite andp_assoc.
 apply prop_andp_subp; intro. simpl in H15.
 repeat rewrite andp_assoc.
 apply subp_trans' with
  (F0 rho * F rho * (stackframe_of f rho' * bind_ret vl (fn_return f) (Q ts x) rho') && funassert Delta rho').
 apply andp_subp'; auto.
 rewrite (sepcon_comm (F0 rho * F rho)).
 apply sepcon_subp'; auto.
 apply sepcon_subp'; auto.
 unfold bind_ret.
 destruct vl.
 apply andp_subp'; auto.
 apply pred_eq_e1; apply (H11 _ _ LATER).
 destruct (fn_return f); auto.
 apply pred_eq_e1; apply (H11 _ _ LATER).
 clear Q' NEQ' H11.
 pose proof I.
 pose proof I.

 intros wx ? w' ? ?.
 assert (n >= level w')%nat.
 apply necR_level in H21.
 apply le_trans with (level wx); auto.
 clear wx H20 H21.
 apply own.bupd_intro.
 intros ora' jm' VR ?.
 subst w'.
 pose (H20:=True).
 assert (FL: exists m2, free_list (m_dry jm')  (Clight.blocks_of_env psi ve) = Some m2). {
 subst rho'.
 rewrite (sepcon_comm (stackframe_of f _)) in H22.
 repeat rewrite <- sepcon_assoc in H22.
 clear - COMPLETE HGG H17' H22 H15.
 destruct H22 as [H22 _].
 eapply can_free_list; try eassumption.
 rewrite <- HGG. auto.
}
destruct FL as [m2 FL2].
 rewrite HGG in COMPLETE.
 assert (ve_of rho' = make_venv ve) by (subst rho'; reflexivity).
 assert (SFFB := stackframe_of_freeable_blocks Delta _ rho' _ ve HGG COMPLETE H17' H21 H15).
 clear H21.
 destruct (free_list_juicy_mem_i _ _ _ (F0 rho * F rho * bind_ret vl (fn_return f) (Q ts x) rho') FL2)
 as [jm2 [FL [? FL3]]].
 eapply sepcon_derives. apply SFFB. apply derives_refl.
 forget (F0 rho * F rho) as F0F.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (stackframe_of _ _)). rewrite sepcon_assoc.
 destruct H22 as [H22 _].
 auto.
 subst m2.
pose (rval := match vl with Some v => v | None => Vundef end).
pose (te2 := match ret with
            | None => tx
            | Some rid => PTree.set rid rval tx
            end).
specialize (H1 EK_normal None te2 vx).
rewrite proj_frame_ret_assert in H1.
simpl proj_ret_assert in H1.
rewrite HR in H1; clear R HR. simpl exit_cont in H1.
unfold seplog.sepcon,  seplog.LiftSepLog  in H1.
specialize (H1 (m_phi jm2)).
spec H1.
clear - FL3 H2 H23.
repeat rewrite <- level_juice_level_phi in *. omega.
specialize (H1 _ (necR_refl _)). simpl in H15.
spec H1; [clear H1 | ].
split; [split(*; [split |]*) |].
{
destruct H22 as [H22 _].
simpl. unfold te2. destruct ret; unfold rval.
destruct vl.
assert (tc_val' (fn_return f) v).
 apply tc_val_tc_val'.
 clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
unfold construct_rho. rewrite <- map_ptree_rel.
apply guard_environ_put_te'. subst rho; auto.
intros.
 cut (t = fn_return f). intros. rewrite H24; auto.
hnf in TCret; rewrite H21 in TCret. subst; auto.
assert (f.(fn_return)=Tvoid).
clear - H22; unfold bind_ret in H22; destruct (f.(fn_return)); normalize in H22; try contradiction; auto.
unfold fn_funsig in H18. rewrite H1 in H18. rewrite H18 in TC5. simpl in TC5.
specialize (TC5 (eq_refl _)); congruence.
rewrite <- H0. auto.
}
{
 destruct H22 as [H22a H22b].
 rewrite seplog.sepcon_comm.
 rewrite <- exp_sepcon1.
 simpl seplog.sepcon.
  rewrite <- sepcon_assoc.
 rewrite sepcon_comm in H22a|-*.
  rewrite sepcon_assoc in H22a.
 assert (bind_ret vl (fn_return f) (Q ts x) rho' * (F0 rho * F rho)
            |-- (maybe_retval (Q ts x) (snd fsig) ret (construct_rho (filter_genv psi) vx te2) *
 (F0 (construct_rho (filter_genv psi) vx te2) *
  EX old: val, substopt ret old F (construct_rho (filter_genv psi) vx te2)))). {
apply sepcon_derives.
*
 clear dependent a. clear H11 H19 H20 H10 H9 H12 H5 H6 H8.
 clear Prog_OK ora ora'.  subst rho' fsig.
 clear H22b VR. clear FL jm2 FL2 FL3.
 clear b H16 H7. clear bl TC2 H14.
 unfold te2; clear te2. unfold rval; clear rval.
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
  unfold te2.
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
 apply H1; clear H1.
 eapply free_list_juicy_mem_lem; eauto.
 eapply sepcon_derives; try apply H22a; auto.
}
{
 destruct H22 as [H22a H22b].
 rewrite VR in H22b; clear - FL H22b. {
 unfold te2; clear te2.
 rewrite corable_funassert in H22b.
 rewrite corable_funassert.
 replace (core (m_phi jm2)) with (core (m_phi jm')).
 apply H22b.
 clear - FL.
 induction FL; auto.
 rewrite <-IHFL.
 rewrite <- H1.
 rewrite free_juicy_mem_core; auto.
}
}
case_eq (@level rmap ag_rmap (m_phi jm')); intros; [solve [constructor] |].
rewrite <- level_juice_level_phi in H21.
destruct (levelS_age1 jm' _ H21) as [jm'' ?].
rewrite -> level_juice_level_phi in H21.
destruct (age_twin' jm' jm2 jm'') as [jm2'' [? ?]]; auto.
apply jsafeN_step with (c' := State (vx)(te2) k) (m' := jm2'').
replace n0 with (level jm2'')
 by (rewrite <- H25;
      apply age_level in H24;
      try rewrite <- level_juice_level_phi in H21;
      clear - H21 H24; omega).
split; auto.
simpl.
rewrite (age_jm_dry H26) in FL2.
destruct vl.
2:{
unfold fn_funsig in H18.
rewrite H18 in TC5. simpl in TC5.
assert (fn_return f = Tvoid). {
 clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
 destruct H22. repeat rewrite <- sepcon_assoc in H.
 destruct H as [? [? [? [_ ?]]]]. destruct (fn_return f); try contradiction H1. auto.
}
specialize (TC5 H27).
apply step_return with f ret Vundef (tx); simpl; auto.
unfold te2.
rewrite TC5. split; auto.
}
assert (tc_val (fn_return f) v).
 clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
 destruct H22. destruct H. apply H.
simpl.
unfold rval.
destruct ret.
apply step_return with (zap_fn_return f) None Vundef (PTree.set i v tx); simpl; auto.
apply step_return with f None Vundef tx; simpl; auto.
split; [ | split; [rewrite <- H25; apply age_level; auto|]]. {
 rewrite (age_jm_dry H26) in FL2.
 clear FL3 H1.
 apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm2).
 apply Pos.le_refl.
 eapply free_list_resource_decay; eauto.
 replace (nextblock (m_dry jm')) with (nextblock (m_dry jm2)).
 apply age1_resource_decay; auto.
 symmetry.
 rewrite (age_jm_dry H26).
 clear - FL2.
 forget (m_dry jm') as m.
 revert m FL2; induction (blocks_of_env psi ve); intros.
 simpl in FL2. inv FL2; auto.
 simpl in FL2. destruct a as [[b lo] hi].
 destruct (free m b lo hi) eqn:?; inv FL2.
 rewrite <- (IHl _ H0).
 apply nextblock_free in Heqo; auto.
}
{ rewrite <- (free_list_juicy_mem_ghost _ _ _ FL).
  apply age1_ghost_of, age_jm_phi; auto. }
replace n0 with (level jm2'')
 by (rewrite <- H25;
      apply age_level in H24;
      try rewrite <- level_juice_level_phi in H21;
      clear - H21 H24; omega).
eapply assert_safe_jsafe, pred_hereditary, H1.
apply age_jm_phi; auto.
}
(* END OF  "spec H19" *)

remember (alloc_juicy_variables psi empty_env jm (fn_vars f)) eqn:AJV.
destruct p as [ve' jm']; symmetry in AJV.
destruct (alloc_juicy_variables_e _ _ _ _ _ _ AJV) as [H15 [H20' CORE]].
assert (MATCH := alloc_juicy_variables_match_venv _ _ _ _ _ AJV).
assert (H20 := alloc_juicy_variables_resource_decay _ _ _ _ _ _ AJV).
rewrite <- Genv.find_funct_find_funct_ptr in H16.
destruct (build_call_temp_env f (eval_exprlist (snd (split (fst fsig))) bl rho))
as [te' ?]; auto.
simpl in TC2.
apply tc_exprlist_length in TC2.
clear - H18 TC2.
unfold fn_funsig in *; subst; simpl in *.
revert bl TC2; induction (fn_params f); destruct bl; intros; auto.
simpl in TC2. destruct a. destruct (split l). inv TC2.
simpl in *.
destruct a. simpl.
destruct (split l); simpl in *. unfold_lift; simpl. f_equal; auto.
destruct (levelS_age1 jm' n) as [jm'' H20x]. rewrite <- H20'; assumption.
apply jsafeN_step
  with (c' := State ve' te' (Kseq f.(fn_body) :: Kseq (Sreturn None)
                                              :: Kcall ret f (vx) (tx) :: k))
       (m' := jm''); auto.
split; auto.
eapply step_call_internal with (vargs:=eval_exprlist (snd (split (fst fsig))) bl rho); eauto.
rewrite <- H3.
erewrite age_jm_dry by eauto.
eapply eval_expr_relate; try solve[rewrite H0; auto]; auto. destruct TC3; eassumption. eauto.
destruct (fsig). unfold fn_funsig in *. inv H18.
erewrite age_jm_dry by eauto.
eapply eval_exprlist_relate; try eassumption; auto.
destruct TC3 ; auto.
unfold type_of_function.
rewrite H18'; destruct fsig; inv H18; auto.
rewrite <- (age_jm_dry H20x); auto.
split.
 destruct H20;  apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm'); auto.
 apply age1_resource_decay; auto.
 split.
 rewrite H20'; apply age_level; auto.
 erewrite <- (alloc_juicy_variables_ghost _ _ _ jm), AJV; simpl.
 apply age1_ghost_of, age_jm_phi; auto.

assert (n >= level jm'')%nat.
clear - H2 H20' H20x.
apply age_level in H20x; omega.
pose (rho3 := mkEnviron (ge_of rho) (make_venv ve') (make_tenv te')).
assert (app_pred (funassert Delta rho3) (m_phi jm'')).
{
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
split; [split (*; [split|]*) |]; auto.
3:{
unfold rho3 in H23. unfold construct_rho. rewrite H0 in H23.
simpl ge_of in H23. auto.
}
split.
2:{ simpl.
split; [ | reflexivity].
apply MATCH.
}
{
rewrite (age_jm_dry H20x) in H15.
unfold func_tycontext'.
unfold construct_rho.


clear - H0 TC2 TC3 H18 H16 H21 H15 H23 H17 H17' H13.
unfold rho3 in *. simpl in *. destruct H23.
destruct rho. inv H0. simpl in *.
remember (split (fn_params f)). destruct p.
assert (TE := TC3).
 destruct TC3 as [TC3 TC3'].
destruct TC3 as [TC3 [TC4 TC5]].
simpl in *. if_tac in H16; try congruence. clear H0.
eapply semax_call_typecheck_environ with (jm := jmx); try eassumption.
erewrite <- age_jm_dry by eauto; auto.
destruct TE; intros; auto.
}
normalize.
split; auto. unfold rho3 in H23. unfold construct_rho. rewrite H0 in H23.
simpl ge_of in H23. auto.
unfold bind_args.
unfold tc_formals.
normalize.
rewrite <- sepcon_assoc.
normalize.
split.
hnf.
{
subst fsig.
destruct TC3 as [TC3 _].
clear - TC3 TC2 H21 H17.
simpl in *.
rewrite list_norepet_app in H17. destruct H17 as [H17 [_ _]].
forget (create_undef_temps (fn_temps f)) as te.
revert  bl te TC2 H21 H17.
induction (fn_params f); simpl; intros; auto.
destruct a. destruct (split l) eqn:?. simpl. simpl @snd in *. simpl @fst in *.
destruct bl; try solve [inv H21].
simpl in H21.
unfold_lift in H21.
inv H17.
unfold tc_exprlist in TC2;
simpl in TC2. repeat rewrite denote_tc_assert_andp in TC2.
destruct TC2. destruct H.
set (te1 := PTree.set i (force_val (sem_cast (typeof e) t (eval_expr e rho))) te) in *.
specialize (IHl bl te1 H0 H21 H2).
split; auto.
assert (eval_id i (construct_rho (filter_genv psi) ve' te') =
             force_val (sem_cast (typeof e) t (eval_expr e rho))). {
clear - H21 H1.
forget (force_val (sem_cast (typeof e) t (eval_expr e rho))) as v.
unfold te1 in *; clear te1.
forget (eval_exprlist l1 bl rho) as dl.
assert ((PTree.set i v te) ! i = Some v).
apply PTree.gss.
forget  (PTree.set i v te) as te0.
revert te0 H1 dl H21 H; induction l; simpl; intros.
unfold eval_id. simpl. destruct dl; inv H21.
unfold make_tenv, Map.get. rewrite H. reflexivity.
destruct a.
destruct dl; try solve [inv H21].
eapply IHl.
contradict H1; auto.
eassumption.
rewrite PTree.gso; auto.
}
rewrite H4.
eapply tc_val_sem_cast; eassumption.
}
{
forget (F0 rho * F rho) as Frame.
subst fsig.
rewrite @snd_split in *.
simpl @fst in *.
 apply (alloc_juicy_variables_age H13 H20x) in AJV.
 forget (fn_params f) as params.
 forget (eval_exprlist (map snd params) bl rho) as args.
 clear - H21 H14 AJV H17 H17' H0 Hvars HGG COMPLETE.
 assert (app_pred (Frame * close_precondition params (fn_vars f) (P ts x)
                               (construct_rho (filter_genv psi) ve' te')) (m_phi jmx)).
 eapply sepcon_derives; try apply H14; auto.
 subst rho.
 eapply make_args_close_precondition; eauto.
 apply list_norepet_app in H17; intuition.
 clear H14.
 forget (Frame *
     close_precondition params (fn_vars f) (P ts x)
       (construct_rho (filter_genv psi) ve' te')) as Frame2.
 clear - H17' H21 AJV H Hvars HGG COMPLETE.
 rewrite HGG. change (stackframe_of' cenv_cs) with stackframe_of.
 eapply alloc_juicy_variables_lem2; eauto.
 unfold var_sizes_ok in Hvars;
 rewrite Forall_forall in Hvars, COMPLETE |- *.
 intros.
 specialize (COMPLETE x H0).
 specialize (Hvars x H0).
 rewrite <- HGG; auto.
}
(* end   "spec H19" *)
}
replace n with (level jm'').
eapply assert_safe_jsafe, own.bupd_mono, H19.
intros ? Hsafe ????.
subst; specialize (Hsafe ora0 _ eq_refl eq_refl).
clear - Hsafe.
destruct (level (m_phi jm0)); simpl in *. constructor.
inv Hsafe. econstructor; eauto. inv H0. inv H. split; auto.
simpl in *. congruence.
simpl in *. unfold cl_halted in H. contradiction.
apply age_level in H20x.
rewrite <- level_juice_level_phi in *; congruence.
Qed.

Lemma func_at_func_at':
 forall fs loc, func_at fs loc |-- func_at' fs loc.
Proof.
unfold func_at, func_at'; destruct fs; intros. hnf; intros.
eexists; eauto.
Qed.

Lemma semax_call:
  forall Delta (A: TypeTree)
  (P Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: super_non_expansive P) (NEQ: super_non_expansive Q)
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
   F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax Espec Delta
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
rename H0 into H1.
intros tx vx.
intros ? ? ? ? [[TC3 ?] ?].
assert (H0': necR w (level a')).
apply nec_nat. apply necR_level in H2. apply le_trans with (level y); auto.
eapply pred_nec_hereditary in H1; [ | apply H0'].
eapply pred_nec_hereditary in Prog_OK; [ | apply H0'].
clear w H0' H0 y H2.
rename a' into w.

rewrite !later_andp in H3.
apply extend_sepcon_andp in H3; auto.
destruct H3 as [H2 H3].
normalize in H3. unfold func_ptr in *.
destruct H3 as [[b [H3 H6]] H5].
generalize H4; intros [_ H7].
destruct (level w) eqn: Hl.
{ apply own.bupd_intro; repeat intro.
  rewrite Hl; constructor. }
rewrite <- Hl in *.
destruct (levelS_age w n) as (w' & Hage & Hw'); auto.
specialize (H7 (b) (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) _ (necR_refl _)).
spec H7.
1: apply func_at_func_at'; apply H6.
destruct H7 as [id [H7 H9]].
hnf in H9.
destruct H2 as [TC1 TC2].
generalize H9; intros [fs H8].
generalize H4; intros [H10 _].
specialize (H10 id fs _ (necR_refl _) H8).
destruct H10 as [v' [H10 H13]].
assert (H11: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)) by reflexivity.
simpl in H10. simpl in H7. inversion2 H7 H10.
unfold func_at in H13.
(* rewrite H12 in H13.*)
destruct fs as [fsig' cc' A' P' Q' NEP' NEQ'].
hnf in H6,H13.
inversion2 H13 H6.
apply inj_pair2 in H14. rename H14 into H15.
pose (H6:=True).
clear H9; pose (H9:=True).

unfold filter_genv in H7.
remember (construct_rho (filter_genv psi) vx tx) as rho.
set (args := eval_exprlist (snd (split argsig)) bl rho).
fold args in H5.
rename H11 into H10'.

destruct (function_pointer_aux A' P P' Q Q' w NEP NEQ NEP' NEQ') as [H10 H11].
f_equal; auto.
clear H15.
specialize (H10 ts x (make_args (map (@fst  _ _) argsig) (eval_exprlist (snd (split argsig))bl rho) rho)).
specialize (H11 ts x).
assert (H14: app_pred (|> (F0 rho * F rho * P' ts x (make_args (map (@fst  _ _) argsig)
  (eval_exprlist (snd (split argsig)) bl rho) rho))) w).
{
  do 3 red in H10.
  apply eqp_later1 in H10.
  apply pred_eq_e2 in H10.
  rewrite later_sepcon.
  eapply (sepcon_subp' (|>(F0 rho * F rho)) _ (|> P ts x (make_args (map (@fst  _ _) argsig) (eval_exprlist (snd (split argsig)) bl rho) rho)) _ (level w)); eauto.
  rewrite <- later_sepcon, sepcon_assoc, later_sepcon.
  eapply derives_e, H5.
  apply sepcon_derives, derives_refl; apply now_later.
}
assert (typecheck_environ Delta rho) as TC4.
{
  destruct TC3 as [TC3 TC4].
  eapply typecheck_environ_sub in TC3; [| eauto].
  auto.
}
eapply later_derives in TC2; [|apply (tc_exprlist_sub _ _ _ TS); auto].
eapply later_derives in TC1; [|apply (tc_expr_sub _ _ _ TS); auto].
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
clear TC7.
apply own.bupd_intro; repeat intro; subst.
eapply semax_call_aux; try eassumption;
 try solve [simpl; assumption].
simpl RA_normal.
auto.
Qed.

Lemma semax_call_alt:
 forall Delta (A: TypeTree)
   (P Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
   (NEP: super_non_expansive P) (NEQ: super_non_expansive Q)
     ts x F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax Espec Delta
       (fun rho => (|> (tc_expr Delta a rho && tc_exprlist Delta (snd (split argsig)) bl rho))  &&
           (func_ptr (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (make_args (map (@fst  _ _) argsig)
                (eval_exprlist (snd (split argsig)) bl rho) rho )))))
         (Scall ret a bl)
         (normal_ret_assert
          (fun rho => (EX old:val, substopt ret old F rho * maybe_retval (Q ts x) retsig ret rho))).
Proof. exact semax_call. Qed.

Lemma semax_call_ext:
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
  semax Espec  Delta P (Scall ret a' bl') Q.
Proof.
intros until 2. intro Hbl. intros.
rewrite semax_unfold in H1|-*.
rename H1 into H2. pose proof I.
intros.
specialize (H2 psi Delta' w TS HGG Prog_OK k F H3 H4).
intros tx vx; specialize (H2 tx vx).
intros ? ? ? ? ?.
specialize (H2 y H5 a'0 H6 H7).
destruct H7 as[[? ?] _].
hnf in H7.
pose proof I.
intros ? J; destruct (H2 _ J) as (? & J' & m' & Hl & Hr & ? & Hsafe); subst.
eexists; split; eauto; exists m'; repeat split; auto.
hnf in Hsafe|-*; intros.
specialize (Hsafe ora jm H10).
eapply convergent_controls_jsafe; try apply Hsafe.
reflexivity.
simpl; intros ? ?. unfold cl_after_external. destruct ret0; auto.
reflexivity.
intros.
specialize (Hsafe H11).
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
clear - TCa TCa' H7 H7' H0 Heqrho HGG TS.
intros.
eapply tc_expr_sub in TCa; [| eauto | eauto].
pose proof (eval_expr_relate _ _ _ _ _ _ jm HGG Heqrho H7 TCa).
pose proof (eval_expr_fun H H1). subst vf.
rewrite H0.
eapply eval_expr_relate; eauto.
}
assert (forall tyargs vargs,
             Clight.eval_exprlist psi vx tx (m_dry jm) bl tyargs vargs ->
             Clight.eval_exprlist psi vx tx (m_dry jm) bl' tyargs vargs). {
clear - TS IF_ONLY TCbl TCbl' Hbl H7 H7' H13 Heqrho HGG.
revert bl bl' Hbl TCbl TCbl' H13; induction tl; destruct bl, bl'; simpl; intros; auto;
 try (clear IF_ONLY; contradiction).
(*unfold_lift in H13; simpl in H13.
inversion H13; clear H13.
*)
 unfold tc_exprlist in TCbl,TCbl'. simpl in TCbl, TCbl'.
repeat rewrite denote_tc_assert_andp in TCbl, TCbl'.
destruct TCbl as [[TCe ?] ?].
destruct TCbl' as [[TCe0 ?] ?].
inversion H; clear H. subst bl0 tyargs vargs.
inversion Hbl; clear Hbl. rewrite <- H5 in *.
eapply (tc_expr_sub _ _ _ TS e rho H7' (m_phi jm)) in TCe.
pose proof (eval_expr_relate _ _ _ _ _ _ _ HGG Heqrho H7 TCe).
pose proof (eval_expr_fun H H6).
repeat rewrite <- cop2_sem_cast in *.
unfold force_val in H1.
rewrite H10 in *.
contradiction IF_ONLY.  (* this needs plenty of work. *)
}
destruct H12; split; auto.
inv H12; [eapply step_call_internal | eapply step_call_external ]; eauto.
rewrite <- H; auto.
rewrite <- H; auto.
auto.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Proof.
induction k; intros.
reflexivity.
destruct a; simpl; auto.
Qed.

Definition cast_expropt (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (eval_expr (Ecast e' t))  | None => `None end.

Lemma call_cont_current_function:
  forall {k i f e t l}, call_cont k = Kcall i f e t :: l -> current_function k = Some f.
Proof. intros. induction k; try destruct a; simpl in *; inv H; auto.
Qed.

Definition tc_expropt Delta (e: option expr) (t: type) : environ -> mpred :=
   match e with None => `!!(t=Tvoid)
                     | Some e' => denote_tc_assert (typecheck_expr Delta (Ecast e' t))
   end.

Lemma  semax_return:
   forall Delta R ret,
      semax Espec Delta
                (fun rho => tc_expropt Delta ret (ret_type Delta) rho &&
                             RA_return R (cast_expropt ret (ret_type Delta) rho) rho)
                (Sreturn ret)
                R.
Proof.
  intros.
  hnf; intros.
  rewrite semax_fold_unfold.
  intros psi Delta'.
  apply prop_imp_i. intros [TS HGG].
  replace (ret_type Delta) with (ret_type Delta')
    by (destruct TS as [_ [_ [? _]]]; auto).
  apply derives_imp.
  clear n.
  intros w ? k F.
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
    eapply sepcon_derives; try apply H1; auto.
    apply andp_left2; auto.
  }
  assert (TC: (tc_expropt Delta ret (ret_type Delta') rho) w').
  {
    clear - H1. destruct H1 as [w1 [w2 [? [? [? ?]]]]]. intros.
    unfold tc_expropt in *.
    destruct ret; try apply H1.
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
    clear TC; intros ? [TC Hsafe] ????.
    specialize (Hsafe ora jm (eq_refl _) H6).
    eapply convergent_controls_jsafe; try apply Hsafe.
    1: simpl; auto.
    1: intros ? ?; simpl; unfold cl_after_external; auto.
    1: simpl; auto.
    intros.
    simpl in H7.
    destruct H7; split; auto.
    revert H7; simpl.
    unfold_lift.
    case_eq (call_cont k); intros.
    - inv H9.
      inv H14.
    - destruct c.
      elimtype False; clear - H7.
       revert l H7; induction k; try destruct a; simpl; intros; try discriminate; eauto.
      elimtype False; clear - H7.
       revert l H7; induction k; try destruct a; simpl; intros; try discriminate; eauto.
      elimtype False; clear - H7.
       revert l H7; induction k; try destruct a; simpl; intros; try discriminate; eauto.
      elimtype False; clear - H7.
       revert l H7; induction k; try destruct a; simpl; intros; try discriminate; eauto.
      destruct l0.
      * clear H0 H2 H8.
        inv H9. fold denote_tc_assert in TC.
        inv H11.
        destruct H17.
        econstructor; try eassumption; simpl.
        2: split; [congruence | eassumption].
        exists (eval_expr e (construct_rho (filter_genv psi) ve te)).
        destruct H3 as [H3' H6].
        assert (typecheck_environ Delta (construct_rho (filter_genv psi) ve te)) as H3
          by (eapply typecheck_environ_sub; eauto).
        assert (TCe: (denote_tc_assert (typecheck_expr Delta e)  (construct_rho (filter_genv psi) ve te)) (m_phi jm)).
        {
          hnf.
          simpl in *.
          rewrite !denote_tc_assert_andp in TC.
          simpl in *; super_unfold_lift.
          destruct TC; auto.
        }
        pose proof tc_expr_sub _ _ _ TS _ _ H3 (m_phi jm) TCe as TCe'.
        split.
        {
          apply eval_expr_relate with (Delta0 := Delta')(m:= jm); auto.
        }
        {
          simpl in H6; rewrite (call_cont_current_function H7) in H6.
          destruct H6 as [_ ?].
          rewrite H6.
          super_unfold_lift.
          rewrite !denote_tc_assert_andp in TC.
          destruct TC as [TC1 TC2]. rewrite H6 in TC2.
          rewrite cop2_sem_cast'; auto.
          2: eapply typecheck_expr_sound; eauto.
          apply cast_exists with (Delta0 := Delta)(phi := m_phi jm); auto.
        }
      * fold denote_tc_assert in TC.
        inv H9.
        symmetry in H14; inv H14.
        destruct H20.
        subst te''. clear H6.
        econstructor; try eassumption; [| simpl; auto].
        exists (eval_expr e (construct_rho (filter_genv psi) ve te)).
        destruct H3 as [H3' H6].
        assert (typecheck_environ Delta (construct_rho (filter_genv psi) ve te)) as H3
          by (eapply typecheck_environ_sub; eauto).
        assert (TCe: (denote_tc_assert (typecheck_expr Delta e)  (construct_rho (filter_genv psi) ve te)) (m_phi jm)).
        {
          hnf.
          simpl in *.
          rewrite !denote_tc_assert_andp in TC.
          simpl in *; super_unfold_lift.
          destruct TC; auto.
        }
        pose proof tc_expr_sub _ _ _ TS _ _ H3 (m_phi jm) TCe as TCe'.
        split.
        {
          apply eval_expr_relate with (Delta0 := Delta); auto.
        }
        {
          simpl in H6; rewrite (call_cont_current_function H7) in H6.
          destruct H6 as [_ ?].
          rewrite !denote_tc_assert_andp in TC.
          destruct TC as [TC1 TC2]. rewrite H6 in TC2.
          rewrite cop2_sem_cast'; auto.
          2: eapply typecheck_expr_sound; eauto.
          apply cast_exists with (Delta0 := Delta)(phi := m_phi jm); auto.
        }
  + eapply own.bupd_mono, H0; eauto.
    intros ? Hsafe ????.
    specialize (Hsafe ora jm (eq_refl _) H6).
    eapply convergent_controls_jsafe; try apply Hsafe.
    1: simpl; auto.
    1: intros ? ?; simpl; unfold cl_after_external; auto.
    1: simpl; auto.
    intros.
    destruct H7; split; auto.
    inv H7.
    rewrite call_cont_idem in H13; auto.
    econstructor; try eassumption.
    auto.
Qed.

End extensions.
