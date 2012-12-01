Load loadpath. 
Require Import veric.base.
Require Import msl.normalize.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.extspec.
Require Import veric.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.
 
Open Local Scope pred.

Section extensions.
Context {Z} (Hspec: juicy_ext_spec Z).

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
     | YES rsh sh k _ => sh = pfullshare /\ isVAL k
     | _ => False
     end) by (destruct (y @ loc); eauto).
clear H0.
revert H1; case_eq (y @ loc); intros; try contradiction.
destruct H1; subst.
destruct (rmap_unage_YES _ _ _ _ _ _ _ H H0).
rewrite H1; simpl; auto.
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

Lemma prop_unext: forall P Q: Prop, P=Q -> (P<->Q).
Proof. intros. subst; split; auto. Qed.

Lemma function_pointer_aux:
  forall A P P' Q Q' (w: rmap), 
   SomeP (A::boolT::environ::nil) (approx (level w) oo packPQ P Q) =
   SomeP (A::boolT::environ::nil) (approx (level w) oo packPQ P' Q') ->
   ( (forall x vl, (! |> (P' x vl <=> P x vl)) w) /\
     (forall x vl, (! |> (Q' x vl <=> Q x vl)) w)).
Proof.
intros.
apply someP_inj in H.
unfold packPQ, compose in H.
split; intros.
apply equal_f with (x,(true,(vl,tt))) in H.
simpl in H.
rewrite @later_fash; auto with typeclass_instances.
intros ? ? m' ?.
split; intros m'' ? ?;  apply f_equal with (f:= fun x => app_pred x m'') in H;
apply prop_unext in H; apply approx_p with (level w); apply H;
apply approx_lt; auto; clear - H0 H1 H2; hnf in H1; apply laterR_level in H1;
apply necR_level in H2; simpl in *;
change compcert_rmaps.R.ag_rmap with ag_rmap in *;
change compcert_rmaps.R.rmap with rmap in *;
omega.
apply equal_f with (x,(false,(vl,tt))) in H.
simpl in H.
rewrite @later_fash; auto with typeclass_instances; intros ? ? m' ?;
split; intros m'' ? ?;  apply f_equal with (f:= fun x => app_pred x m'') in H;
apply prop_unext in H; apply approx_p with (level w); apply H;
apply approx_lt; auto; clear - H0 H1 H2; hnf in H1; apply laterR_level in H1;
apply necR_level in H2; simpl in *;
change compcert_rmaps.R.ag_rmap with ag_rmap in *;
change compcert_rmaps.R.rmap with rmap in *; omega.
Qed.


Lemma semax_fun_id:
      forall id fsig (A : Type) (P' Q' : A -> assert)
              Delta P Q c
      (GLBL: (var_types Delta) ! id = None),
    (glob_types Delta) ! id = Some (Global_func (mk_funspec fsig A P' Q')) ->
       semax Hspec Delta (fun rho => P rho 
                                && fun_assert  fsig A P' Q' (eval_lvalue (Evar id (Tfunction (type_of_params (fst fsig)) (snd fsig))) rho))
                              c Q ->
       semax Hspec Delta P c Q.
Proof.
intros.
rewrite semax_unfold in H0|-*.
rename H0 into H1; pose proof I.
intros.
specialize (H1 psi w Prog_OK k F H2 H3).
intros te ve w' ? w'' ? ?.
apply (H1 te ve w' H4 w'' H5); clear H1.
destruct H6; split; auto.
destruct H1 as [H1 ?]; split; auto.
normalize.
split; auto.
assert (app_pred (believe Hspec Delta psi Delta) (level w'')).
apply pred_nec_hereditary with (level w'); eauto.
apply nec_nat; apply necR_level; auto.
apply pred_nec_hereditary with w; eauto.
apply nec_nat; auto.
pose proof H1. unfold typecheck_environ in H9.
hnf in H9.
apply andb_true_iff in H9. destruct H9 as [_ SAME].
hnf in H1. apply typecheck_environ_sound in H1.
destruct H1 as [_ [_ H1]].
rename GLBL into GL1.
specialize (H1 _ _ H).
apply typecheck_mode_eqv in SAME.
specialize (SAME _ _ H).
destruct SAME as [SAME | [t SAME]]; [ | congruence].
clear - H6 H8 H SAME (*H9*) H1.
destruct H6 as [H6 H6'].
specialize (H6 _ _  _(necR_refl _) H).
destruct H6 as [v [loc [[? ?] ?]]].
simpl in H0, H1, H2.
(*destruct H9; try congruence.*)
specialize (H8 v fsig A P' Q' _ (necR_refl _)).
 
unfold filter_genv in H0. simpl in H0.
invSome.
assert (v = Vptr b Int.zero) by (destruct (type_of_global psi b); inv H6; auto).
subst v.
unfold val2adr in H2.
rewrite Int.signed_zero in H2.
subst loc.
spec H8. exists id. split; auto. exists b; auto.
simpl in SAME.
exists b.
split.
unfold eval_lvalue, eval_var.
simpl ve_of. unfold Map.get. rewrite SAME.
simpl. unfold filter_genv. rewrite H0.
destruct (type_of_global psi b); inv H6; auto.
rewrite eqb_type_refl.
replace (eqb_typelist (type_of_params (fst fsig)) (type_of_params (fst fsig))) with true.
simpl; auto.
clear; induction (type_of_params (fst fsig)); simpl; auto.
rewrite <- IHt; simpl; auto.
rewrite eqb_type_refl; auto.
hnf; auto.
intro loc.
hnf.
if_tac; auto.
subst.
hnf. auto.
hnf; auto.
Qed.

Definition free_list_juicy_mem:
  forall jm bl m, free_list (m_dry jm) bl = Some m -> juicy_mem.
Admitted.

Lemma can_alloc_variables:
  forall jm vl, exists ve', exists jm',
          list_norepet (map (@fst _ _) vl) ->
          Clight.alloc_variables empty_env (m_dry jm) vl ve' (m_dry jm') /\
          (resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\ level jm = S (level jm')).
Admitted.


Lemma build_call_temp_env:
  forall f vl, 
     list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)) ->
  exists te,  bind_parameter_temps (fn_params f) vl
                     (create_undef_temps (fn_temps f)) = Some te.
Admitted.

Lemma resource_decay_funassert:
  forall G rho b w w',
         resource_decay b w w' ->
         app_pred (funassert G rho) w ->
         app_pred (funassert G rho) w'.
Admitted.


Definition substopt {A} (ret: option ident) (v: val) (P: environ -> A)  : environ -> A :=
   match ret with
   | Some id => subst id v P
   | None => P
   end.

Lemma exprlist_eval :
  forall (Delta : tycontext) (fsig : funsig) (a : expr) 
     (bl : list expr) (psi : genv) (vx : env) (tx : temp_env) 
     (rho : environ) (jm : juicy_mem),
   (tc_expr Delta a rho) (m_phi jm) ->
   (tc_exprlist Delta (snd (split (fst fsig))) bl rho) (m_phi jm) ->
   map typeof bl = map snd (fst fsig) ->
   typecheck_environ rho Delta = true ->
   rho = construct_rho (filter_genv psi) vx tx ->
   (funassert Delta rho) (m_phi jm) ->
   forall f : function,
   fsig = fn_funsig f ->
   forall te' : temp_env,
   bind_parameter_temps (fn_params f)
     (eval_exprlist (snd (split (fst fsig))) bl rho)
     (create_undef_temps (fn_temps f)) = Some te' ->
   Clight.eval_exprlist psi vx tx (m_dry jm) bl
     (type_of_params (fn_params f))
     (eval_exprlist (snd (split (fst fsig))) bl rho). 
Proof.
intros. 
destruct fsig. unfold fn_funsig in *. inv H5. simpl. simpl in H6. 
generalize dependent bl. generalize dependent te'. 
induction (fn_params f); intros; destruct bl; try solve[constructor | simpl in *; congruence]. 

simpl. destruct a0. remember (split l). destruct p. simpl.  unfold lift2 in *.
  simpl in H0. rewrite <- Heqp in H0. simpl in H0. unfold lift2 in *. 
  destruct H0 as [[? ?] ?].
  econstructor; eauto. eapply eval_expr_relate; eauto. 
  eapply cast_exists; eauto.
 (*    simpl in H6. rewrite <- Heqp in H6. simpl in H6. 
     eapply IHl; auto.  simpl in H1.  simpl. inv H1. auto. 
   simpl. rewrite <- Heqp. simpl. auto.
  simpl.
*)
  admit.  (* This should be provable with an extra hypothesis that the params are all distinct *)
Qed.

Lemma pass_params_ni :
  forall  l2
     (te' : temp_env) (id : positive) te l,
   bind_parameter_temps l2
     l
     (te) = 
   Some te' ->
   (In id (map fst l2) -> False) ->
   Map.get (make_tenv te') id = te ! id.  
Proof.
intros. simpl in *.  generalize dependent l. revert te. 
revert te'. 
induction(l2); intros; simpl in *. 
destruct l.  inv H. 
unfold make_tenv.  unfold Map.get. auto.
congruence.

simpl in *. destruct a. 
destruct l.
congruence. 
simpl in *. 
remember (bind_parameter_temps l2 l te). destruct o. inv H.
intuition. symmetry in Heqo. 
specialize (H0 _ _ _ Heqo).  rewrite <- H0.  
unfold Map.get. unfold make_tenv.  
(* rewrite PTree.gso; auto.  *) admit.
(* congruence. *) admit.

Qed. 

Lemma smaller_temps_exists : forall l l1 l2 te id i,
bind_parameter_temps l l1 (PTree.set id Vundef (create_undef_temps l2)) = Some te ->
i <> id -> 
exists te', (bind_parameter_temps l l1 (create_undef_temps l2) = Some te' /\ te' ! i = te ! i). 
Proof. 
intros. 
generalize dependent l1. 
revert l2 te.
induction l; intros. 
simpl in *. destruct l1; auto. inv H. eexists. split. auto. 
rewrite PTree.gso; auto. congruence. 

simpl in *. destruct a. destruct l1. congruence. simpl in *.
remember (bind_parameter_temps l l1
          (PTree.set id Vundef (create_undef_temps l2))). 
destruct o. 
edestruct IHl. eauto. destruct H1. 
(* rewrite H1. eexists. split. eauto.  
inv H. 
repeat rewrite PTree.gsspec. if_tac. auto. auto. congruence. 
*) admit. admit.
Qed.


Lemma alloc_vars_lookup : 
forall id m1 l ve m2 e ,
list_norepet (map fst l) ->
(forall i, In i (map fst l) -> e ! i = None) ->
Clight.alloc_variables (e) m1 l ve m2 ->
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

Lemma alloc_vars_lemma : forall id l m1 m2 ve ve'
(SD : forall i, In i (map fst l) -> ve ! i = None),
list_norepet (map fst l) ->

Clight.alloc_variables ve m1 l ve' m2 ->
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
destruct (eq_dec i id). subst. intuition. rewrite PTree.gso; auto. 
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
     (H15 : alloc_variables empty_env (m_dry jm) (fn_vars f) ve' (m_dry jm'))
    (TC3 : tc_te_denote (make_tenv tx) (temp_types Delta))
    (TC4 : tc_ve_denote (make_venv vx) (var_types Delta))
    (TC5 : tc_ge_denote (filter_genv psi) (glob_types Delta))
   (H : forall (b : ident) (b0 : funspec) (a' : rmap),
    necR (m_phi jm') a' ->
    (glob_types Delta) ! b = Some (Global_func b0) ->
    exists b1 : val,
      exists b2 : address,
        (filter_genv psi b = Some (b1, type_of_funspec b0) /\ val2adr b1 b2) /\
        (func_at b0 b2) a')
   (H1 : forall (b : address) (b0 : funspec) (a' : rmap),
     necR (m_phi jm') a' ->
     (func_at b0 b) a' ->
     exists b1 : ident,
       exists b2 : val,
         (filter_genv psi b1 = Some (b2, type_of_funspec b0) /\ val2adr b2 b) /\
         (exists fs : funspec,
            (glob_types Delta) ! b1 = Some (Global_func fs)))
   (l : list ident) (l0 : list type) 
    (Heqp : (l, l0) = split (fn_params f))
   (TC2 : denote_tc_assert (typecheck_exprlist Delta l0 bl)
        (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)))
   (H21 : bind_parameter_temps (fn_params f)
        (eval_exprlist l0 bl
           (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)))
        (create_undef_temps (fn_temps f)) = Some te')
   (TE : typecheck_environ
       (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)) Delta =
     true),
   typecheck_environ
     (mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te'))
     (make_tycontext_t (fn_params f) (fn_temps f), make_tycontext_v (fn_vars f),
     fn_return f, glob_types Delta) = true.
Proof.
 intros.
 pose (rho3 := mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).
  
unfold typecheck_environ. repeat rewrite andb_true_iff. 
repeat split. clear H H1 H15. rewrite typecheck_te_eqv. 
unfold tc_te_denote. intros. simpl. 
unfold func_tycontext' in *. 
unfold temp_types in *. simpl in *.
apply func_tycontext_t_sound in H; auto.
 clear - H21 H TC2 TC3 Heqp H17 TE. 

destruct H. (*in params*)
destruct H. subst.
generalize dependent (fn_temps f). 
generalize dependent l. generalize dependent l0.
generalize dependent bl. generalize dependent te'. 
induction (fn_params f); intros.  inv H. simpl in *.
destruct a. simpl in *. remember (split l). destruct p. 
simpl in *. destruct H. clear IHl. destruct bl. inv H.  inv Heqp. inv TC2.   
inv H. inv Heqp. simpl in *. unfold lift2 in *. 
destruct TC2 as [[? ?] ?].
rewrite (pass_params_ni _ _ id _ _ H21) by (inv H17; contradict H4; apply in_app; auto).
rewrite PTree.gss. unfold cast_exp.  
exists (force_val
          (Cop.sem_cast
             (eval_expr e
                (mkEnviron (filter_genv psi) (make_venv vx)
                   (fun id0 : positive => tx ! id0))) 
             (typeof e) ty)). 
split.
auto. right. eapply typecheck_val_eval_cast with (Delta := Delta). 
apply TE. 
auto. auto. inv Heqp. 
destruct bl.  inv TC2. 
inv H17.
simpl in *.  unfold lift2 in *. destruct TC2 as [[? ?] ? ].
assert (i <> id). intuition. subst. apply H2. apply in_or_app. left.
apply in_map with (f := fst) in H. apply H.

(*
remember (bind_parameter_temps l
            (eval_exprlist l4 bl
               (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)))
            (create_undef_temps l2)). 
destruct o. inv H21. unfold Map.get. unfold make_tenv at 1. 
assert (i <> id). intuition. subst. apply H2. apply in_or_app. left.
apply in_map with (f := fst) in H. apply H. rewrite PTree.gso; auto. 
edestruct IHl; eauto. congruence. 
*) admit.


(*In temps*)
destruct H. subst.
apply list_norepet_app in H17. destruct H17 as [? [? ?]]. 
generalize dependent (fn_params f). generalize dependent bl.
generalize dependent l0. generalize dependent l. generalize dependent te'.  

induction (fn_temps f); intros.  
inv H. 

simpl in *. destruct H. destruct a. inv H. simpl in *. 
clear IHl. exists Vundef. simpl in *. split; auto. inv H1.  
assert (In id (map fst (l2)) -> False). 
intros. 
unfold list_disjoint in *. eapply H2. eauto. left. auto. auto.
eapply pass_params_ni with (id := id) in H21; auto.  rewrite PTree.gss in *. auto. 


destruct a. 
destruct (eq_dec id i). subst. 
apply pass_params_ni with (id := i) in H21. 
rewrite PTree.gss in *. exists  Vundef. auto.
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

rewrite typecheck_ve_eqv. 
unfold tc_ve_denote. intros. 



clear TC3 TC5. 
simpl in *. unfold tc_ve_denote in *.
unfold func_tycontext' in *. unfold var_types in *. 
simpl in *. apply func_tycontext_v_sound in H0; auto.  
generalize dependent (m_dry jm).
assert (forall id, In id (map fst (fn_vars f)) -> empty_env ! id = None). 
intros. rewrite PTree.gempty; auto. 
generalize dependent empty_env. 
induction (fn_vars f); intros. inversion H15. subst.   
inv H0. 

simpl in H0. 
destruct H0. destruct a. inv H0. 
inv H15.  apply alloc_vars_lookup with (id := id) in H10. 
unfold Map.get. unfold make_venv. rewrite H10. 
rewrite PTree.gss. eauto. inv H17'; auto. 
intros. inv H17'. rewrite PTree.gsspec. if_tac.
subst. intuition.  
apply H2. simpl in *. auto. 
rewrite PTree.gss; eauto. 

inv H17'; inv H15. 
apply IHl1 in H12. destruct H12. 
exists x. auto. auto. auto. intros. 
simpl in *. rewrite PTree.gso. apply H2; auto. 
intro. subst. intuition. 

unfold ge_of in *. simpl in *. 
rewrite <- typecheck_ge_eqv in TC5. auto.

unfold all_var_ids. simpl in *. 
unfold typecheck_environ in *. rewrite andb_true_iff in TE. 
destruct TE as [_ TE]. 
rewrite typecheck_mode_eqv in *. 
unfold tc_mode_denote in *. intros. simpl in *. 
specialize (TE id t H0). 
unfold make_venv.
unfold func_tycontext'. unfold var_types. simpl in *.
assert (empty_env ! id = None). rewrite PTree.gempty. auto. 
generalize dependent empty_env.  generalize dependent (m_dry jm). 
induction (fn_vars f); intros. inversion H15.  subst. left. 
auto.
simpl in *. destruct a. inv H15. 
rewrite PTree.gsspec. if_tac. eauto.

apply IHl1 in H11. destruct H11. auto. right. 
congruence. 
inv H17'. auto. rewrite PTree.gso; auto.
Qed. 

Lemma semax_call_aux:
 forall (Delta : tycontext) (A : Type)
  (P Q Q' : A -> assert) (x : A) (F : environ -> pred rmap)
  (F0 : assert) (ret : option ident) (fsig : funsig) (a : expr)
  (bl : list expr) (R : ret_assert) (psi : genv) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)
  (ora : Z) (jm : juicy_mem) (b : block) (id : ident),
   Cop.classify_fun (typeof a) =
   Cop.fun_case_f (type_of_params (fst fsig)) (snd fsig) ->
   tc_expr Delta a rho (m_phi jm) ->
   tc_exprlist Delta (snd (split (fst fsig))) bl rho (m_phi jm) ->
    map typeof bl = map (@snd _ _) (fst fsig) ->
    typecheck_environ rho Delta = true ->
    (snd fsig=Tvoid <-> ret=None) ->
    closed_wrt_modvars (Scall ret a bl) F0 ->
    R EK_normal None = (fun rho0 : environ => EX old:val, substopt ret old F rho0 * Q x (get_result ret rho0)) ->
    rho = construct_rho (filter_genv psi) vx tx ->
    (*filter_genv psi = ge_of rho ->*)
    eval_expr a rho = Vptr b Int.zero ->
    (funassert Delta rho) (m_phi jm) ->
    (rguard Hspec psi (exit_tycon (Scall ret a bl) Delta) (frame_ret_assert R F0) k) (level (m_phi jm)) ->
    (believe Hspec Delta psi Delta) (level (m_phi jm)) ->
    (glob_types Delta)!id = Some (Global_func (mk_funspec fsig A P Q')) ->
    Genv.find_symbol psi id = Some b ->
    (forall vl : environ, (!|>(Q' x vl <=> Q x vl)) (m_phi jm)) ->
    (|>(F0 rho * F rho *
           P x (make_args (map (@fst  _ _) (fst fsig)) 
             (eval_exprlist (snd (split (fst fsig))) bl rho) rho)
            )) (m_phi jm) ->
   jsafeN Hspec psi (level (m_phi jm)) ora
     (State (vx) (tx) (Kseq (Scall ret a bl) :: k)) jm.
Proof.
intros Delta A P Q Q' x F F0 ret fsig a bl R psi vx tx k rho ora jm b id.
intros TC0 TC1 TC2 TC4 TC3 TC5 H HR H0 H3 H4 H1 Prog_OK H8 H7 H11 H14.
pose (H6:=True); pose (H9 := True); pose (H16:=True);
pose (H12:=True); pose (H10 := True); pose (H5:=True).
(*************************************************)
assert (Prog_OK' := Prog_OK).
specialize (Prog_OK' (Vptr b Int.zero) fsig A P Q' _ (necR_refl _)).
(*************************************************)
case_eq (level (m_phi jm)); [solve [simpl; auto] | intros n H2].
simpl.
destruct (levelS_age1 _ _ H2) as [phi' H13].
assert (LATER: laterR (level (m_phi jm)) n) by (constructor 1; rewrite H2; reflexivity).
spec Prog_OK'.
hnf. exists id; split; auto.
exists b; split; auto.
clear H16.
clear H10 H6 H5 H8.
specialize (H14 _ (age_laterR H13)).
do 4 (pose proof I).
destruct Prog_OK'.
admit.  (* external case *)
destruct H15 as [b' [f [[? [? [? ?]]] ?]]].
destruct H18 as [H17' H18].
inversion H15; clear H15; subst b'.
specialize (H19 x n LATER).
rewrite semax_fold_unfold in H19.
apply (pred_nec_hereditary _ _ n (laterR_necR LATER)) in Prog_OK.
pose (F0F := fun _: environ => F0 rho * F rho).
specialize (H19 _ _ (necR_refl _) (Prog_OK)  
                      (Kseq (Sreturn None) :: Kcall ret f (vx) (tx) :: k)
                       F0F _ (necR_refl _)).
unfold F0F in *; clear F0F.
spec H19 ; [clear H19 |].
split.
repeat intro; f_equal. 
intros ek vl te ve.  
unfold frame_ret_assert.
remember ((construct_rho (filter_genv psi) ve te)) as rho'.
rewrite <- (sepcon_comm (stackframe_of f rho')).
unfold function_body_ret_assert.
destruct ek; try solve [normalize].
apply prop_andp_subp; intro.
repeat rewrite andp_assoc.
apply subp_trans' with
 (F0 rho * F rho * (stackframe_of f rho' * bind_ret vl (fn_return f) (Q x) rho') && funassert Delta rho').
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
clear Q' H11.
pose proof I.
pose proof I.

intros wx ? w' ? ?.
assert (n >= level w')%nat.
apply necR_level in H21.
apply le_trans with (level wx); auto.
clear wx H20 H21.
intros ora' jm' VR ?.
subst w'.
pose (H20:=True).
assert (FL: exists m2, free_list (m_dry jm')  (Clight.blocks_of_env vx) = Some m2).
admit.  (* prove this from H22, stackframe_of *)
destruct FL as [m2 FL].
pose (jm2 := free_list_juicy_mem _ _ _ FL).
assert (FL2: free_list (m_dry jm') (Clight.blocks_of_env (ve)) = Some (m_dry jm2)) by admit.
assert (FL3: level jm' = level jm2) by admit.
pose (rval := match vl with Some v => v | None => Vundef end). 
pose (te2 := match ret with
            | None => tx
            | Some rid => PTree.set rid rval tx
            end).
specialize (H1 EK_normal None te2 vx).
unfold frame_ret_assert in H1.  
rewrite HR in H1; clear R HR. simpl exit_cont in H1.
specialize (H1 (m_phi jm2)).
spec H1; [ admit | ]. (* easy *)
specialize (H1 _ (necR_refl _)). simpl in H15. 
spec H1; [clear H1 | ].
split.
simpl. unfold te2. destruct ret; unfold rval.
destruct vl.   
assert (typecheck_val v (fn_return f) = true).
 clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
 destruct H22. destruct H. apply H. 
unfold construct_rho. rewrite <- map_ptree_rel.
apply typecheck_environ_put_te'. subst rho; auto.
intros. cut (fst t = fn_return f). intros. rewrite H24; auto. 
admit.  
assert (f.(fn_return)=Tvoid).  
clear - H22; unfold bind_ret in H22; destruct (f.(fn_return)); normalize in H22; try contradiction; auto. 
unfold fn_funsig in H18. rewrite H1 in H18. rewrite H18 in TC5. simpl in TC5.
destruct TC5 as [TC5 _]. specialize (TC5 (eq_refl _)); congruence. 


rewrite <- H0. auto.
auto. 
normalize. exists rval.
admit.  (* very plausible *)
hnf in H1. 
specialize (H1 ora' jm2).
specialize (H1 (eq_refl _) (eq_refl _)).
case_eq (@level rmap ag_rmap (m_phi jm')); intros; [solve [auto] |].
destruct (levelS_age1 jm' _ H21) as [jm'' ?].
destruct (age_twin' jm' jm2 jm'') as [jm2'' [? ?]]; auto.
pose proof (age_safe _ _ _ _ H26 _ _ _ H1).
exists  (State (vx)(te2) k); exists jm2''.
replace n0 with (level jm2'') by admit.  (* easy *) 
split; auto.
split.
simpl.
rewrite (age_jm_dry H26) in FL2.
destruct vl. 
Focus 2.
assert (f.(fn_return)=Tvoid). 
clear - H22; unfold bind_ret in H22; destruct (f.(fn_return)); normalize in H22; try contradiction; auto.
unfold fn_funsig in H18. rewrite H28 in H18. rewrite H18 in TC5. simpl in TC5.
destruct TC5 as [TC5 _]; specialize (TC5 (eq_refl _)). unfold te2 in *. rewrite TC5 in *.
apply step_return with f None Vundef (tx); simpl; auto. 
assert (typecheck_val v (fn_return f) = true).
 clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
 destruct H22. destruct H. apply H.
destruct ret.
simpl.
unfold rval.
apply step_return with (zap_fn_return f) None v (PTree.set i v tx); simpl; auto.
elimtype False.
clear - H28 H18 TC5. subst fsig. unfold fn_funsig in TC5. simpl in TC5.
destruct TC5. rewrite H0 in H28 by auto.
clear - H28. destruct v; simpl in *; congruence. 
admit.  (* not too difficult *)
(* END OF  "spec H19" *)

destruct (can_alloc_variables jm (fn_vars f)) as [ve' [jm' [? ?]]].
auto.
rewrite <- Genv.find_funct_find_funct_ptr in H16.
destruct (build_call_temp_env f (eval_exprlist (snd (split (fst fsig))) bl rho))
as [te' ?]; auto.
exists (State ve' te' (Kseq f.(fn_body) :: Kseq (Sreturn None) 
                                     :: Kcall ret f (vx) (tx) :: k)).
exists  jm'.
split.
split; auto.
eapply step_call_internal with (vargs:=eval_exprlist (snd (split (fst fsig))) bl rho); eauto. 
rewrite <- H3.  
eapply eval_expr_relate; try solve[rewrite H0; auto]; eauto. 
destruct (fsig). unfold fn_funsig in *. inv H18. 
eapply exprlist_eval; eauto. 
unfold type_of_function. destruct fsig; inv H18; auto. 

assert (n >= level jm')%nat.
destruct H20. clear - H22 H2.
change (level (m_phi jm)) with (level jm) in H2.
omega.
pose (rho3 := mkEnviron (ge_of rho) (make_venv ve') (make_tenv te')).
assert (app_pred (funassert Delta rho3) (m_phi jm')).
clear - H4 H20. destruct H20 as [? _].
apply (resource_decay_funassert _ _ _ _ _ H) in H4.
unfold rho3; clear rho3.
apply H4.
specialize (H19 te' ve' _ H22 _ (necR_refl _)).
spec H19; [clear H19|].
split; [split|]; auto. Focus 3. 
unfold rho3 in H23. unfold construct_rho. rewrite H0 in H23.
simpl ge_of in H23. auto. 
hnf. unfold func_tycontext'.
unfold construct_rho.  
clear - H0 TC2 TC3 H18 H16 H21 H15 H23 H17 H17'. 
unfold rho3 in *. simpl in *. destruct H23. 
destruct rho. inv H0. simpl in *. 
remember (split (fn_params f)). destruct p.
assert (TE := TC3). 
 apply typecheck_environ_sound in TC3.
destruct TC3 as [TC3 [TC4 TC5]]. 
simpl in *. if_tac in H16; try congruence. clear H0. 

eapply semax_call_typecheck_environ; eassumption.

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
clear - TC2 H21 TC4 H17.
admit.  (* should be easy *)
admit.  (* plausible?  *)
(* end   "spec H19" *)

specialize (H19 ora jm').
apply age_level in H13.
destruct H20.
change (level jm = S n) in H2. rewrite H2 in H24; inversion H24. subst n.
auto.

Qed.

Lemma semax_call: 
    forall Delta A (P Q: A -> assert) x F ret fsig a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params (fst fsig)) (snd fsig) -> 
           match_fsig fsig bl ret = true ->
  semax Hspec Delta
       (fun rho =>  tc_expr Delta a rho && tc_exprlist Delta (snd (split (fst fsig))) bl rho  && 
           (fun_assert  fsig A P Q (eval_expr a rho) && 
          (F rho * P x (make_args (map (@fst  _ _) (fst fsig))
                (eval_exprlist (snd (split (fst fsig))) bl rho) rho ))))
         (Scall ret a bl)
         (normal_ret_assert 
          (fun rho => (EX old:val, substopt ret old F rho * Q x (get_result ret rho)))).
Proof.
rewrite semax_unfold.  intros ? ? ? ? ? ? ? ? ? ? TCF ?.
destruct (match_fsig_e _ _ _ H) as [TC4 TC5]; clear H.
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
intros ora jm _ ?.
subst w.
apply extend_sepcon_andp in H3; auto.
destruct H3 as [H2 H3].
normalize in H3. unfold fun_assert in *. unfold res_predicates.fun_assert in *. 
destruct H3 as [[b [H3 H6]] H5].
specialize (H6 (b,0)).
rewrite jam_true in H6 by auto.
hnf in H3.
generalize H4; intros [_ H7].
specialize (H7 (b,0) (mk_funspec fsig A P Q) _ (necR_refl _) H6).
destruct H7 as [id [v [[H7 H8] H9]]].
hnf in H9.
simpl in H8. unfold val2adr in H8. destruct v; try contradiction.
symmetry in H8; inv H8.
rename H11 into H12.
destruct H2 as [TC1 TC2].
assert (H8: exists fs, (glob_types Delta)!id = Some (Global_func fs)).
auto.
destruct H8 as [fs H8].
generalize H4; intros [H10 _].
specialize (H10 id fs _ (necR_refl _) H8).
destruct H10 as [v' [b' [[H10] H13]]].
assert (H11: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)).
reflexivity.
simpl in H10. simpl in H7. inversion2 H7 H10.
simpl in H0. subst b'.
unfold func_at in H13.
rewrite H12 in H13.
destruct fs as [fsig' A' P' Q'].
assert (fsig' = fsig).
 clear - H6 H13.
 unfold pureat in *. simpl in *. inversion2 H6 H13. auto.
clear H15; subst fsig'.
hnf in H6,H13.
rewrite H6  in H13.
(*change (In (id, mk_funspec fsig A' P' Q') G) in H8. *)
inversion H13; clear H13.
subst A'.
apply inj_pair2 in H10. rename H10 into H15.
clear H6; pose (H6:=True).
clear H9; pose (H9:=True).

unfold filter_genv in H7.
invSome.
assert (b0=b/\ i=Int.zero) by (destruct (type_of_global psi b0); inv H10; auto).
destruct H0; subst b0 i.
clear H11. pose (H16:=True).
clear H12; pose (H12:=True).
remember (construct_rho (filter_genv psi) vx tx) as rho.
set (args := eval_exprlist (snd (split (fst fsig))) bl rho).
fold args in H5.
rename H10 into H10'.
destruct (function_pointer_aux A P P' Q Q' (m_phi jm)) as [H10 H11].
f_equal; auto.
clear H15.
specialize (H10 x (make_args (map (@fst  _ _) (fst fsig)) (eval_exprlist (snd (split (fst fsig)))bl rho) rho)).
specialize (H11 x).
rewrite <- sepcon_assoc in H5.
assert (H14: app_pred (|> (F0 rho * F rho * P' x (make_args (map (@fst  _ _) (fst fsig))
  (eval_exprlist (snd (split (fst fsig))) bl rho) rho))) (m_phi jm)).
do 3 red in H10.
apply eqp_later1 in H10.
rewrite later_sepcon.
apply pred_eq_e2 in H10.
eapply (sepcon_subp' (|>(F0 rho * F rho)) _ (|> P x (make_args (map (@fst  _ _) (fst fsig)) (eval_exprlist (snd (split (fst fsig))) bl rho) rho)) _ (level (m_phi jm))); eauto.
rewrite <- later_sepcon. apply now_later; auto.
eapply semax_call_aux; try eassumption.

unfold normal_ret_assert.
extensionality rho'.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
auto.
Qed.

Lemma semax_call_ext:
     forall Delta P Q ret a tl bl a' bl',
      typeof a = typeof a' ->
      (forall rho, 
          !! (typecheck_environ rho Delta = true) && P rho |-- !! (eval_expr a rho = eval_expr a' rho /\
                                           eval_exprlist tl bl rho = eval_exprlist tl bl'  rho )) ->
  semax Hspec Delta P (Scall ret a bl) Q ->
  semax Hspec  Delta P (Scall ret a' bl') Q.
Proof.
intros.
rewrite semax_unfold in H1|-*.
rename H1 into H2. pose proof I.
intros.
specialize (H2 psi w Prog_OK k F H3 H4).
intros tx vx; specialize (H2 tx vx).
intros ? ? ? ? ?.
specialize (H2 y H5 a'0 H6 H7).
destruct H7 as [[? ?] _].
hnf in H7.
pose proof I.
hnf in H2|-*; intros.
specialize (H2 ora jm H10).
eapply convergent_controls_safe; try apply H2.
reflexivity.
simpl; intros ? ?. unfold cl_after_external. destruct ret0; auto.
reflexivity.
intros.
destruct H8 as [w1 [w2 [_ [_ ?]]]].
remember (construct_rho (filter_genv psi) vx tx) as rho.
specialize (H0 rho w2 (conj H7 H8)).
destruct H0.
assert (forall vf, Clight.eval_expr psi vx tx (m_dry jm) a vf
               -> Clight.eval_expr psi vx tx (m_dry jm) a' vf).
clear - H H0 H1 H7 H9 .
admit.  (* typechecking proof, without typechecking on a we can't do relate
                               Also need uniqueness proof for eval_expr *) 
assert (forall tyargs vargs, 
             Clight.eval_exprlist psi vx tx (m_dry jm) bl tyargs vargs ->
             Clight.eval_exprlist psi vx tx (m_dry jm) bl' tyargs vargs).
clear - H12 H1 H7.
admit.  (* typechecking proof, same difficulties as above *) 
destruct H12; split; auto.
inv H12; [eapply step_call_internal | eapply step_call_external ]; eauto.
rewrite <- H; auto.
rewrite <- H; auto.
auto.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Admitted.

Lemma  semax_return :
   forall Delta R ret,
      semax Hspec Delta 
                (fun rho => R EK_return (eval_expropt ret rho) rho)
                (Sreturn ret)
                R.
Proof.
intros.
hnf; intros.
rewrite semax_fold_unfold.
intros psi.
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
apply nec_nat.
apply necR_level in H2.
apply le_trans with (level n); auto.
apply (pred_nec_hereditary _ _ _ H4) in H0.
clear w n H2 H1 H4.
destruct H3 as [[H3 ?] ?].
pose proof I. 
remember ((construct_rho (filter_genv psi) ve te)) as rho.
specialize (H0 EK_return (eval_expropt ret rho) te ve).
specialize (H0 _ (le_refl _) _ (necR_refl _)).
spec H0.
rewrite <- Heqrho.
unfold frame_ret_assert.
split; auto.
split; auto.
rewrite sepcon_comm; auto.
intros ? ? ? ?.
specialize (H0 ora jm (eq_refl _) H6).
eapply convergent_controls_safe; try apply H0.
simpl; auto.
intros ? ?; simpl.
unfold cl_after_external.
auto.
simpl; auto.
intros.
simpl in H7.
destruct H7; split; auto.
revert H7; simpl.
destruct ret. simpl.
case_eq (call_cont k); intros.
inv H9.
inv H14.
destruct c.
elimtype False; clear - H7.
admit.  (* easy *)
elimtype False; clear - H7.
admit.  (* easy *)
elimtype False; clear - H7.
admit.  (* easy *)
elimtype False; clear - H7.
admit.  (* easy *)
destruct l0.
clear H0 H2 H8.
inv H9.
destruct optid.
destruct H17; congruence.
inv H11.
destruct H17.
econstructor; try eassumption; simpl.
2: split; [congruence | eassumption].
exists (eval_expr e (construct_rho (filter_genv psi) ve te)).
split.
apply eval_expr_relate with (Delta := Delta); auto.
admit.  (* typechecking proof, only works if e (ret) typechecks*)
admit.  (* typechecking proof, but this will be difficult because I think there's not enough
                 information to know that f is really the same as the function that Delta assumes *)
inv H9.
destruct optid.
destruct H20; congruence.
symmetry in H14; inv H14.
destruct H20.
elimtype False.
admit.  (* typechecking proof, but this will be difficult because I think there's not enough
                 information to know that f is really the same as the function that Delta assumes;
               if we could know that, then the fact that fn_return f = Tvoid would do it *)
simpl.
intro.
inv H7.
econstructor; try eassumption.
rewrite call_cont_idem in H13; auto.
Qed.

End extensions.
