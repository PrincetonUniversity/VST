Require Import Coq.Logic.FunctionalExtensionality.
Require Import VST.veric.juicy_base.
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
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
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas (*VST.veric.juicy_mem_ops*).
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.semax_conseq.
Import LiftNotation.

Lemma TTL3 l: typelist_of_type_list (Clight_core.typelist2list l) = l.
Proof. induction l; simpl; trivial. f_equal; trivial . Qed.

Notation mk_funspec' := (@mk_funspec (fun A => A -d> argsassert) (fun A => A -d> assert)).

Section mpred.

Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs}.

Lemma typecheck_expr_sound' :
  forall {CS'} Delta rho e,
    typecheck_environ Delta rho ->
    tc_expr(CS := CS') Delta e rho ⊢ ⌜tc_val (typeof e) (eval_expr e rho)⌝.
Proof.
  intros; apply typecheck_expr_sound; done.
Qed.

Lemma tc_environ_make_args':
 forall argsig retsig bl rho Delta
   (Htc : tc_environ Delta rho),
  tc_exprlist Delta (snd (split argsig)) bl rho
  ⊢ ⌜tc_environ (funsig_tycontext (argsig, retsig)) (make_args (map fst argsig)
         (eval_exprlist (snd (split argsig)) bl rho) rho)⌝.
Proof.
  intros.
  rewrite /tc_environ /tc_exprlist /=.
  revert bl; induction argsig; destruct bl as [ | b bl]; simpl; intros; unfold_lift.
  * iPureIntro; intros _; split3; hnf; try split; intros; try rewrite /funsig_tycontext /lookup /ptree_lookup ?Maps.PTree.gempty // in H |- *.
    destruct H as [? H]; inv H.
  * iPureIntro; done.
  * destruct a as [i ti]; simpl.
    destruct (split argsig) eqn:?; simpl.
    unfold_lift; iPureIntro; inversion 1.
  * destruct a as [i ti]; simpl.
    destruct (split argsig) eqn:?; simpl.
    specialize (IHargsig bl).
    rewrite /typecheck_expr; fold typecheck_expr.
    rewrite !denote_tc_assert_andp.
    unfold_lift.
    rewrite IHargsig; clear IHargsig.
    iIntros "(H & (%Ht & % & %))".
    unfold typecheck_environ; simpl.
    rewrite tc_val_sem_cast //.
    iDestruct "H" as %?%tc_val_tc_val'; iPureIntro.
    split3; auto.
    unfold typecheck_temp_environ; intros ?? Hset.
    destruct (ident_eq i id).
    - subst.
      rewrite /lookup /ptree_lookup Maps.PTree.gss in Hset; inv Hset.
      rewrite Map.gss; eauto.
    - rewrite Map.gso //.
      apply (Ht id ty).
      rewrite /lookup /ptree_lookup Maps.PTree.gso // in Hset.
Qed.

(* Scall *)

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

Definition substopt {A} (ret: option ident) (v: environ -> val) (P: environ -> A)  : environ -> A :=
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
t1 !! id = t !! id.
Proof.
induction l1;
intros.
simpl in *. destruct l2; inv H0. auto.
simpl in H0. destruct a. destruct l2; inv H0.
specialize (IHl1 l2 (Maps.PTree.set i v t) id t1).
simpl in H. intuition. setoid_rewrite Maps.PTree.gsspec in H3.
destruct (peq id i). subst; tauto. auto.
Qed.

Lemma pass_params_ni :
  forall  l2
     (te' : temp_env) (id : positive) te l,
   bind_parameter_temps l2 l (te) = Some te' ->
   (In id (map fst l2) -> False) ->
   Map.get (make_tenv te') id = te !! id.
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
t1 !! i = t2 !! i ->
te !! i = te2 !! i.
Proof.
induction l1; intros; simpl in *; try destruct a; destruct l2; inv H; inv H0.
apply H1.
eapply IHl1. apply H3. apply H2.
repeat setoid_rewrite Maps.PTree.gsspec. destruct (peq i i0); auto.
Qed.


Lemma smaller_temps_exists' : forall l l1 te te' id i t,
bind_parameter_temps l l1 (Maps.PTree.set id Vundef t) = Some te ->
i <> id ->
(bind_parameter_temps l l1 t = Some te') -> te' !! i = te !! i.
Proof.
induction l; intros.
- simpl in *. destruct l1; inv H. inv H1. setoid_rewrite Maps.PTree.gso; auto.
- simpl in *. destruct a. destruct l1; inv H.
  eapply smaller_temps_exists2. apply H1. apply H3.
  intros. repeat setoid_rewrite Maps.PTree.gsspec. rewrite Maps.PTree.gsspec. destruct (peq i i0); auto.
  destruct (peq i id). subst. tauto. auto.
Qed.

Lemma smaller_temps_exists'' : forall l l1 te id i t,
bind_parameter_temps l l1 (Maps.PTree.set id Vundef t)=  Some te ->
i <> id ->
exists te', (bind_parameter_temps l l1 t = Some te').
Proof.
intros.
eapply bind_exists_te; eauto.
Qed.

Lemma smaller_temps_exists : forall l l1 te id i t,
bind_parameter_temps l l1 (Maps.PTree.set id Vundef t)=  Some te ->
i <> id -> 
exists te', (bind_parameter_temps l l1 t = Some te' /\ te' !! i = te !! i).
Proof.
intros. destruct (smaller_temps_exists'' _ _ _ _ _ _ H H0) as [x ?].
exists x. split. auto.
eapply smaller_temps_exists'; eauto.
Qed.


Lemma alloc_vars_lookup :
forall ge id m1 l ve m2 e ,
list_norepet (map fst l) ->
(forall i, In i (map fst l) -> e !! i = None) ->
Clight.alloc_variables ge (e) m1 l ve m2 ->
(exists v, e !! id = Some v) ->
ve !! id = e !! id.
Proof.
intros.
generalize dependent e.
revert ve m1 m2.

induction l; intros.
inv H1. auto.

inv H1. simpl in *. inv H.
destruct H2.
assert (id <> id0).
intro. subst.  specialize (H0 id0). spec H0. auto. rewrite H // in H0.
eapply IHl in H10.
setoid_rewrite Maps.PTree.gso in H10; auto.
auto. intros. setoid_rewrite Maps.PTree.gsspec. if_tac. subst. tauto.
apply H0. auto.
setoid_rewrite Maps.PTree.gso; auto. eauto.
Qed.

Lemma alloc_vars_lemma : forall ge id ty l m1 m2 ve ve'
(SD : forall i, In i (map fst l) -> ve !! i = None),
list_norepet (map fst l) ->
Clight.alloc_variables ge ve m1 l ve' m2 ->
(In (id, ty) l ->
exists v, ve' !! id = Some (v, ty)).
Proof.
  intros.
  generalize dependent ve.
  revert m1 m2.
  induction l; intros; first done.
  destruct a; simpl in *.
  destruct H1 as [[=] | H1].
  - subst. inv H0. inv H. apply alloc_vars_lookup with (id := id) in H9; auto.
    rewrite H9. setoid_rewrite Maps.PTree.gss. eauto.
    { intros. destruct (peq i id); first by subst; tauto. setoid_rewrite Maps.PTree.gso; eauto. }
    { setoid_rewrite Maps.PTree.gss; eauto. }
  - inv H0. inv H. apply IHl in H10; auto.
    intros. setoid_rewrite Maps.PTree.gsspec. if_tac; last eauto. subst; done.
Qed.

Lemma alloc_vars_match_venv_gen: forall ge ve m l0 l ve' m',
  match_venv (make_venv ve) l0 ->
  Clight.alloc_variables ge ve m l ve' m' ->
  match_venv (make_venv ve') (l0 ++ l).
Proof.
  intros.
  revert dependent l0; induction H0; intros.
  { rewrite app_nil_r //. }
  specialize (IHalloc_variables (l0 ++ [(id, ty)])).
  rewrite -assoc in IHalloc_variables; apply IHalloc_variables.
  rewrite /match_venv /make_venv in H1 |- *; intros i; specialize (H1 i).
  destruct (eq_dec i id).
  - subst; rewrite Maps.PTree.gss in_app; simpl; auto.
  - rewrite Maps.PTree.gso //.
    destruct (Maps.PTree.get i e) as [(?, ?)|]; first rewrite in_app; simpl; auto.
Qed.

Lemma alloc_vars_match_venv: forall ge m l ve' m',
  Clight.alloc_variables ge empty_env m l ve' m' ->
  match_venv (make_venv ve') l.
Proof.
  intros; eapply (alloc_vars_match_venv_gen _ _ _ []) in H; auto.
  rewrite /match_venv /make_venv; intros.
  rewrite Maps.PTree.gempty //.
Qed.

Lemma semax_call_typecheck_environ:
  forall (Delta : tycontext) (args: list val) (psi : genv)
           m (b : Values.block) (f : function)
     (H17 : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
     (H17' : list_norepet (map fst (fn_vars f)))
     (H16 : Genv.find_funct_ptr psi b = Some (Internal f))
     (ve' : env) m' (te' : temp_env)
     (H15 : alloc_variables psi empty_env m (fn_vars f) ve' m')
     (TC5: typecheck_glob_environ (filter_genv psi) (glob_types Delta))
     (TC8 : tc_vals (snd (split (fn_params f))) args)
     (H21 : bind_parameter_temps (fn_params f) args
              (create_undef_temps (fn_temps f)) = Some te'),
   typecheck_environ (func_tycontext' f Delta)
      (construct_rho (filter_genv psi) ve' te').
Proof.
  intros.
  pose (rho3 := mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).
  split3; auto.
  - unfold typecheck_temp_environ; simpl; intros ?? H.
    apply func_tycontext_t_sound in H; auto.
    clear - H21 H TC8 H17.
    destruct (in_dec (EqDec_prod _ _ _ _) (id, ty) (fn_params f)).
    + forget (create_undef_temps (fn_temps f)) as temps.
      rewrite snd_split in TC8.
      generalize dependent temps. generalize dependent args. generalize dependent te'.
      induction (fn_params f); intros; first done.
      destruct a; simpl in *.
      destruct args; first done.
      destruct TC8 as [TC8' TC8].
      clear H; destruct i as [H | H].
      * inv H.
        rewrite -> (pass_params_ni _ _ id _ _ H21)
           by (inv H17; contradict H1; apply in_app; auto).
        rewrite /lookup /ptree_lookup Maps.PTree.gss.
        apply tc_val_tc_val' in TC8'; eauto.
      * inv H17; eauto.
    + destruct H as [? | H]; first done.
      apply list_norepet_app in H17 as (? & ? & Hdisj).
      rewrite -> (pass_params_ni _ _ id _ _ H21).
      2: { intros; contradiction (Hdisj id id); auto.
          rewrite in_map_iff; exists (id, ty); auto. }
      clear - H; forget (fn_temps f) as temps; induction temps; first done.
      destruct a; simpl in *.
      destruct (eq_dec i id).
      * subst; rewrite /lookup /ptree_lookup Maps.PTree.gss; eauto.
        eexists; split; eauto; apply tc_val'_Vundef.
      * rewrite /lookup /ptree_lookup Maps.PTree.gso //.
        destruct H; [by inv H | eauto].
  - rewrite /typecheck_var_environ /=; intros.
    rewrite (func_tycontext_v_sound (fn_vars f) id ty); auto.
    rewrite /Map.get /make_venv.
    split.
    + intros; eapply alloc_vars_lemma; eauto.
      intros; apply Maps.PTree.gempty.
    + intros (? & H); apply alloc_vars_match_venv in H15.
      rewrite /match_venv /make_venv in H15.
      specialize (H15 id); rewrite H // in H15.
Qed.

Lemma free_list_free:
  forall m b lo hi l' m',
       free_list m ((b,lo,hi)::l') = Some m' ->
         {m2 | free m b lo hi = Some m2 /\ free_list m2 l' = Some m'}.
Proof.
  simpl; intros.
  destruct (free m b lo hi). eauto. inv H.
Qed.

Definition freeable_blocks: list (Values.block * BinInt.Z * BinInt.Z) -> mpred :=
  fold_right (fun (bb: Values.block*BinInt.Z * BinInt.Z) a =>
                        match bb with (b,lo,hi) =>
                                          VALspec_range (hi-lo) Share.top (b,lo) ∗ a
                        end)
                    emp.

Lemma stackframe_of_freeable_blocks:
  forall {CS'} Delta f rho ge ve,
      cenv_sub (@cenv_cs CS') (genv_cenv ge) ->
      Forall (fun it => complete_type (@cenv_cs CS') (snd it) = true) (fn_vars f) ->
      list_norepet (map fst (fn_vars f)) ->
      ve_of rho = make_venv ve ->
      guard_environ (func_tycontext' f Delta) f rho ->
       stackframe_of f rho ⊢ freeable_blocks (blocks_of_env ge ve).
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
 trans (foldr bi_sep emp (map (fun idt => var_block Share.top idt rho) (fn_vars f))).
 { clear; induction (fn_vars f); simpl; auto; monPred.unseal. rewrite -IHl; by monPred.unseal. }
 unfold var_block. unfold eval_lvar. monPred.unseal; simpl.
 rewrite H0. unfold make_venv. forget (ge_of rho) as ZZ. rewrite H0 in H7; clear rho H0.
 revert ve H1 H7; induction (fn_vars f); simpl; intros.
 case_eq (Maps.PTree.elements ve); simpl; intros; auto.
 destruct p as [id ?].
 pose proof (Maps.PTree.elements_complete ve id p). rewrite H0 in H2. simpl in H2.
 specialize (H7 id). unfold make_venv in H7. rewrite H2 in H7; auto.
 destruct p; inv H7.
 inv H.
 destruct a as [id ty]. simpl in *.
 simpl in COMPLETE. inversion COMPLETE; subst.
 clear COMPLETE; rename H5 into COMPLETE; rename H2 into COMPLETE_HD.
 specialize (IHl COMPLETE H4 (Maps.PTree.remove id ve)).
 assert (exists b, Maps.PTree.get id ve = Some (b,ty)). {
  specialize (H1 id ty).
  setoid_rewrite Maps.PTree.gss in H1. destruct H1 as [[b ?] _]; auto. exists b; apply H.
 }
 destruct H as [b H].
 destruct (@Maps.PTree.elements_remove _ id (b,ty) ve H) as [l1 [l2 [? ?]]].
 rewrite H0.
 rewrite map_app. simpl map.
 trans (freeable_blocks ((b,0,@Ctypes.sizeof ge ty) :: (map (block_of_binding ge) (l1 ++ l2)))).
 2:{
   clear.
   induction l1; simpl; try auto.
   destruct a as [id' [hi lo]]. simpl in *.
   rewrite -IHl1.
   rewrite !assoc (comm _ (VALspec_range _ _ _ )) //. }
 unfold freeable_blocks; simpl. rewrite <- H2.
 apply bi.sep_mono.
 { unfold Map.get. rewrite H. rewrite eqb_type_refl.
   unfold memory_block. iIntros "(% & % & H)".
   rename H6 into H99.
   rewrite memory_block'_eq.
   2: rewrite Ptrofs.unsigned_zero; lia.
   2:{ rewrite Ptrofs.unsigned_zero. rewrite Zplus_0_r.
       rewrite Z2Nat.id.
       change (Ptrofs.unsigned Ptrofs.zero) with 0 in H99.
       lia.
       unfold sizeof.
       pose proof (sizeof_pos ty); lia. }
 rewrite Z.sub_0_r.
 unfold memory_block'_alt.
 rewrite -> if_true by apply readable_share_top.
 rewrite Z2Nat.id.
 + rewrite (cenv_sub_sizeof HGG); auto.
 + unfold sizeof; pose proof (sizeof_pos ty); lia. }
 etrans; last apply IHl.
 clear - H3.
 induction l; simpl; auto.
 destruct a as [id' ty']. simpl in *.
 apply bi.sep_mono; auto.
 replace (Map.get (fun id0 : positive => Maps.PTree.get id0 (Maps.PTree.remove id ve)) id')
   with (Map.get (fun id0 : positive => Maps.PTree.get id0 ve) id'); auto.
 unfold Map.get.
 rewrite Maps.PTree.gro; auto.
 intros id' ty'; specialize (H1 id' ty').
 { split; intro.
 - destruct H1 as [H1 _].
   assert (id<>id').
   intro; subst id'.
   clear - H3 H5; induction l; simpl in *. setoid_rewrite Maps.PTree.gempty in H5; inv H5.
   destruct a; simpl in *.
   setoid_rewrite Maps.PTree.gso in H5. auto. auto.
   destruct H1 as [v ?].
   setoid_rewrite Maps.PTree.gso; auto.
   exists v. unfold Map.get. rewrite Maps.PTree.gro; auto.
 - unfold Map.get in H1,H5.
   assert (id<>id').
     clear - H5; destruct H5. intro; subst. rewrite Maps.PTree.grs in H. inv H.
   rewrite -> Maps.PTree.gro in H5 by auto.
   rewrite <- H1 in H5. setoid_rewrite -> Maps.PTree.gso in H5; auto. }
 hnf; intros.
 destruct (make_venv (Maps.PTree.remove id ve) id0) eqn:H5; auto.
 destruct p.
 unfold make_venv in H5.
 destruct (peq id id0).
 subst. rewrite Maps.PTree.grs in H5. inv H5.
 rewrite -> Maps.PTree.gro in H5 by auto.
 specialize (H7 id0). unfold make_venv in H7. rewrite H5 in H7.
 destruct H7; auto. inv H6; congruence.
Qed.

Definition maybe_retval (Q: @assert Σ) retty ret :=
 assert_of (match ret with
 | Some id => fun rho => ⌜tc_val' retty (eval_id id rho)⌝ ∧ Q (get_result1 id rho)
 | None =>
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => ∃ v: val, ⌜tc_val' retty v⌝ ∧ Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end).

Lemma Forall_filter: forall {A} P (l: list A) f, Forall P l -> Forall P (List.filter f l).
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

Lemma free_stackframe :
  forall {CS'} Delta f m ge ve te
  (NOREP: list_norepet (map (@fst _ _) (fn_vars f)))
  (COMPLETE: Forall (fun it => complete_type (@cenv_cs CS') (snd it) = true) (fn_vars f))
  (HGG: cenv_sub (@cenv_cs CS') (genv_cenv ge)),
   guard_environ (func_tycontext' f Delta) f
        (construct_rho (filter_genv ge) ve te) ->
   mem_auth m ∗ stackframe_of f (construct_rho (filter_genv ge) ve te) ⊢
   |==> ∃ m2, ⌜free_list m (blocks_of_env ge ve) = Some m2⌝ ∧ mem_auth m2.
Proof.
  intros.
  iIntros "(Hm & stack)".
  rewrite stackframe_of_freeable_blocks //.
  clear.
  forget (blocks_of_env ge ve) as el.
  iInduction el as [|] "IHel" forall (m); first eauto.
  destruct a as ((id, b), t); simpl.
  iDestruct "stack" as "(H & stack)".
  iDestruct (VALspec_range_can_free with "[$Hm $H]") as %(m' & ?).
  rewrite /= Zplus_minus in H; rewrite H.
  iMod (VALspec_range_free with "[$Hm $H]") as "Hm".
  iApply ("IHel" with "Hm stack").
Qed.

Definition tc_fn_return (Delta: tycontext) (ret: option ident) (t: type) :=
 match ret with
 | None => True%type
 | Some i => match (temp_types Delta) !! i with Some t' => t=t' | _ => False%type end
 end.

Lemma same_glob_funassert':
  forall Delta1 Delta2 rho rho',
     (forall id, (glob_specs Delta1) !! id = (glob_specs Delta2) !! id) ->
      ge_of rho = ge_of rho' ->
              funassert Delta1 rho ⊣⊢ funassert Delta2 rho'.
Proof.
  assert (forall Delta Delta' rho rho',
             (forall id, (glob_specs Delta) !! id = (glob_specs Delta') !! id) ->
             ge_of rho = ge_of rho' ->
             funassert Delta rho ⊢ funassert Delta' rho') as H; last by intros; iSplit; iApply H.
  intros ???? H; simpl; intros ->.
  iIntros "(#? & H2)"; iSplit.
  - iIntros "!>" (??); rewrite -H //.
  - setoid_rewrite <- H; done.
Qed.

Definition thisvar (ret: option ident) (i : ident) : Prop :=
 match ret with None => False | Some x => x=i end.

Lemma closed_wrt_modvars_Scall:
  forall ret a bl, @closed_wrt_modvars Σ (Scall ret a bl) = closed_wrt_vars (thisvar ret).
Proof.
intros.
unfold closed_wrt_modvars.
extensionality F.
f_equal.
 extensionality i; unfold modifiedvars, modifiedvars', insert_idset.
 unfold isSome, idset0, insert_idset; destruct ret; simpl; auto.
 destruct (ident_eq i0 i).
 subst. setoid_rewrite Maps.PTree.gss. apply prop_ext; split; auto.
 setoid_rewrite -> Maps.PTree.gso; last auto. rewrite Maps.PTree.gempty.
 apply prop_ext; split; intro; contradiction.
Qed.

Lemma assert_safe_for_external_call {psi E curf vx ret ret0 tx k z'} :
      assert_safe Espec psi E curf vx (set_opttemp ret (force_val ret0) tx)
         (Cont k) (construct_rho (filter_genv psi) vx (set_opttemp ret (force_val ret0) tx)) ⊢
  jsafeN Espec psi E z' (Returnstate (force_val ret0) (Kcall ret curf vx tx k)).
Proof.
  iIntros "H".
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "? !>".
  iExists _, _; iSplit; first by iPureIntro; constructor.
  iFrame.
  by iApply assert_safe_jsafe'.
Qed.

Lemma semax_call_external
 E (Delta : tycontext)
 (A : Type)
 (P : A -> argsassert)
 (Q : A -> assert)
 (F0 : assert)
 (ret : option ident) (curf : function) (fsig : typesig) (cc : calling_convention)
 (R : ret_assert) (psi : genv) (vx : env) (tx : temp_env)
 (k : cont) (rho : environ) (ora : OK_ty) (b : Values.block)
 (TCret : tc_fn_return Delta ret (snd fsig))
 (TC3 : guard_environ Delta curf rho)
 (TC5 : snd fsig = Tvoid -> ret = None)
 (H : closed_wrt_vars (thisvar ret) F0)
 (H0 : rho = construct_rho (filter_genv psi) vx tx)
 (args : list val)
 (ff : Clight.fundef)
 (H16 : Genv.find_funct psi (Vptr b Ptrofs.zero) = Some ff)
 (TC8 : tc_vals (fst fsig) args)
 (Hargs : Datatypes.length (fst fsig) = Datatypes.length args)
 (ctl : cont) (Hctl : ∀ ret0 z', assert_safe Espec psi E curf vx (set_opttemp ret (force_val ret0) tx)
             (exit_cont EK_normal None k)  (construct_rho (filter_genv psi) vx (set_opttemp ret (force_val ret0) tx)) ⊢
    jsafeN Espec psi E z' (Returnstate (force_val ret0) ctl)) :
 □ believe_external Espec psi E (Vptr b Ptrofs.zero) fsig cc A P Q -∗
 ▷ (<affine> rguard Espec psi E Delta curf (frame_ret_assert R F0) k -∗
    funassert Delta rho -∗
    F0 rho -∗
    (|={E}=> ∃ (x1 : A) (F1 : assert),
               (F1 rho ∗ P x1 (ge_of rho, args))
               ∧ (∀ rho' : environ,
                    ■ ((∃ old : val, substopt ret (` old) F1 rho' ∗
                          maybe_retval (Q x1) (snd fsig) ret rho') -∗ RA_normal R rho'))) -∗
    jsafeN Espec psi E ora (Callstate ff args ctl)).
Proof.
pose proof TC3 as Hguard_env.
destruct TC3 as [TC3 TC3'].
rewrite /believe_external H16.
iIntros "#ext".
destruct ff; first done.
iDestruct "ext" as "((-> & -> & %Eef & %Hinline) & He & Htc)".
rename t into tys.
iIntros "!> rguard fun F0 HR".
iMod "HR" as (??) "((F1 & P) & #HR)".
iMod ("He" $! psi x1 (F0 rho ∗ F1 rho) (typlist_of_typelist tys) args with "[F0 F1 P]") as "He1".
{ subst rho; iFrame; iPureIntro; split; auto.
  (* typechecking arguments *)
  rewrite Eef; simpl.
  clear - TC8. rewrite TTL2.
  revert args TC8; induction (Clight_core.typelist2list tys); destruct args; intros; try discriminate; auto.
  inv TC8.
  split; auto.
  apply tc_val_has_type; auto. }
clear TC8. simpl fst in *. simpl snd in *.
rewrite /jsafeN jsafe_unfold /jsafe_pre.
iIntros "!>" (?) "s"; iDestruct ("He1" with "s") as (x') "(pre & post)".
destruct Hinline as [Hinline | ?]; last done.
iRight; iRight; iExists _, _, _; iSplit.
{ iPureIntro; simpl.
  rewrite Hinline //. }
rewrite Eef TTL3; iFrame "pre".
iDestruct "rguard" as "#rguard".
iNext.
iIntros (?? [??]) "?".
iMod ("post" with "[$]") as (?) "(? & Q & F0 & F)".
iDestruct ("Htc" with "[Q]") as %Htc; first by iFrame.
pose (tx' := match ret,ret0 with
                   | Some id, Some v => Maps.PTree.set id v tx
                   | _, _ => tx
                   end).
iSpecialize ("rguard" $! EK_normal None tx' vx).
set (rho' := construct_rho _ _ _).
iPoseProof ("HR" $! rho' with "[Q F]") as "R".
{ iExists match ret with
       | Some id =>
           match tx !! id with
           | Some old => old
           | None => Vundef
           end
       | None => Vundef
       end; subst rho' tx'; unfold_lift; destruct ret; simpl.
  * destruct ret0.
    2: { clear - TC5 Htc; destruct t0; try contradiction; by spec TC5. }
    destruct TC3 as [TC3 _].
    hnf in TC3; simpl in TC3.
    hnf in TCret.
    destruct ((temp_types Delta) !! i) as [ti|] eqn: Hi; try contradiction.
    destruct (TC3 _ _ Hi) as (vi & Htx & ?); subst. 
    rewrite /get_result1 /eval_id /= /make_tenv /Map.get in Htx |- *; rewrite /lookup /ptree_lookup Maps.PTree.gss Htx.
    rewrite /subst /env_set /= -map_ptree_rel Map.override Map.override_same //; iFrame.
    iSplit; first by iPureIntro; apply tc_val_tc_val'; destruct ti; try (specialize (TC5 eq_refl)).
    rewrite /make_ext_rval.
    destruct ti; try destruct i0, s; try destruct f; try (specialize (TC5 eq_refl)); iFrame; first done; destruct v; contradiction.
  * subst rho; iFrame.
    destruct (eq_dec t0 Tvoid); first by subst.
    destruct ret0; last by destruct t0; contradiction.
    iAssert (∃ v0 : val, ⌜tc_val' t0 v0⌝ ∧ Q x1 (env_set (globals_only (construct_rho (filter_genv psi) vx tx)) ret_temp v0)) with "[Q]" as "?"; last by destruct t0; iFrame.
    iExists v; iSplit; first by iPureIntro; apply tc_val_tc_val'; destruct t0.
    rewrite /make_ext_rval /env_set /=.
    destruct t0; try destruct i, s; try destruct f; try (specialize (TC5 eq_refl)); iFrame; first done; destruct v; contradiction. }
iIntros "!>"; iExists _, _; iSplit; first done; iFrame.
assert (tx' = set_opttemp ret (force_val ret0) tx) as Htx'.
{ subst tx'.
  clear - Htc TCret TC5. hnf in Htc, TCret.
  destruct ret0, ret; simpl; auto.
  destruct ((temp_types Delta) !! i); try contradiction.
  destruct t0; try contradiction. spec TC5; auto. inv TC5. }
iSpecialize ("rguard" with "[-]").
{ rewrite proj_frame /=; monPred.unseal; iFrame.
  iSplit; [|iSplitR "fun"].
  * iPureIntro; subst rho rho' tx'.
    destruct ret; last done; destruct ret0; last done.
    rewrite /construct_rho -map_ptree_rel.
    apply guard_environ_put_te'; try done.
    simpl in TCret; intros ? Hi; rewrite Hi in TCret; subst.
    apply tc_val_tc_val'; destruct t; try (specialize (TC5 eq_refl)); done.
  * iSplit; last done.
    rewrite (H _ (make_tenv tx')); first by subst.
    subst rho tx'; rewrite /= /Map.get /make_tenv.
    destruct ret; last auto; destruct ret0; last auto.
    intros j; destruct (eq_dec j i); simpl; subst; auto.
    rewrite Maps.PTree.gso; auto.
  * iApply (same_glob_funassert' _ _ _ rho' with "fun"); subst rho rho'; done. }
subst rho' tx'; rewrite Htx'.
by iApply Hctl.
Qed.

Lemma ge_of_make_args:
    forall s a rho, ge_of (make_args s a rho) = ge_of rho.
Proof.
induction s; intros.
 destruct a; auto.
 simpl in *. destruct a0; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

Lemma ve_of_make_args:
    forall s a rho, length s = length a -> ve_of (make_args s a rho) = (Map.empty _).
Proof.
induction s; intros.
 destruct a; inv H; auto.
 simpl in *. destruct a0; inv H; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

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
  forall bodyparams args ge tx ve' te' (P : @argsassert Σ),
    list_norepet (map fst bodyparams) ->
    bind_parameter_temps bodyparams args tx = Some te' ->
    Forall (fun v : val => v <> Vundef) args ->
    P (filter_genv ge, args)
   ⊢ close_precondition (map fst bodyparams) P
           (construct_rho (filter_genv ge) ve' te').
Proof.
intros *. intros LNR BP VUNDEF.
iIntros "P"; iExists args; iFrame; iPureIntro; repeat (split; auto).
clear - LNR BP VUNDEF.
generalize dependent te'. generalize dependent tx. generalize dependent args.
induction bodyparams; simpl; intros; destruct args; inv BP; simpl; auto.
+ destruct a; discriminate.
+ destruct a. inv LNR. inv VUNDEF. simpl. erewrite <- IHbodyparams by eauto.
  f_equal.
  rewrite (pass_params_ni _ _ _ _ _ H0 H2) /lookup /ptree_lookup Maps.PTree.gss //.
Qed.

Lemma alloc_block:
 forall m n m' b (Halloc : Mem.alloc m 0 n = (m', b))
   (Hn : 0 <= n < Ptrofs.modulus),
   mem_auth m ==∗ mem_auth m' ∗ memory_block Share.top n (Vptr b Ptrofs.zero).
Proof.
  intros.
  iIntros "Hm"; iMod (mapsto_alloc_bytes with "Hm") as "($ & H)"; iIntros "!>".
  rewrite /memory_block Ptrofs.unsigned_zero.
  iSplit; first by iPureIntro; lia.
  rewrite Z.sub_0_r memory_block'_eq; [| lia..].
  rewrite /memory_block'_alt if_true; last auto.
  rewrite /VALspec_range Nat2Z.id.
  iApply (big_sepL_mono with "H"); intros.
  rewrite address_mapsto_VALspec_range /= VALspec1 //.
Qed.

Lemma alloc_stackframe {CS'}:
  forall m f (ge: genv) te
      (HGG: cenv_sub (@cenv_cs CS') (genv_cenv ge))
      (COMPLETE: Forall (fun it => complete_type (@cenv_cs CS') (snd it) = true) (fn_vars f))
      (Hsize: Forall (fun var => @Ctypes.sizeof ge (snd var) <= Ptrofs.max_unsigned) (fn_vars f)),
      list_norepet (map fst (fn_vars f)) ->
      mem_auth m ==∗ ∃ m' ve, ⌜Clight.alloc_variables ge empty_env m (fn_vars f) ve m' ∧ match_venv (make_venv ve) (fn_vars f)⌝ ∧
        mem_auth m' ∗ stackframe_of f (construct_rho (filter_genv ge) ve te).
Proof.
  intros.
  cut (mem_auth m ==∗ ∃ (m' : Memory.mem) (ve : env),
    ⌜(∀i, sub_option (empty_env !! i) (ve !! i)) ∧ alloc_variables ge empty_env m (fn_vars f) ve m'⌝
    ∧ mem_auth m' ∗ stackframe_of f (construct_rho (filter_genv ge) ve te)).
  { intros Hgen; rewrite Hgen; iIntros ">(% & % & (% & %) & ?) !>".
    iExists _, _; iFrame; iPureIntro; repeat (split; auto).
    eapply alloc_vars_match_venv; eauto. }
  rewrite /stackframe_of.
  forget (fn_vars f) as vars. clear f.
  assert (forall i, In i (map fst vars) -> empty_env !! i = None) as Hout.
  { intros; apply Maps.PTree.gempty. }
  forget empty_env as ve0.
  revert ve0 m Hout Hsize; induction vars; intros; simpl; iIntros "Hm".
  - iExists m, ve0; iFrame; monPred.unseal; iPureIntro.
    split; auto; split; auto.
    + intros; apply sub_option_refl.
    + constructor.
  - destruct a as (id, ty).
    destruct (Mem.alloc m 0 (sizeof ty)) as (m', b) eqn: Halloc.
    inv COMPLETE; inv Hsize; inv H.
    rewrite cenv_sub_sizeof // in H4.
    iMod (alloc_block with "Hm") as "(Hm & block)".
    { pose proof sizeof_pos ty; unfold sizeof, Ptrofs.max_unsigned in *; simpl in *; lia. }
    unshelve iMod (IHvars _ _ (Maps.PTree.set id (b,ty) ve0) with "Hm") as (?? (Hsub & ?)) "(Hm & ?)"; try done.
    { intros; rewrite /lookup /ptree_lookup Maps.PTree.gso //; last by intros ->.
      apply Hout; simpl; auto. }
    iIntros "!>"; iExists _, _; monPred.unseal; iFrame.
    rewrite /var_block /eval_lvar; monPred.unseal; simpl.
    replace (Map.get _ _) with (Some (b, ty)).
    rewrite eqb_type_refl; iFrame; iPureIntro; simpl.
    + split; last done; split.
      * intros i; specialize (Hsub i).
        destruct (eq_dec i id); last by rewrite /lookup /ptree_lookup Maps.PTree.gso in Hsub.
        subst; rewrite Hout //; simpl; auto.
      * econstructor; eauto.
        rewrite cenv_sub_sizeof //.
    + rewrite /Map.get /=.
      specialize (Hsub id); rewrite /lookup /ptree_lookup Maps.PTree.gss // in Hsub.
Qed.

Lemma map_snd_typeof_params:
  forall al bl, map snd al = map snd bl -> type_of_params al = type_of_params bl.
Proof.
induction al as [|[? ?]]; destruct bl as [|[? ?]]; intros; inv H; simpl; f_equal; auto.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Proof.
induction k; intros; simpl; auto.
Qed.

Lemma guard_fallthrough_return:
 forall (psi : genv) E (f : function)
   (ctl : cont) (ek : exitkind) (vl : option val)
  (te : temp_env) (ve : env) (rho' : environ)
  (P4 : assert),
  call_cont ctl = ctl ->
  (bind_ret vl (fn_return f) P4 rho' -∗
     assert_safe Espec psi E f ve te (exit_cont EK_return vl ctl) rho') ⊢
  (proj_ret_assert (function_body_ret_assert (fn_return f) P4) ek
      vl rho' -∗
   assert_safe Espec psi E f ve te (exit_cont ek vl ctl) rho').
Proof.
intros.
iIntros "Hsafe ret".
destruct ek; simpl proj_ret_assert; try monPred.unseal; try iDestruct "ret" as "[_ []]"; last by iApply "Hsafe"; iFrame.
iDestruct "ret" as (->) "ret"; simpl.
destruct (type_eq (fn_return f) Tvoid).
2:{ destruct (fn_return f); first contradiction; done. }
rewrite e.
iSpecialize ("Hsafe" with "[$]").
rewrite /assert_safe.
iIntros (? Hrho); iSpecialize ("Hsafe" $! _ Hrho).
destruct ctl; try done;
exfalso; clear - H; simpl in H; set (k:=ctl) in *;
unfold k at 1 in H; clearbody k;
induction ctl; try discriminate; eauto.
Qed.

Lemma semax_call_aux2
  {CS'} E (Delta : tycontext)
  (A : Type)
  (Q : A -> assert)
  (x : A)
  (F : assert)
  (F0 : assert)
  (ret : option ident)
  (curf : function)
  (fsig : typesig)
  (a : expr) (bl : list expr) (R : ret_assert)
  (psi : genv)
  (f : function)
  (TCret : tc_fn_return Delta ret (snd fsig))
  (TC5 : snd fsig = Tvoid -> ret = None)
  (H : closed_wrt_modvars (Scall ret a bl) F0)
  (HGG : cenv_sub (@cenv_cs CS') (genv_cenv psi))
  (COMPLETE : Forall
             (fun it : ident * type => complete_type (@cenv_cs CS') (snd it) = true)
             (fn_vars f))
  (H17 : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
  (H17' : list_norepet (map fst (fn_vars f)))
  (H18 : fst fsig = map snd (fst (fn_funsig f)) /\
      snd fsig = snd (fn_funsig f))
  vx tx k rho
  (H0 : rho = construct_rho (filter_genv psi) vx tx)
  (TC3 : guard_environ Delta curf rho)
  ctl (Hcont : call_cont ctl = ctl)
  (Hctl : ∀ ret0 z', assert_safe Espec psi E curf vx (set_opttemp ret (force_val ret0) tx)
             (exit_cont EK_normal None k)  (construct_rho (filter_genv psi) vx (set_opttemp ret (force_val ret0) tx)) ⊢
    jsafeN Espec psi E z' (Returnstate (force_val ret0) ctl)):
  (∀ rho' : environ,
        ■ ((∃ old : val,
               substopt ret (liftx old) F rho' ∗
               maybe_retval (Q x) (snd fsig) ret rho') -∗
              RA_normal R rho')) -∗
  ▷ rguard Espec psi E Delta curf (frame_ret_assert R F0) k -∗
  ⌜closed_wrt_modvars (fn_body f) (assert_of (fun _ : environ => F0 rho ∗ F rho))⌝ ∧
  rguard Espec psi E (func_tycontext' f Delta) f
         (frame_ret_assert
            (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x))
                              (stackframe_of' cenv_cs f)) (assert_of (fun _ : environ => F0 rho ∗ F rho)))
         ctl.
Proof.
  iIntros "#HR #rguard"; iSplit.
  { iPureIntro; repeat intro; f_equal. }
  iIntros (ek vl te ve) "!>".
  rewrite !proj_frame.
  monPred.unseal.
  iIntros "(% & ((F0 & F) & stack & Q) & fun)".
  iApply (guard_fallthrough_return with "[-Q] Q").
  iIntros "Q".
  set (rho' := construct_rho _ _ _).
  change (stackframe_of' cenv_cs f rho') with (stackframe_of f rho').
  rewrite /assert_safe.
  iIntros (? _); simpl.
  pose (rval := force_val vl).
  iAssert (▷ jsafeN Espec psi E ora (Returnstate rval (call_cont ctl))) with "[-stack]" as "Hsafe". 
  { iNext.
    iAssert ⌜match vl with Some v => tc_val (fn_return f) v | None => fn_return f = Tvoid end⌝ with "[Q]" as %TCvl.
    { rewrite /rval; destruct vl; simpl.
      + iDestruct "Q" as "[$ _]".
      + destruct (fn_return f); done. }
    iPoseProof ("HR" $! (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) with "[F Q]") as "R".
    { destruct H18 as [_ Hsig]; rewrite Hsig /fn_funsig /= in TC5 |- *.
      iExists match ret with
       | Some id =>
           match tx !! id with
           | Some old => old
           | None => Vundef
           end
       | None => Vundef
       end; subst rho'; unfold_lift; destruct ret; simpl.
      + destruct TC3 as [[TC3 _] _].
        hnf in TC3; simpl in TC3.
        hnf in TCret.
        destruct ((temp_types Delta) !! i) as [ti|] eqn: Hi; try contradiction.
        destruct (TC3 _ _ Hi) as (vi & Htx & ?); subst.
        rewrite /get_result1 /eval_id /= /make_tenv /Map.get in Htx |- *; rewrite /lookup /ptree_lookup Maps.PTree.gss Htx.
        rewrite /subst /env_set /= -map_ptree_rel Map.override Map.override_same //; iFrame.
        rewrite /rval; destruct vl; simpl.
        * iSplit; first by iPureIntro; apply tc_val_tc_val', TCvl.
          iDestruct "Q" as "[% $]".
        * iSplit; first by iPureIntro; apply tc_val'_Vundef.
          rewrite TCvl in TC5; specialize (TC5 eq_refl); done.
      + subst rho; iFrame.
        destruct vl; simpl; last by rewrite TCvl.
        iDestruct "Q" as (TCv) "Q".
        destruct (fn_return f); first contradiction; iExists _; iFrame; apply tc_val_tc_val' in TCv; iPureIntro; done. }
    iSpecialize ("rguard" $! EK_normal None with "[F0 R fun]").
    { rewrite proj_frame; subst rho; simpl proj_ret_assert; monPred.unseal; iFrame.
      iFrame "#".
      iSplit.
      + iPureIntro.
        destruct H18 as [H18 H18b].
        destruct ret; last done.
        unfold rval; destruct vl; simpl.
        * rewrite /construct_rho /set_opttemp -map_ptree_rel.
          apply guard_environ_put_te'; auto.
          simpl in TCret; intros ? Hi; rewrite Hi in TCret; subst.
          rewrite H18b; by apply tc_val_tc_val', TCvl.
        * rewrite H18b /= TCvl in TC5; specialize (TC5 eq_refl); done.
      + iSplit; last done; iSplit; last done.
        destruct ret as [ret|]; last done.
        rewrite closed_wrt_modvars_Scall in H.
        rewrite -(H (construct_rho (filter_genv psi) vx tx)); first done.
        simpl; intros.
        destruct (eq_dec ret i); first auto.
        rewrite -map_ptree_rel Map.gso; auto. }
    rewrite Hcont; by iApply Hctl. }
  destruct vl.
  - iIntros (?).
    iApply (bi.impl_intro_l (_ ∗ _) with "[stack Hsafe]"); last by iSplitL "stack"; [iApply "stack" | iApply "Hsafe"].
    iIntros "H".
    iApply jsafe_step; rewrite /jstep_ex.
    iIntros (?) "(Hm & ?)".
    iAssert ⌜∃ v' : val, Clight.eval_expr psi ve te m e v' ∧ Cop.sem_cast v' (typeof e) (fn_return f) m = Some v⌝ as %(v1 & ? & ?).
    { iDestruct "H" as "[H _]"; iApply ("H" with "Hm"). }
    iDestruct "H" as "(_ & stack & ?)".
    iMod (free_stackframe with "[$Hm $stack]") as (??) "Hm".
    iIntros "!>"; iExists _, _; iSplit; last iFrame.
    iPureIntro; rewrite {1}Hcont; econstructor; done.
  - iApply jsafe_step; rewrite /jstep_ex.
    iIntros (?) "(Hm & ?)".
    iMod (free_stackframe with "[$Hm $stack]") as (??) "Hm".
    iIntros "!>"; iExists _, _; iSplit; last iFrame.
    iPureIntro; rewrite {1}Hcont; econstructor; done.
Qed.

Lemma tc_eval_exprlist:
  forall {CS'} Delta tys bl rho,
    typecheck_environ Delta rho ->
    tc_exprlist(CS := CS') Delta tys bl rho ⊢
    ⌜tc_vals tys (eval_exprlist tys bl rho)⌝.
Proof.
induction tys; destruct bl; simpl in *; intros; auto.
unfold tc_exprlist in *; simpl.
unfold typecheck_expr; fold typecheck_expr.
rewrite !denote_tc_assert_andp IHtys // tc_val_sem_cast //.
unfold_lift; auto.
Qed.

Lemma tc_vals_length: forall tys vs, tc_vals tys vs -> length tys = length vs.
Proof.
induction tys; destruct vs; simpl; intros; auto; try contradiction.
destruct H; auto.
Qed.

Lemma eval_exprlist_relate:
  forall CS' (Delta : tycontext) (tys: typelist)
     (bl : list expr) (psi : genv) (vx : env) (tx : temp_env)
     (rho : environ) m,
   typecheck_environ Delta rho ->
   cenv_sub (@cenv_cs CS') (genv_cenv psi) ->
   rho = construct_rho (filter_genv psi) vx tx ->
   mem_auth m ∗ denote_tc_assert (typecheck_exprlist(CS := CS') Delta (typelist2list tys) bl) rho ⊢
   ⌜Clight.eval_exprlist psi vx tx m bl
     tys
     (@eval_exprlist CS' (typelist2list tys) bl rho)⌝.
Proof.
  intros.
  revert bl; induction tys; destruct bl; simpl; intros; iIntros "[Hm H]"; try iDestruct "H" as "[]".
  { iPureIntro; constructor. }
  unfold typecheck_expr; fold typecheck_expr.
  rewrite !denote_tc_assert_andp.
  iDestruct (IHtys with "[$Hm H]") as %?; first by iDestruct "H" as "[_ $]".
  rewrite bi.and_elim_l.
  iDestruct (eval_expr_relate with "[$Hm H]") as %?; first by iDestruct "H" as "[$ _]".
  iDestruct (cast_exists with "H") as %?.
  rewrite typecheck_expr_sound //; iDestruct "H" as (?) "H".
  iDestruct (cop2_sem_cast' with "[$Hm $H]") as %?; iPureIntro.
  econstructor; eauto.
  unfold_lift; congruence.
Qed.

Lemma believe_exists_fundef':
  forall {CS}
    {b : Values.block} {id_fun : ident} {psi : genv} E {Delta : tycontext}
    {fspec: funspec}
  (Findb : Genv.find_symbol (genv_genv psi) id_fun = Some b)
  (H3: (glob_specs Delta) !! id_fun = Some fspec),
  (⊢ believe(CS := CS) Espec E Delta psi Delta) ->
  {f : Clight.fundef | Genv.find_funct_ptr (genv_genv psi) b = Some f /\
   type_of_fundef f = type_of_funspec fspec}.
Proof.
  intros.
  destruct fspec as [fsig cc A P Q].
  simpl.
  assert (⊢ believe_external Espec psi E (Vptr b Ptrofs.zero) fsig cc A P Q ∨ believe_internal Espec psi E Delta (Vptr b Ptrofs.zero) fsig cc A P Q) as Bel.
  { rewrite /bi_emp_valid H.
    iIntros "H"; iApply "H"; iPureIntro.
    exists id_fun; eauto. }
  destruct (Genv.find_funct_ptr psi b) as [f|] eqn:Eb; swap 1 2.
  { assert (⊢ False : mpred) as HF; last by apply ouPred.consistency in HF.
    rewrite /bi_emp_valid Bel.
    iIntros "[BE | BI]".
    + unfold believe_external.
      unfold Genv.find_funct in *. rewrite -> if_true by trivial.
      rewrite Eb //.
    + iDestruct "BI" as (b' fu (? & ? & ? & ? & ? & ? & ? & ? & ?)) "_"; congruence. }
  exists f; split; auto.
  clear H; match goal with H : ⊢ ?P |- ?Q => assert (P ⊢ ⌜Q⌝) as HQ; last by rewrite HQ in H; apply ouPred.pure_soundness in H end.
  iIntros "[BE | BI]".
  - rewrite /believe_external /=.
    if_tac; last done.
    rewrite Eb.
    destruct f as [ | ef sigargs sigret c'']; first done.
    iDestruct "BE" as ((Es & -> & ASD & _)) "(#? & _)"; inv Es.
    rewrite TTL3 //.
  - iDestruct "BI" as (b' fu (? & ? & ? & ? & ? & ? & ? & ? & ?)) "_"; iPureIntro.
    unfold fn_funsig in *. simpl fst in *; simpl snd in *.
    assert (b' = b) by congruence. subst b'.
    assert (f = Internal fu) by congruence; subst; simpl.
    unfold type_of_function; destruct fsig; simpl in *; subst.
    rewrite TTL1 //.
Qed.

Lemma believe_exists_fundef:
  forall {CS}
    {b : Values.block} {id_fun : ident} {psi : genv} E {Delta : tycontext}
    {fspec: funspec}
  (Findb : Genv.find_symbol (genv_genv psi) id_fun = Some b)
  (H3: (glob_specs Delta) !! id_fun = Some fspec),
  believe(CS := CS) Espec E Delta psi Delta ⊢
  ⌜∃ f : Clight.fundef,
   Genv.find_funct_ptr (genv_genv psi) b = Some f /\
   type_of_fundef f = type_of_funspec fspec⌝.
Proof.
  intros.
  destruct fspec as [[params retty] cc A P Q].
  simpl.
  iIntros "Believe".
  iSpecialize ("Believe" with "[%]").
  { exists id_fun; eauto. }
  iDestruct "Believe" as "[BE|BI]".
  - rewrite /believe_external /=.
    if_tac; last done.
    destruct (Genv.find_funct_ptr psi b) eqn: Hf; last done.
    iExists _; iSplit; first done.
    destruct f as [ | ef sigargs sigret c'']; first done.
    iDestruct "BE" as ((Es & -> & ASD & _)) "(#? & _)"; inv Es.
    rewrite TTL3 //.
  - iDestruct "BI" as (b' fu (? & WOB & ? & ? & ? & ? & wob & ? & ?)) "_"; iPureIntro.
    unfold fn_funsig in *. simpl fst in *; simpl snd in *.
    assert (b' = b) by congruence. subst b'.
    eexists; split; first done; simpl.
    unfold type_of_function; subst.
    rewrite TTL1 //.
Qed.

Lemma eval_exprlist_relate':
  forall CS' (Delta : tycontext) (tys: typelist)
     (bl : list expr) (psi : genv) (vx : env) (tx : temp_env)
     (rho : environ) m tys',
   typecheck_environ Delta rho ->
   cenv_sub (@cenv_cs CS') (genv_cenv psi) ->
   rho = construct_rho (filter_genv psi) vx tx ->
   tys' = typelist2list tys ->
   mem_auth m ∗ denote_tc_assert (typecheck_exprlist(CS := CS') Delta (typelist2list tys) bl) rho ⊢
   ⌜Clight.eval_exprlist psi vx tx m bl
     tys
     (@eval_exprlist CS' tys' bl rho)⌝.
Proof. intros. subst tys'. eapply eval_exprlist_relate; eassumption. Qed.

Lemma tc_vals_Vundef {args ids} (TC:tc_vals ids args): Forall (fun v : val => v <> Vundef) args.
Proof.
generalize dependent ids. induction args; intros. constructor.
destruct ids; simpl in TC. contradiction. destruct TC.
constructor; eauto. intros N; subst. apply (tc_val_Vundef _ H).
Qed.

Lemma semax_call_aux0 {CS'}
  E (Delta : tycontext) (psi : genv) (ora : OK_ty) (b : Values.block) (id : ident) cc
  A0 P (x : A0) A deltaP deltaQ retty clientparams
  (F0 : assert) F (ret : option ident) (curf: function) args
  (R : ret_assert) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)

  (Spec: (glob_specs Delta)!!id = Some (mk_funspec (clientparams, retty) cc A deltaP deltaQ))
  (FindSymb: Genv.find_symbol psi id = Some b)
  (TCRet: tc_fn_return Delta ret retty)
  (GuardEnv: guard_environ Delta curf rho)
  (Hretty: retty=Tvoid -> ret=None)
  (Closed: closed_wrt_vars (thisvar ret) F0)
  (CSUB: cenv_sub (@cenv_cs CS') (genv_cenv psi))
  (Hrho: rho = construct_rho (filter_genv psi) vx tx)
  (ff : Clight.fundef) (H16 : Genv.find_funct psi (Vptr b Ptrofs.zero) = Some ff)
  (H16' : type_of_fundef ff = type_of_funspec (mk_funspec (clientparams, retty) cc A deltaP deltaQ))
  (TC8 : tc_vals clientparams args)
  ctl (Hcont : call_cont ctl = ctl)
  (Hctl : ∀ ret0 z', assert_safe Espec psi E curf vx (set_opttemp ret (force_val ret0) tx)
             (exit_cont EK_normal None k)  (construct_rho (filter_genv psi) vx (set_opttemp ret (force_val ret0) tx)) ⊢
    jsafeN Espec psi E z' (Returnstate (force_val ret0) ctl)):
  □ believe Espec E Delta psi Delta -∗
  ▷ (F0 rho ∗ F rho ∗ P x (ge_of rho, args) -∗
     funassert Delta rho -∗
     □ ■ (F rho ∗ P x (ge_of rho, args) ={E}=∗
                          ∃ (x1 : A) (F1 : assert),
                            (F1 rho ∗ deltaP x1 (ge_of rho, args))
                            ∧ (∀ rho' : environ,
                                 ■ ((∃ old:val, substopt ret (`old) F1 rho' ∗ maybe_retval (deltaQ x1) retty ret rho') -∗
                                    RA_normal R rho'))) -∗
  <affine> rguard Espec psi E Delta curf (frame_ret_assert R F0) k -∗
  jsafeN Espec psi E ora (Callstate ff args ctl)).
Proof.
  iIntros "#Bel".
  iPoseProof ("Bel" with "[%]") as "Bel'".
  { exists id; eauto. }
  pose proof (tc_vals_length _ _ TC8) as Hlen.
  iDestruct "Bel'" as "[BE | BI]".
  - (* external call *)
    iPoseProof (semax_call_external with "BE") as "Hsafe".
    iNext; iIntros "(F0 & ?) fun #HR rguard".
    iApply ("Hsafe" with "rguard fun F0").
    by iApply "HR".
  - (* internal call *)
    iDestruct "BI" as (b' f (H3a & H3b & COMPLETE & H17 & H17' & Hvars & H18 & H18')) "BI".
    injection H3a as <-; change (Genv.find_funct psi (Vptr b Ptrofs.zero) = Some (Internal f)) in H3b.
    rewrite H16 in H3b; inv H3b.
    iSpecialize ("BI" with "[%] [%]").
    { intros; apply tycontext_sub_refl. }
    { apply cenv_sub_refl. }
    iNext; iIntros "(F0 & P) fun #HR rguard".
    iMod ("HR" with "P") as (??) "((? & ?) & #post)".
    iSpecialize ("BI" $! x1); rewrite semax_fold_unfold.
    iPoseProof ("BI" with "[%] [Bel] [rguard]") as "#guard".
    { split3; eauto; [apply tycontext_sub_refl | apply cenv_sub_refl]. }
    { done. }
    { iIntros "!>"; rewrite bi.affinely_elim.
      iApply (semax_call_aux2 _ _ _ _ _ _ _ _ _ (clientparams,retty) (Econst_int Int.zero tint) nil with "post rguard"); try done.
      * rewrite closed_wrt_modvars_Scall //.
      * destruct H18' as [-> _]; rewrite H18 //. }
    iApply jsafe_step; rewrite /jstep_ex.
    iIntros (?) "(Hm & ?)".
    destruct (build_call_temp_env f args) as (te & Hte).
    { rewrite /= in H18; rewrite H18 map_length // in Hlen. }
    iMod (alloc_stackframe with "Hm") as (?? [??]) "(Hm & stack)".
    { unfold var_sizes_ok in Hvars.
      rewrite !Forall_forall in Hvars, COMPLETE |- *.
      intros v H0. specialize (COMPLETE v H0). specialize (Hvars v H0).
      rewrite (cenv_sub_sizeof CSUB); auto. }
    iIntros "!>"; iExists _, _; iSplit.
    { apply list_norepet_append_inv in H17 as (? & ? & ?).
      iPureIntro; constructor; constructor; done. }
    iFrame.
    iApply ("guard" with "[-]"); last by iIntros "!> !>"; iPureIntro.
    iSplit.
    + iPureIntro.
      split; last done.
      eapply semax_call_typecheck_environ; eauto.
      * rewrite -Genv.find_funct_find_funct_ptr //.
      * destruct GuardEnv as ((? & ? & ?) & ?); done.
      * rewrite snd_split -H18 //.
    + iFrame; monPred.unseal; iFrame.
      monPred.unseal; iFrame; iSplit; last done.
      apply list_norepet_app in H17 as [H17 [_ _]].
      rewrite /bind_args; monPred.unseal; iSplit.
      * iPureIntro.
        rewrite /tc_formals -H18 //.
        match goal with H: tc_vals _ ?A |- tc_vals _ ?B => replace B with A; auto end.
        clear - H17 Hte. forget (create_undef_temps (fn_temps f)) as te0.
        revert args te0 te Hte H17.
        induction (fn_params f); destruct args; intros; auto; try discriminate.
        { destruct a; inv Hte. }
        destruct a; simpl in Hte. inv H17.
        rewrite (IHl _ _ _ Hte) //.
        simpl; f_equal.
        unfold eval_id, construct_rho; simpl.
        erewrite pass_params_ni; try eassumption.
        setoid_rewrite Maps.PTree.gss. reflexivity.
      * iApply (make_args_close_precondition _ _ _ _ ve); last done.
        eapply tc_vals_Vundef; eauto.
Qed.

Lemma semax_call_aux {CS'}
  E (Delta : tycontext) (psi : genv) (ora : OK_ty) (b : Values.block) (id : ident) cc
  A0 P (x : A0) A deltaP deltaQ retty clientparams
  (F0 : assert) F (ret : option ident) (curf: function) args (a : expr)
  (bl : list expr) (R : ret_assert) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)

  (Spec: (glob_specs Delta)!!id = Some (mk_funspec (clientparams, retty) cc A deltaP deltaQ))
  (FindSymb: Genv.find_symbol psi id = Some b)

  (Classify: Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list clientparams) retty cc)
  (TCRet: tc_fn_return Delta ret retty)
  (Argsdef: args = @eval_exprlist CS' clientparams bl rho)
  (Hlen : length clientparams = length args)
  (GuardEnv: guard_environ Delta curf rho)
  (Hretty: retty=Tvoid -> ret=None)
  (Closed: closed_wrt_modvars (Scall ret a bl) F0)
  (CSUB: cenv_sub (@cenv_cs CS') (genv_cenv psi))
  (Hrho: rho = construct_rho (filter_genv psi) vx tx)
  (EvalA: eval_expr a rho = Vptr b Ptrofs.zero):

  □ believe Espec E Delta psi Delta -∗
  (▷tc_expr Delta a rho ∧ ▷tc_exprlist Delta clientparams bl rho) ∧
  (▷ (F0 rho ∗ F rho ∗ P x (ge_of rho, args))) -∗
  funassert Delta rho -∗
  □ ▷ ■ (F rho ∗ P x (ge_of rho, args) ={E}=∗
                          ∃ (x1 : A) (F1 : assert),
                            (F1 rho ∗ deltaP x1 (ge_of rho, args))
                            ∧ (∀ rho' : environ,
                                 ■ ((∃ old:val, substopt ret (`old) F1 rho' ∗ maybe_retval (deltaQ x1) retty ret rho') -∗
                                    RA_normal R rho'))) -∗
  ▷ <affine> rguard Espec psi E Delta curf (frame_ret_assert R F0) k -∗
   jsafeN Espec psi E ora
     (State curf (Scall ret a bl) k vx tx).
Proof.
  iIntros "#Bel H fun #HR rguard".
  iDestruct (believe_exists_fundef with "Bel") as %[ff [H16 H16']].
  rewrite <- Genv.find_funct_find_funct_ptr in H16.
  rewrite /jsafeN jsafe_unfold /jsafe_pre.
  iIntros "!>" (?) "(Hm & ?)".
  iRight; iLeft.
  rewrite (add_and (_ ∧ ▷ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "((_ & H) & _)"; destruct GuardEnv; iApply (tc_eval_exprlist with "H").
  iDestruct "H" as "(H & >%TC8)".
  iCombine "Hm H" as "H".
  rewrite (add_and (mem_auth m ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & (H & _) & _)"; destruct GuardEnv; iApply (eval_expr_relate with "[$Hm $H]").
  iDestruct "H" as "[H >%EvalA']".
  rewrite -(@TTL5 clientparams); rewrite (add_and (mem_auth m ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & (_ & H) & _)"; destruct GuardEnv; iApply (eval_exprlist_relate' with "[$Hm $H]").
  iDestruct "H" as "[H >%Hargs]".
  rewrite TTL5 in Hargs |- *; iDestruct "H" as "(Hm & H)".
  iIntros "!>"; iExists _, _; iSplit.
  { iPureIntro; eapply step_call with (vargs:=args); subst; eauto.
    rewrite EvalA //. }
  iDestruct "H" as "(_ & F0 & P)".
  iFrame.
  rewrite closed_wrt_modvars_Scall in Closed.
  subst args; iApply (semax_call_aux0 with "Bel [F0 P] [fun] HR rguard"); [done | | | done].
  - intros; apply assert_safe_for_external_call.
  - iNext; iFrame.
Qed.

Lemma eval_exprlist_length : forall lt le rho, length lt = length le -> length (eval_exprlist lt le rho) = length le.
Proof.
  induction lt; simpl; auto; intros.
  destruct le; inv H; simpl.
  rewrite IHlt //.
Qed.

Lemma semax_call_si:
  forall E Delta (A: Type)
   (P : A -> argsassert)
   (Q : A -> assert)
   (x : A)
   F ret argsig retsig cc a bl
   (TCF : Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retsig cc)
   (TC5 : retsig = Tvoid -> ret = None)
   (TC7 : tc_fn_return Delta ret retsig),
  semax Espec E Delta
       (▷(tc_expr Delta a ∧ tc_exprlist Delta argsig bl) ∧
           (assert_of (fun rho => func_ptr_si E (mk_funspec' (argsig,retsig) cc A P Q) (eval_expr a rho)) ∗
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (Q x) retsig ret)).
Proof.
  intros.
  rewrite semax_unfold; intros.
  rename argsig into clientparams. rename retsig into retty.
  iIntros "#Prog_OK" (???) "[%Closed #rguard]".
  iIntros (tx vx) "!>".
  monPred.unseal; iIntros "(%TC3 & (F0 & H) & fun)".
  assert (TC7': tc_fn_return Delta' ret retty).
  { clear - TC7 TS.
    hnf in TC7|-*. destruct ret; auto.
    destruct ((temp_types Delta) !! i) eqn:?; try contradiction.
    destruct TS as [H _].
    specialize (H i); rewrite Heqo in H. subst t; done. }
  assert (Hpsi: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)) by reflexivity.
  remember (construct_rho (filter_genv psi) vx tx) as rho.
  iAssert (func_ptr_si E (mk_funspec' (clientparams, retty) cc A P Q) (eval_expr(CS := CS) a rho)) as "#funcatb".
  { iDestruct "H" as "(_ & $ & _)". }
  rewrite {2}(affine (func_ptr_si _ _ _)) left_id.
  rewrite /func_ptr_si.
  iDestruct "funcatb" as (b EvalA nspec) "[SubClient funcatb]".
  destruct nspec as [nsig ncc nA nP nQ].
  iAssert (∃ id deltaP deltaQ, ⌜Genv.find_symbol psi id = Some b ∧ (glob_specs Delta') !! id = Some (mk_funspec' nsig ncc nA deltaP deltaQ)⌝ ∧
    ▷ (nP ≡ deltaP) ∧ ▷ (nQ ≡ deltaQ)) as (id deltaP deltaQ (RhoID & SpecOfID)) "#(HeqP & HeqQ)".
  { iDestruct "fun" as "(FA & FD)".
    rewrite /Map.get /filter_genv.
    iDestruct ("FD" with "[funcatb]") as %(id & ? & fs & ?).
    { by iExists _, _, _. }
    iDestruct ("FA" with "[%]") as (b0 ?) "funcatv"; first done.
    assert (b0 = b) as -> by congruence.
    iDestruct (func_at_agree with "funcatb funcatv") as (??????? ([=] & ->)) "?"; subst.
    repeat match goal with H : existT _ _ = existT _ _ |- _ => apply inj_pair2 in H end; subst.
    iExists _, _, _; iSplit; done. }
  set (args := @eval_exprlist CS clientparams bl rho).
  set (args' := @eval_exprlist CS' clientparams bl rho).
  iDestruct "SubClient" as "[[%NSC %Hcc] ClientAdaptation]"; subst cc. destruct nsig as [nparams nRetty].
  inversion NSC; subst nRetty nparams; clear NSC.
  simpl fst in *; simpl snd in *.
  assert (typecheck_environ Delta rho) as TC4.
  { clear - TC3 TS.
    destruct TC3 as [TC3 TC4].
    eapply typecheck_environ_sub in TC3; [| eauto].
    auto. }
  iIntros (? _).
  rewrite (add_and (_ ∧ ▷ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "((_ & H) & _)"; destruct HGG; iApply (typecheck_exprlist_sound_cenv_sub with "H").
  iDestruct "H" as "(H & >%HARGS)".
  fold args in HARGS; fold args' in HARGS.
  setoid_rewrite tc_exprlist_sub; [|done..]. setoid_rewrite tc_expr_sub; [|done..].
  rewrite (add_and (_ ∧ ▷ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "((_ & H) & _)"; destruct HGG; iApply (tc_exprlist_length with "H").
  iDestruct "H" as "(H & >%LENbl)".
  assert (LENargs: Datatypes.length clientparams = Datatypes.length args).
  { rewrite LENbl eval_exprlist_length //. }
  assert (TCD': tc_environ Delta' rho) by eapply TC3.
  rewrite (add_and (_ ∧ ▷ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "((_ & H) & _)"; iApply (tc_eval_exprlist with "H").
  iDestruct "H" as "(H & >%TCargs)"; fold args in TCargs.
  iSpecialize ("ClientAdaptation" $! x (ge_of rho, args)).
  rewrite (bi.pure_True (argsHaveTyps _ _)).
  2: { clear -TCargs. clearbody args. generalize dependent clientparams.
       induction args; intros.
       - destruct clientparams; simpl in *. constructor. contradiction.
       - destruct clientparams; simpl in *. contradiction. destruct TCargs.
         apply tc_val_has_type in H; simpl. apply IHargs in H0.
         constructor; eauto. }
  rewrite bi.True_and.
  assert (CSUBpsi:cenv_sub (@cenv_cs CS) psi).
  { destruct HGG as [CSUB' HGG]. apply (cenv_sub_trans CSUB' HGG). }
  destruct HGG as [CSUB HGG].
  rewrite (add_and (_ ∧ ▷ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "((H & _) & _)"; iApply (typecheck_expr_sound_cenv_sub with "H").
  iDestruct "H" as "(H & >%Heval_eq)"; rewrite Heval_eq in EvalA.
  subst rho; iApply (@semax_call_aux CS' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normal_ret_assert
                   (∃ old : val, assert_of (substopt ret (` old) (monPred_at F)) ∗
                      maybe_retval (Q x) retty ret)) with "Prog_OK [F0 H] [fun] [] [rguard]"); try reflexivity; [| by monPred.unseal | | by repeat monPred.unseal].
  - iCombine "F0 H" as "H"; rewrite bi.sep_and_l; iSplit.
    + rewrite bi.later_and; iDestruct "H" as "[(_ & ?) _]".
      rewrite tc_exprlist_cenv_sub // tc_expr_cenv_sub //.
    + iNext; iDestruct "H" as "[_ $]".
  - iClear "funcatb". iIntros "!> !> !>".
    iIntros "(F & P)".
    iMod ("ClientAdaptation" with "P") as (??) "[H #post]".
    rewrite !discrete_fun_equivI.
    iSpecialize ("HeqP" $! x1); iSpecialize ("HeqQ" $! x1); iRewrite "HeqP" in "H".
    iExists x1, (F ∗ ⎡F1⎤); iIntros "!>"; monPred.unseal; iSplit; first by iDestruct "H" as "($ & $)".
    iIntros (?) "!> (% & F & nQ)"; simpl.
    destruct ret; simpl.
    + iExists old; iDestruct "F" as "($ & F1)".
      iRewrite -"HeqQ" in "nQ".
      iDestruct "nQ" as "($ & nQ)"; iApply "post"; iFrame; by iPureIntro.
    + iExists Vundef; iDestruct "F" as "($ & F1)".
      destruct (type_eq retty Tvoid); subst.
      * iRewrite -"HeqQ" in "nQ".
        iApply "post"; iFrame; by iPureIntro.
      * destruct retty; first contradiction; iDestruct "nQ" as (v ?) "nQ"; iRewrite -"HeqQ" in "nQ"; iExists v; (iSplit; [by iPureIntro|];
          iApply "post"; iFrame; by iPureIntro).
Qed.

Definition semax_call_alt := semax_call_si.

Lemma semax_call:
  forall E Delta (A: Type)
  (P : A -> argsassert)
  (Q : A -> assert)
  (x : A)
  F ret argsig retsig cc a bl
  (TCF : Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retsig cc)
  (TC5 : retsig = Tvoid -> ret = None)
  (TC7 : tc_fn_return Delta ret retsig),
  semax Espec E Delta
       ((▷(tc_expr Delta a ∧ tc_exprlist Delta argsig bl))  ∧
           (assert_of (fun rho => func_ptr E (mk_funspec' (argsig,retsig) cc A P Q) (eval_expr a rho)) ∗
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (Q x) retsig ret)).
Proof.
  intros.
  eapply semax_pre, semax_call_si; [|done..].
  split => rho.
  monPred.unseal; rewrite bi.and_elim_r func_ptr_fun_ptr_si //.
Qed.

(*Lemma semax_call_ext {CS Espec}:
   forall (IF_ONLY: False),
     forall Delta P Q ret a tl bl a' bl',
      typeof a = typeof a' ->
      map typeof bl = map typeof bl' ->
      (forall rho,
          ⌜ (typecheck_environ Delta rho) ∧ P rho ⊢
            tc_expr Delta a rho ∧ tc_exprlist Delta tl bl rho ∧
            tc_expr Delta a' rho ∧ tc_exprlist Delta tl bl' rho ∧
            ⌜ (eval_expr a rho = eval_expr a' rho /\
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
intros ? ? ? ? ? Hext ?.
specialize (H2 y H5 _ _ H6 Hext H7).
destruct H7 as[[? ?] _].
hnf in H7.
pose proof I.
eapply fupd.fupd_mono, H2.
intros ? Hsafe ?? Hora ???.
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
destruct H8 as [w1 [w2 [H8' [_ ?]]]].
assert (H8'': @extendM rmap _ _ _ _ _ _ w2 a'') by (eexists; eauto). clear H8'.
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
(*eapply @denote_tc_resource with (a' := m_phi jm) in TCa; auto.
eapply @denote_tc_resource with (a' := m_phi jm) in TCa'; auto.
eapply @denote_tc_resource with (a' := m_phi jm) in TCbl; auto.
eapply @denote_tc_resource with (a' := m_phi jm) in TCbl'; auto.*)
assert (forall vf, Clight.eval_expr psi vx tx (m_dry jm) a vf
               -> Clight.eval_expr psi vx tx (m_dry jm) a' vf). {
clear - TCa TCa' H7 H7' H0 Heqrho HGG TS HGpsi.
intros.
eapply tc_expr_sub in TCa; [| eauto | eauto].
(* In theory, we might have given up ownership of a relevant location
   in the viewshift from a'' to jm. In practice, if we did,
   surely the evaluation of a would fail too? *)
pose proof (eval_expr_relate _ _ _ _ _ _ jm HGpsi Heqrho H7 TCa).
pose proof (eval_expr_fun H H1). subst vf.
rewrite H0.
eapply eval_expr_relate; eauto.
}
assert (forall tyargs vargs,
             Clight.eval_exprlist psi vx tx (m_dry jm) bl tyargs vargs ->
             Clight.eval_exprlist psi vx tx (m_dry jm) bl' tyargs vargs). {
clear - IF_ONLY TCbl TCbl' H13 Hbl H7' Heqrho HGpsi.
revert bl bl' H13 Hbl TCbl TCbl'; induction tl; destruct bl, bl'; simpl; intros; auto;
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
unfold_lift in H13.
inv H13.
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
destruct H25 as [H25 | H25]; inv H25.
destruct H25 as [H25 | H25]; inv H25.
Qed.*)

Definition cast_expropt {CS} (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (eval_expr(CS := CS) (Ecast e' t))  | None => `None end.

Lemma tc_expropt_char {CS'} Delta e t: tc_expropt (CS := CS') Delta e t =
                                      match e with None => ⌜t=Tvoid⌝
                                              | Some e' => tc_expr(CS := CS') Delta (Ecast e' t)
                                      end.
Proof. reflexivity. Qed.

Lemma RA_return_castexpropt_cenv_sub {CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta rho (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS) Delta ret t rho ⊢ ⌜@cast_expropt CS ret t rho = @cast_expropt CS' ret t rho⌝.
Proof.
  rewrite /tc_expropt /tc_expr; destruct ret; simpl.
  + unfold_lift. rewrite /typecheck_expr; fold typecheck_expr.
    rewrite denote_tc_assert_andp (typecheck_expr_sound_cenv_sub CSUB) //.
    iIntros "(-> & _)"; done.
  + iIntros; iPureIntro; done.
Qed.

Lemma tc_expropt_cenv_sub {CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta rho (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS) Delta ret t rho ⊢ tc_expropt (CS := CS') Delta ret t rho.
Proof.
  rewrite !tc_expropt_char.
  pose proof (tc_expr_cenv_sub CSUB).
  destruct ret; trivial; auto.
Qed.

Lemma tc_expropt_cspecs_sub {CS'} (CSUB: cspecs_sub CS CS') Delta rho (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS) Delta ret t rho ⊢ tc_expropt (CS := CS') Delta ret t rho.
Proof.
  destruct CSUB as [CSUB _].
  apply tc_expropt_cenv_sub; done.
Qed.

Lemma tc_expropt_sub {CS'} E Delta Delta' rho (TS:tycontext_sub E Delta Delta') (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS') Delta ret t rho ⊢ tc_expropt (CS := CS') Delta' ret t rho.
Proof.
  rewrite !tc_expropt_char.
  specialize (tc_expr_sub _ _ _ _ TS); intros.
  destruct ret; [ eapply H; assumption | trivial].
Qed.

Lemma semax_return:
   forall E Delta R ret,
      semax Espec E Delta
                (tc_expropt Delta ret (ret_type Delta) ∧
                             assert_of (`(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ)))
                (Sreturn ret)
                R.
Proof.
  intros.
  rewrite semax_unfold; intros.
  destruct HGG as [CSUB HGG].
  replace (ret_type Delta) with (ret_type Delta')
    by (destruct TS as [_ [_ [? _]]]; auto).
  iIntros "#Prog_OK" (???) "[%Hclosed #rguard]".
  iIntros (??) "!> (% & H & ?)".
  monPred.unseal.
  set (rho := construct_rho _ _ _).
  iSpecialize ("rguard" $! EK_return (@cast_expropt CS' ret (ret_type Delta') rho) tx vx).
  destruct H as (H & ? & Hret).
  assert (TCD: typecheck_environ Delta rho) by (eapply typecheck_environ_sub; eauto); clear TS.
  iAssert (tc_expropt Delta ret (ret_type Delta') rho ∧
    assert_safe Espec psi E f vx tx
                (exit_cont EK_return (@cast_expropt CS' ret (ret_type Delta') rho) k)
                (construct_rho (filter_genv psi) vx tx)) with "[-]" as "H".
  { iSplit.
    + rewrite tc_expropt_cenv_sub //.
      iDestruct "H" as "(? & $ & _)".
    + iApply "rguard".
      rewrite proj_frame /=; subst rho.
      rewrite RA_return_castexpropt_cenv_sub //.
      monPred.unseal; unfold_lift. iDestruct "H" as "($ & -> & ?)"; iFrame. iPureIntro; done. }
  iIntros (? _).
  rewrite /assert_safe /=.
  iApply (convergent_controls_jsafe _ _ _ (State f (Sreturn ret) (call_cont k) vx tx)); try done.
  { inversion 1; subst; try match goal with H : _ \/ _ |- _ => destruct H; done end.
    + rewrite call_cont_idem; constructor; auto.
    + rewrite call_cont_idem; econstructor; eauto. }
  destruct ret; simpl.
  - (* If we did a view-shift here, we could lose the typechecking (by giving up mem that makes pointers in e valid). *)
    iApply bi.impl_elim_r; iSplit; last by iDestruct "H" as "[_ H]"; iApply ("H" with "[%]").
    iIntros (?) "Hm"; iDestruct "H" as "[H _]".
    rewrite /tc_expr /typecheck_expr; fold typecheck_expr.
    rewrite denote_tc_assert_andp.
    subst rho; iDestruct (eval_expr_relate(CS := CS') with "[$Hm H]") as %?; [| iDestruct "H" as "[$ _]" |]; try done.
    iDestruct (typecheck_expr_sound' with "[H]") as %Htc; first iDestruct "H" as "($ & _)".
    iDestruct (cop2_sem_cast' with "[$Hm H]") as %?; first iDestruct "H" as "[_ $]".
    rewrite cast_exists //; iDestruct "H" as %Hcast.
    iPureIntro; unfold_lift; rewrite /force_val1 -Hret.
    rewrite -> Hcast in *; eauto.
  - iDestruct "H" as "[_ H]"; iApply "H"; done.
Qed.

End mpred.
