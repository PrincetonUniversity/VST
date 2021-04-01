Require Import VST.floyd.proofauto.
Require Import VST.veric.Clight_initial_world.
Require Import VST.floyd.assoclists.
Require Import VST.floyd.PTops.
Require Export VST.floyd.QPcomposite.
Require Export VST.floyd.quickprogram.

Lemma semax_body_subsumespec {cs} V V' F F' f iphi (SB: @semax_body V F cs f iphi)
  ( HVF : forall i : positive,
      sub_option (make_tycontext_g V F) ! i (make_tycontext_g V' F') ! i)
  (HF : forall i : ident, subsumespec (find_id i F) (find_id i F')):
   @semax_body V' F' cs f iphi.
Proof. eapply semax_body_subsumption. apply SB. clear SB.
    red; simpl. repeat split; trivial; intros i.
    - destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! i); trivial.
    - rewrite 2 make_tycontext_s_find_id; trivial.
    - rewrite PTree.gempty; simpl; trivial.
Qed.

Lemma semax_body_binaryintersection':
  forall (V : varspecs) (G : funspecs) (cs : compspecs) (f : function) (sp1 sp2 : ident * funspec)
    sg cc A1 P1 Q1 Pne1 Qne1 A2 P2 Q2 Pne2 Qne2,
  semax_body V G f sp1 ->
  semax_body V G f sp2 -> forall
  (W1: snd sp1 = mk_funspec sg cc A1 P1 Q1 Pne1 Qne1)
  (W2: snd sp2 = mk_funspec sg cc A2 P2 Q2 Pne2 Qne2),
  semax_body V G f (fst sp1, binary_intersection' (snd sp1) (snd sp2) W1 W2).
Proof. intros. eapply semax_body_binaryintersection. trivial. apply H0.
  apply binary_intersection'_sound.
Qed.

Lemma semax_body_binaryintersection'':
  forall (V : varspecs) (G : funspecs) (cs : compspecs) (f : function) i (sp1 sp2 : funspec)
    (*(phi : funspec)*) sg cc A1 P1 Q1 Pne1 Qne1 A2 P2 Q2 Pne2 Qne2,
  semax_body V G f (i,sp1) ->
  semax_body V G f (i,sp2) -> forall
  (W1: sp1 = mk_funspec sg cc A1 P1 Q1 Pne1 Qne1)
  (W2: sp2 = mk_funspec sg cc A2 P2 Q2 Pne2 Qne2),
  semax_body V G f (i, binary_intersection' sp1 sp2 W1 W2).
Proof. intros.
apply (semax_body_binaryintersection' _ _ _ _ _ _ sg cc A1 P1 Q1 Pne1 Qne1 A2 P2 Q2 Pne2 Qne2 H H0 W1 W2).
Qed.

Lemma semax_body_subsumespec_GprogNil (V : varspecs) F (cs:compspecs) f iphi:
       semax_body V nil f iphi -> list_norepet (map fst V ++ map fst F) ->
       semax_body V F f iphi.
  Proof. intros. eapply semax_body_subsumespec. apply H.
    + intros i; red.
      rewrite 2 semax_prog.make_context_g_char; trivial.
      rewrite 2 initial_world.make_tycontext_s_find_id; simpl. 
      remember (initial_world.find_id i V). destruct o; [ symmetry in Heqo | trivial].
      rewrite (assoclists.list_norepet_find_id_app_exclusive1 H0 Heqo); trivial. simpl.
      rewrite app_nil_r. apply list_norepet_append_left in H0; trivial.
    + intros i; red. simpl; trivial.
  Qed.

Lemma binary_intersection'_sub1:
  forall (f : compcert_rmaps.typesig) (c : calling_convention) (A1 : rmaps.TypeTree)
    (P1 : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (ArgsTT A1)) mpred)
    (Q1 : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A1))
            mpred) (P1_ne : args_super_non_expansive P1) (Q1_ne : super_non_expansive Q1)
    (A2 : rmaps.TypeTree)
    (P2 : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (ArgsTT A2)) mpred)
    (Q2 : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A2))
            mpred) (P2_ne : args_super_non_expansive P2) (Q2_ne : super_non_expansive Q2)
    (phi psi : funspec) (Hphi : phi = mk_funspec f c A1 P1 Q1 P1_ne Q1_ne)
    (Hpsi : psi = mk_funspec f c A2 P2 Q2 P2_ne Q2_ne),
  seplog.funspec_sub (binary_intersection' phi psi Hphi Hpsi) phi.
Proof. intros. apply binary_intersection'_sub. Qed. 

Lemma binary_intersection'_sub2:
  forall (f : compcert_rmaps.typesig) (c : calling_convention) (A1 : rmaps.TypeTree)
    (P1 : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (ArgsTT A1)) mpred)
    (Q1 : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A1))
            mpred) (P1_ne : args_super_non_expansive P1) (Q1_ne : super_non_expansive Q1)
    (A2 : rmaps.TypeTree)
    (P2 : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (ArgsTT A2)) mpred)
    (Q2 : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A2))
            mpred) (P2_ne : args_super_non_expansive P2) (Q2_ne : super_non_expansive Q2)
    (phi psi : funspec) (Hphi : phi = mk_funspec f c A1 P1 Q1 P1_ne Q1_ne)
    (Hpsi : psi = mk_funspec f c A2 P2 Q2 P2_ne Q2_ne),
  seplog.funspec_sub (binary_intersection' phi psi Hphi Hpsi) psi.
Proof. intros. apply binary_intersection'_sub. Qed. 

Lemma binary_intersection'_sub  {f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne} (phi psi:funspec) Hphi Hpsi:
  funspec_sub (@binary_intersection' f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne phi psi Hphi Hpsi) phi /\
  funspec_sub (@binary_intersection' f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne phi psi Hphi Hpsi) psi.
Proof. apply binary_intersection'_sub. Qed.

Lemma binary_intersection'_sub'  {f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne} (phi psi:funspec) Hphi Hpsi tau
  (X: tau = @binary_intersection' f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne phi psi Hphi Hpsi):
  funspec_sub tau phi /\ funspec_sub tau psi.
Proof. subst. apply binary_intersection'_sub. Qed.

Lemma mapsto_zeros_mapsto_nullval sh b z t:
   readable_share sh ->
   Z.divide (align_chunk Mptr) (Ptrofs.unsigned z) ->
   (mapsto_memory_block.mapsto_zeros 
            (size_chunk Mptr) sh (Vptr b z))
   |-- (!! (and (Z.le Z0 (Ptrofs.unsigned z))
                  (Z.lt
                     (Z.add (size_chunk Mptr)
                        (Ptrofs.unsigned z)) Ptrofs.modulus)))
      && (mapsto sh 
               (Tpointer t noattr) (Vptr b z) nullval).
Proof. intros. apply mapsto_memory_block.mapsto_zeros_mapsto_nullval; trivial. Qed.

Definition genv_find_func (ge:Genv.t Clight.fundef type) i f :=
  exists b, Genv.find_symbol ge i = Some b /\
        Genv.find_funct_ptr ge b = Some f.

  Lemma progfunct_GFF {p i fd}: list_norepet (map fst (prog_defs p)) ->
        find_id i (prog_funct p) = Some fd -> genv_find_func (Genv.globalenv p) i fd.
  Proof. intros. apply find_id_e in H0. 
    apply semax_prog.find_funct_ptr_exists; trivial.
    apply (semax_prog.in_prog_funct_in_prog_defs _ _ _ H0). 
  Qed.

Lemma funspec_sub_cc phi psi: funspec_sub phi psi ->
      callingconvention_of_funspec phi = callingconvention_of_funspec psi.
Proof. destruct phi; destruct psi; simpl. intros [[_ ?] _]; trivial. Qed.

Definition semaxfunc_InternalInfo C V G (ge : Genv.t Clight.fundef type) id f phi := 
  (id_in_list id (map fst G) && semax_body_params_ok f)%bool = true /\
  Forall (fun it : ident * type => complete_type (@cenv_cs C)(snd it) = true) (fn_vars f) /\
  var_sizes_ok (fn_vars f) /\
  fn_callconv f = callingconvention_of_funspec phi/\
  semax_body V G f (id, phi) /\
  genv_find_func ge id (Internal f).

Definition semaxfunc_ExternalInfo Espec (ge : Genv.t Clight.fundef type) (id : ident)
    (ef : external_function) (argsig : typelist) (retsig : type) (cc : calling_convention) phi := 
  match phi with mk_funspec (argsig', retsig') cc' A P Q NEP NEQ => 
  retsig = retsig' /\ cc=cc' /\
  argsig' = typelist2list argsig /\
  ef_sig ef = mksignature (typlist_of_typelist argsig) (rettype_of_type retsig) cc /\
  (ef_inline ef = false \/ withtype_empty A) /\
  (forall (gx : genviron) (ts : list Type) x (ret : option val),
   Q ts x (make_ext_rval gx (rettype_of_type retsig) ret) && !! Builtins0.val_opt_has_rettype ret (rettype_of_type retsig) |-- !! tc_option_val retsig ret) /\
  @semax_external Espec ef A P Q /\
  genv_find_func ge id (External ef argsig retsig cc)
  end.

Lemma InternalInfo_subsumption {ge cs V V' F F' i f phi}
  (HVF : forall i, (sub_option (make_tycontext_g V F) ! i) ((make_tycontext_g V' F') ! i))
  (HF : forall i, subsumespec (find_id i F) (find_id i F'))
  (LNRF : list_norepet (map fst F))
  (H : semaxfunc_InternalInfo cs V F ge i f phi):
  semaxfunc_InternalInfo cs V' F' ge i f phi.
Proof.
  destruct H as [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 Hb6]]]]].
  repeat split; trivial.
  + apply andb_true_iff in Hb1; destruct Hb1 as [X Y]; rewrite Y, andb_true_r.
    clear - X HF LNRF. apply id_in_list_true_i. apply id_in_list_true in X.
    apply In_map_fst_find_id in X; trivial. destruct X as [phi PHI].
    specialize (HF i); rewrite PHI in HF. destruct HF as [phi' [PHI' Sub]].
    apply find_id_In_map_fst in PHI'; trivial.
  + eapply semax_body_subsumption. eassumption. clear - HF HVF.
    red; simpl. repeat split; trivial; intros i.
    - destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! i); trivial.
    - rewrite 2 make_tycontext_s_find_id; trivial.
    - rewrite PTree.gempty; simpl; trivial.
Qed.

Lemma InternalInfo_envs_sub {CS CS'} (CSUB: cspecs_sub CS CS') ge ge'
  V G  i f phi (H : semaxfunc_InternalInfo CS V G ge i f phi) (FFunc: genv_find_func ge' i (Internal f)):
semaxfunc_InternalInfo CS' V G ge' i f phi.
Proof. 
  destruct H as [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 Hb6]]]]].
  repeat split; try assumption.
  - destruct CSUB as [CSE _]. clear - CSE Hb2. induction Hb2; constructor; trivial.
    apply (@semax.complete_type_cenv_sub _ _ CSE _ H).
  - destruct CSUB as [CSE _]. clear - CSE Hb2 Hb3. unfold var_sizes_ok in *.
    induction Hb3; trivial. inv Hb2. constructor. 2: eauto.
    unfold sizeof.
    rewrite (@expr_lemmas4.cenv_sub_sizeof _ _ CSE); trivial.
  - apply (semax_body_cenv_sub CSUB); trivial.
Qed.

Lemma InternalInfo_funspec_sub {cs V G ge i f phi}
     (SFI: semaxfunc_InternalInfo cs V G ge i f phi)
     (phi' : funspec) (Fsub : funspec_sub phi phi'):
semaxfunc_InternalInfo cs V G ge i f phi'.
Proof.
  destruct SFI as [? [? [? [? [? ?]]]]].
  rewrite (funspec_sub_cc _ _ Fsub) in H2.
  split; intuition.
  eapply semax_body_funspec_sub. eassumption. trivial.
  apply andb_true_iff in H; destruct H as [ _ H].
  apply andb_true_iff in H; destruct H as [H _].
  apply compute_list_norepet_e; trivial.
Qed.

Lemma ExternalInfo_envs_sub Espec ge ge'
    i ef argsig retsig cc phi
  (H : semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi) 
  (FFunc: genv_find_func ge' i (External ef argsig retsig  cc)):
semaxfunc_ExternalInfo Espec ge' i ef argsig retsig cc phi.
Proof.
  destruct phi. destruct t. simpl. 
  destruct H as [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 [Hb7 [Hb8 [Hb9 Hb10]]]]]]]]].
  repeat split; trivial.
Qed.

Lemma TTL7: forall l l' (L:typelist_of_type_list l = typelist_of_type_list l'), l=l'.
Proof. induction l; destruct l'; simpl; intros; trivial; inv L. f_equal. auto. Qed.

Lemma InternalInfo_cc {cs V G ge i f phi} (SF: @semaxfunc_InternalInfo cs V G ge i f phi):
  fn_callconv f = callingconvention_of_funspec phi.
Proof. destruct SF as [b [? [? [? [? [? ?]]]]]]; trivial. Qed.

Lemma ExternalInfo_cc {Espec ge i ef tys rt cc phi} (SF: @semaxfunc_ExternalInfo Espec ge i ef tys rt cc phi):
  cc = callingconvention_of_funspec phi.
Proof. destruct phi. destruct t. destruct SF as [? [? _]]; subst; trivial. Qed.

Lemma internalInfo_binary_intersection {cs V G ge i f phi1 phi2 phi}
      (F1_internal : semaxfunc_InternalInfo cs V G ge i f phi1)
      (F2_internal : semaxfunc_InternalInfo cs V G ge i f phi2)
      (BI : binary_intersection phi1 phi2 = Some phi):
   semaxfunc_InternalInfo cs V G ge i f phi.
Proof.
  destruct F1_internal as [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 Hb6]]]]].
  destruct F2_internal as [Kb1 [Kb2 [Kb3 [Kb4 [Kb5 KHb6]]]]].
  rewrite Hb4 in Kb4; inv Kb4.
  red; repeat split; trivial.
  + apply callconv_of_binary_intersection in BI; destruct BI as [X Y].
    rewrite Hb4, X; trivial.
  + assert (Hi: i = fst (i, phi1)) by reflexivity. rewrite Hi; clear Hi. simpl fst.
    apply (semax_body_binaryintersection _ (i,phi1) (i, phi2)); trivial.
Qed.

Lemma length_of_typelist2: forall l, length (typelist2list l) = length (typlist_of_typelist l).
Proof. induction l; simpl; trivial. rewrite IHl; trivial. Qed.

Lemma externalInfo_binary_intersection {Espec ge i ef argsig retsig cc phi1 phi2 phi}
      (F1_external : semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi1)
      (F2_external : semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi2)
      (BI : binary_intersection phi1 phi2 = Some phi):
  semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi.
Proof.
  destruct (callconv_of_binary_intersection BI) as [CC1 CC2].
  destruct phi. destruct t as [params rt]. simpl in CC1, CC2. 
  destruct phi1 as [[params1 rt1] c1 A1 P1 Q1 P1ne Q1ne]. simpl in CC1. subst c1.
  destruct F1_external as [RT1 [C1 [PAR1 [Sig1 [EF1 [ENT1 [EXT1 GFF1]]]]]]].
  destruct phi2 as [[params2 rt2] c2 A2 P2 Q2 P2ne Q2ne]. simpl in CC2. subst c2.
  destruct F2_external as [RT2 [C2 [PAR2 [Sig2 [EF2 [ENT2 [EXT2 GFF2]]]]]]].
  subst cc rt1 rt2. 
  assert (FSM:= @binary_intersection_typesigs _ _ _ BI). simpl typesig_of_funspec in FSM.
  destruct FSM as [FSM1 FSM2].
  inversion FSM1; subst retsig params1; clear FSM1.
  inversion FSM2; subst params2 params; clear FSM2 H1. 

  split3; trivial.
  split3; trivial.
  split3. 
  + unfold binary_intersection in BI. rewrite 2 if_true in BI by trivial. inv BI.
    apply inj_pair2 in H1; subst P. apply inj_pair2 in H2; subst Q. simpl.
    clear - EF1 EF2. destruct (ef_inline ef). 2: left; trivial.
    destruct EF1; try congruence. 
    destruct EF2; try congruence.
    right. red; simpl; intros ? [x X]; destruct x. apply (H ts X). apply (H0 ts X).
  + intros. unfold binary_intersection in BI. rewrite 2 if_true in BI by trivial. inv BI.
    apply inj_pair2 in H1; subst P. apply inj_pair2 in H2; subst Q. simpl.
    destruct x as [b BB]. destruct b; simpl.
      * apply (ENT1 gx ts BB). 
      * apply (ENT2 gx ts BB).
  + split; trivial.
    eapply semax_external_binaryintersection. apply EXT1. apply EXT2.
      apply BI.
      rewrite Sig2; simpl. rewrite length_of_typelist2. trivial. 
Qed.

Lemma find_funspec_sub: forall specs' specs 
      (HE1 : map fst specs' = map fst specs)
      (HE2 : Forall2 funspec_sub (map snd specs) (map snd specs'))
      i phi' (F : find_id i specs' = Some phi'),
   exists phi : funspec, find_id i specs = Some phi /\ funspec_sub phi phi'.
Proof.
    induction specs'; intros. inv F.
    destruct specs; inv HE1; inv HE2.
    destruct a as [i' psi']. destruct p as [j psi]. simpl in *; subst.
    if_tac; subst. inv F. eexists; split; [ reflexivity | trivial].
    destruct (IHspecs' _ H1 H6 _ _ F) as [phi [Phi PHI]]; clear IHspecs'.
    exists phi; split; trivial.
Qed.

Lemma subsumespec_app l1 l2 k1 k2 i
          (L1K1: subsumespec (find_id i l1) (find_id i k1)) 
          (L2K2: subsumespec (find_id i l2) (find_id i k2))
          (D:list_disjoint (map fst l2) (map fst k1)):
      subsumespec (find_id i (l1++l2)) (find_id i (k1++k2)).
Proof.
  red. rewrite ! find_id_app_char.
  remember (find_id i l1) as p1. destruct p1; simpl in *; symmetry in Heqp1.
+ destruct L1K1 as [phi [? ?]].
  rewrite H. exists phi; split; trivial.
+ remember (find_id i l2) as p2. destruct p2; simpl in *; symmetry in Heqp2; trivial.
  destruct L2K2 as [phi [? ?]].
  rewrite (list_disjoint_map_fst_find_id1 D _ _ Heqp2), H.
  exists phi; split; trivial.
Qed.

Lemma subsumespec_app_right_left l k1 k2 i
          (LK: subsumespec (find_id i l) (find_id i k1)):
      subsumespec (find_id i l) (find_id i (k1++k2)).
Proof.
  red. rewrite ! find_id_app_char. destruct (find_id i l); trivial.
  destruct LK as [phi [? ?]]. rewrite H. exists phi; split; trivial.
Qed.
 
Lemma subsumespec_app_right_right l k1 k2 i
          (LK: subsumespec (find_id i l) (find_id i k2))
          (Hi: find_id i k1= None):
      subsumespec (find_id i l) (find_id i (k1++k2)).
Proof.
  red. rewrite ! find_id_app_char, Hi. destruct (find_id i l); trivial.
Qed.

Lemma subsumespec_app_left l1 l2 k i
          (LK1: subsumespec (find_id i l1) (find_id i k)) 
          (LK2: find_id i l1 = None -> subsumespec (find_id i l2) (find_id i k)):
      subsumespec (find_id i (l1++l2)) (find_id i k).
Proof.
  red. rewrite ! find_id_app_char. 
  destruct (find_id i l1); trivial. simpl in *. specialize (LK2 (eq_refl _)).
  destruct (find_id i l2); trivial.
Qed.

Definition isInternal (fd:globdef (Ctypes.fundef Clight.function) type) :=
   match fd with Gfun (Internal _) => true | _ => false end.

Definition IntIDs (p: QP.program function): list ident := 
  map fst ((filter (fun x => isInternal (snd x))) (PTree.elements (QP.prog_defs p))).

Lemma IntIDs_elim {i p}:
   In i (IntIDs p) -> exists f, In (i, Gfun (Internal f)) (PTree.elements (QP.prog_defs p)).
Proof. unfold IntIDs; forget (PTree.elements (QP.prog_defs p)) as l. 
  induction l; simpl; intros. contradiction.
  destruct a; simpl in *.
  destruct g; simpl in *.
+ destruct f.
  - simpl in H. destruct H; subst. eexists; left; reflexivity.
     apply IHl in H; destruct H. exists x; right; trivial.
   - apply IHl in H; destruct H. exists x; right; trivial.
+ apply IHl in H; destruct H. exists x; right; trivial.
Qed.

Lemma IntIDs_e {i p}: In i (IntIDs p) -> 
      exists f, PTree.get i (QP.prog_defs p) = Some ( Gfun (Internal f)).
Proof. intros. apply IntIDs_elim in H. destruct H. exists x.
   apply PTree.elements_complete.  trivial.
Qed.

Lemma IntIDs_intro {i p f}: In (i, Gfun (Internal f)) (PTree.elements (QP.prog_defs p)) -> In i (IntIDs p).
Proof. unfold IntIDs.
  forget (PTree.elements (QP.prog_defs p)) as l. 
  induction l; simpl; intros. contradiction.
  destruct a; simpl in *.
  destruct g; simpl in *.
+ destruct H.
  - inv H; simpl. left; trivial.
  - apply IHl in H; clear IHl. 
    destruct f0; simpl; trivial. right; trivial.
+ destruct H. congruence. auto. 
Qed.

Lemma IntIDs_i {i p f}: PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) -> In i (IntIDs p).
Proof. intros. apply PTree.elements_correct in H.
 eapply IntIDs_intro. eassumption.
Qed.

Definition SF {Espec cs V ge} G (i:ident) (fd:Clight.fundef) (phi:funspec) :=
  match fd with
    Internal f => semaxfunc_InternalInfo cs V G ge i f phi
  | External ef argsig retsig cc => semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi
  end.

Definition isGvar (x: ident * globdef (fundef function) type) := 
           match (snd x) with Gvar v => true | _ => false end.

Definition Vardefs (p: QP.program Clight.function) := 
     filter isGvar (PTree.elements (QP.prog_defs p)).

Definition globs2pred (gv: globals) (x: ident * globdef (fundef function) type) : mpred :=
  match x with (i, d) => match d with
                           Gfun _ => emp
                         | Gvar v => !!(headptr (gv i)) && globvar2pred gv (i,v)
                         end
  end.

Definition InitGPred (V:list (ident * globdef (fundef function) type)) (gv: globals) :mpred := 
   fold_right sepcon emp (map (globs2pred gv) V).

Definition globals_ok (gv: globals) := forall i, headptr (gv i) \/ gv i = Vundef.

Definition QPvarspecs (p: QP.program function) : varspecs :=
 map (fun iv => (fst iv, gvar_info (snd iv))) (QPprog_vars p).

(* VSTexterns, "E": Syscalls, functions implemented in assembly... These functions are represented
  as GFun(external ...) in Clight, but nevertheless should be in G (and hence 
  should be justified by a semaxfunc - in fact by a semax_func_extern. Since they are in G
  they may be in Exports, too. -*)
Record Component {Espec:OracleKind} (V: varspecs)
      (E Imports: funspecs) (p: QP.program Clight.function) (Exports: funspecs) (GP: globals -> mpred) (G: funspecs) := {
  Comp_prog_OK: QPprogram_OK p;
  Comp_Imports_external: forall i, In i (map fst Imports) -> 
                         exists f ts t cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc));

  Comp_cs: compspecs := compspecs_of_QPcomposite_env _ (proj2 Comp_prog_OK);
  Comp_LNR: list_norepet (map fst V ++ map fst (G ++ Imports));
  Comp_Externs_LNR: list_norepet (map fst E);

  Comp_Exports_LNR: list_norepet (map fst Exports);

  (*VSTexternals are External functions in CompCert*)
  Comp_Externs: forall i, In i (map fst E) -> 
                exists f ts t cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc));
  Comp_G_dom: forall i, In i (IntIDs p ++ (map fst E)) <-> In i (map fst G);
  Comp_G_E: forall i, In i (map fst E) -> find_id i E = find_id i G;
  Comp_G_justified: forall i phi fd,
                    PTree.get i (QP.prog_defs p) = Some (Gfun fd) ->
                    find_id i G = Some phi ->
                    @SF Espec Comp_cs V (QPglobalenv p) (Imports ++ G) i fd phi;
(*
  Comp_G_Exports: forall i phi (E: find_id i Exports = Some phi), 
                  exists phi', find_id i G = Some phi' /\ funspec_sub phi' phi;*)
  Comp_G_Exports: forall i phi (E: find_id i Exports = Some phi),
                  match find_id i G with
                    Some phi' => funspec_sub phi' phi
                  | None => exists phi', find_id i Imports = Some phi' /\ funspec_sub phi' phi
                  end;

  Comp_MkInitPred: forall gv,   globals_ok gv -> InitGPred (Vardefs p) gv |-- GP gv
}.

Definition Comp_prog {Espec V E Imports p Exports GP G} (c:@Component Espec V E Imports p Exports GP G):= p.
Definition Comp_G {Espec V E Imports p Exports GP G} (c:@Component Espec V E Imports p Exports GP G):= G.

Definition VSU {Espec} E Imports p Exports GP:=
  ex (@Component Espec (QPvarspecs p) E Imports p Exports GP).
  

Arguments Comp_Imports_external {Espec V E Imports p Exports GP G} / c.
Arguments Comp_prog_OK {Espec V E Imports p Exports GP G} / c.
Arguments Comp_cs {Espec V E Imports p Exports GP G} / c.
Arguments Comp_LNR {Espec V E Imports p Exports GP G} / c.
Arguments Comp_Externs_LNR {Espec V E Imports p Exports GP G} / c.
Arguments Comp_Exports_LNR {Espec V E Imports p Exports GP G} / c.
Arguments Comp_Externs {Espec V E Imports p Exports GP G} / c.
Arguments Comp_G_dom {Espec V E Imports p Exports GP G} / c.
Arguments Comp_G_justified {Espec V E Imports p Exports GP G} / c.
Arguments Comp_G_Exports {Espec V E Imports p Exports GP G} / c.
Arguments Comp_G_E {Espec V E Imports p Exports GP G} / c.
Arguments Comp_MkInitPred {Espec V E Imports p Exports GP G} / c.

Section Component.
Variable Espec: OracleKind.
Variable V: varspecs.
Variable E Imports: funspecs.
Variable p: QP.program Clight.function.
Variable Exports: funspecs.
Variable GP: globals -> mpred.
Variable G: funspecs.

Variable c: @Component Espec V E Imports p Exports GP G.

Lemma Comp_G_LNR: list_norepet (map fst G).
Proof.
pose proof (Comp_LNR c).
rewrite list_norepet_app in H.
destruct H as [_ [? _]].
rewrite map_app in H.
rewrite list_norepet_app in H; destruct H as [? [? ?]].
apply H.
Qed.

Lemma Comp_ExternsImports_LNR: list_norepet (map fst (E++Imports)).
Proof.
pose proof (Comp_LNR c).
rewrite list_norepet_app in H.
destruct H as [_ [? _]].
rewrite map_app in H.
rewrite list_norepet_app in H; destruct H as [? [? ?]].
rewrite map_app, list_norepet_app; split3; auto.
apply (Comp_Externs_LNR c).
intros i j ? ? ?; subst j; apply (H1 i i); auto.
rewrite <- (Comp_G_dom c).
rewrite in_app; auto.
Qed. 

Lemma Comp_Imports_LNR: list_norepet (map fst Imports).
Proof.
pose proof (Comp_LNR c).
rewrite list_norepet_app in H; destruct H as [_ [? _]].
rewrite map_app, list_norepet_app in H; apply H.
Qed.

Lemma Comp_E_in_G_find: forall i phi, find_id i E = Some phi -> find_id i (Comp_G c) = Some phi.
Proof. intros. rewrite <- (Comp_G_E c); trivial. apply find_id_In_map_fst in H; trivial. Qed.

Lemma Comp_E_in_G: forall {i}, In i (map fst E) -> In i (map fst (Comp_G c)).
Proof. intros. apply In_map_fst_find_id in H. destruct H.
  apply Comp_E_in_G_find in H. apply find_id_In_map_fst in H; trivial. 
  apply (Comp_Externs_LNR c).
Qed. 

Lemma Comp_LNR_Interns: list_norepet (IntIDs p).
Proof.
  eapply sublist_norepet.
  unfold IntIDs.
  instantiate (1:= map fst (PTree.elements (QP.prog_defs p))).
2: apply PTree.elements_keys_norepet.
  remember (PTree.elements (QP.prog_defs p)) as l; clear.
  induction l; simpl; intros. constructor.
  destruct a; simpl. destruct g; [destruct f |]; subst; constructor; auto.
Qed.

Lemma LNR_Internals_Externs: list_norepet (IntIDs p ++ map fst E).
Proof.
  specialize (Comp_Externs_LNR c); specialize Comp_LNR_Interns; intros.
  apply list_norepet_app; split3; trivial.
  do 5 intros ?; subst.
  apply (Comp_Externs c) in H2. destruct H2 as [ef [tys [rt [cc Hy]]]].
  apply IntIDs_e in H1; destruct H1. congruence.
Qed.

Lemma Comp_G_intern {i} (Hi: In i (map fst (Comp_G c))):
      ( ~ In i (map fst E)) <->
      ( exists f, PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) ).
Proof. 
  apply list_in_map_inv in Hi. destruct Hi as [[ii phi] [H Hi]]; simpl in H; subst ii.
  apply in_map_fst in Hi. rewrite <- (Comp_G_dom c) in Hi.
  apply in_app_or in Hi; destruct Hi.
+ split; intros.
  - apply IntIDs_e in H; destruct H.
    rewrite H. exists x; trivial.
  - destruct H0. intros N. specialize LNR_Internals_Externs.
    rewrite list_norepet_app; intros [? [? X]]. apply (X i i); trivial.
+ split; intros. contradiction.
  destruct H0 as [f Hf]. apply (Comp_Externs c) in H. destruct H as [? [? [? [? ?]]]]. congruence.
Qed.

Lemma Comp_G_extern {i} (Hi: In i (map fst (Comp_G c))):
      (In i (map fst E)) <->
      exists ef tys rt cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External ef tys rt cc)).
Proof. 
  apply list_in_map_inv in Hi. destruct Hi as [[ii phi] [H Hi]]; simpl in H; subst ii.
  apply in_map_fst in Hi. rewrite <- (Comp_G_dom c) in Hi.
  apply in_app_or in Hi; destruct Hi.
+ split; intros.
  - specialize LNR_Internals_Externs.
    rewrite list_norepet_app; intros [? [? X]]. elim (X i i); trivial.
  - apply IntIDs_e in H; destruct H. destruct H0 as [ef [tys [rt [cc He]]]]; congruence.
+ split; intros; trivial.
  apply c in H; trivial.
Qed.

Lemma Comp_G_elim {i} (Hi: In i (map fst (Comp_G c))):
      (In i (map fst E) /\ exists ef tys rt cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External ef tys rt cc)))
    \/ ((~In i (map fst E)) /\ In i (IntIDs p) /\ exists f, PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f))).
Proof.
  destruct (in_dec ident_eq i (map fst E)).
+ left. split; trivial. apply (Comp_G_extern Hi); trivial.
+ right; split; trivial. apply (Comp_G_intern Hi) in n. split; trivial.
  destruct n. apply IntIDs_i in H; trivial.
Qed.

Lemma Comp_G_in_Fundefs {i} (Hi: In i (map fst (Comp_G c))):
      exists fd, PTree.get i (QP.prog_defs p) = Some (Gfun fd).
Proof. 
  destruct (in_dec ident_eq  i (map fst E)).
+ apply (Comp_G_extern Hi) in i0. destruct i0 as [ef [tys [rt [cc Hef]]]].
   eauto.
+ apply (Comp_G_intern Hi) in n. destruct n as [f Hf]. eauto.
Qed.

Lemma Comp_G_in_progdefs' {i phi} (Hi: find_id i (Comp_G c) = Some phi):
      exists fd, PTree.get i (QP.prog_defs p) = Some (Gfun fd).
Proof. apply find_id_In_map_fst in Hi. 
  apply Comp_G_in_Fundefs in Hi; destruct Hi.
  eauto.
Qed.

Lemma Comp_G_in_Fundefs' {i phi} (Hi: find_id i (Comp_G c) = Some phi):
      exists fd, PTree.get i (QP.prog_defs p) = Some (Gfun fd).
Proof. apply find_id_In_map_fst in Hi. apply Comp_G_in_Fundefs; trivial. Qed.

Lemma Comp_G_in_progdefs {i} (Hi: In i (map fst (Comp_G c))):
      exists fd, PTree.get i (QP.prog_defs p) = Some (Gfun fd).
Proof.
  apply Comp_G_elim in Hi.
  destruct Hi as [[HE [ef [tys [rt [cc H]]]]] | [HE [INT [f H]]]]; rewrite H; eexists; reflexivity.
Qed.

Lemma Comp_Imports_in_Fundefs {i phi}: find_id i Imports = Some phi ->
      exists f , PTree.get i (QP.prog_defs p) = Some (Gfun f).
Proof.
  specialize (Comp_Imports_external c); intros. apply find_id_e in H0. apply in_map_fst in H0.
  destruct (H _ H0) as [f [ts [t [cc Hf]]]]; clear H. eauto.
Qed.

Lemma Comp_Exports_in_Fundefs {i phi}: find_id i Exports = Some phi ->
      exists f , PTree.get i (QP.prog_defs p) = Some (Gfun f).
Proof.
  intros. apply (Comp_G_Exports c) in H.
  remember (find_id i G) as x; symmetry in Heqx; destruct x as [psi | ].
+ apply Comp_G_in_Fundefs' in Heqx; trivial.
+ destruct H as [phi' [IMP FS]].
  apply Comp_Imports_in_Fundefs in IMP; trivial.
Qed.

Lemma Comp_Imports_in_progdefs {i}: 
 In i (map fst(Imports)) -> In i (map fst (PTree.elements (QP.prog_defs p))).
Proof.
  specialize (Comp_Imports_external c); intros.
  destruct (H _ H0) as [f [ts [t [cc Hf]]]]; clear H.
  apply PTree.elements_correct in  Hf.
  apply (in_map fst) in Hf. auto.
Qed.

Lemma Comp_Exports_in_progdefs {i}: 
   In i (map fst(Exports)) -> In i (map fst (PTree.elements (QP.prog_defs p))).
Proof.
  intros. apply In_map_fst_find_id in H; [ destruct H | apply c].
  apply Comp_Exports_in_Fundefs in H. destruct H.
  apply PTree.elements_correct in  H.
  apply (in_map fst) in H. auto.
Qed.

Lemma Comp_Imports_ExternalFundefs {i phi}:
      find_id i Imports = Some phi ->
      exists ef tys rt cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External ef tys rt cc)).
Proof.
  specialize (Comp_Imports_external c); intros. apply find_id_In_map_fst in H0.
  apply (H _ H0).
Qed.

Lemma Comp_Interns_disjoint_from_Imports: list_disjoint (IntIDs p) (map fst Imports).
Proof.
  intros x y X Y.
  apply (Comp_Imports_external c) in Y. destruct Y as [f [ef [ts [t FE]]]].
  apply list_in_map_inv in X. destruct X as [[j fd] [J FD]]; simpl in J; subst j.
  apply filter_In in FD.  simpl in FD; destruct FD. unfold isInternal in H0.
  intro; subst. destruct fd; try congruence. destruct f0; try congruence.
  apply PTree.elements_complete in H. congruence.
Qed. 

Lemma Comp_ExternsImports_disjoint: list_disjoint (map fst E) (map fst Imports).
Proof. specialize (Comp_ExternsImports_LNR). rewrite map_app, list_norepet_app; intros X; apply X. Qed.

Lemma Comp_G_disjoint_from_Imports: list_disjoint (map fst Imports) (map fst (Comp_G c)).
Proof.
  do 5 intros ?; subst. rewrite <- (Comp_G_dom c) in H0. apply in_app_or in H0; destruct H0.
+ apply (list_disjoint_notin y Comp_Interns_disjoint_from_Imports) in H0; contradiction.
+ apply (list_disjoint_notin y Comp_ExternsImports_disjoint) in H0; contradiction. 
Qed.

Lemma Comp_ctx_LNR: list_norepet (map fst(Imports ++ Comp_G c)).
Proof.
  rewrite map_app. apply list_norepet_append.
  apply Comp_Imports_LNR.
  apply Comp_G_LNR.
  apply Comp_G_disjoint_from_Imports.
Qed.

Lemma Comp_G_disjoint_from_Imports_find_id {i phi} (Hi: find_id i Imports = Some phi): 
      find_id i (Comp_G c) = None.
Proof. apply (list_disjoint_map_fst_find_id1 Comp_G_disjoint_from_Imports _ _ Hi). Qed.

Lemma Comp_entail {GP'} (H: forall gv, GP gv |-- GP' gv):
      @Component Espec V E Imports p Exports GP' G.
Proof. intros. destruct c. econstructor; try assumption.
apply Comp_G_justified0.
 intros; eapply derives_trans. apply Comp_MkInitPred0; auto. cancel.
Qed.

Lemma Comp_entail_starTT:
      @Component Espec V E Imports p Exports (GP * TT)%logic G.
Proof. intros. apply Comp_entail. intros; simpl; apply sepcon_TT. Qed.

Lemma Comp_entail_TT:
      @Component Espec V E Imports p Exports TT G.
Proof. intros. eapply Comp_entail. intros; simpl. apply TT_right. Qed.

Lemma Comp_entail_split {GP1 GP2} (H: forall gv, GP gv |-- (GP1 gv * GP2 gv)%logic):
      @Component Espec V E Imports p Exports (fun gv => GP1 gv * TT)%logic G.
Proof. intros. eapply Comp_entail. intros; simpl.
  eapply derives_trans. apply H. cancel.
Qed.

Lemma Comp_Imports_sub Imports' (HI1: map fst Imports' = map fst Imports)
      (HI2: Forall2 funspec_sub (map snd Imports') (map snd Imports)): 
      @Component Espec V E Imports' p Exports GP G.
Proof.
  assert (AUX1: forall i, subsumespec ((find_id i (Imports ++ Comp_G c)))
                                      ((find_id i (Imports' ++ Comp_G c)))).
  { intros.
    remember (find_id i (Imports ++ Comp_G c)) as s; symmetry in Heqs; destruct s; simpl; trivial.
    rename f into phi. apply find_id_app in Heqs; destruct Heqs.
    + assert (exists phi', find_id i Imports' = Some phi' /\ funspec_sub phi' phi).
      { clear - H HI1 HI2. symmetry in HI1. eapply find_funspec_sub; eassumption. }
      destruct H0 as [phi' [H' Sub]]. 
      rewrite find_id_app1 with (x:=phi'); trivial.
      apply funspec_sub_sub_si in Sub.
      exists phi'; split; trivial.
    + rewrite find_id_app2 with (x:=phi); trivial.
      - exists phi; split; [ trivial | apply funspec_sub_si_refl; trivial ].
      - specialize Comp_ctx_LNR. subst. rewrite ! map_app, HI1; trivial. }
  assert (AUX2: forall V' i, sub_option ((make_tycontext_g V' (Imports ++ Comp_G c)) ! i)
                                     ((make_tycontext_g V' (Imports' ++ Comp_G c)) ! i)).
  { intros. specialize (AUX1 i).
    remember ((make_tycontext_g V' (Imports ++ Comp_G c)) ! i) as q; symmetry in Heqq; destruct q; simpl; trivial.
    remember (find_id i (Imports ++ Comp_G c)) as w; symmetry in Heqw; destruct w; simpl in *.
    + destruct AUX1 as [psi [X Y]]. 
      erewrite semax_prog.make_tycontext_s_g in Heqq. instantiate (1:=f) in Heqq.
      - rewrite <- Heqq; clear Heqq. 
        erewrite semax_prog.make_tycontext_s_g. 
        2: rewrite make_tycontext_s_find_id; eassumption.
        f_equal. specialize (Y (compcert_rmaps.RML.empty_rmap 0)). simpl in Y.
        exploit Y; trivial. intros Q.
        apply (type_of_funspec_sub_si _ _ _ Q).
      - rewrite make_tycontext_s_find_id. eassumption.
    + rewrite semax_prog.make_tycontext_g_G_None in Heqq by trivial.
      rewrite semax_prog.make_tycontext_g_G_None; trivial.
      apply find_id_None_iff. apply find_id_None_iff in Heqw. intros N; apply Heqw.
      rewrite map_app in *. rewrite HI1 in N. trivial. } 
  eapply Build_Component; subst; try solve [apply c].
+ rewrite HI1; apply c. 
+ rewrite map_app, HI1, <- map_app; apply c.
+ intros. specialize (Comp_G_justified c i _ _ H H0); intros. destruct fd.
  -  eapply InternalInfo_subsumption. apply AUX2. apply AUX1. apply Comp_ctx_LNR. apply H1.
  - auto.
+ intros i phi PHI. specialize (Comp_G_Exports c _ _ PHI). destruct (find_id i G); trivial.
  intros [psi [PSI Psi]].
  symmetry in HI1. specialize (find_funspec_sub _ _ HI1 HI2 _ _ PSI) as [tau [Tau TAU]].
  exists tau; split; trivial. eapply funspec_sub_trans; eassumption.
+ apply (Comp_MkInitPred c).
Qed.

(*Together with Lemma  Comp_Exports_suboption, this lemma means we can abstract or hide exports*)
Lemma Comp_Exports_sub1 Exports' (HE1: map fst Exports' = map fst Exports)
      (HE2: Forall2 funspec_sub (map snd Exports) (map snd Exports')):
      @Component Espec V E Imports p Exports' GP G.
Proof.
  eapply Build_Component; try apply c.
+ rewrite HE1; apply c. 
+ intros i phi Hi. rename phi into phi'.
  assert (X: exists phi, find_id i Exports = Some phi /\ funspec_sub phi phi').
  { clear - HE1 HE2 Hi. eapply find_funspec_sub; eassumption. }
  destruct X as [phi [Phi PHI]].
  specialize (Comp_G_Exports c _ _ Phi).
  destruct (find_id i G); intros.
  - eapply funspec_sub_trans; eassumption.
  - destruct H as [tau [Tau TAU]]. exists tau; split; trivial.
    eapply funspec_sub_trans; eassumption.
+ apply (Comp_MkInitPred c).
Qed.

Lemma Comp_Exports_sub2 Exports' (LNR: list_norepet (map fst Exports'))
      (HE2: forall i, sub_option (find_id i Exports') (find_id i Exports)):
      @Component Espec V E Imports p Exports' GP G.
Proof.
  eapply Build_Component (*with (Comp_G c)*); try apply c; trivial.
+ intros i phi' Hi. specialize (HE2 i). rewrite Hi in HE2; simpl in HE2.
  apply c; trivial.
+apply (Comp_MkInitPred c).
Qed.

Definition funspecs_sqsub Exp Exp' :=
  forall i phi', find_id i Exp' = Some phi' ->
         exists phi, find_id i Exp = Some phi /\ funspec_sub phi phi'.

Lemma funspecs_sqsub_app l1 l2 m1 m2 (LM1: map fst l1 = map fst m1) (LM2: map fst l2= map fst m2)
      (LNR: list_norepet (map fst (l1++l2))):
      (funspecs_sqsub l1 m1 /\ funspecs_sqsub l2 m2) = funspecs_sqsub (l1++l2) (m1++m2).
Proof. unfold funspecs_sqsub. rewrite map_app in LNR. destruct (list_norepet_append_inv _ _ _ LNR) as [_[ _ D]]; clear LNR.
apply prop_ext; split; intros.
+ rewrite assoclists.find_id_app_char in *. destruct H. specialize (H i). specialize (H1 i).
  destruct (find_id i m1).
  - inv H0. destruct (H _ (eq_refl _)) as [? [X ?]]. rewrite X. eexists; split; auto.
  - destruct (H1 _ H0) as [? [X ?]]. 
    destruct (assoclists.find_id_None_iff i l1). rewrite H4, X. eexists; split; auto.
    apply list_disjoint_sym in D. 
    apply find_id_In_map_fst in H0; rewrite <- LM2 in H0.
    apply (list_disjoint_notin i D H0).
+ split; intros.
  - specialize (H i). rewrite assoclists.find_id_app_char, H0 in H.
    destruct (H _ (eq_refl _)) as [? [? ?]]; clear H.
    rewrite assoclists.find_id_app_char in H1.
    destruct (find_id i l1). eexists; split; eauto.
    apply find_id_In_map_fst in H0. apply find_id_In_map_fst in H1. rewrite <- LM1 in H0.
    elim (D i i H0 H1); trivial.
 - specialize (H i). rewrite assoclists.find_id_app_char, H0 in H.
   apply find_id_In_map_fst in H0. rewrite <- LM2 in H0.
   apply list_disjoint_sym in D. 
   specialize (list_disjoint_notin i D H0); intros.
   rewrite assoclists.find_id_app_char in H.
   destruct (assoclists.find_id_None_iff i l1). rewrite (H3 H1) in H.
   destruct (assoclists.find_id_None_iff i m1).
   rewrite LM1 in H1. rewrite (H5 H1) in H. apply H; trivial.
Qed.

Lemma funspecs_sqsub_refl l: funspecs_sqsub l l.
Proof. red; intros. exists phi'; split; trivial. apply funspec_sub_refl. Qed.

Lemma funspecs_sqsub_nil: funspecs_sqsub nil nil. 
Proof. red; intros. inv H. Qed.

Lemma funspecs_sqsub_cons i phi l phi' l': 
      funspec_sub phi phi' -> funspecs_sqsub l l' ->
      funspecs_sqsub ((i,phi)::l) ((i,phi')::l').
Proof. intros; simpl. red; intros; simpl. simpl in H1.
  if_tac in H1.
+ inv H1. exists phi; split; trivial.
+ apply H0; trivial.
 Qed.

Lemma funspecs_sqsub_D i phi l phi' l': 
      funspecs_sqsub ((i,phi)::l) ((i,phi')::l') ->
      list_norepet (map fst ((i,phi)::l)) -> map fst l = map fst l' ->
      funspec_sub phi phi' /\ funspecs_sqsub l l'.
Proof. intros; simpl; split.
+ specialize (H i); simpl in H. rewrite 2 if_true in H; trivial.
  destruct (H _ (eq_refl _)) as [? [X ?]]. inv X. trivial.
+ red; intros. specialize (H i0); simpl in H.
  assert (Y: i0<>i). 
  { intros N; subst. simpl in H0. inv H0.
    apply find_id_In_map_fst in H2. rewrite H1 in H5; contradiction. }
  rewrite 2 if_false in H; auto.
Qed.

Lemma Comp_Exports_sub Exports' (LNR: list_norepet (map fst Exports'))
      (HE2: funspecs_sqsub Exports Exports'):
      @Component Espec V E Imports p Exports' GP G.
Proof.
  eapply Build_Component (*with (Comp_G c)*); try apply c; trivial.
+ intros i phi' Hi. destruct (HE2 _ _ Hi) as [phi [H1 H2]].
  specialize (Comp_G_Exports c _ _ H1). destruct (find_id i G); intros.
  - eapply funspec_sub_trans; eassumption.
  - destruct H as [tau [Tau TAU]]. exists tau; split; trivial.
    eapply funspec_sub_trans; eassumption.
+ apply (Comp_MkInitPred c).
Qed.

End Component.

Arguments Comp_LNR {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_LNR {Espec V E Imports p Exports GP G} c.
Arguments Comp_ctx_LNR {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_disjoint_from_Imports {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_disjoint_from_Imports_find_id {Espec V E Imports p Exports GP G} c.
Arguments Comp_Interns_disjoint_from_Imports {Espec V E Imports p Exports GP G} c.
Arguments Comp_Exports_in_progdefs {Espec V E Imports p Exports GP G} c.

Arguments Comp_ExternsImports_LNR {Espec V E Imports p Exports GP G} c.
Arguments Comp_Externs_LNR {Espec V E Imports p Exports GP G} c.
Arguments Comp_Imports_in_Fundefs {Espec V E Imports p Exports GP G} c.
Arguments Comp_Exports_in_Fundefs {Espec V E Imports p Exports GP G} c.
Arguments Comp_Imports_in_progdefs {Espec V E Imports p Exports GP G} c.
Arguments Comp_Exports_in_progdefs {Espec V E Imports p Exports GP G} c.

Arguments Comp_G_intern {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_extern {Espec V E Imports p Exports GP G} c.

Arguments Comp_Imports_LNR {Espec V E Imports p Exports GP G} c.
Arguments LNR_Internals_Externs {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_in_Fundefs {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_in_Fundefs' {Espec V E Imports p Exports GP G} c.
Arguments Comp_E_in_G {Espec V E Imports p Exports GP G} c.
Arguments Comp_E_in_G_find {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_elim {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_in_progdefs {Espec V E Imports p Exports GP G} c.
Arguments Comp_G_in_progdefs' {Espec V E Imports p Exports GP G} c.
Arguments Comp_Imports_sub {Espec V E Imports p Exports GP G} c.
Arguments Comp_Exports_sub {Espec V E Imports p Exports GP G} c.
Arguments Comp_entail {Espec V E Imports p Exports GP G} c.


Section VSU_rules.
Variable Espec: OracleKind.
Variable E Imports: funspecs.
Variable p : QP.program Clight.function.
Variable Exports: funspecs.
Variable GP: globals -> mpred.
Variable vsu: @VSU Espec E Imports p Exports GP.

Lemma VSU_Imports_sub Imports' (HI1: map fst Imports' = map fst Imports)
      (HI2: Forall2 funspec_sub (map snd Imports') (map snd Imports)): 
      @VSU Espec E Imports' p Exports GP.
Proof. destruct vsu as [G c]. exists G. eapply Comp_Imports_sub; eassumption. Qed.

Lemma VSU_Exports_sub1 Exports' (HE1: map fst Exports' = map fst Exports)
      (HE2: Forall2 funspec_sub (map snd Exports) (map snd Exports')):
      @VSU Espec E Imports p Exports' GP.
Proof. destruct vsu as [G c]. exists G. eapply Comp_Exports_sub1; eassumption. Qed.

Lemma VSU_Exports_sub Exports' (LNR: list_norepet (map fst Exports'))
      (HE2: funspecs_sqsub Exports Exports'):
      @VSU Espec E Imports p Exports' GP.
Proof. destruct vsu as [G c]. exists G. eapply Comp_Exports_sub; eassumption. Qed.

Lemma VSU_entail {GP'} : (forall gv, GP gv |-- GP' gv) -> 
      @VSU Espec E Imports p Exports GP'.
Proof. intros. destruct vsu as [G C].
  exists G. apply (Comp_entail C _ H).
Qed.

End VSU_rules.

(*
Definition VSU_G  {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP)
  := proj1_sig v.
*)

Definition VSU_Imports {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := Imports.
Definition VSU_Externs {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := E.
Definition VSU_Exports {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := Exports.
Definition VSU_prog {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := p.
Definition VSU_Espec {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := Espec.
Definition VSU_GP {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := GP.

Arguments VSU_Externs {Espec E Imports p Exports GP} / _ .
Arguments VSU_Exports {Espec E Imports p Exports GP} / _ .
Arguments VSU_Imports {Espec E Imports p Exports GP} / _ .
Arguments VSU_prog {Espec E Imports p Exports GP} / _ .
Arguments VSU_Espec {Espec E Imports p Exports GP} / _ .
Arguments VSU_GP {Espec E Imports p Exports GP} / _ .

Definition merge_specs (phi1:funspec) (sp2: option funspec): funspec :=
  match sp2 with 
    Some phi2 => match binary_intersection phi1 phi2 with
                                  Some phi => phi
                                | None => (*None*) phi1
                            end
  | None => phi1
  end.

Lemma merge_specs_succeed {phi1 phi2}:
      typesig_of_funspec phi1 = typesig_of_funspec phi2 ->
      callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2 ->
  binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2)).
Proof. intros.
  simpl. destruct phi1; destruct phi2; simpl in *. rewrite H.  subst c0.
  rewrite ! if_true; trivial.
Qed.

Definition G_merge_aux {f} (l1 l2 : list (ident * funspec)) : list (ident * funspec):=
  map (fun x => match x with (i,phi1) =>
                    (i, f phi1 (find_id i l2))
                   end) l1.

Lemma G_merge_aux_find_id1 {f}: forall {l1 l2 i phi1} (Hi: find_id i l1 = Some phi1),
  find_id i (@G_merge_aux f l1 l2) = Some (f phi1 (find_id i l2)).
Proof. clear.
  induction l1; simpl; intros. inv Hi.
  destruct a. if_tac; subst. inv Hi; trivial. eauto.
Qed.

Lemma G_merge_aux_find_id2 {f}: forall {l1 l2 i phi} (Hi: find_id i (@G_merge_aux f l1 l2) = Some phi),
  exists phi1, find_id i l1 = Some phi1 /\ phi = f phi1 (find_id i l2).
Proof. clear.
  induction l1; simpl; intros. inv Hi.
  destruct a. if_tac; subst. inv Hi. exists f0; split; trivial. eauto.
Qed.

Lemma G_merge_aux_find_id3 {f}: forall {l1 l2 i}, find_id i l1 = None <-> find_id i (@G_merge_aux f l1 l2) = None.
Proof. clear.
  induction l1; simpl; split; intros; trivial; 
  destruct a; if_tac; subst; try congruence; apply (IHl1 l2); trivial.
Qed.

Lemma G_merge_aux_dom {f}: forall {l1 l2}, map fst (@G_merge_aux f l1 l2) = map fst l1.
Proof. clear.
  induction l1; simpl; intros; trivial; destruct a; simpl in *. f_equal; auto.
Qed.

Lemma G_merge_aux_consR {f}: forall {l1 l2 i} (Hi:find_id i l1 = None) phi2, 
     @G_merge_aux f l1 ((i,phi2)::l2) = @G_merge_aux f l1 l2.
Proof. clear.
  induction l1; simpl; intros; trivial; destruct a; simpl in *. 
  destruct (Memory.EqDec_ident i0 i); subst; simpl in *. rewrite if_true in Hi; [ discriminate | trivial].
  rewrite if_false in Hi. rewrite IHl1; trivial. intros ?; subst; contradiction.
Qed.

Lemma G_merge_aux_length {f}: forall {l1 l2}, length (@G_merge_aux f l1 l2) = length l1.
Proof. clear.
  induction l1; simpl; intros; trivial; destruct a; simpl in *. f_equal; auto.
Qed.

Lemma G_merge_aux_InDom {f} {l1 l2 i}: In i (map fst (@G_merge_aux f l1 l2)) <-> In i (map fst l1).
Proof. clear. rewrite G_merge_aux_dom. split; trivial. Qed.

Definition G_merge (l1 l2 : list (ident * funspec)):=
  @G_merge_aux merge_specs l1 l2 ++ 
  filter (fun x => match x with (i,a) => match find_id i l1 with 
                                                 Some phi => false | None => true end end) l2.

Lemma G_merge_find_id_SomeSome {l1 l2 i phi1 phi2}: 
      forall (Hi1: find_id i l1 = Some phi1) (Hi2: find_id i l2 = Some phi2)
               (Sigs: typesig_of_funspec phi1 = typesig_of_funspec phi2)
             (CCs: callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2),
      exists phi, binary_intersection phi1 phi2 = Some phi /\
                  find_id i (G_merge l1 l2) = Some phi.
Proof. clear. intros.
  unfold G_merge. rewrite find_id_app_char, (G_merge_aux_find_id1 Hi1), Hi2.
  rewrite (merge_specs_succeed Sigs CCs). eexists; split; reflexivity.
Qed.

Lemma G_merge_find_id_SomeNone {l1 l2 i phi1}:
      forall (Hi1: find_id i l1 = Some phi1) (Hi2: find_id i l2 = None),
      find_id i (G_merge l1 l2) = Some phi1.
Proof. clear. intros. 
  unfold G_merge. rewrite find_id_app_char, (G_merge_aux_find_id1 Hi1), Hi2. reflexivity.
Qed.

Lemma G_merge_find_id_NoneSome {l1 l2 i phi2}:
      forall (Hi1: find_id i l1 = None) (Hi2: find_id i l2 = Some phi2)
             (LNR2: list_norepet (map fst l2)),
      find_id i (G_merge l1 l2) = Some phi2.
Proof. clear.
  intros. destruct (@G_merge_aux_find_id3 merge_specs l1 l2 i) as [X _].
  unfold G_merge. rewrite find_id_app_char, (X Hi1), find_id_filter_char, Hi2, Hi1; trivial.
Qed.

Lemma G_merge_find_id_NoneNone {l1 l2 i}:
      forall (Hi1: find_id i l1 = None) (Hi2: find_id i l2 = None)
             (LNR2: list_norepet (map fst l2)),
      find_id i (G_merge l1 l2) = None.
Proof. clear.
  intros. destruct (@G_merge_aux_find_id3 merge_specs l1 l2 i) as [X _].
  unfold G_merge. rewrite find_id_app_char, (X Hi1), find_id_filter_char, Hi2; trivial.
Qed.

Lemma G_merge_find_id_None {l1 l2 i} (Hi: find_id i (G_merge l1 l2) = None)
            (LNR2: list_norepet (map fst l2)):
      match find_id i l1, find_id i l2 with
        None, None => True
      | Some phi1, Some phi2 => ~ (typesig_of_funspec phi1 = typesig_of_funspec phi2/\
                                   callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
      | _, _ => False
      end.
Proof. clear - Hi LNR2.
  intros. unfold G_merge in Hi. rewrite find_id_app_char in Hi. 
  remember (find_id i l1) as u; symmetry in Hequ; destruct u as [phi1 | ]. 
+ rewrite (G_merge_aux_find_id1 Hequ) in Hi. congruence. 
+ destruct (@G_merge_aux_find_id3 merge_specs l1 l2 i) as [X _].
  rewrite (X Hequ), find_id_filter_char, Hequ in Hi by trivial.
  destruct (find_id i l2); [ congruence | trivial].
Qed.

Lemma G_merge_dom: forall {l1 l2}, map fst (G_merge l1 l2) = 
      map fst (l1 ++ filter (fun x => match x with (i,a) => match find_id i l1 with 
                                                 Some phi => false | None => true end end) l2).
Proof. clear.
  unfold G_merge; intros. rewrite 2 map_app. rewrite G_merge_aux_dom; trivial.
Qed.

Lemma G_merge_InDom {l1 l2 i} (LNR1:list_norepet (map fst l1)): 
      In i (map fst (G_merge l1 l2)) <-> 
      In i (map fst l1) \/ (~ (In i (map fst l1)) /\ In i (map fst l2)).
Proof. clear - LNR1. rewrite G_merge_dom.
  rewrite map_app; split; intros.
+ apply in_app_or in H; destruct H. left; trivial. right. 
  apply list_in_map_inv in H. destruct H as [[j phi] [J H]]. simpl in J; subst.
  apply filter_In in H; destruct H. split.
  - intros N. apply In_map_fst_find_id in N; [destruct N | trivial]. rewrite H1 in H0; congruence.
  - apply in_map_fst in H; trivial.
+ apply in_or_app. destruct H as [H1 | [H1 H2]]; [left; trivial | right].
  apply list_in_map_inv in H2. destruct H2 as [[j phi] [J H]]. simpl in J; subst.
  eapply in_map_fst. apply filter_In. split. eassumption.
  remember (find_id j l1) as u; destruct u as [psi |]; [ symmetry in Hequ | trivial].
  apply find_id_In_map_fst in Hequ. contradiction. 
Qed.

Lemma G_merge_find_id_Some: forall {l1 l2 i phi} (Hi: find_id i (G_merge l1 l2) = Some phi)
 (LNR2: list_norepet (map fst l2)),
  match find_id i l1 with
     Some phi1 => phi = merge_specs phi1 (find_id i l2)
  | None => find_id i l2 = Some phi
  end.
Proof.
  intros. unfold G_merge in Hi; rewrite find_id_app_char, find_id_filter_char in Hi; trivial.
  remember (find_id i (G_merge_aux l1 l2)) as u; symmetry in Hequ; destruct u.
+ inv Hi. apply G_merge_aux_find_id2 in Hequ. destruct Hequ as [phi1 [X Y]].
  rewrite X; trivial.
+ apply G_merge_aux_find_id3 in Hequ. rewrite Hequ in Hi. rewrite Hequ.
  remember (find_id i l2) as q; destruct q; inv Hi; trivial.
Qed.

Lemma G_merge_nil_l {G}: G_merge nil G = G.
Proof.
  induction G. reflexivity. destruct a; simpl in *.
  unfold G_merge in *. simpl in *. rewrite IHG; trivial.
Qed.

Lemma G_merge_nil_r {G}: G_merge G nil = G.
Proof.
  induction G. reflexivity. destruct a; simpl in *.
  unfold G_merge in *. simpl in *. rewrite IHG; trivial.
Qed.

Lemma G_merge_cons_l_None {i phi1 l1 l2} (LNR: list_norepet (map fst ((i,phi1)::l1)))
      (Hi: find_id i l2 = None):
      G_merge ((i,phi1)::l1) l2 =
      (i,phi1) :: G_merge l1 (filter (fun x => negb (ident_eq i (fst x))) l2).
Proof.
  inv LNR. unfold G_merge; simpl. rewrite Hi, filter_filter. simpl. f_equal. f_equal.
  + f_equal. induction l2; simpl; trivial. destruct a; simpl in *. 
    destruct (ident_eq i i0); subst; simpl in *. rewrite if_true in Hi; [ discriminate | trivial].
    rewrite if_false in Hi by trivial. f_equal. apply IHl2; trivial.
  + f_equal. extensionality x; destruct x as [j phi2]; simpl.
    destruct (ident_eq i j); subst; simpl.
    - apply find_id_None_iff in H1. rewrite H1, if_true; trivial.
    - rewrite if_false, andb_true_r. trivial. intros N; subst; elim n; trivial.
Qed.

Lemma G_merge_cons_l_Some {i phi1 l2 phi2} l1 (Hi: find_id i l2 = Some phi2)
      (SIG: typesig_of_funspec phi1 = typesig_of_funspec phi2)
      (CC: callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
      (LNR: list_norepet (map fst ((i,phi1)::l1)))
      (LNR2: list_norepet (map fst l2)):
      exists phi, binary_intersection phi1 phi2 = Some phi /\
      G_merge ((i,phi1)::l1) l2 =
      (i,phi) :: G_merge l1 (filter (fun x => negb (ident_eq i (fst x))) l2).
Proof. 
  specialize (merge_specs_succeed SIG CC); intros. clear SIG.
  inv LNR. eexists; split. eassumption. unfold G_merge; simpl. rewrite H, Hi, filter_filter. f_equal.
  induction l1; simpl.
  + f_equal. extensionality x; destruct x as [j psi]; simpl.
    destruct (ident_eq j i); subst; simpl.
    - rewrite if_true; trivial. destruct (ident_eq i i); [ | elim n]; trivial.
    - rewrite if_false by trivial. destruct (ident_eq i j); [ congruence | trivial].
  + destruct a as [j psi1]. simpl in *.  inv H3.
    destruct (ident_eq j i); subst. { elim H2. left; trivial. }
    remember (find_id i l1) as t; symmetry in Heqt; destruct t.
    { apply find_id_In_map_fst in Heqt. elim H2. right; trivial. } clear H2 H (*SIG*) CC. 
    destruct (find_id_None_iff i l1) as [A1 A2]. specialize (IHl1 (A1 Heqt) H5).
    destruct (app_inj_length IHl1) as [X1 X2]; clear IHl1. rewrite 2 G_merge_aux_length; trivial.
    rewrite find_id_filter_char by trivial. simpl.
    f_equal.
    { remember (find_id j l2) as u; symmetry in Hequ; destruct u as [psi |]; trivial.
      destruct (ident_eq i j); [ congruence | reflexivity]. }
    rewrite <- X1; clear X1; f_equal.
    destruct (find_id_in_split Hi LNR2) as [la1 [l2b [Hl2 [Hi2a Hi2b]]]]; subst l2; clear Hi. 
    rewrite ! filter_app; simpl in *. rewrite ! filter_app in X2; simpl in X2.
    rewrite ! if_true, Heqt in * by trivial. unfold Memory.EqDec_ident.
    destruct (ident_eq i j); [ congruence | simpl]; clear n0.
    destruct (ident_eq i i); [ simpl in *; clear e | congruence].
    f_equal.
    * f_equal. extensionality x. destruct x as [ii phi]; simpl.
      destruct (ident_eq ii i); subst.
      - clear X2. rewrite Heqt, if_false; [ simpl | congruence]. destruct (ident_eq i i); [ reflexivity | congruence].
      - destruct (ident_eq ii j); simpl; trivial. destruct (ident_eq i ii); [ congruence | simpl ]. rewrite andb_true_r; trivial.
    * f_equal. extensionality x. destruct x as [ii phi]; simpl.
      rewrite negb_ident_eq_symm.
      destruct (ident_eq ii i); subst.
      - rewrite Heqt, if_false; [ trivial | congruence].
      - simpl. rewrite andb_true_r; trivial.
Qed.

Lemma subsumespec_G_merge_l l1 l2 i
  (SigsCC: forall phi1 phi2, find_id i l1 = Some phi1 -> find_id i l2 = Some phi2 ->
    typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
    callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2):
 subsumespec (find_id i l1) (find_id i (G_merge l1 l2)).
Proof.
  red. remember (find_id i l1) as q1; symmetry in Heqq1. remember (find_id i l2) as q2; symmetry in Heqq2.
  destruct q1 as [phi1 |]; destruct q2 as [phi2 |]; trivial.
+ destruct (G_merge_find_id_SomeSome Heqq1 Heqq2) as [phi [BI Phi]]. apply SigsCC; trivial. apply SigsCC; trivial.
  rewrite Phi.
  eexists; split. trivial. apply funspec_sub_sub_si. apply binaryintersection_sub in BI. apply BI.
+ rewrite (G_merge_find_id_SomeNone Heqq1 Heqq2).
  eexists; split. reflexivity. apply funspec_sub_si_refl.
Qed.

Lemma subsumespec_G_merge_r l1 l2 i
  (SigsCC: forall phi1 phi2, find_id i l1 = Some phi1 -> find_id i l2 = Some phi2 ->
    typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
    callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
  (LNR: list_norepet (map fst l2)):
 subsumespec (find_id i l2) (find_id i (G_merge l1 l2)).
Proof.
  red. remember (find_id i l1) as q1; symmetry in Heqq1. remember (find_id i l2) as q2; symmetry in Heqq2.
  destruct q1 as [phi1 |]; destruct q2 as [phi2 |]; trivial.
+ destruct (G_merge_find_id_SomeSome Heqq1 Heqq2) as [phi [BI Phi]]. apply SigsCC; trivial. apply SigsCC; trivial.
  rewrite Phi. eexists; split. trivial. apply funspec_sub_sub_si. apply binaryintersection_sub in BI. apply BI.
+ rewrite (G_merge_find_id_NoneSome Heqq1 Heqq2) by trivial. eexists; split. reflexivity. apply funspec_sub_si_refl.
Qed.  

Lemma G_merge_None_l l1 l2 i: find_id i l1 = None -> list_norepet (map fst l2) -> find_id i (G_merge l1 l2) = find_id i l2.
Proof. intros.
  remember (find_id i l2). destruct o; symmetry in Heqo.
  rewrite (G_merge_find_id_NoneSome H Heqo); trivial.
  rewrite (G_merge_find_id_NoneNone H Heqo); trivial.
Qed.

Lemma G_merge_None_r l1 l2 i: find_id i l2 = None -> list_norepet (map fst l2) -> find_id i (G_merge l1 l2) = find_id i l1.
Proof. intros.
  remember (find_id i l1). destruct o; symmetry in Heqo.
  rewrite (G_merge_find_id_SomeNone Heqo H); trivial.
  rewrite (G_merge_find_id_NoneNone Heqo H); trivial.
Qed.

Definition Fundefs_match (p1 p2: QP.program Clight.function) (Imports1 Imports2:funspecs) := 
           forall i fd1 fd2,
                         PTree.get i (QP.prog_defs p1) = Some (Gfun fd1) ->
                         PTree.get i (QP.prog_defs p2) = Some (Gfun fd2) ->
                         match fd1, fd2 with
                           Internal _, Internal _ => True
                         | Internal _, External _ _ _ _ => exists phi2, find_id i Imports2 = Some phi2
                         | External _ _ _ _, Internal _ => exists phi1, find_id i Imports1 = Some phi1
                         | External _ _ _ _ , External _ _ _ _  => True
                         end.

Lemma G_merge_find_id_Some_D i l1 l2 phi: find_id i (G_merge l1 l2) = Some phi ->list_norepet (map fst l2) ->
      exists psi, find_id i l1 = Some psi \/ find_id i l2 = Some psi.
Proof.
 intros. apply G_merge_find_id_Some in H; trivial.
 destruct (find_id i l1). eexists; left; reflexivity. eexists; right; eauto.
Qed.

Lemma G_merge_aux_LNR f l1 (L1: list_norepet (map fst l1)) l2:
      list_norepet (map fst (@G_merge_aux f l1 l2)).
Proof. rewrite G_merge_aux_dom; trivial. Qed.

Lemma G_merge_LNR: forall l1 (L1: list_norepet (map fst l1)) l2 (L2: list_norepet (map fst l2)), 
      list_norepet (map fst (G_merge l1 l2)).
Proof.
  intros. unfold G_merge. rewrite map_app, list_norepet_app; split3. apply G_merge_aux_LNR; trivial.
  apply list_norepet_map_fst_filter; trivial.
  rewrite G_merge_aux_dom. do 5 intros ?; subst.
  apply in_map_iff in H0. destruct H0 as [[? ?] [? ?]]. simpl in *; subst. apply filter_In in H1; destruct H1.
  apply In_map_fst_find_id in H. destruct H. rewrite H in H1. inv H1. trivial.
Qed.

Lemma G_merge_sqsub1 l1 l2
  (H: forall i phi1 phi2, find_id i l1 = Some phi1 -> find_id i l2 = Some phi2 ->
      typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
      callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2): 
funspecs_sqsub (G_merge l1 l2) l1.
Proof.
  intros ? phi1 ?.
  remember (find_id i l2) as w; destruct w as [phi2 |]; symmetry in Heqw.
+ destruct (H _ _ _ H0 Heqw); clear H.
  destruct (G_merge_find_id_SomeSome H0 Heqw) as [phi [PHI Sub]]; trivial.
  apply binaryintersection_sub in PHI.
  exists phi; split; trivial. apply PHI.
+ exists phi1; split. apply G_merge_find_id_SomeNone; trivial. apply funspec_sub_refl.
Qed.

Lemma G_merge_sqsub2 l1 l2 (LNR: list_norepet (map fst l2))
  (H: forall i phi1 phi2, find_id i l1 = Some phi1 -> find_id i l2 = Some phi2 ->
      typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
      callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2): 
funspecs_sqsub (G_merge l1 l2) l2.
Proof.
  intros ? phi2 ?.
  remember (find_id i l1) as w; destruct w as [phi1 |]; symmetry in Heqw.
+ destruct (H _ _ _ Heqw H0); clear H.
  destruct (G_merge_find_id_SomeSome Heqw H0) as [phi [PHI Sub]]; trivial.
  apply binaryintersection_sub in PHI.
  exists phi; split; trivial. apply PHI.
+ exists phi2; split. apply G_merge_find_id_NoneSome; trivial. apply funspec_sub_refl.
Qed.

Lemma G_merge_sqsub3 l1 l2 l (LNR2: list_norepet (map fst l2))
  (H: forall i phi1 phi2, find_id i l1 = Some phi1 -> find_id i l2 = Some phi2 ->
      typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
      callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
      (H1: funspecs_sqsub l l1) (H2: funspecs_sqsub l l2):
funspecs_sqsub l (G_merge l1 l2).
Proof.
  intros ? phi ?. specialize (H1 i). specialize (H2 i). specialize (H i).
  specialize (G_merge_find_id_Some H0 LNR2); intros.
  remember (find_id i l1) as w1; symmetry in Heqw1; destruct w1 as [phi1 |].
+ destruct (H1 _ (eq_refl _)) as [psi1 [F1 Sub1]]; clear H1.
  remember (find_id i l2) as w2; symmetry in Heqw2; destruct w2 as [phi2 |].
  - destruct (H2 _ (eq_refl _)) as [psi2 [F2 Sub2]]; clear H2.
    rewrite F2 in F1. inv F1. exists psi1. split; trivial.
    destruct (H phi1 phi2); trivial; clear H.
    specialize (merge_specs_succeed H1 H2); intros BI.
    apply (BINARY_intersection_sub3 _ _ _ BI); trivial.
  - subst; simpl. exists psi1; split; trivial.
+ auto.
Qed.

Lemma SF_subsumespec {Espec cs V ge G i fd phi}
      (HSF: @SF Espec cs V ge G i fd phi) G' V'
      (H: forall j, subsumespec (find_id j G) (find_id j G'))
      (HV: forall j t, find_id j V = Some t -> find_id j V' = Some t)
      (D: forall j t, find_id j V = Some t -> find_id j G' = None)
      (LNR: list_norepet (map fst G)):
      @SF Espec cs V' ge G' i fd phi.
Proof.
destruct fd.
+ simpl. eapply InternalInfo_subsumption; [ intros j | apply H | apply LNR | apply HSF].
  specialize (H j). specialize (D j).
  remember (find_id j G) as q; symmetry in Heqq; destruct q as [psi |]. 
  - destruct H as [omega [HH Sub]].
    erewrite 2 semax_prog.make_tycontext_s_g; try
      (rewrite semax_prog.find_id_maketycontext_s; eassumption).
    simpl. 
    specialize (Sub (compcert_rmaps.RML.empty_rmap 0)).
    apply type_of_funspec_sub_si in Sub.
    simpl in Sub; rewrite Sub; reflexivity. reflexivity.
  - simpl in *. rewrite semax_prog.make_tycontext_g_G_None; trivial.
    remember (find_id j V) as p; destruct p; symmetry in Heqp; simpl; trivial.
    specialize (D t).
    rewrite semax_prog.make_tycontext_g_G_None; auto.
+ apply HSF.
Qed. 

(*It may be possible to eliminate this condition by modifying the definition
  of binary intersection such that instead of requiring parameter names
  to be identical the names are suitably renamed. Note that equality of the
  argument (and return) types already holds, by the semaxfunc properties inside c1 and c2 *)

Lemma HContexts {Espec V1
      E1 Imports1 Exports1 V2 E2 Imports2 Exports2 p1 p2 p GP1 GP2 G1 G2}
      (c1: @Component Espec V1 E1 Imports1 p1 Exports1 GP1 G1)
      (c2: @Component Espec V2 E2 Imports2 p2 Exports2 GP2  G2)
      (Linked : QPlink_progs p1 p2 = Errors.OK p)
      (FM: Fundefs_match p1 p2 Imports1 Imports2):
      forall i phi1 phi2,
             find_id i G1 = Some phi1 ->
             find_id i G2 = Some phi2 ->
             typesig_of_funspec phi1 = typesig_of_funspec phi2.
Proof. intros. specialize (FM i).
  specialize (Comp_G_in_Fundefs' c1 _ _ H) as [fd1 FD1].
  specialize (Comp_G_in_Fundefs' c2 _ _ H0) as [fd2 FD2].
  specialize (Comp_G_justified c1 _ _ _ FD1 H); intros SF1.
  specialize (Comp_G_justified c2 _ _ _ FD2 H0); intros SF2.
  rewrite FD1, FD2 in *. specialize (FM _ _ (eq_refl _) (eq_refl _)).
  unfold QPlink_progs in Linked.
  destruct (  merge_builtins (QP.prog_builtins p1)
              (QP.prog_builtins p2)) eqn:?H; try discriminate;
  unfold Errors.bind at 1 in Linked.
  destruct (merge_PTrees _ _ _) eqn:?H; try discriminate; 
  unfold Errors.bind at 1 in Linked.
  clear Linked.
  apply (merge_PTrees_e i) in H2.
  rewrite FD1,FD2 in H2.
 destruct H2 as [fd [? _]].
  destruct fd1; destruct fd2.
+ (*II*) inv FM. 
  destruct phi1 as [[? ?] ? ? ? ? ? ?].
  destruct phi2 as [[? ?] ? ? ? ? ? ?].
  destruct SF1 as [? [? [? [? [[? [? _]] _]]]]].
  destruct SF2 as [? [? [? [? [[? [? _]] _]]]]].
  simpl in *.
  subst.
  destruct (function_eq f f0) eqn:?H; inv H2.
  apply function_eq_prop in H6; subst; auto.
+
  destruct FM as [psi2 Psi2].
  apply (Comp_G_disjoint_from_Imports_find_id c2) in Psi2; unfold Comp_G in Psi2; congruence. 
+ destruct FM as [psi1 Psi1].
  apply (Comp_G_disjoint_from_Imports_find_id c1) in Psi1; unfold Comp_G in Psi1; congruence.
+ inv FM.
  destruct phi1 as [[? ?] ? ? ? ? ? ?].
  destruct phi2 as [[? ?] ? ? ? ? ? ?].
  destruct SF1 as [? [? [? _]]].
  destruct SF2 as [? [? [? _]]]. subst.
  unfold merge_globdef in H2.
  destruct (fundef_eq 
         (External e t0 t4 c3) (External e0 t2 t5 c4)) eqn:?H; inv H2.
  apply fundef_eq_prop in H3. inv H3. auto.
Qed.

Lemma find_id_elements:
  forall {A} i (m: PTree.t A), find_id i (PTree.elements m) = PTree.get i m.
Proof.
 intros.
 destruct (m ! i) eqn:?H.
 pose proof (PTree.elements_correct _ _ H).
 apply find_id_i; auto.
  apply PTree.elements_keys_norepet.
 apply find_id_None_iff.
 intro Hx. apply list_in_map_inv in Hx. destruct Hx as [[? ?] [? ?]]; subst i.
 apply PTree.elements_complete in H1.
 simpl in H. congruence.
Qed.

Lemma disjoint_varspecs_e:
  forall p1 p2 i v1 v2,
  list_disjoint (map fst (Vardefs p1)) (map fst (Vardefs p2)) ->
  (QP.prog_defs p1) ! i = Some (Gvar v1) ->
  (QP.prog_defs p2) ! i = Some (Gvar v2) ->
  False.
Proof.
intros.
apply PTree.elements_correct in H0.
apply PTree.elements_correct in H1.
unfold Vardefs in H.
forget (PTree.elements (QP.prog_defs p1)) as e1.
forget (PTree.elements (QP.prog_defs p2)) as e2.
apply (H i i); auto.
clear - H0. induction e1; simpl in *; auto. destruct H0; subst; simpl; auto.
destruct (isGvar a).  right; auto.  auto. 
clear - H1. induction e2; simpl in *; auto. destruct H1; subst; simpl; auto.
destruct (isGvar a).  right; auto.  auto. 
Qed.

Definition is_var_in {F} i p :=
     match PTree.get i (@QP.prog_defs F p) with
     | None => True
     | Some (Gvar _) => True
     | Some (Gfun _) => False
     end.

Definition PTree_disjoint {A} (a: PTree.t A) {B} (b: PTree.t B) : bool :=
  PTree.fold (fun c i _ => c && isNone (PTree.get i b))%bool a true.

Lemma QPvarspecs_norepet:
  forall p, list_norepet (map fst (QPvarspecs p)).
Proof.
clear.
intros.
unfold QPvarspecs.
unfold QPprog_vars.
pose proof (PTree.elements_keys_norepet (QP.prog_defs p)).
induction (PTree.elements (QP.prog_defs p)).
constructor.
inv H.
destruct a.
destruct g; simpl; auto.
constructor; auto.
contradict H2.
clear - H2.
simpl.
induction l; simpl; auto.
destruct a,g; simpl in H2; auto.
destruct H2; auto.
Qed.

Lemma find_id_QPvarspecs: forall p i t, find_id i (QPvarspecs p) = Some t <->
   (exists g, (QP.prog_defs p) ! i = Some (Gvar g) /\ gvar_info g = t).
Proof.
intros.
unfold QPvarspecs, QPprog_vars.
transitivity (exists g, find_id i (PTree.elements (QP.prog_defs p)) = Some (Gvar g) /\ gvar_info g = t).
pose proof (PTree.elements_keys_norepet (QP.prog_defs p)).
induction (PTree.elements (QP.prog_defs p)).
simpl. split; intro H0. inv H0. destruct H0 as [? [? ?]]. inv H0.
inv H.
destruct a,g.
rewrite IHl; auto.
split; intros [g [? ?]]. exists g; split; auto. simpl; auto. rewrite if_false; auto. contradict H2. subst p0.
simpl. eapply find_id_In_map_fst; eauto.
exists g; split; auto.
simpl in H. if_tac in H; auto. inv H.
simpl.
if_tac. subst p0.
split;  intro. inv H. eauto. destruct H as [g [? ?]]. inv H. auto.
simpl in H2. apply IHl; auto.
split; intros [g [? ?]]; exists g; split; auto.
rewrite <- find_id_elements; auto.
rewrite find_id_elements; auto.
Qed.

Lemma subsumespec_i: forall x y : option funspec, 
  match x with
  | Some hspec =>
       exists gspec, y = Some gspec /\ TT |-- funspec_sub_si gspec hspec
 | None => True
end ->
  subsumespec x y.
Proof.
intros.
red.
change seplog.funspec_sub_si with funspec_sub_si.
change (predicates_hered.derives predicates_hered.TT ?A)
  with (TT |-- A).
auto.
Qed.

Definition varspecsJoin (V1 V2 V: varspecs) :=
forall i, match find_id i V1, find_id i V2, find_id i V with
  | Some gv1, Some gv2, Some gv => gv1 = gv /\ gv2 = gv
  | None, gv2, gv => gv2 = gv
  | gv1, None, gv => gv1 = gv
  | _, _, _ => False
 end.

Section ComponentJoin.
Variable Espec: OracleKind.
Variable V1 V2: varspecs.
Variable E1 Imports1 Exports1 G1 E2 Imports2 Exports2 G2: funspecs.
Variable p1 p2: QP.program Clight.function.
Variable GP1 GP2: globals -> mpred.
Variable c1: @Component Espec V1 E1 Imports1 p1 Exports1 GP1 G1.
Variable c2: @Component Espec V2 E2 Imports2 p2 Exports2 GP2 G2.

Variable V: varspecs.
Variable p: QP.program Clight.function.
Variable Linked : QPlink_progs p1 p2 = Errors.OK p.
Variable LNR_V: list_norepet (map fst V).

Variable HV: varspecsJoin V1 V2 V.

Local Lemma HV1 : forall i phi, find_id i V1 = Some phi -> find_id i V = Some phi.
Proof.
intros.
specialize (HV i).
rewrite H in HV.
destruct (find_id i V2); auto.
destruct (find_id i V); auto.
destruct HV; subst; auto.
contradiction.
Qed.

Local Lemma HV2 : forall i phi, find_id i V2 = Some phi -> find_id i V = Some phi.
intros.
specialize (HV i).
rewrite H in HV.
destruct (find_id i V1); auto.
destruct (find_id i V); auto.
destruct HV; subst; auto.
contradiction.
Qed.

Variable Disj_V1p2: list_disjoint (map fst V1) (map fst E2 ++ map fst Imports2 ++ IntIDs p2).
Variable Disj_V2p1: list_disjoint (map fst V2) (map fst E1 ++ map fst Imports1 ++ IntIDs p1).

Lemma ha_env_cs_of_compspecs_of_QPcomposite_env:
 forall ce H, @ha_env_cs (compspecs_of_QPcomposite_env ce H) = PTree.map1 QP.co_ha ce.
Proof.
clear.
intros.
destruct H as [H1 [? [? [? [? [? ?]]]]]]; simpl; auto.
Qed.

Lemma la_env_cs_of_compspecs_of_QPcomposite_env:
 forall ce H, @la_env_cs (compspecs_of_QPcomposite_env ce H) = PTree.map1 QP.co_la ce.
Proof.
clear.
intros.
destruct H as [H1 [? [? [? [? [? ?]]]]]]; simpl; auto.
Qed.

Lemma samedom_composite_env_of_QPcomposite_env:
 forall ce H, PTree_samedom (composite_env_of_QPcomposite_env ce H) ce.
Proof.
induction ce; simpl; intros; auto.
destruct H as [? [? ?]].
simpl; auto.
destruct o; split3; auto.
Qed.

Lemma PTree_samedom_trans {A B C}:
 forall  (m1: PTree.t A) (m2: PTree.t B) (m3: PTree.t C),
  PTree_samedom m1 m2 -> PTree_samedom m2 m3 -> PTree_samedom m1 m3.
Proof.
induction m1; destruct m2, m3; intros; try contradiction; auto.
destruct H as [? [? ?]]; destruct H0 as [? [? ?]].
constructor.
destruct o,o0,o1; try contradiction; auto.
destruct o,o0,o1; try contradiction; auto.
split.
eapply IHm1_1; eauto.
eapply IHm1_2; eauto.
split.
eapply IHm1_1; eauto.
eapply IHm1_2; eauto.
Qed.

Lemma PTree_samedom_sym {A B}:
 forall  (m1: PTree.t A) (m2: PTree.t B),
  PTree_samedom m1 m2 -> PTree_samedom m2 m1.
Proof.
induction m1; destruct m2; intros; try contradiction; auto.
destruct H as [? [? ?]]; split3; auto.
destruct o,o0; try contradiction; auto.
Qed.

Lemma PTree_samedom_map1: forall {A B} (f: A -> B),
 forall m,  PTree_samedom (PTree.map1 f m) m.
Proof.
induction m; simpl; intros; auto.
split3; auto.
destruct o; simpl; auto.
Qed.

Variable FundefsMatch: Fundefs_match p1 p2 Imports1 Imports2.

Definition HC := HContexts c1 c2 Linked FundefsMatch.

(********************Assumptions involving E1 and E2  ********)

Variable Externs1_Hyp: list_disjoint (map fst E1) (IntIDs p2).
Variable Externs2_Hyp: list_disjoint (map fst E2) (IntIDs p1).

(************************************************************)

(*one could try to weaken this hypothesis by weakening the second condition to In i (IntIDs p1),
  so that it is possible to delay resolving the spec for an extern in case several modules prove (mergaable but different) specs for it. The present cluase forces one to use match with the first spec one finds*)
Variable SC1: forall i phiI, 
              find_id i Imports2 = Some phiI ->
              In i (map fst E1 ++ IntIDs p1) ->
              exists phiE, find_id i Exports1 = Some phiE /\ funspec_sub phiE phiI.

(*same comment here*)
Variable SC2: forall i phiI,
              find_id i Imports1 = Some phiI ->
              In i (map fst E2 ++ IntIDs p2) ->
              exists phiE, find_id i Exports2 = Some phiE /\ funspec_sub phiE phiI.

Variable HImports: forall i phi1 phi2, find_id i Imports1 = Some phi1 -> find_id i Imports2 = Some phi2 -> phi1=phi2.

Definition JoinedImports := 
          filter (fun x => negb (in_dec ident_eq (fst x) (map fst E2 ++ IntIDs p2))) Imports1 ++
          filter (fun x => negb (in_dec ident_eq (fst x) (map fst E1 ++ IntIDs p1 ++ map fst Imports1))) Imports2.

Local Definition Exports := G_merge Exports1 Exports2.

Lemma LNR_Imports: list_norepet (map fst JoinedImports).
Proof. unfold JoinedImports. subst. clear - c1 c2. rewrite map_app, list_norepet_app; split3.
    - specialize (Comp_Imports_LNR c1). clear. apply list_norepet_map_fst_filter.
    - specialize (Comp_Imports_LNR c2). clear. apply list_norepet_map_fst_filter.
    - clear. intros x1 x2 X1 X2.
      apply list_in_map_inv in X1; destruct X1 as [[i phi1] [Hi X1]]; simpl in Hi; subst i.
      apply list_in_map_inv in X2. destruct X2 as [[i phi2] [Hi X2]]; simpl in Hi; subst i.
      apply filter_In in X1; destruct X1 as [X1 Y1]. 
      apply filter_In in X2; destruct X2 as [X2 Y2].
      simpl in *. intros ?; subst.
      destruct (in_dec ident_eq x2 (map fst E2 ++IntIDs p2)); [ inv Y1 | clear Y1].
      destruct (in_dec ident_eq x2 (map fst E1 ++ IntIDs p1 ++ map fst Imports1)); [inv Y2 | clear Y2]. 
      elim n0. apply in_or_app. right. apply in_or_app. right. eapply in_map_fst. apply X1.
Qed.

Lemma LNR_Exports: list_norepet (map fst Exports).
Proof. unfold Exports. subst. clear - c1 c2. rewrite G_merge_dom, map_app, list_norepet_app; split3.
    - apply c1.
    - eapply sublist_norepet. apply sublist_map_fst. apply sublist_filter. apply c2.
    - clear -c1. intros x1 x2 X1 X2 N; subst.
      apply list_in_map_inv in X1; destruct X1 as [[i phi1] [Hi X1]]; simpl in Hi; subst i.
      apply list_in_map_inv in X2; destruct X2 as [[i phi2] [Hi X2]]; simpl in Hi; subst i.
      apply filter_In in X2; destruct X2 as [X2 Y2].
      apply find_id_i in X1. rewrite X1 in Y2. congruence. apply c1.
Qed.

Definition is_funct_in {F} i p :=
     match PTree.get i (@QP.prog_defs F p) with
     | None => False
     | Some (Gvar _) => False
     | Some (Gfun _) => True
     end.

Lemma Imports_in_Fundefs: forall x, In x (map fst JoinedImports) ->
     is_funct_in x p1 \/ is_funct_in x p2.
Proof. unfold JoinedImports. clear - c1 c2; intros. 
          specialize (Comp_Imports_in_Fundefs c1) ; intros CIF1.
          specialize (Comp_Imports_in_Fundefs c2) ; intros CIF2.
          rewrite map_app in H.
          apply in_app_or in H; destruct H.
          * apply list_in_map_inv in H; destruct H as [[i phi] [Phi PHI]]; simpl in Phi; subst x.
            apply filter_In in PHI; simpl in PHI; destruct PHI. apply find_id_i in H; [ | apply (Comp_Imports_LNR c1)].
            destruct (CIF1 _ _ H) as [f Hf].
            left. hnf. rewrite Hf; auto.
          * apply list_in_map_inv in H; destruct H as [[i phi] [Phi PHI]]; simpl in Phi; subst x.
            apply filter_In in PHI; simpl in PHI; destruct PHI. apply find_id_i in H; [ | apply (Comp_Imports_LNR c2)].
            destruct (CIF2 _ _ H) as [f Hf].
            right; hnf. rewrite Hf; auto.
Qed.

Lemma Calling_conventions_match {i psi1 psi2}
      (Hpsi1: find_id i (Comp_G c1) = Some psi1)
      (Hpsi2 : find_id i (Comp_G c2) = Some psi2):
callingconvention_of_funspec psi1 = callingconvention_of_funspec psi2.
Proof. 
  clear - Linked Hpsi1 Hpsi2.
  unfold QPlink_progs in Linked.
  destruct (  merge_builtins (QP.prog_builtins p1)
              (QP.prog_builtins p2)) eqn:?H; try discriminate;
  unfold Errors.bind at 1 in Linked.
  destruct (merge_PTrees _ _ _) eqn:?H; try discriminate; 
  unfold Errors.bind at 1 in Linked.
  clear - H0 Hpsi1 Hpsi2.
  apply (merge_PTrees_e i) in H0.
  destruct (Comp_G_elim c1 i); [apply find_id_In_map_fst in Hpsi1; trivial | | ];
  (destruct (Comp_G_elim c2 i); [apply find_id_In_map_fst in Hpsi2; trivial | | ]).
-
   destruct H as [? [? [? [? [? ?]]]]].
   destruct H1 as [? [? [? [? [? ?]]]]].
   rewrite H2 in *; rewrite H3 in *.
   pose proof (Comp_G_justified c1 _ _ _ H2 Hpsi1).
   apply ExternalInfo_cc in H4; rewrite <- H4.
   pose proof (Comp_G_justified c2 _ _ _ H3 Hpsi2).
   apply ExternalInfo_cc in H5; rewrite <- H5.
   destruct H0 as [g [? _]].
   simpl in H0.
   destruct (eqb_external_function x x3 &&
        eqb_typelist x0 x4 && eqb_type x1 x5)%bool; [ | discriminate].
   destruct (eqb_calling_convention x2 x6)%bool eqn:?H; [ | discriminate].
   apply eqb_calling_convention_prop; auto.
-
   destruct H as [? [? [? [? [? ?]]]]].
   destruct H1 as [? [? [? ?]]].
   rewrite H2 in *; rewrite H4 in *.
   pose proof (Comp_G_justified c1 _ _ _ H2 Hpsi1).
   apply ExternalInfo_cc in H5; rewrite <- H5.
   pose proof (Comp_G_justified c2 _ _ _ H4 Hpsi2).
   apply InternalInfo_cc in H6; rewrite <- H6.
   destruct H0 as [g [? _]].
   unfold merge_globdef in H0.
   destruct (eqb_signature
         (signature_of_fundef (External x x0 x1 x2))
         (signature_of_fundef (Internal x3))) eqn:?H; [ | discriminate].
   apply eqb_signature_prop in H7.
   simpl in H7.
   inv H7. auto.
-
   destruct H1 as [? [? [? [? [? ?]]]]].
   destruct H as [? [? [? ?]]].
   rewrite H2 in *; rewrite H4 in *.
   pose proof (Comp_G_justified c1 _ _ _ H4 Hpsi1).
   apply InternalInfo_cc in H5; rewrite <- H5.
   pose proof (Comp_G_justified c2 _ _ _ H2 Hpsi2).
   apply ExternalInfo_cc in H6; rewrite <- H6.
   destruct H0 as [g [? _]].
   unfold merge_globdef in H0.
   destruct (eqb_signature
         (signature_of_fundef (Internal x3))
         (signature_of_fundef (External x x0 x1 x2))) eqn:?H; [ | discriminate].
   apply eqb_signature_prop in H7.
   simpl in H7.
   inv H7. auto.
-
   destruct H as [? [? [? ?]]].
   destruct H1 as [? [? [? ?]]].
   rewrite H3 in *; rewrite H5 in *.
   pose proof (Comp_G_justified c1 _ _ _ H3 Hpsi1).
   apply InternalInfo_cc in H6; rewrite <- H6.
   pose proof (Comp_G_justified c2 _ _ _ H5 Hpsi2).
   apply InternalInfo_cc in H7; rewrite <- H7.
   destruct H0 as [g [? _]].
   unfold merge_globdef in H0.
   destruct (function_eq x x0) eqn:Hx; inv H0.
  apply function_eq_prop in Hx; subst; auto.
Qed.

Lemma InitGPred_nilD gv: InitGPred nil gv = emp.
Proof. clear. reflexivity. Qed.

Lemma InitGPred_consD X a gv:
      InitGPred (a :: X) gv = (globs2pred gv a * InitGPred X gv)%logic.
Proof. clear. reflexivity. Qed.

Lemma InitGPred_middleD Y a gv: forall X,
      InitGPred (Y ++ a :: X) gv = (globs2pred gv a * InitGPred Y gv * InitGPred X gv)%logic.
Proof. clear.
  induction Y; simpl; intros.
+ rewrite InitGPred_consD, InitGPred_nilD, sepcon_emp; reflexivity.
+ rewrite InitGPred_consD, IHY, InitGPred_consD. apply pred_ext; cancel.
Qed.

Lemma InitGPred_app gv: forall X Y, 
      InitGPred (X ++ Y) gv = (InitGPred X gv * InitGPred Y gv)%logic.
Proof. clear.
  induction X; simpl; intros. rewrite InitGPred_nilD, emp_sepcon; trivial.
  rewrite ! InitGPred_consD, IHX, sepcon_assoc; trivial.
Qed.

Lemma globs2predD_true a gv: true = isGvar a ->
      globs2pred gv a = EX i v, !! (a=(i,Gvar v) /\ headptr (gv i)) && globvar2pred gv (i, v).
Proof. clear. unfold globs2pred. destruct a. unfold isGvar; simpl. destruct g; intros. discriminate.
 apply pred_ext. Intros. Exists i v. entailer!.
 Intros ii vv. inv H0. entailer!.
Qed.

Lemma globs2predD_false a gv: false = isGvar a ->
      globs2pred gv a = emp.
Proof. clear. unfold globs2pred. destruct a. unfold isGvar; simpl. destruct g; trivial. discriminate.
Qed.

Lemma list_disjoint_app_inv {A} (l1 l2 l: list A): 
      list_disjoint (l1++l2) l -> list_disjoint l1 l /\ list_disjoint l2 l.
Proof. clear; intros.
  split; intros x y X Y.
  apply (H x y); [ apply in_or_app; left |] ; trivial.
  apply (H x y); [ apply in_or_app; right |] ; trivial.
Qed.

Lemma list_disjoint_consD {A} (a:A) l1 l: 
      list_disjoint (a::l1) l -> (~ In a l) /\ list_disjoint l1 l.
Proof. clear; intros; split.
  intros N. elim (H a a); [ left | | ]; trivial.
  intros x y X Y. apply (H x y); [ right |] ; trivial.
Qed.

Lemma list_disjoint_middleD {A} (a:A) l1 l2 l: 
      list_disjoint (l1++a::l2) l -> (~ In a l) /\ list_disjoint (l1++l2) l.
Proof. clear; intros. apply list_disjoint_app_inv in H; destruct H.
  apply list_disjoint_consD in H0; destruct H0. split; trivial.
  apply list_disjoint_app_L; trivial.
Qed.

Lemma list_norepet_middleD {A} (a:A) l1 l2: 
      list_norepet (l1++a::l2) -> (~ In a (l1++l2)) /\ list_norepet (l1++l2).
Proof. clear; intros. apply list_norepet_app in H; destruct H as [? [? ?]].
inv H0. split. intros N. apply in_app_or in N. destruct N; try contradiction.
apply (H1 a a); [ | left | ]; trivial.
apply list_disjoint_cons_right in H1.
apply list_norepet_app; split3; trivial.
Qed.

Lemma list_norepet_app_inv {A}: forall l1 m1 l2 m2 (a:A),
      m1 ++ a :: m2 = l1 ++ a :: l2 -> ~ In a (l1 ++ l2) ->
      list_norepet (l1 ++ l2) -> m1 ++ m2 = l1 ++ l2.
Proof. clear. induction l1.
+ destruct m1; simpl in *; intros; inv H; trivial.
  elim H0. apply in_or_app. right; left; trivial.
+ destruct m1; simpl in *; intros; inv H.
  - elim H0; left; trivial.
  - inv H1. rewrite (IHl1 _ _ _ _ H4); trivial. intros N. apply H0. right; trivial.
Qed.

Lemma map_app_inv {A B C}: forall (l1 l2: list (A*B)) (m: list (A*C)),
      map fst (l1 ++ l2) = map fst m ->
      exists m1 m2, map fst l1 = map fst m1 /\ map fst l2 = map fst m2 /\ m=m1++m2.
Proof. clear.
  induction l1; simpl; intros.
+ exists nil, m; simpl; split3; trivial.
+ destruct m; inv H. destruct (IHl1 _ _ H2) as [u1 [u2 [U1 [U2 U]]]]; clear IHl1; subst.
  exists (p::u1), u2. simpl. rewrite H1, U1, U2; split3; trivial. 
Qed.

Lemma filter_involutive {A f} (l: list A): filter f (filter f l) = filter f l.
Proof. clear. rewrite filter_filter. induction l; simpl. trivial .
destruct (f a); simpl; rewrite IHl; trivial.
Qed.

Lemma filter_redundant {A f l}: (forall (a:A), In a l -> f a = true) -> filter f l = l.
Proof. clear.
induction l; simpl; intros. trivial.
rewrite H. 2: left; trivial. rewrite IHl; trivial. intros. apply H. right; trivial.
Qed.

Definition Functions_preserved (p1 p2 p: QP.program Clight.function) i:=
         match PTree.get i (QP.prog_defs p1), PTree.get i (QP.prog_defs p2) with
         | Some (Gfun (Internal f1)), Some (Gfun (Internal f2)) => 
                       PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f1)) /\
                       PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f2))
         | Some (Gfun _), Some (Gvar _) => False
         | Some (Gvar _), Some (Gfun _) => False
         | Some (Gvar v1), Some (Gvar v2) => 
            (v1.(gvar_info) = v2.(gvar_info) /\ 
             v1.(gvar_readonly) = v2.(gvar_readonly) /\ 
             v1.(gvar_volatile) = v2.(gvar_volatile)) /\ 
           (v1.(gvar_init) = nil /\ PTree.get i (QP.prog_defs p) = Some (Gvar v2) \/
            v2.(gvar_init) = nil /\ PTree.get i (QP.prog_defs p) = Some (Gvar v1))
         |  Some (Gfun (Internal f1)), _ => 
                       PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f1))
         | _, Some (Gfun (Internal f2)) => 
                       PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f2))
         | Some (Gfun (External ef1 tys1 rt1 cc1)), Some (Gfun (External ef2 tys2 rt2 cc2)) =>
               PTree.get i (QP.prog_defs p) = Some (Gfun (External ef1 tys1 rt1 cc1)) /\
               PTree.get i (QP.prog_defs p) = Some (Gfun (External ef2 tys2 rt2 cc2))
         | Some (Gfun (External ef1 tys1 rt1 cc1)), _ =>
               PTree.get i (QP.prog_defs p) = Some (Gfun (External ef1 tys1 rt1 cc1))
         | _, Some (Gfun (External ef2 tys2 rt2 cc2)) =>
               PTree.get i (QP.prog_defs p) = Some (Gfun (External ef2 tys2 rt2 cc2))
         | Some (Gvar v), None => PTree.get i (QP.prog_defs p) = Some (Gvar v)
         | None, Some (Gvar v) => PTree.get i (QP.prog_defs p) = Some (Gvar v)
         | None, None => PTree.get i (QP.prog_defs p) = None
         end.

Lemma Linked_Functions_preserved: forall p1 p2 p (Linked: QPlink_progs p1 p2 = Errors.OK p),
  forall i, Functions_preserved p1 p2 p i.
Proof.
clear.
intros.
  unfold QPlink_progs in Linked.
  destruct (  merge_builtins (QP.prog_builtins p1)
              (QP.prog_builtins p2)) eqn:?H; try discriminate;
  unfold Errors.bind at 1 in Linked.
  destruct (merge_PTrees _ _ _) eqn:?H; try discriminate; 
  unfold Errors.bind at 1 in Linked.
  destruct (merge_consistent_PTrees QPcomposite_eq
              (QP.prog_comp_env p1)
              (QP.prog_comp_env p2)); try discriminate.
  unfold Errors.bind at 1 in Linked.
  destruct (eqb_ident (QP.prog_main p1)
               (QP.prog_main p2)); inv Linked.
  apply (merge_PTrees_e i) in H0.
 hnf; intros. simpl QP.prog_defs.
  destruct ((QP.prog_defs p1) ! i) eqn:J1, ((QP.prog_defs p2) ! i) eqn:J2.
-
  destruct H0 as [h [H8 H0]]; rewrite ?H0.
  destruct g0,g; unfold merge_globdef in H8.
  destruct f,f0; inv H8;
  match type of H2 with  (if ?A then _ else _) = _ => destruct A eqn:?H; inv H2 end; auto.
  apply function_eq_prop in H1; subst f0; auto.
  split; auto.
  rewrite !andb_true_iff in H1. destruct H1 as [[[? ?] ?] ?].
  apply eqb_typelist_prop in H2.
  apply eqb_type_spec in H3.
  apply eqb_calling_convention_prop in H4. subst; auto.
  f_equal. f_equal. f_equal.
  apply eqb_external_function_prop; auto.
  destruct v; inv H8.
  destruct f; inv H8.
  destruct v, v0. unfold merge_globvar in H8.
  match type of H8 with context [if ?A then _ else _] => destruct A eqn:?H; inv H8 end; auto.
  destruct (eqb_type gvar_info gvar_info0) eqn:?H; [ | discriminate].
  apply eqb_type_true in H2. subst.
  destruct (bool_eq gvar_readonly gvar_readonly0) eqn:?H; [ | discriminate].
  apply bool_eq_ok in H2; subst.
  inv H1. (* USE THIS PART IF overlap_Gvar=true: 
  apply bool_eq_ok in H1; subst.
  simpl.
  split; auto.
  destruct (linking.isnil gvar_init) eqn:?H; inv H3; auto.
  destruct gvar_init; inv H1.
  right; split; auto.
  destruct (linking.isnil gvar_init0) eqn:?H; inv H4; auto.
  destruct gvar_init0; inv H2.
  left; split; auto.
*)
-
  destruct g; auto. destruct f; auto.
-
  destruct g; auto. destruct f; auto.
- rewrite H0; auto.
Qed.

Lemma merge_globdef_noGvar:
 forall g1 g2 g, merge_globdef g1 g2 = Errors.OK (Gvar g) -> False.
Proof.
clear.
intros.
destruct g1,g2; simpl in H.
destruct f,f0; simpl in H;
try match type of H with (if ?A then _ else _) = _ => destruct A end;
 inv H.
destruct f; inv H.
destruct v; inv H.
destruct v,v0; inv H.
Qed.

Lemma InitGPred_join {gv}:
  forall  (p1 p2 p : QP.program function)
  (H : globals_ok gv)
  (Linked : QPlink_progs p1 p2 = Errors.OK p),
  InitGPred (Vardefs p) gv |-- InitGPred (Vardefs p1) gv * InitGPred (Vardefs p2) gv.
Proof.
clear.
intros.
unfold Vardefs.
unfold QPlink_progs in Linked.
destruct (merge_builtins (QP.prog_builtins p1)
              (QP.prog_builtins p2)); try discriminate.
destruct (merge_PTrees merge_globdef 
                 (QP.prog_defs p1) (QP.prog_defs p2)) eqn:?H; try discriminate.
simpl in Linked.
destruct (merge_consistent_PTrees QPcomposite_eq
              (QP.prog_comp_env p1) (QP.prog_comp_env p2)); try discriminate.
simpl in Linked.
destruct (eqb_ident (QP.prog_main p1) (QP.prog_main p2)); try discriminate.
inv Linked. simpl.
rename t into m.
forget (QP.prog_defs p1) as m1.
forget (QP.prog_defs p2) as m2.
clear - H0.
assert (forall i,
match find_id i (PTree.elements m1) with
    | Some x1 =>
        match find_id i (PTree.elements m2) with
        | Some x2 =>
            exists x,
              merge_globdef x1 x2 = Errors.OK x /\ find_id i (PTree.elements m) = Some x
        | None => find_id i (PTree.elements m) = Some x1
        end
    | None =>
        match find_id i (PTree.elements m2) with
        | Some x2 => find_id i (PTree.elements m)= Some x2
        | None => find_id i (PTree.elements m) = None
        end
    end)
  by (intro i; rewrite !find_id_elements; apply merge_PTrees_e; auto).
clear - H.
pose proof (PTree.elements_keys_norepet m).
pose proof (PTree.elements_keys_norepet m1).
pose proof (PTree.elements_keys_norepet m2).
forget (PTree.elements m1) as al1.
forget (PTree.elements m2) as al2.
forget (PTree.elements m) as al.
clear m m1 m2.
unfold InitGPred. {
assert (forall i,
 match  find_id i (filter isGvar al)  with
 | None => find_id i (filter isGvar al1) = None /\ find_id i (filter isGvar al2) = None
 | Some g => find_id i (filter isGvar al1) = Some g /\ find_id i (filter isGvar al2) = None
                \/ find_id i (filter isGvar al2) = Some g /\ find_id i (filter isGvar al1) = None
  end). {
 intro i; specialize (H i).
 rewrite !find_id_filter_char by auto.
 destruct (find_id i al1) as [g1|] eqn:?H;
 destruct (find_id i al2) as [g2|] eqn:?H;
 first [rewrite H | (destruct H as [g [H H5]]; rewrite H5)]; auto.
 destruct g1 as [g1|g1], g2 as [g2|g2]; simpl; auto.
 destruct g; try (contradiction (merge_globdef_noGvar _ _ _ H)); simpl; auto.
 destruct g; try (contradiction (merge_globdef_noGvar _ _ _ H)); simpl; auto.
 destruct g2, g1; inv H.
 destruct g; try (contradiction (merge_globdef_noGvar _ _ _ H)); simpl; auto.
 destruct g1,g2; inv H.
 destruct g1,g2; inv H.
 destruct g1; simpl; auto.
 destruct g2; simpl; auto.
}
 clear H. rename H3 into H.
apply (@list_norepet_map_fst_filter _ isGvar) in H0.
apply (@list_norepet_map_fst_filter _ isGvar) in H1.
apply (@list_norepet_map_fst_filter _ isGvar) in H2.
assert (F0: forall i g, In (i,g) (filter isGvar al) -> isGvar (i,g) = true)
  by (intros ? ? Hx; apply (proj2 (proj1 (filter_In _ _ _) Hx))).
assert (F1: forall i g, In (i,g) (filter isGvar al1) -> isGvar (i,g) = true)
  by (intros ? ? Hx; apply (proj2 (proj1 (filter_In _ _ _) Hx))).
assert (F2: forall i g, In (i,g) (filter isGvar al2) -> isGvar (i,g) = true)
  by (intros ? ? Hx; apply (proj2 (proj1 (filter_In _ _ _) Hx))).
 forget (filter isGvar al) as bl.
 forget (filter isGvar al1) as bl1.
 forget (filter isGvar al2) as bl2.
 clear al1 al2 al. rename bl into al. rename bl1 into al1. rename bl2 into al2.
revert al1 al2 H H1 H2 F1 F2 ; induction al as [|[i [g|g]]]; simpl; intros.
-
assert (al1=nil).
 destruct al1 as [|[i g]]; auto. destruct (H i) as [Hx _]; simpl in Hx; rewrite if_true in Hx by auto; inv Hx.
assert (al2=nil).
 destruct al2 as [|[i g]]; auto. destruct (H i) as [_ Hx]; simpl in Hx; rewrite if_true in Hx by auto; inv Hx.
subst. simpl. rewrite sepcon_emp; auto.
-
rewrite emp_sepcon.
inv H0.
simpl fst in *.
apply IHal; clear IHal; auto.
intros.
specialize (H i); rewrite if_true in H by auto.
destruct H as [[??]|[??]]; apply find_id_e in H.
apply F1 in H; inv H.
apply F2 in H; inv H.
intro j.
specialize (H j).
if_tac in H.
subst j.
destruct H as [[??]|[??]]; apply find_id_e in H.
apply F1 in H. inv H.
apply F2 in H; inv H.
auto.
-
simpl fst in *. inv H0.
specialize (IHal H6).
spec IHal. intros; apply F0; right; auto.
pose (noti i (jx: ident * globdef (fundef function) type) := 
             negb (Pos.eqb i (fst jx))).
pose proof (H i). rewrite if_true in H0 by auto.

assert (forall g bl i,
          list_norepet (map fst bl) ->
          (forall j g0, In (j, g0) bl -> isGvar (j, g0) = true) ->
          find_id i bl = Some g ->
             fold_right sepcon emp (map (globs2pred gv) bl) =
             sepcon (globs2pred gv (i,g)) (fold_right sepcon emp (map (globs2pred gv) (filter (noti i) bl)))). {
   clear.
   intros. 
   assert (H8: isGvar (i,g) = true). apply H0. apply find_id_e; auto.
   destruct g; inv H8.
   revert bl i H H0 H1.
   induction bl as [|[??]]; intros until 1; intros H9  H0.
   inv H0.
   simpl in H. inv H.
   unfold map. fold (map (globs2pred gv)).
   unfold fold_right; fold (fold_right sepcon emp).
   unfold filter; fold (filter (noti i0)).
   simpl in H0.
   if_tac in H0. subst i0. inv H0.
   unfold noti at 1. simpl fst. rewrite Pos.eqb_refl. unfold negb. f_equal.
  clear - H3.
  induction bl as [|[j ?]]; simpl; auto.
  unfold noti at 1.  simpl fst. rewrite (proj2 (Pos.eqb_neq i j)).
  simpl. f_equal; auto. apply IHbl. contradict H3; simpl; auto.
  contradict H3; subst; left; auto.
  unfold noti at 1; simpl fst. rewrite (proj2 (Pos.eqb_neq i0 i)); auto.
  unfold negb.
  unfold map; fold (map (globs2pred gv)).
   unfold fold_right; fold (fold_right sepcon emp).
  rewrite <- !sepcon_assoc.
  rewrite (sepcon_comm (globs2pred gv (i0,Gvar v))).
 rewrite !sepcon_assoc.
  f_equal.
  apply IHbl; auto.
  intros. apply H9. right; auto.
}
 assert (H12: forall i (bl: list (ident * globdef (fundef function) type)), find_id i (filter (noti i) bl) = None). {
  induction bl as [|[??]]; simpl; auto.
  unfold noti at 1. simpl fst.
  destruct (Pos.eqb_spec i0 i1). subst; simpl; auto.
  simpl. rewrite if_false by auto. auto.
}
assert (H13: forall j i, j<>i -> 
             forall (bl: list (ident * globdef (fundef function) type)),
                find_id j (filter (noti i) bl) = find_id j bl). {
 clear; induction bl as [|[??]]; simpl; auto.
 unfold noti at 1. simpl fst.
  destruct (Pos.eqb_spec i i0). subst; simpl; auto.
 rewrite if_false by auto. auto.
 simpl. if_tac; auto.
}
destruct H0 as [[??]|[??]].
+
 rewrite (H3 _ _ _ H1 F1 H0); clear H3.
 rewrite sepcon_assoc.
 apply sepcon_derives. apply derives_refl.
 apply IHal; clear IHal; auto.
 intro j.
 specialize (H j).
 if_tac in H.
 subst j.
 rewrite H4.
 apply find_id_None_iff in H5.
 rewrite H5. split; auto.
 destruct (find_id j al) eqn:?H.
rewrite H13 by auto.
auto.
rewrite H13 by auto.
auto.
apply list_norepet_map_fst_filter; auto.
intros.
apply F1; auto.
apply filter_In in H3. destruct H3; auto.
+
 rewrite (H3 _ _ _ H2 F2 H0); clear H3.
 rewrite (sepcon_comm (fold_right _ _ _)).
 rewrite sepcon_assoc.
 apply sepcon_derives. apply derives_refl.
 rewrite sepcon_comm.
 apply IHal; clear IHal; auto.
 intro j.
 specialize (H j).
 if_tac in H.
 subst j.
 rewrite H4.
 apply find_id_None_iff in H5.
 rewrite H5; auto.
 rewrite H13 by auto.
 auto.
 apply list_norepet_map_fst_filter; auto.
 intros.
 apply F2; auto.
 apply filter_In in H3. destruct H3; auto.
}
Qed.

Lemma compspecs_eq: forall cs1 cs2: compspecs,
  @cenv_cs cs1 = @cenv_cs cs2 ->
  @ha_env_cs cs1 = @ha_env_cs cs2 ->
  @la_env_cs cs1 = @la_env_cs cs2 ->
  cs1 = cs2.
Proof.
clear.
destruct cs1,cs2;simpl; intros; subst; f_equal; auto; apply proof_irr.
Qed.

Let E := G_merge E1 E2.
Let G := G_merge (Comp_G c1) (Comp_G c2).

Lemma In_map_fst_filter3:
  forall {A} (i: ident) (f: ident*A -> bool) (l: list (ident*A)),
   In i (map fst (filter f l)) -> In i (map fst l).
Proof.
clear.
induction l; simpl; intros; auto.
destruct (f a); auto.
destruct H; auto.
Qed.

Local Lemma LNR_VGI: list_norepet (map fst V ++ map fst (G ++ JoinedImports)).
Proof.
 rewrite list_norepet_app; split3; auto;
  [ rewrite map_app, list_norepet_app; split3; auto | ].
  - apply G_merge_LNR; [ apply (Comp_G_LNR c1) | apply (Comp_G_LNR c2)].
  - apply LNR_Imports.
  - apply list_disjoint_sym.
   clear; unfold JoinedImports; subst G. do 5 intros ?; subst.
      apply list_in_map_inv in H. destruct H as [[i phi] [Q Hi]]; simpl in Q; subst y.
      apply (@G_merge_InDom (Comp_G c1) (Comp_G c2) i (Comp_G_LNR c1)) in H0. 
      apply in_app_or in Hi; destruct Hi as [Hi | Hi]; apply filter_In in Hi; simpl in Hi.
      + destruct Hi. apply in_map_fst in H.
        apply (list_disjoint_notin i (Comp_G_disjoint_from_Imports c1)) in H.
        destruct H0 as [HH1 | [_ HH2]]. contradiction.
        destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)); simpl in H1. inv H1. clear H1.
        apply n; clear n; apply in_or_app.
        apply Comp_G_elim in HH2; destruct HH2. left; apply H0. right; apply H0.
      + destruct Hi. destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)). inv H1. clear H1.
        apply n; clear n; apply in_or_app. destruct H0 as [HH1 | [_ HH2]].
        * apply Comp_G_elim in HH1. destruct HH1. left; apply H0. destruct H0 as [? [? [f Hf]]]. right.
          apply in_or_app. left; trivial.
        * apply in_map_fst in H; elim ((Comp_G_disjoint_from_Imports c2) i i); trivial.
  - 
    clear - Disj_V1p2 Disj_V2p1 HV LNR_V.
    intros i j ? ? ?; subst j.
    specialize (HV i). 
    apply In_map_fst_find_id in H; auto. destruct H; rewrite H in HV.
    assert (In i (map fst V1) \/ In i (map fst V2)). {
      destruct (find_id i V1) eqn:?H.
      apply find_id_In_map_fst in H1; auto.
      apply find_id_In_map_fst in HV; auto.
   }
   clear HV H.
   destruct H1. 
  +
     pose proof (Comp_LNR c1). rewrite list_norepet_app in H1.
     destruct H1 as [_ [_ ?]].
     pose proof (list_disjoint_notin _ H1 H); clear H1.
     pose proof (list_disjoint_notin _ Disj_V1p2 H); clear Disj_V1p2 H.
     assert (~In i (IntIDs p2 ++ map fst E2)). {
       contradict H1. rewrite !in_app. rewrite in_app in H1; clear - H1; tauto.
     }
     assert (~In i (map fst Imports2)). { contradict H1; clear - H1; rewrite !in_app; tauto. }
     rewrite (Comp_G_dom c2 i) in H. clear H1.
     rewrite map_app in H2. rewrite in_app in H2.
     apply Classical_Prop.not_or_and in H2; destruct H2.
     rewrite map_app, in_app in H0.
     destruct H0.
     * apply G_merge_InDom in H0; [ | apply (Comp_G_LNR c1)].
        destruct H0 as [? | [_ ?]]; contradiction.
     *
       unfold JoinedImports in H0.
       rewrite map_app, in_app  in H0; destruct H0; apply In_map_fst_filter3 in H0; contradiction.
  +
     pose proof (Comp_LNR c2). rewrite list_norepet_app in H1.
     destruct H1 as [_ [_ ?]].
     pose proof (list_disjoint_notin _ H1 H); clear H1.
     pose proof (list_disjoint_notin _ Disj_V2p1 H); clear Disj_V2p1 H.
     assert (~In i (IntIDs p1 ++ map fst E1)). {
       contradict H1. rewrite !in_app. rewrite in_app in H1; clear - H1; tauto.
     }
     assert (~In i (map fst Imports1)). { contradict H1; clear - H1; rewrite !in_app; tauto. }
     rewrite (Comp_G_dom c1 i) in H. clear H1.
     rewrite map_app in H2. rewrite in_app in H2.
     apply Classical_Prop.not_or_and in H2; destruct H2.
     rewrite map_app, in_app in H0.
     destruct H0.
     * apply G_merge_InDom in H0; [ | apply (Comp_G_LNR c1)].
        destruct H0 as [? | [_ ?]]; contradiction.
     *
       unfold JoinedImports in H0.
       rewrite map_app, in_app  in H0; destruct H0; apply In_map_fst_filter3 in H0; contradiction.
Qed.

Local Lemma LNR_G: list_norepet (map fst G).
Proof.
  subst G; clear.
  apply G_merge_LNR; [ apply (Comp_G_LNR c1) | apply (Comp_G_LNR c2)].
Qed.

Local Lemma LNR_G_Imports: list_norepet (map fst (JoinedImports++G)).
Proof.
  pose proof LNR_VGI; clear - H.
  rewrite map_app in *.
  rewrite list_norepet_app in H; destruct H as [_ [? _]].
  rewrite list_norepet_app in H|-*; destruct H as[? [? ?]]; split3; auto.
  apply list_disjoint_sym; auto.
Qed.

Local Lemma Condition1:
     forall i, In i (map fst JoinedImports) ->
        exists (f : external_function) (ts : typelist) (t : type) (cc : calling_convention),
        PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc)). 
Proof.
unfold JoinedImports; clear - c1 c2 Linked. intros. rewrite map_app in H. apply in_app_or in H; destruct H.
  - clear - H c1 c2 Linked.
    apply list_in_map_inv in H. destruct H as [[j phi] [H J]]. simpl in H; subst j.
    apply filter_In in J. simpl in J. destruct J as [J1 J2]. 

    destruct (Comp_Imports_external c1 i) as [ef [ts [t [cc FND]]]].
    { apply (in_map fst) in J1. apply J1. }
     assert (FP := Linked_Functions_preserved _ _ _ Linked i). hnf in FP. rewrite FND in FP.
     destruct ((QP.prog_defs p2) ! i) eqn:Hequ.
    * destruct g; eauto. destruct f; eauto.
       destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)). inv J2. 
         elim n. apply in_or_app. right. apply in_map_iff.
         exists (i, Gfun (Internal f)); simpl; split; trivial. 
         rewrite filter_In; simpl. split; trivial.
         apply PTree.elements_correct in Hequ; auto.
         destruct FP. do 4 eexists; eassumption. contradiction.
    * do 4 eexists; eassumption.

  - assert (FP := Linked_Functions_preserved _ _ _ Linked i).
    apply list_in_map_inv in H. destruct H as [[j phi] [H J]]. simpl in H; subst j.
    apply filter_In in J. simpl in J. destruct J as [J1 J2]. 

    destruct (Comp_Imports_external c2 i) as [ef [ts [t [cc FND]]]].
    { apply (in_map fst) in J1. apply J1. }
    
    hnf in FP. rewrite FND in FP.
    remember ((QP.prog_defs p1) ! i) as u; symmetry in Hequ; destruct u.
    * destruct g; eauto. 
      destruct f; eauto.
      destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)). inv J2. 
         elim n. apply in_or_app. right. apply in_or_app. left. apply in_map_iff.
         exists (i, Gfun (Internal f)); simpl; split; trivial. 
         rewrite filter_In; simpl. split; trivial.
        apply PTree.elements_correct; trivial.
         destruct FP. do 4 eexists; eassumption. contradiction.
    * eauto.
Qed.

Local Lemma Condition2:
 forall i : ident, In i (map fst E) ->
        exists ef ts t cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External ef ts t cc)).
Proof.
  intros; unfold E. 
    assert (FP := Linked_Functions_preserved _ _ _ Linked i). hnf in FP.
    apply G_merge_InDom in H. destruct H as [Hi | [NE Hi]].
  - destruct (Comp_Externs c1 _ Hi) as [ef [tys [rt [cc P1i]]]]. exists ef, tys, rt, cc.
    clear - P1i Hi FP Externs1_Hyp c2.
    hnf in FP; rewrite P1i in FP.
    remember ((QP.prog_defs p2) ! i) as u; symmetry in Hequ; destruct u.
    * destruct g; eauto. destruct f; eauto.
         apply IntIDs_i in Hequ.
         elim (Externs1_Hyp i i); trivial. destruct FP; auto. contradiction.
    * trivial.
  - destruct (Comp_Externs c2 _ Hi) as [ef [tys [rt [cc P2i]]]]. exists ef, tys, rt, cc.
    clear - P2i Hi FP Externs2_Hyp Externs1_Hyp c2 c1 FundefsMatch.
    specialize (FundefsMatch i).
    rewrite P2i in *. 
    remember ((QP.prog_defs p1) ! i) as u; symmetry in Hequ; destruct u.
    * destruct g; eauto. destruct f.
       ++ clear - Hequ Externs2_Hyp Hi. apply IntIDs_i in Hequ.
         elim (Externs2_Hyp i i); trivial.
      ++ specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)).
         destruct FP; trivial.
      ++ contradiction.
    * trivial.
  - apply (Comp_Externs_LNR c1).
Qed.

Local Lemma SUBSUME1 : forall i : ident,
           subsumespec (find_id i (Imports1 ++ Comp_G c1)) (find_id i (JoinedImports ++ G)).
Proof.
  assert (JUST2 := Comp_G_justified c2).
  assert (JUST1 := Comp_G_justified c1).
  unfold JoinedImports; subst G; intros i. 
  assert (HCi := HC i).
  assert (CC := @Calling_conventions_match i).
  clear - c1 c2 CC HCi Externs2_Hyp Externs1_Hyp SC1 SC2 JUST1 JUST2.
   apply subsumespec_app_left; intros; apply subsumespec_i.
  - rewrite ! find_id_app_char. 
             remember (find_id i Imports1) as q1; symmetry in Heqq1; destruct q1 as [phi1 |]; simpl; trivial.
             specialize (list_disjoint_map_fst_find_id1 (Comp_G_disjoint_from_Imports c1) _ _ Heqq1); intros.
             rewrite G_merge_None_l; trivial. 2: apply (Comp_G_LNR c2).
             rewrite find_id_filter_char, Heqq1 by apply (Comp_Imports_LNR c1); simpl.
             destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)); simpl.
             2: exists phi1; split; [ reflexivity | apply funspec_sub_si_refl; trivial].
             rewrite find_id_filter_char by apply (Comp_Imports_LNR c2); simpl.
             destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)); simpl.
           { 
             destruct (SC2 _ _ Heqq1 i0) as [tau [TAU Tau]]; clear SC2.
             specialize (Comp_G_Exports c2 _ _ TAU).
             apply in_app_or in i0; destruct i0 as [Hi | Hi].
             * specialize (Comp_G_E c2 i Hi); simpl; intros X. 
               apply In_map_fst_find_id in Hi. 2: apply c2. destruct Hi as [phi PHI].
               rewrite <- X, PHI.
               exists phi; split.
               + rewrite X in PHI. destruct (find_id i Imports2); apply PHI.
               + apply funspec_sub_sub_si. eapply funspec_sub_trans; eassumption.
             * intros. remember (find_id i G2) as g; symmetry in Heqg; destruct g as [omega |].
               + exists omega; split. destruct (find_id i Imports2); apply Heqg.
                 apply funspec_sub_sub_si. eapply funspec_sub_trans; eassumption.
               + destruct H0 as [sig [SIG Sig]]. apply find_id_In_map_fst in SIG.
                 elim (Comp_Interns_disjoint_from_Imports c2 i i); trivial. } (* apply IntIDs_e in Hi.
                 destruct (Comp_Imports_external c2 i). Search IntIDs. rewrite SIG.   specialize (Comp_G_Exports c2 _ _ TAU).   
               Search In map fst find_id.*)
           { elim n; clear - Heqq1. apply  find_id_In_map_fst in Heqq1. apply in_or_app; right. apply in_or_app; right; trivial. }
(*             
             assert (X: exists gspec, find_id i (Comp_G c2) = Some gspec /\ TT |-- funspec_sub_si gspec phi1).
             { destruct (Comp_G_dom c2 i) as [XX YY]. apply XX in i0.
             destruct (find_id i Imports2); trivial.
Print Component.
             + apply find_id_None_iff in H.
               remember (find_id i (Comp_G c2)) as w2; symmetry in Heqw2; destruct w2 as [psi2 |].
               * exists psi2; split. destruct (find_id i Imports2); trivial.
                 destruct (SC2 _ _ Heqq1 i0) as [tau2 [Tau2 SubTau]].
                 apply funspec_sub_sub_si. apply @funspec_sub_trans with tau2; trivial.
                 specialize (Comp_G_Exports c2 _ _ Tau2). unfold Comp_G in Heqw2. rewrite Heqw2; trivial.
               * destruct (SC2 _ _ Heqq1 i0) as [tau2 [TAU Tau]].
                 specialize (Comp_G_Exports c2 _ _ TAU). unfold Comp_G in Heqw2; rewrite Heqw2.
                 intros [xi [Xi XI]]. rewrite Xi. congruence.

 
                 destruct (Comp_G_Exports c2 _ _ TAU) as [omega [Omega OM]].
                 clear - Heqw2 Omega. unfold Comp_G in Heqw2; congruence.
             + destruct (SC2 _ _ Heqq1 i0) as [tau2 [TAU Tau]]. 
               destruct (Comp_G_Exports c2 _ _ TAU) as [omega [Omega OM]]; unfold Comp_G; rewrite Omega.
               specialize (Comp_G_disjoint_from_Imports c2); intros.
               rewrite (list_disjoint_map_fst_find_id2 (Comp_G_disjoint_from_Imports c2) _ _ Omega).
               exists omega; split; trivial. apply funspec_sub_sub_si. apply @funspec_sub_trans with tau2; trivial.*)
  -
      remember (find_id i (Comp_G c1)) as d; symmetry in Heqd; destruct d as [phi1 |]; simpl; trivial.
               rewrite!  find_id_app_char, find_id_filter_None_I; [ | trivial | apply (Comp_Imports_LNR c1) ].
               rewrite find_id_filter_char by apply (Comp_Imports_LNR c2); simpl.
               remember (find_id i Imports2) as w2; symmetry in Heqw2; destruct w2 as [psi2 |]; simpl.
               + destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)); simpl.
                 * rewrite (G_merge_find_id_SomeNone Heqd (list_disjoint_map_fst_find_id1 (Comp_G_disjoint_from_Imports c2) _ _ Heqw2)).
                   eexists; split. reflexivity. apply funspec_sub_si_refl; trivial.
                 * apply find_id_In_map_fst in Heqd. apply (Comp_G_dom c1) in Heqd.
                   elim n; clear - Heqd. rewrite app_assoc. apply in_or_app. left; apply in_app_or in Heqd; apply in_or_app. destruct Heqd; auto.
               + remember (find_id i (Comp_G c2)) as q2; destruct q2 as [phi2 |]; symmetry in Heqq2; simpl; trivial.
                 * destruct (G_merge_find_id_SomeSome Heqd Heqq2) as [phi [BI PHI]].
                   { apply HCi; trivial. }
                   { auto. } 
                   rewrite PHI. exists phi; split; trivial. apply binaryintersection_sub in BI. apply funspec_sub_sub_si.
                   apply BI. 
                 * rewrite G_merge_None_r, Heqd; trivial. exists phi1. split; trivial. apply funspec_sub_si_refl; trivial.
                   apply (Comp_G_LNR c2). 
Qed.

Local Lemma SUBSUME2 : forall i : ident,
           subsumespec (find_id i (Imports2 ++ Comp_G c2))
             (find_id i (JoinedImports ++ G)).
Proof. 
  assert (JUST2 := Comp_G_justified c2).
  assert (JUST1 := Comp_G_justified c1).
  intros i. 
  assert (CC := @Calling_conventions_match i).
  assert (HCi := HC i).
  apply subsumespec_i.
  remember (find_id i (Imports2 ++ Comp_G c2)) as u; symmetry in Hequ; destruct u as [phi2 |]; [| simpl; trivial].
  rewrite find_id_app_char in Hequ.
  unfold JoinedImports. rewrite <- app_assoc, ! find_id_app_char, ! find_id_filter_char; try apply (Comp_Imports_LNR c2) ; try apply (Comp_Imports_LNR c1).
  simpl. remember (find_id i Imports2) as q; symmetry in Heqq; destruct q as [phi2' |].
   + subst G. inv Hequ. clear - i  Heqq SC1 HImports.
         specialize (list_disjoint_map_fst_find_id1 (Comp_G_disjoint_from_Imports c2) _ _ Heqq); intros.
        rewrite G_merge_None_r; trivial. 2: apply (Comp_G_LNR c2).
        destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)); simpl.
        - apply find_id_None_iff in H; elim H.
          apply (Comp_G_dom c2 i). apply in_or_app. apply in_app_or in i0. destruct i0; auto.
        - remember (find_id i Imports1) as w1; symmetry in Heqw1; destruct w1 as [ph1 |].
          * specialize (HImports _ _ _ Heqw1 Heqq); subst.
            eexists; split. reflexivity. apply funspec_sub_si_refl; trivial.
          * destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)); simpl.
            ++ rewrite app_assoc in i0; apply in_app_or in i0; destruct i0.
               -- destruct (SC1 _ _ Heqq H0) as [phi1 [EXP1 Sub]].
                  specialize (Comp_G_Exports c1 _ _ EXP1).
                  remember (find_id i G1) as g; symmetry in Heqg; destruct g; intros.
                  ** exists f; split; trivial. apply funspec_sub_sub_si. (* as [psi1 [G1i Psi1]].
                  eexists; split. eassumption. apply funspec_sub_sub_si.*)
                  apply @funspec_sub_trans with phi1; trivial.
                  ** destruct H1 as [tau [? _]]. congruence.
               -- apply find_id_None_iff in Heqw1. contradiction.
            ++ eexists; split. reflexivity. apply funspec_sub_si_refl; trivial.
      + destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)); simpl.
        - subst G.
          remember (find_id i (Comp_G c1)) as q1; symmetry in Heqq1; destruct q1 as [phi1 |].
          * destruct (G_merge_find_id_SomeSome Heqq1 Hequ) as [phi [BI Sub]].
            { apply HCi; trivial. }
            { auto. } 
             exists phi; split.
             -- destruct (find_id i Imports1); trivial.
             -- apply funspec_sub_sub_si. eapply (binaryintersection_sub). apply BI.
          * rewrite (G_merge_find_id_NoneSome Heqq1 Hequ).
            exists phi2; split. destruct (find_id i Imports1); trivial. apply funspec_sub_si_refl; trivial.
            apply (Comp_G_LNR c2).
        - elim n. apply find_id_In_map_fst in Hequ. rewrite <- (Comp_G_dom c2) in Hequ. elim n; apply in_or_app.
          apply in_app_or in Hequ; destruct Hequ; auto.
Qed.

Local Lemma LNR4_V1 : list_norepet (map fst V1 ++ map fst (JoinedImports ++ G)).
Proof.
  pose proof I. pose proof LNR_VGI.
  rewrite list_norepet_app; split3.
  pose proof (Comp_LNR c1). rewrite list_norepet_app in H1; apply H1.
  apply LNR_G_Imports.
    intros i j ? ? ?; subst j.
    assert (H' := Comp_LNR c1). rewrite list_norepet_app in H'. destruct H' as [_ [_ H']].
    pose proof (list_disjoint_notin _ H' H1); clear H'.
    pose proof (list_disjoint_notin _ Disj_V1p2 H1); clear Disj_V1p2 H1.
    clear - H2 H3 H4.
    rewrite map_app, in_app in H3.
    apply Classical_Prop.not_or_and in H3; destruct H3.
    rewrite in_app in H4; apply Classical_Prop.not_or_and in H4; destruct H4.
    rewrite in_app in H3; apply Classical_Prop.not_or_and in H3; destruct H3.
    assert (~In i (map fst G2)). {
      rewrite <- (Comp_G_dom c2 i).
     rewrite in_app. tauto.
   }
   clear H4 H1.
   rewrite map_app, in_app in H2; destruct H2.
 -
    unfold JoinedImports in H1.
    rewrite map_app, in_app in H1; destruct H1.
    apply In_map_fst_filter3 in H1. contradiction.
    apply In_map_fst_filter3 in H1. contradiction.
 - apply G_merge_InDom in H1; [ | apply (Comp_G_LNR c1)].
    destruct H1 as [? | [_ ?]]; try contradiction.
Qed.

Local Lemma LNR4_V2 : list_norepet (map fst V2 ++ map fst (JoinedImports ++ G)).
Proof.
  pose proof I. pose proof LNR_VGI.
  rewrite list_norepet_app; split3.
  pose proof (Comp_LNR c2). rewrite list_norepet_app in H1; apply H1.
  apply LNR_G_Imports.
    intros i j ? ? ?; subst j.
    assert (H' := Comp_LNR c2). rewrite list_norepet_app in H'. destruct H' as [_ [_ H']].
    pose proof (list_disjoint_notin _ H' H1); clear H'.
    pose proof (list_disjoint_notin _ Disj_V2p1 H1); clear Disj_V2p1 H1.
    clear - H2 H3 H4.
    rewrite map_app, in_app in H3.
    apply Classical_Prop.not_or_and in H3; destruct H3.
    rewrite in_app in H4; apply Classical_Prop.not_or_and in H4; destruct H4.
    rewrite in_app in H3; apply Classical_Prop.not_or_and in H3; destruct H3.
    assert (~In i (map fst G1)). {
      rewrite <- (Comp_G_dom c1 i).
     rewrite in_app. tauto.
   }
   clear H4 H1.
   rewrite map_app, in_app in H2; destruct H2.
 -
    unfold JoinedImports in H1.
    rewrite map_app, in_app in H1; destruct H1.
    apply In_map_fst_filter3 in H1. contradiction.
    apply In_map_fst_filter3 in H1. contradiction.
 - apply G_merge_InDom in H1; [ | apply (Comp_G_LNR c1)].
    destruct H1 as [? | [_ ?]]; try contradiction.
Qed.

Local Lemma G_dom:
forall i : ident, In i (IntIDs p ++ map fst E) <-> In i (map fst G).
  clear - Linked Externs2_Hyp.
   intros. subst G; unfold E. split; intros. 
  - apply G_merge_InDom; [ apply (Comp_G_LNR c1) | apply in_app_or in H; destruct H].
    * destruct (in_dec ident_eq i (map fst (Comp_G c1))). left; trivial. right; split; trivial.
      apply c2. 
     assert (FP := Linked_Functions_preserved _ _ _ Linked i). hnf in FP.
      destruct ((QP.prog_defs p1) ! i ) as [ [ [|] |] | ] eqn:?.
      ++ clear - Heqo FP H n.
            elim n. apply c1. apply in_or_app; left. 
            apply IntIDs_i in Heqo; trivial.
      ++ clear - Heqo FP H n c2. 
            destruct ((QP.prog_defs p2) ! i) as [[[|]|]|] eqn:Heqq2.
            apply in_or_app; left.
            apply IntIDs_i in Heqq2; trivial.
            destruct FP as [FP FP']. inversion2 FP FP'.
            apply In_map_fst_find_id in H. destruct H. 
               rewrite find_id_filter_char in H; trivial; simpl in H.
               rewrite find_id_elements in H. rewrite FP in H. inv H.
               apply PTree.elements_keys_norepet.
               apply list_norepet_map_fst_filter; apply PTree.elements_keys_norepet.
            apply IntIDs_e in H; destruct H.  contradiction.
            apply IntIDs_e in H; destruct H.  congruence.
       ++ clear - Heqo FP H n c2.
            apply IntIDs_e in H. destruct H as [f ?]. rewrite H in FP.
             destruct ((QP.prog_defs p2) ! i) as [[[|]|]|] eqn:Heqq2; try contradiction.
             destruct FP as [_ [[_ ?] | [_ ?]]]; discriminate. discriminate.

       ++ clear - Heqo FP H n c2.
            destruct ((QP.prog_defs p2) ! i) as [[[|]|]|] eqn:Heqq2; try contradiction.
            apply in_or_app; left.
            apply IntIDs_i in Heqq2; trivial.
            apply In_map_fst_find_id in H. destruct H. 
               rewrite find_id_filter_char in H; trivial; simpl in H.
               rewrite find_id_elements in H. rewrite FP in H. inv H.
               apply PTree.elements_keys_norepet.
               apply list_norepet_map_fst_filter; apply PTree.elements_keys_norepet.
            apply IntIDs_e in H; destruct H.  congruence.
            apply IntIDs_e in H; destruct H.  congruence.
    * apply G_merge_InDom in H; [ destruct H as [H | [HE H]] | apply (Comp_Externs_LNR c1)].
      ++ left. apply In_map_fst_find_id in H. destruct H. apply (Comp_E_in_G_find c1) in H. apply find_id_In_map_fst in H; trivial. apply (Comp_Externs_LNR c1).
      ++ right. split; [ intros N | apply Comp_E_in_G; trivial ].
         apply (list_disjoint_notin  _ Externs2_Hyp H). apply (Comp_G_dom c1) in N. apply in_app_or in N; destruct N; [ trivial | contradiction].
  - assert (FP := Linked_Functions_preserved _ _ _ Linked i). hnf in FP. 
    apply G_merge_InDom in H; [ destruct H as [H | [HE H]] | apply (Comp_G_LNR c1)].
    * apply (Comp_G_dom c1) in H.  apply in_app_or in H; apply in_or_app; destruct H.
      ++ left. apply In_map_fst_find_id in H; [ destruct H as [fd Hfd] | apply Comp_LNR_Interns].
         clear - c1 FP Hfd. 
         rewrite find_id_filter_char in Hfd; [ | apply PTree.elements_keys_norepet].
         rewrite find_id_elements in Hfd.
         destruct ((QP.prog_defs p1) ! i); try discriminate.
         destruct g; [ simpl in Hfd | discriminate].
         destruct f; inv Hfd.
         destruct  ((QP.prog_defs p2) ! i) as [ [ [|] | ] | ]; try contradiction.
         destruct FP as [FP _]; apply IntIDs_i in FP; trivial.
         apply IntIDs_i in FP; trivial.
         apply IntIDs_i in FP; trivial.
      ++ right. apply G_merge_InDom. apply (Comp_Externs_LNR c1). left; trivial.
    * apply in_or_app. apply Comp_G_elim in H. destruct H as [[HE2 EXT] | [HE2 [INT [f FI]]]].
      ++ right. apply G_merge_InDom.  apply (Comp_Externs_LNR c1). 
         right; split; trivial. intros N. apply HE. apply Comp_E_in_G. apply N.
      ++ rewrite FI in FP. 
             left; destruct  ((QP.prog_defs p1) ! i) as [ [ [|] | ] | ];
                  try apply IntIDs_i in FP; trivial.
              destruct FP as [FP _]; apply IntIDs_i in FP; trivial. contradiction.
Qed.


Local Lemma G_E: 
 forall i : ident, In i (map fst E) -> find_id i E = find_id i G.
Proof.
subst G; unfold E; intros. assert (FP := Linked_Functions_preserved _ _ _ Linked i); hnf in FP.
  destruct (In_map_fst_find_id H) as [phi Phi]. apply G_merge_LNR. apply (Comp_Externs_LNR c1).  apply (Comp_Externs_LNR c2). 
  symmetry; rewrite Phi. apply G_merge_find_id_Some in Phi. remember (find_id i E1) as q1; symmetry in Heqq1; destruct q1 as [phi1 |]. 
  - specialize (Comp_E_in_G_find c1 _ _ Heqq1); intros.
    remember (find_id i E2) as q2; symmetry in Heqq2; destruct q2 as [phi2 |].
    * specialize (Comp_E_in_G_find c2 _ _ Heqq2); intros.
      unfold G_merge. apply find_id_app1. erewrite  G_merge_aux_find_id1. 2: eassumption. rewrite H1, Phi; trivial.
    * simpl in Phi. subst phi1. rewrite (G_merge_find_id_SomeNone H0); trivial.
      remember (find_id i (Comp_G c2)) as u; symmetry in Hequ; destruct u as [psi2 |]; trivial.
      apply find_id_In_map_fst in Hequ. apply Comp_G_elim in Hequ. destruct Hequ as [[HH _] | [_ [? ]]].
      apply find_id_None_iff in Heqq2. contradiction. 
      apply In_map_fst_find_id in H1. destruct H1. rewrite(list_disjoint_map_fst_find_id1 Externs1_Hyp _ _ Heqq1) in H1. inv H1.
      apply list_norepet_map_fst_filter.
      apply PTree.elements_keys_norepet.
  - specialize (Comp_E_in_G_find c2 _ _ Phi); intros.
     apply G_merge_find_id_NoneSome; trivial; [ | apply (Comp_G_LNR c2)].
      remember (find_id i (Comp_G c1)) as u; symmetry in Hequ; destruct u as [psi1 |]; trivial.
      apply find_id_In_map_fst in Hequ. apply Comp_G_elim in Hequ. destruct Hequ as [[HH _] | [_ [? ]]].
      apply find_id_None_iff in Heqq1. contradiction. 
      apply In_map_fst_find_id in H1. destruct H1. rewrite(list_disjoint_map_fst_find_id1 Externs2_Hyp _ _ Phi) in H1. inv H1.
      apply list_norepet_map_fst_filter.
      apply PTree.elements_keys_norepet.
  - apply (Comp_Externs_LNR c2).
Qed.

Let  OKp:= QPlink_progs_OK _ _ _ Linked (Comp_prog_OK c1) (Comp_prog_OK c2).

Let cs := compspecs_of_QPcomposite_env (@QP.prog_comp_env function p)
     (@proj2
        (@list_norepet ident
           (@map (ident * QP.builtin) ident (@fst ident QP.builtin)
              (@QP.prog_builtins function p) ++
            @map (positive * globdef (fundef function) type) positive
              (@fst positive (globdef (fundef function) type))
              (@PTree.elements (globdef (fundef function) type)
                 (@QP.prog_defs function p))))
        (QPcompspecs_OK (@QP.prog_comp_env function p)) OKp).

Let cs1 := 
        (compspecs_of_QPcomposite_env (@QP.prog_comp_env function p1)(@proj2
              (@list_norepet ident
                 (@map (ident * QP.builtin) ident
                    (@fst ident QP.builtin)
                    (@QP.prog_builtins function p1) ++
                  @map (positive * globdef (fundef function) type)
                    positive
                    (@fst positive (globdef (fundef function) type))
                    (@PTree.elements (globdef (fundef function) type)
                       (@QP.prog_defs function p1))))
              (QPcompspecs_OK (@QP.prog_comp_env function p1))
              (@Comp_prog_OK Espec V1 E1 Imports1 p1 Exports1 GP1 G1 c1))).

Let cs2 := (compspecs_of_QPcomposite_env (@QP.prog_comp_env function p2)
           (@proj2
              (@list_norepet ident
                 (@map (ident * QP.builtin) ident
                    (@fst ident QP.builtin)
                    (@QP.prog_builtins function p2) ++
                  @map (positive * globdef (fundef function) type)
                    positive
                    (@fst positive (globdef (fundef function) type))
                    (@PTree.elements (globdef (fundef function) type)
                       (@QP.prog_defs function p2))))
              (QPcompspecs_OK (@QP.prog_comp_env function p2))
              (@Comp_prog_OK Espec V2 E2 Imports2 p2 Exports2 GP2 G2 c2))).

Local Lemma CS1 : cspecs_sub cs1 cs.
Proof.
  destruct  (linked_compspecs' _ _ _
                   (proj2 (Comp_prog_OK c1))
                   (proj2 (Comp_prog_OK c2))
                   Linked)
   as [_ [CS1 CS2]].
 apply (cspecs_sub_of_QPsub _ _ (proj2 (Comp_prog_OK c1)) (proj2 OKp) ) in CS1.
 auto.
Qed.

Local Lemma CS2: cspecs_sub cs2 cs.
Proof.
  destruct  (linked_compspecs' _ _ _
                   (proj2 (Comp_prog_OK c1))
                   (proj2 (Comp_prog_OK c2))
                   Linked)
   as [_ [CS1 CS2]].
 apply (cspecs_sub_of_QPsub _ _ (proj2 (Comp_prog_OK c2)) (proj2 OKp)) in CS2.
 auto.
Qed.

Local Lemma G_justified:
  forall (i : positive) (phi : funspec) (fd : fundef function),
    (QP.prog_defs p) ! i = Some (Gfun fd) ->
     find_id i G = Some phi -> 
      @SF Espec cs V (QPglobalenv p) (JoinedImports ++ G) i fd phi.
Proof.
  assert (JUST2 := Comp_G_justified c2).
  assert (JUST1 := Comp_G_justified c1).
  assert (SUBSUME1 := SUBSUME1). 
  assert (SUBSUME2 := SUBSUME2). 
  assert (LNR4_V1 := LNR4_V1). 
  assert (LNR4_V2 := LNR4_V2). 
 subst G. intros.
  assert (HCi := HC i).
  assert (FP := Linked_Functions_preserved _ _ _ Linked i). hnf in FP. specialize (FundefsMatch i).
  apply G_merge_find_id_Some in H0. 2: apply (Comp_G_LNR c2).
  remember (find_id i (Comp_G c1)) as q1; symmetry in Heqq1; destruct q1 as [phi1 |].
  - subst phi; 
    exploit (Comp_G_in_Fundefs' c1). apply Heqq1. intros [fd1 FD1].
    specialize (JUST1 _ _ _ FD1 Heqq1).
    specialize (SF_subsumespec JUST1 _ V SUBSUME1 HV1
                          (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V1)
                  (Comp_ctx_LNR c1)); clear JUST1 SUBSUME1; intros SF1.
    remember (find_id i (Comp_G c2)) as q2; symmetry in Heqq2; destruct q2 as [phi2 |].
    * exploit (Comp_G_in_Fundefs' c2). apply Heqq2. intros [fd2 FD2].
      specialize (JUST2 _ _ _ FD2 Heqq2).
      specialize (SF_subsumespec JUST2 _  V SUBSUME2 HV2 
    (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V2) (Comp_ctx_LNR c2)); clear JUST2 SUBSUME2; intros SF2.
      rewrite FD1, FD2, H in *. specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl.
      destruct fd1; destruct fd2.
      ++ (*Internal/Internal*)
         destruct FP as [FP FP']; inv FP. inv FP'.
         assert (BI : binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2))).
         { apply merge_specs_succeed. apply HCi; auto.
           apply InternalInfo_cc in SF1. rewrite <- SF1.
           apply InternalInfo_cc in SF2.  trivial. }
         simpl.
         eapply internalInfo_binary_intersection; [ | | apply BI].
         --
            apply (InternalInfo_envs_sub CS1 (QPglobalenv p1)); [ apply SF1 | clear - H OKp].
            apply QPfind_funct_ptr_exists; auto.
         -- apply (InternalInfo_envs_sub CS2 (QPglobalenv p2)); [ apply SF2 | clear - H OKp].
            apply QPfind_funct_ptr_exists; auto.
      ++ (*InternalExternal*) 
         clear - FP FundefsMatch Externs2_Hyp FD1 FD2 Heqq1 Heqq2.
         apply find_id_In_map_fst in Heqq2. apply Comp_G_elim in Heqq2. destruct Heqq2 as [[? ?]|  [? ?]].
         -- elim (list_disjoint_notin i Externs2_Hyp H). clear - FD1 c1. 
            apply IntIDs_i in FD1; trivial.
         -- destruct H0 as [? [? ?]]. congruence.
      ++ (*ExternalInternal*)
         clear - FP FundefsMatch Externs1_Hyp FD1 FD2 Heqq1 Heqq2.
         apply find_id_In_map_fst in Heqq1. apply Comp_G_elim in Heqq1. destruct Heqq1 as [[? ?]|  [? ?]].
         -- elim (list_disjoint_notin i Externs1_Hyp H). clear - FD2 c2.
              apply IntIDs_i in FD2; trivial. 
         -- destruct H0 as [? [? ?]]. congruence.
      ++ (*ExternalExternal*)
         destruct FP as [FP FP']; inv FP. inv FP'.
         assert (BI : binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2))).
         { apply merge_specs_succeed. apply HCi; auto.
           apply ExternalInfo_cc in SF1. rewrite <- SF1. 
           apply ExternalInfo_cc in SF2. trivial. }
         eapply (externalInfo_binary_intersection); [ | | apply BI].
         -- eapply ExternalInfo_envs_sub; [ apply SF1 |  ].
            apply QPfind_funct_ptr_exists; auto.
         -- eapply ExternalInfo_envs_sub; [ apply SF2 |  ].
              apply QPfind_funct_ptr_exists; auto.
    * (*i in G1 but not in G2*)
      apply find_id_In_map_fst in Heqq1. apply Comp_G_elim in Heqq1. 
      rewrite FD1 in *. destruct Heqq1 as [[HE EF1] | [HE [INT1 IF1]]].
      ++ destruct EF1 as [ef [tys [rt [cc EF1]]]].
          inv EF1.
         destruct ((QP.prog_defs p2) ! i) as [ [[|]|] | ] eqn:Heqw2.
         -- clear - c2 HE Externs1_Hyp Heqw2. elim (list_disjoint_notin i Externs1_Hyp HE).
              apply IntIDs_i in Heqw2; trivial.
         -- specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch.
              destruct FP as [FP FP']. inversion2 FP FP'.
               rewrite FP in H. inv H. simpl.
               eapply ExternalInfo_envs_sub; [ apply SF1 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
         -- clear FundefsMatch. contradiction FP.
         -- rewrite FP in H. inv H. simpl.
               eapply ExternalInfo_envs_sub; [ apply SF1 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto. 
      ++ destruct IF1 as [f IF1]. inv IF1.
             destruct ((QP.prog_defs p2) ! i) as [ [[|]|] | ] eqn:Heqw2.
         -- specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch. 
               destruct FP as [FP FP']. inversion2 FP FP'.
               rewrite FP in H. inv H. 
               apply (InternalInfo_envs_sub CS1 (QPglobalenv p1)); [ apply SF1 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
         -- specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch. 
               rewrite FP in H. inv H. 
               apply (InternalInfo_envs_sub CS1 (QPglobalenv p1)); [ apply SF1 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
         -- clear FundefsMatch Heqw2.  contradiction FP.
         -- clear FundefsMatch Heqw2.
             rewrite FP in H. inv H. simpl. 
             apply (InternalInfo_envs_sub CS1 (QPglobalenv p1)); [ apply SF1 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
   - (*i in G2 but not in G1 -- symmetric*) 
      specialize (JUST2 i phi). specialize (JUST1 i). rewrite <- H0 in JUST2.
      apply find_id_In_map_fst in H0. apply Comp_G_elim in H0.
      destruct H0 as [[HE EF2] | [HE [INT2 IF2]]].
      ++ destruct EF2 as [ef [tys [rt [cc EF2]]]]. specialize (JUST2 _ EF2 (eq_refl _)).
             destruct ((QP.prog_defs p1) ! i) as [ [[|]|] | ] eqn:Heqw1.
         --  clear - c1 HE Externs2_Hyp Heqw1. elim (list_disjoint_notin i Externs2_Hyp HE). 
               apply IntIDs_i in Heqw1; trivial.
         -- rewrite EF2 in FundefsMatch, FP. 
               specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch.
               destruct FP as [FP FP']. inversion2 FP FP'.
               rewrite FP in H. inv H. simpl.
               eapply ExternalInfo_envs_sub; [ apply JUST2 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
         -- clear FundefsMatch. rewrite EF2 in FP. contradiction FP. 
         -- clear FundefsMatch. rewrite EF2 in FP. rewrite FP in H. inv H. simpl.
               eapply ExternalInfo_envs_sub; [ apply JUST2 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
      ++ destruct IF2 as [f IF2]. rewrite IF2 in *.
         specialize (JUST2 _ (eq_refl _) (eq_refl _)).
         specialize (SF_subsumespec JUST2 _ _ SUBSUME2 HV2 (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V2) (Comp_ctx_LNR c2)); clear JUST2 SUBSUME2; intros SF2.
         destruct ((QP.prog_defs p1) ! i) as [ [[|]|] | ] eqn:Heqw1.
         -- specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch.
               destruct FP as [FP FP']. inversion2 FP FP'.
               rewrite FP in H. inv H.
               clear JUST1.
               apply (InternalInfo_envs_sub CS2 (QPglobalenv p2)); [ apply SF2 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
         -- specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. 
               destruct FundefsMatch as [psi2 PSI2].
               rewrite FP in H. inv H. simpl.
               apply (InternalInfo_envs_sub CS2 (QPglobalenv p2)); [ apply SF2 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
          -- clear FundefsMatch Heqw1. contradiction FP.
          -- clear FundefsMatch Heqw1.
             rewrite FP in H. inv H. simpl.
             apply (InternalInfo_envs_sub CS2 (QPglobalenv p2)); [ apply SF2 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
Qed.

Local Lemma G_Exports:
  forall (i : ident) (phi : funspec),
   find_id i Exports = Some phi ->
   match find_id i G with
     Some phi' => funspec_sub phi' phi
   | None =>  exists phi' : funspec, find_id i JoinedImports = Some phi' /\ funspec_sub phi' phi
  end.
Proof.
 (*TODO: clean up this proof*)
  intros i phi Hi. unfold Exports. subst G.
  assert (HCi := HC i).
  specialize (G_merge_find_id_Some Hi (Comp_Exports_LNR c2)); clear Hi; intros Hi.
  assert (FP := Linked_Functions_preserved _ _ _ Linked i).
  hnf in FP. clear FP. (*NEW*)
  unfold Comp_G.
  remember (find_id i G1) as u1; symmetry in Hequ1; destruct u1 as [phi1 |].
  - remember (find_id i G2) as u2; symmetry in Hequ2; destruct u2 as [phi2 |]. 
    * 
      assert (SigsPhi:typesig_of_funspec phi1 = typesig_of_funspec phi2).
      { apply (HCi phi1 phi2); trivial. }
      specialize (Calling_conventions_match Hequ1 Hequ2); intros CCPhi.

      destruct (G_merge_find_id_SomeSome Hequ1 Hequ2 SigsPhi CCPhi) as [phi' [BI' PHI']].
      rewrite PHI'. (* exists phi'; split. trivial. *)clear PHI'.
      apply binaryintersection_sub in BI'.
      destruct BI' as [Phi1' Phi2'].
      remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
      ++ subst phi. (*clear FP.*)
         specialize (Comp_G_Exports c1 _ _ Heqq1).
         unfold Comp_G in Hequ1. rewrite Hequ1; intros TAU1.
(*
        ** clear FP. (*   as [tau1 [Tau1 TAU1]].*)
         unfold Comp_G in Hequ1. rewrite Hequ1 in Tau1; inv Tau1.*)
         remember (find_id i Exports2) as q2; symmetry in Heqq2; destruct q2 as [psi2 |].

         2: solve [simpl; eapply @funspec_sub_trans with phi1; trivial ]. 

         specialize (Comp_G_Exports c2 _ _ Heqq2).
         unfold Comp_G in Hequ2. rewrite Hequ2; intros TAU2.

         assert (SigsPsi: typesig_of_funspec psi1 =typesig_of_funspec psi2).
         { clear - SigsPhi TAU1 TAU2. destruct phi1; destruct phi2.
           destruct psi1; destruct TAU1 as [AA1 _].
           destruct psi2; destruct TAU2 as [AA2 _]. simpl in *.
           destruct AA1; destruct AA2; subst; trivial. }
         assert (CCPsi: callingconvention_of_funspec psi1 = callingconvention_of_funspec psi2).
         { clear - CCPhi TAU1 TAU2. apply funspec_sub_cc in TAU1. apply funspec_sub_cc in TAU2. 
           rewrite <- TAU1, <- TAU2; trivial. }
         destruct (G_merge_find_id_SomeSome Heqq1 Heqq2 SigsPsi CCPsi) as [tau' [BI TAU']].
         simpl. rewrite BI. clear - BI Phi1' Phi2' TAU1 TAU2.
         apply (BINARY_intersection_sub3 _ _ _ BI); clear BI.
         apply @funspec_sub_trans with phi1; trivial.
         apply @funspec_sub_trans with phi2; trivial.
      ++ specialize (Comp_G_Exports c2 _ _ Hi).
         unfold Comp_G in Hequ2; rewrite Hequ2; intros TAU2.
         apply @funspec_sub_trans with phi2; trivial. 

    * rewrite (G_merge_find_id_SomeNone Hequ1 Hequ2).
      remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
      ++ subst. (*eexists; split. reflexivity.*)
         specialize (Comp_G_Exports c1 _ _ Heqq1). unfold Comp_G in Hequ1; rewrite Hequ1; intros PSI.
         eapply funspec_sub_trans. apply PSI.
         apply type_of_funspec_sub in PSI. (* clear FP.*)
         (*clear - Heqq1 Hequ2 c2 PSI.*) remember (find_id i Exports2) as w; symmetry in Heqw; destruct w as [psi2 |].
         -- specialize (Comp_G_Exports c2 _ _ Heqw).
            unfold Comp_G in Hequ2; rewrite Hequ2. intros [phi [PHI Phi]]. simpl.
            remember (binary_intersection psi1 psi2); symmetry in Heqo; destruct o. 2: apply funspec_sub_refl. 
            apply (BINARY_intersection_sub3 _ _ _ Heqo psi1). apply funspec_sub_refl.
            eapply funspec_sub_trans with phi; trivial.
            destruct (SC1 _ _ PHI) as [tau [TAU Tau]].
            { apply find_id_In_map_fst in Hequ1. apply (Comp_G_dom c1) in Hequ1. clear - Hequ1.
              apply in_app_or in Hequ1. apply in_or_app. destruct Hequ1; [ right | left]; trivial. }
            rewrite TAU in Heqq1; inv Heqq1; trivial.
         -- simpl. apply funspec_sub_refl; trivial.
      ++ (*eexists; split. reflexivity. clear FP.*)
         unfold Comp_G in Hequ2. specialize (Comp_G_Exports c2 i phi); rewrite Hi, Hequ2.
         intros X. destruct X as [tau [TAU Tau]]; trivial.
         eapply funspec_sub_trans with tau; trivial.
         destruct (SC1 _ _ TAU) as [omega [OMEGA Omega]].
         { apply find_id_In_map_fst in Hequ1. apply (Comp_G_dom c1) in Hequ1. clear - Hequ1.
              apply in_app_or in Hequ1. apply in_or_app. destruct Hequ1; [ right | left]; trivial. }
         congruence. 
  - (*clear FP. unfold Comp_G in Hequ1.*)
    remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
    * specialize (Comp_G_Exports c1 _ _ Heqq1); rewrite Hequ1.
      intros X; destruct X as [psi [Psi PSI]].
      rewrite G_merge_None_l; trivial. subst phi.
      remember (find_id i Exports2) as w; symmetry in Heqw; destruct w.
      + specialize (Comp_G_Exports c2 _ _ Heqw); unfold Comp_G.
        remember (find_id i G2) as u; symmetry in Hequ; destruct u; simpl; intros.
        ++ (*exists f0. split; trivial. clear HCi.*)
           apply find_id_In_map_fst in Hequ. apply (Comp_G_dom c2) in Hequ.
           destruct (SC2 _ _ Psi) as [omega [OMEGA Omega]].
              ** clear - Hequ. apply in_or_app. apply in_app_or in Hequ. destruct Hequ; [ right | left]; trivial.
              ** rewrite OMEGA in Heqw ; inv Heqw. eapply funspec_sub_trans with f; trivial.
                 exploit (@merge_specs_succeed psi1 f).
                 { apply typesig_of_funspec_sub in Omega; rewrite Omega.
                   apply typesig_of_funspec_sub in PSI; rewrite PSI; trivial. }
                 { apply funspec_sub_cc in Omega; rewrite Omega.
                   apply funspec_sub_cc in PSI; rewrite PSI; trivial. } 
                 intros X; rewrite X. apply (BINARY_intersection_sub3 _ _ _ X).
                 apply funspec_sub_trans with psi; trivial. apply funspec_sub_refl.
        ++ destruct H as [omega [OMEGA Omega]]. specialize (HImports _ _ _ Psi OMEGA). subst omega.
           clear HCi SC1 SC2. unfold JoinedImports.
           exists psi. rewrite find_id_app_char, find_id_filter_char, Psi.
           2:{ specialize (Comp_ctx_LNR c1).  rewrite map_app. apply list_norepet_append_inv. }
           simpl.
           destruct ((in_dec ident_eq i (map fst E2 ++ IntIDs p2))); simpl.
           ** destruct ( Comp_G_dom c2 i) as [X _].
              exploit X; clear X.
              -- clear - i0. apply in_or_app. apply in_app_or in i0. destruct i0; [ right | left]; trivial.
              -- intros X; apply find_id_None_iff in X. contradiction. trivial .
           ** split; trivial.
              exploit (@merge_specs_succeed psi1 f).
                 { apply typesig_of_funspec_sub in Omega; rewrite <- Omega.
                   apply typesig_of_funspec_sub in PSI; rewrite PSI; trivial. }
                 { apply funspec_sub_cc in Omega; rewrite <- Omega.
                   apply funspec_sub_cc in PSI; rewrite PSI; trivial. } 
                 intros X; rewrite X. apply (BINARY_intersection_sub3 _ _ _ X); trivial.
      +(*
      + specialize (Comp_ctx_LNR c2). rewrite map_app. apply list_norepet_append_inv.
      + *)clear HCi. specialize (SC2 _ _ Psi). 
        remember (find_id i G2) as u; symmetry in Hequ; destruct u.
        { apply find_id_In_map_fst in Hequ. rewrite <- ( Comp_G_dom c2) in Hequ.
          destruct SC2 as [? [? ?]]; [| congruence].
          clear - Hequ. apply in_or_app. apply in_app_or in Hequ. destruct Hequ; [ right | left]; trivial. }
        simpl. unfold JoinedImports.
        exists psi. rewrite find_id_app_char, find_id_filter_char, Psi.
        2:{ specialize (Comp_ctx_LNR c1).  rewrite map_app. apply list_norepet_append_inv. }
        simpl.
        destruct ((in_dec ident_eq i (map fst E2 ++ IntIDs p2))); simpl.
        ++ destruct ( Comp_G_dom c2 i) as [X _].
           exploit X; clear X.
           -- clear - i0. apply in_or_app. apply in_app_or in i0. destruct i0; [ right | left]; trivial.
           -- intros X; apply find_id_None_iff in X. contradiction. trivial .
        ++ split; trivial.
      + specialize (Comp_ctx_LNR c2). rewrite map_app. apply list_norepet_append_inv.
   * clear HCi. rewrite G_merge_None_l; trivial.
     2:{ specialize (Comp_ctx_LNR c2). rewrite map_app. apply list_norepet_append_inv. }
     specialize (Comp_G_Exports c2 _ _ Hi).
     remember (find_id i G2 ) as w; destruct w; symmetry in Heqw; trivial; intros.
     destruct H as [tau [Tau TAU]]. unfold JoinedImports. rewrite find_id_app_char, find_id_filter_char.
     remember (find_id i Imports1) as u; symmetry in Hequ; destruct u; simpl.
     + destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)); simpl.
       { apply find_id_None_iff in Heqw. elim Heqw. apply (Comp_G_dom c2 i).
         apply in_or_app. apply in_app_or in i0. destruct i0; [ right | left]; trivial. }
        exists f; split; trivial. 
        specialize (HImports _ _ _ Hequ Tau); subst f. trivial.
     + rewrite find_id_filter_char, Tau; simpl.
       destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)) ; simpl.
       { apply find_id_None_iff in Hequ1. elim Hequ1. apply (Comp_G_dom c1 i).
         apply in_or_app. apply in_app_or in i0. destruct i0; [ right | left]; trivial.
         apply in_app_or in H. destruct H; trivial. apply find_id_None_iff in Hequ. contradiction. }
       exists tau; split; trivial.
       specialize (Comp_ctx_LNR c2). rewrite map_app. apply list_norepet_append_inv.
     + specialize (Comp_ctx_LNR c1). rewrite map_app. apply list_norepet_append_inv.
Qed.
(*Old statement:
Local Lemma G_Exports:
  forall (i : ident) (phi : funspec),
   find_id i Exports = Some phi ->
  exists phi' : funspec, find_id i G = Some phi' /\ funspec_sub phi' phi.
Proof.
 (*TODO: clean up this proof*)
  intros i phi Hi. unfold Exports. subst G.
  assert (HCi := HC i).
  specialize (G_merge_find_id_Some Hi (Comp_Exports_LNR c2)); clear Hi; intros Hi.
  assert (FP := Linked_Functions_preserved _ _ _ Linked i).
  hnf in FP.
  remember (find_id i (Comp_G c1)) as u1; symmetry in Hequ1; destruct u1 as [phi1 |].
  - remember (find_id i (Comp_G c2)) as u2; symmetry in Hequ2; destruct u2 as [phi2 |]. 
    * 
      assert (SigsPhi:typesig_of_funspec phi1 = typesig_of_funspec phi2).
      { apply (HCi phi1 phi2); trivial. }
      specialize (Calling_conventions_match Hequ1 Hequ2); intros CCPhi.

      destruct (G_merge_find_id_SomeSome Hequ1 Hequ2 SigsPhi CCPhi) as [phi' [BI' PHI']].
      rewrite PHI'. exists phi'; split. trivial. clear PHI'.
      apply binaryintersection_sub in BI'.
      destruct BI' as [Phi1' Phi2'].
      remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
      ++ subst phi. clear FP.
         specialize (Comp_G_Exports c1 _ _ Heqq1).
         unfold Comp_G in Hequ1. rewrite Hequ1; intros TAU1.
(*
        ** clear FP. (*   as [tau1 [Tau1 TAU1]].*)
         unfold Comp_G in Hequ1. rewrite Hequ1 in Tau1; inv Tau1.*)
         remember (find_id i Exports2) as q2; symmetry in Heqq2; destruct q2 as [psi2 |].

         2: solve [simpl; eapply @funspec_sub_trans with phi1; trivial ]. 

         specialize (Comp_G_Exports c2 _ _ Heqq2).
         unfold Comp_G in Hequ2. rewrite Hequ2; intros TAU2.

         assert (SigsPsi: typesig_of_funspec psi1 =typesig_of_funspec psi2).
         { clear - SigsPhi TAU1 TAU2. destruct phi1; destruct phi2.
           destruct psi1; destruct TAU1 as [AA1 _].
           destruct psi2; destruct TAU2 as [AA2 _]. simpl in *.
           destruct AA1; destruct AA2; subst; trivial. }
         assert (CCPsi: callingconvention_of_funspec psi1 = callingconvention_of_funspec psi2).
         { clear - CCPhi TAU1 TAU2. apply funspec_sub_cc in TAU1. apply funspec_sub_cc in TAU2. 
           rewrite <- TAU1, <- TAU2; trivial. }
         destruct (G_merge_find_id_SomeSome Heqq1 Heqq2 SigsPsi CCPsi) as [tau' [BI TAU']].
         simpl. rewrite BI. clear - BI Phi1' Phi2' TAU1 TAU2.
         apply (BINARY_intersection_sub3 _ _ _ BI); clear BI.
         apply @funspec_sub_trans with phi1; trivial.
         apply @funspec_sub_trans with phi2; trivial.
      ++ specialize (Comp_G_Exports c2 _ _ Hi).
         unfold Comp_G in Hequ2; rewrite Hequ2; intros TAU2.
         apply @funspec_sub_trans with phi2; trivial. 

    * rewrite (G_merge_find_id_SomeNone Hequ1 Hequ2).
      remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
      ++ subst. eexists; split. reflexivity.
         specialize (Comp_G_Exports c1 _ _ Heqq1). unfold Comp_G in Hequ1; rewrite Hequ1; intros PSI.
         eapply funspec_sub_trans. apply PSI.
         apply type_of_funspec_sub in PSI. clear FP.
         (*clear - Heqq1 Hequ2 c2 PSI.*) remember (find_id i Exports2) as w; symmetry in Heqw; destruct w as [psi2 |].
         -- specialize (Comp_G_Exports c2 _ _ Heqw).
            unfold Comp_G in Hequ2; rewrite Hequ2. intros [phi [PHI Phi]]. simpl.
            remember (binary_intersection psi1 psi2); symmetry in Heqo; destruct o. 2: apply funspec_sub_refl. 
            apply (BINARY_intersection_sub3 _ _ _ Heqo psi1). apply funspec_sub_refl.
            eapply funspec_sub_trans with phi; trivial.
            destruct (SC1 _ _ PHI) as [tau [TAU Tau]].
            { apply find_id_In_map_fst in Hequ1. apply (Comp_G_dom c1) in Hequ1. clear - Hequ1.
              apply in_app_or in Hequ1. apply in_or_app. destruct Hequ1; [ right | left]; trivial. }
            rewrite TAU in Heqq1; inv Heqq1; trivial.
         -- simpl. apply funspec_sub_refl; trivial.
      ++ eexists; split. reflexivity. clear FP.
         unfold Comp_G in Hequ2. specialize (Comp_G_Exports c2 i phi); rewrite Hi, Hequ2.
         intros X. destruct X as [tau [TAU Tau]]; trivial.
         eapply funspec_sub_trans with tau; trivial.
         destruct (SC1 _ _ TAU) as [omega [OMEGA Omega]].
         { apply find_id_In_map_fst in Hequ1. apply (Comp_G_dom c1) in Hequ1. clear - Hequ1.
              apply in_app_or in Hequ1. apply in_or_app. destruct Hequ1; [ right | left]; trivial. }
         congruence. 
  - clear FP. unfold Comp_G in Hequ1.
    remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
    * specialize (Comp_G_Exports c1 _ _ Heqq1); rewrite Hequ1.
      intros X; destruct X as [psi [Psi PSI]].
      rewrite G_merge_None_l; trivial. subst phi.
      remember (find_id i Exports2) as w; symmetry in Heqw; destruct w.
      + specialize (Comp_G_Exports c2 _ _ Heqw); unfold Comp_G.
        remember (find_id i G2) as u; symmetry in Hequ; destruct u; simpl; intros.
        ++ exists f0. split; trivial. clear HCi.
           apply find_id_In_map_fst in Hequ. apply (Comp_G_dom c2) in Hequ.
           destruct (SC2 _ _ Psi) as [omega [OMEGA Omega]].
              ** clear - Hequ. apply in_or_app. apply in_app_or in Hequ. destruct Hequ; [ right | left]; trivial.
              ** rewrite OMEGA in Heqw ; inv Heqw. eapply funspec_sub_trans with f; trivial.
                 exploit (@merge_specs_succeed psi1 f).
                 { apply typesig_of_funspec_sub in Omega; rewrite Omega.
                   apply typesig_of_funspec_sub in PSI; rewrite PSI; trivial. }
                 { apply funspec_sub_cc in Omega; rewrite Omega.
                   apply funspec_sub_cc in PSI; rewrite PSI; trivial. } 
                 intros X; rewrite X. apply (BINARY_intersection_sub3 _ _ _ X).
                 apply funspec_sub_trans with psi; trivial. apply funspec_sub_refl.
        ++ destruct H as [omega [Omega OMEGA]]. specialize (HImports _ _ _ Psi Omega). subst omega.
           clear HCi SC1 SC2. red in FundefsMatch. Comp_Imports_external. intros.  simpl. in Heqr. congruence.


           -- rewrite (@merge_specs_succeed psi1 f) in Heqr. congruence.
              ** clear Heqr. eapply funspec_sub_trans with f; trivial.
           
           exploit (@merge_specs_succeed psi1 f). intros.  simpl. in Heqr. congruence.
BINARY_intersection_sub3
           remember (binary_intersection psi1 f) as r; symmetry in Heqr; destruct r.
           -- eapply funspec_sub_trans. apply H.
              apply (BINARY_intersection_sub3 _ _ _ Heqr). 2: apply funspec_sub_refl.
              apply find_id_In_map_fst in Hequ. apply (Comp_G_dom c2) in Hequ.
              destruct (SC2 _ _ Psi) as [omega [OMEGA Omega]].
              ** clear - Hequ. apply in_or_app. apply in_app_or in Hequ. destruct Hequ; [ right | left]; trivial.
              ** rewrite OMEGA in Heqw ; inv Heqw. eapply funspec_sub_trans with psi; trivial.
           -- rewrite (@merge_specs_succeed psi1 f) in Heqr. congruence.
              ** clear Heqr. eapply funspec_sub_trans with f; trivial.
     
 unfold Comp_G. 
      rewrite G_merge_None_l; trivial. 2: apply c2. Search find_id G_merge. simpl. congruence.  unfold Comp_G in Hequ1; congruence.
    * destruct (Comp_G_Exports c2 _ _ Hi) as [psi2 [Psi2 PSI2]]. unfold Comp_G in *.
      rewrite (G_merge_find_id_NoneSome Hequ1 Psi2).
      eexists; split. reflexivity. trivial. apply (Comp_G_LNR c2).
Qed.*)

Local Lemma MkInitPred:
   forall gv : globals, globals_ok gv -> InitGPred (Vardefs p) gv |-- GP1 gv * GP2 gv.
Proof.
    intros.
  eapply derives_trans. 
  2: apply sepcon_derives; [ apply (Comp_MkInitPred c1 gv) | apply (Comp_MkInitPred c2 gv)]; auto.
  apply InitGPred_join; auto.
Qed.

Local Lemma LNR_E: list_norepet (map fst E).
Proof.
apply G_merge_LNR.
apply (Comp_Externs_LNR c1).
apply (Comp_Externs_LNR c2).
Qed.

Lemma ComponentJoin:
   @Component Espec V E JoinedImports p Exports ((fun gv => GP1 gv * GP2 gv)%logic) G.
Proof.
apply Build_Component with OKp; trivial.
+ apply Condition1.
+ apply LNR_VGI.
+ apply LNR_E.
+ apply LNR_Exports.
+ apply Condition2.
+ apply G_dom.
+ apply G_E.
+ apply G_justified.
+ apply G_Exports.
+ apply MkInitPred.
Qed.

End ComponentJoin.

Definition VSULink_Imports'
 {Espec E1 Imports1 p1 Exports1 GP1 E2 Imports2 p2 Exports2 GP2}
  (vsu1: @VSU Espec E1 Imports1 p1 Exports1 GP1)
  (vsu2: @VSU Espec E2 Imports2 p2 Exports2 GP2)  := 
      filter (fun x => negb (in_dec ident_eq (fst x) (map fst E2 ++ IntIDs p2))) Imports1 ++
      filter (fun x => negb (in_dec ident_eq (fst x) (map fst E1 ++ IntIDs p1 ++ map fst Imports1))) Imports2.

Definition VSULink_Imports_aux (Imports1 Imports2: funspecs) 
   (kill1 kill2: PTree.t unit) :=
  filter (fun x => isNone (kill1 ! (fst x))) Imports1 ++
  filter (fun x => isNone (kill2 ! (fst x))) Imports2.

Definition VSULink_Imports
 {Espec E1 Imports1 p1 Exports1 GP1 E2 Imports2 p2 Exports2 GP2}
  (vsu1: @VSU Espec E1 Imports1 p1 Exports1 GP1)
  (vsu2: @VSU Espec E2 Imports2 p2 Exports2 GP2)  := 
 VSULink_Imports_aux Imports1 Imports2 
    (fold_left (fun m i => PTree.set i tt m) (map fst E2 ++ IntIDs p2) (PTree.empty unit))
    (fold_left (fun m i => PTree.set i tt m) (map fst E1 ++ IntIDs p1 ++ map fst Imports1) (PTree.empty _)).

Lemma VSULink_Imports_eq:
  @VSULink_Imports = @VSULink_Imports'.
Proof.
assert (forall i al,
  isNone
    (fold_left
       (fun (m : PTree.t unit) (i0 : positive) => PTree.set i0 tt m)
       al (PTree.empty unit)) ! i =
   negb (proj_sumbool (in_dec ident_eq i al))). {
intros.
replace (fold_left
              (fun (m : PTree.t unit) (i0 : positive) => PTree.set i0 tt m)
              al (PTree.empty unit))
 with (PTree_Properties.of_list (map (fun i => (i,tt)) al)).
match goal with |- isNone ?A = _ => destruct A eqn:?H end.
apply PTree_Properties.in_of_list in H.
destruct (in_dec ident_eq i al).
reflexivity.
apply (in_map fst) in H.
simpl in H.
rewrite map_map in H.
simpl in H.
rewrite map_id in H. contradiction.
destruct (in_dec ident_eq i al); [ | reflexivity].
simpl.
replace al with (map fst (map (fun i => (i,tt)) al)) in i0
  by (rewrite map_map, map_id; auto).
apply PTree_Properties.of_list_dom in i0.
destruct i0 as [? ?H].
rewrite H in H0. inv H0.
unfold PTree_Properties.of_list.
forget (PTree.empty unit) as m.
revert m; induction al; simpl; auto.
}
unfold VSULink_Imports, VSULink_Imports_aux, VSULink_Imports'.
extensionality Espec.
extensionality E1 Imports1 p1.
extensionality Exports1 GP1.
extensionality E2 Imports2 p2.
extensionality Exports2 GP2.
extensionality v1 v2.
f_equal; f_equal;
extensionality ix; destruct ix as [i x]; simpl; auto.
Qed.

Lemma QPlink_progs_varspecsJoin:
 forall (p1 p2 p : QP.program function)
   (Linked : QPlink_progs p1 p2 = Errors.OK p),
  varspecsJoin (QPvarspecs p1) (QPvarspecs p2) (QPvarspecs p).
Proof.
  intros.
  pose proof (QPlink_progs_globdefs _ _ _ Linked).
  clear - H.
  intro i. apply (merge_PTrees_e i) in H.
  destruct (find_id i (QPvarspecs p1)) eqn:?H.
  rewrite find_id_QPvarspecs in H0. destruct H0 as [? [? ?]]. rewrite H0 in H.
  destruct (find_id i (QPvarspecs p2)) eqn:?H.
  rewrite find_id_QPvarspecs in H2. destruct H2 as [? [? ?]]. rewrite H2 in H.
  destruct H as [? [? ?]]. simpl in H. destruct x,x0; inv H. subst t.
  destruct ((QP.prog_defs p2) ! i) eqn:?H. destruct H as [? [? ?]].
  destruct g; inv H. destruct x,v; inv H5.
  symmetry. rewrite find_id_QPvarspecs; eauto.
  destruct (find_id i (QPvarspecs p2)) eqn:?H.
  apply find_id_QPvarspecs in H1. destruct H1 as [? [? ?]]. subst t.
  rewrite H1 in H.
  destruct (find_id i (QPvarspecs p)) eqn:?H.
  apply find_id_QPvarspecs in H2. destruct H2 as [? [? ?]]. subst t.
  rewrite H2 in H.
  destruct ((QP.prog_defs p1) ! i) eqn:?H.
  destruct H as [? [? ?]]. inv H4. destruct g; inv H. destruct f; inv H5.
  destruct v,x; inv H5. inv H; auto.
  destruct ((QP.prog_defs p1) ! i) eqn:?H.
  destruct H as [? [? ?]]. destruct g; inv H. destruct f; inv H6.
  destruct v,x; inv H6.
  rewrite (proj2 (find_id_QPvarspecs p i (gvar_info x))) in H2.
  inv H2.
  eauto.
  destruct (find_id i (QPvarspecs p)) eqn:?H; auto.
  apply find_id_QPvarspecs in H2. destruct H2 as [? [? ?]]. subst t.
  rewrite H2 in H.
  clear H2.
  destruct ((QP.prog_defs p1) ! i) eqn:?H.
  destruct ((QP.prog_defs p2) ! i) eqn:?H.
  destruct H as [? [? ?]]. inv H4.
  destruct g,g0; inv H.
  destruct f,f0. destruct (function_eq  f f0); inv H5.
  revert H5; simple_if_tac; intro; try discriminate.
  revert H5; simple_if_tac; intro; try discriminate.
  revert H5; simple_if_tac; intro; try discriminate.
  destruct f; inv H5. destruct v,v0; inv H5. inv H.
  rewrite (proj2 (find_id_QPvarspecs p1 i (gvar_info x))) in H0. inv H0.
  eauto.
  destruct ((QP.prog_defs p2) ! i) eqn:?H. inv H.
  rewrite (proj2 (find_id_QPvarspecs p2 i (gvar_info x))) in H1. inv H1.
  eauto.
  inv H.
Qed.

Lemma VSULink 
 {Espec E1 Imports1 p1 Exports1 GP1 E2 Imports2 p2 Exports2 GP2}
  (vsu1: @VSU Espec E1 Imports1 p1 Exports1 GP1)
  (vsu2: @VSU Espec E2 Imports2 p2 Exports2 GP2) 
 (p : QP.program Clight.function)
 (Linked : QPlink_progs p1 p2 = Errors.OK p)
 (FundefsMatch: Fundefs_match p1 p2 Imports1 Imports2)
 (Externs1_Hyp: list_disjoint (map fst E1) (IntIDs p2))
 (Externs2_Hyp: list_disjoint (map fst E2) (IntIDs p1))
 (*one could try to weaken this hypothesis by weakening the second condition to In i (IntIDs p1),
    so that it is possible to delay resolving the spec for an extern in case several modules prove (mergaable but different) specs for it. The present cluase forces one to use match with the first spec one finds*)
 (SC1: forall i phiI, find_id i Imports2 = Some phiI -> In i (map fst E1 ++ IntIDs p1) ->
              exists phiE, find_id i Exports1 = Some phiE /\ funspec_sub phiE phiI)
   (*same comment here*)
 (SC2: forall i phiI, find_id i Imports1 = Some phiI -> In i (map fst E2 ++ IntIDs p2) ->
                          exists phiE, find_id i Exports2 = Some phiE /\ funspec_sub phiE phiI)
 (HImports: forall i phi1 phi2, find_id i Imports1 = Some phi1 -> find_id i Imports2 = Some phi2 -> phi1=phi2) :
 @VSU Espec (G_merge E1 E2) (VSULink_Imports vsu1 vsu2) p (G_merge Exports1 Exports2) (GP1 * GP2)%logic.
Proof. 
  destruct vsu1 as [G1 comp1].
  destruct vsu2 as [G2 comp2].
  exists  (G_merge G1 G2).
  assert (HG1: G1 = Comp_G comp1) by reflexivity.
  assert (HG2: G2 = Comp_G comp2) by reflexivity.
  replace (G_merge G1 G2) with (G_merge (Comp_G comp1) (Comp_G comp2))
    by (clear - HG1 HG2; subst; auto).
  rewrite VSULink_Imports_eq.
  apply ComponentJoin; trivial.
 -
  apply QPvarspecs_norepet.
 -
  apply QPlink_progs_varspecsJoin; auto.
 -
  intros i j ? ? ?; subst j.
  apply In_map_fst_find_id in H; [ | apply QPvarspecs_norepet]. destruct H.
  apply find_id_QPvarspecs in H. destruct H as [? [? ?]]. subst x.
  pose proof (merge_PTrees_e i _ _ _ _ (QPlink_progs_globdefs _ _ _ Linked)).
  rewrite H in H1.
  assert (exists f, (QP.prog_defs p2) ! i = Some (Gfun f)). {
  rewrite !in_app in H0; destruct H0 as [?|[?|?]].
  apply (Comp_Externs comp2) in H0. destruct H0 as [? [? [? [? ?]]]]. eauto.
  apply (Comp_Imports_external comp2) in H0. destruct H0 as [? [? [? [? ?]]]]. eauto.
  apply IntIDs_elim in H0. destruct H0.
  apply PTree.elements_complete in H0. eauto.
 }
  destruct H2. rewrite H2 in H1. destruct H1 as [? [? ?]]. inv H1.
 -
  intros i j ? ? ?; subst j.
  apply In_map_fst_find_id in H; [ | apply QPvarspecs_norepet]. destruct H.
  apply find_id_QPvarspecs in H. destruct H as [? [? ?]]. subst x.
  pose proof (merge_PTrees_e i _ _ _ _ (QPlink_progs_globdefs _ _ _ Linked)).
  rewrite H in H1.
  assert (exists f, (QP.prog_defs p1) ! i = Some (Gfun f)). {
  rewrite !in_app in H0; destruct H0 as [?|[?|?]].
  apply (Comp_Externs comp1) in H0. destruct H0 as [? [? [? [? ?]]]]. eauto.
  apply (Comp_Imports_external comp1) in H0. destruct H0 as [? [? [? [? ?]]]]. eauto.
  apply IntIDs_elim in H0. destruct H0.
  apply PTree.elements_complete in H0. eauto.
 }
  destruct H2. rewrite H2 in H1. destruct H1 as [? [? ?]]. inv H1. destruct x; inv H5.
Qed.
