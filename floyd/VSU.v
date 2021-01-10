Require Import VST.floyd.proofauto.
Require Import VST.veric.Clight_initial_world.
Require Import VST.floyd.assoclists.
Require Import VST.floyd.PTops.
Require Export VST.floyd.QPcomposite.
Require Export VST.floyd.quickprogram.

(* Coercion QPprogram_of_program: program >-> QP.program. *)

Lemma semax_body_subsumespec {cs} V V' F F' f iphi (SB: @semax_body V F cs f iphi)
  (HVF : forall i : positive,
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
    (*(phi : funspec)*) sg cc A1 P1 Q1 Pne1 Qne1 A2 P2 Q2 Pne2 Qne2,
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
Proof. apply binary_intersection'_sub. (*apply binary_intersection'_sound.*) Qed.

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
      && ((*mapsto_memory_block.*)mapsto sh 
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
  var_sizes_ok (*cenv_cs*) (fn_vars f) /\
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

Lemma ExternalInfo_funspec_sub {Espec ge i e ts t c phi}
(SFE: semaxfunc_ExternalInfo Espec ge i e ts t c phi)
(phi' : funspec)
(Fsub : funspec_sub phi phi'):
semaxfunc_ExternalInfo Espec ge i e ts t c phi'.
Proof.
  specialize (type_of_funspec_sub _ _ Fsub).
  specialize (funspec_sub_cc _ _ Fsub). intros CC TS.
  destruct phi; destruct phi'. destruct t0; destruct t1.
  simpl in CC, TS. inv TS. apply TTL7 in H0. subst l0; clear H2.
  specialize (@semax_external_funspec_sub Espec _ _ _ e _ _ _ _ _ _ _ _ _ _ Fsub); intros E.
  destruct SFE as [? [? [? [? [? [? [? ?]]]]]]]. subst t1 c1.
  destruct Fsub as [_ Fsub]. subst l.
Abort. (*
  repeat split; trivial.
  + destruct H3; [ left; trivial | ]. admit. (*empty_type -- add in funspec_sub?*)
  + intros. specialize (Fsub ts0 x).  simpl in Fsub. clear. Print make_ext_rval. apply andp_left2. clear. apply prop_derives. intros.
    unfold rettype_of_type in H.
    if_tac in H; subst.
    - simpl. destruct ret; trivial.
    - destruct ret; simpl in *. 
      * destruct t; try discriminate; simpl in *. red. red.  destruct t; simpl in *. Search step_lemmas.has_opttyp. Print tc_option_val'. specialize (Fsub ts0 x). simpl in Fsub. admit. 
  + eapply E; clear E. 2: eassumption. rewrite H2; clear H2; f_equal. clear.
    rewrite <- TTL2, semax_prog.TTL6; trivial.
Abort.*)

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
  destruct phi. destruct t as [params rt]. simpl in CC1, CC2(*, SIG1, SIG2*). 
  destruct phi1 as [[params1 rt1] c1 A1 P1 Q1 P1ne Q1ne]. simpl in (*SIG1,*) CC1. subst (*sig1*) c1.
  destruct F1_external as [RT1 [C1 [PAR1 [Sig1 [EF1 [ENT1 [EXT1 GFF1]]]]]]].
  destruct phi2 as [[params2 rt2] c2 A2 P2 Q2 P2ne Q2ne]. simpl in (*SIG2,*) CC2. subst (*sig2*) c2.
  destruct F2_external as [RT2 [C2 [PAR2 [Sig2 [EF2 [ENT2 [EXT2 GFF2]]]]]]].
  subst cc rt1 rt2. 
  (*assert (FSM:= binary_intersection_funsigs_match BI). simpl funsig_of_funspec in FSM.*)
  assert (FSM:= @binary_intersection_typesigs _ _ _ BI). simpl typesig_of_funspec in FSM.
  destruct FSM as [FSM1 FSM2].
  inversion FSM1; subst retsig params1; clear FSM1.
  inversion FSM2; subst params2 params; clear FSM2 H1. 
(*  subst rt.*)
(*  assert (RETTY:= binary_intersection_retty BI). unfold return_of_funspec in RETTY. simpl in RETTY; subst rt.*)
 (* assert (ParamTypes12:= funsigs_match_type_of_params FSM). simpl in ParamTypes12. rewrite ParamTypes12 in *; clear Kb5.*)
(*  assert (ArgTypes := binary_intersection_argtypes BI). simpl in ArgTypes.*)
(*Parameter ids:list ident.*)
(* red.
  rewrite <- Kb3 in Hb3. subst ids'.*)

  split3; trivial.
  split3; trivial.
  split3. 
  + unfold binary_intersection in BI. rewrite 2 if_true in BI by trivial. inv BI.
    apply inj_pair2 in H1; subst P. apply inj_pair2 in H2; subst Q. simpl.
 (*  split3.*)
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

(*now in seplog
Lemma Forall2_funspec_sub_refl: forall l, Forall2 funspec_sub l l.
Proof. induction l; constructor; trivial. apply funspec_sub_refl. Qed. 

Lemma Forall2_funspec_sub_trans: forall l1 l2, Forall2 funspec_sub l1 l2 ->
   forall l3, Forall2 funspec_sub l2 l3 -> Forall2 funspec_sub l1 l3.
Proof.
  induction l1; intros; inv H; inv H0; constructor; eauto. 
  eapply funspec_sub_trans; eassumption.
Qed.*)

Lemma subsumespec_app l1 l2 k1 k2 i
          (L1K1: subsumespec (find_id i l1) (find_id i k1)) 
          (L2K2: subsumespec (find_id i l2) (find_id i k2))
          (D:list_disjoint (map fst l2) (map fst k1)):
      subsumespec (find_id i (l1++l2)) (find_id i (k1++k2)).
Proof.
  red. rewrite ! find_id_app_char. (* specialize (L1K1 i). specialize (L2K2 i).*)
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
  red. rewrite ! find_id_app_char. (* specialize (LK i).*) destruct (find_id i l); trivial.
  destruct LK as [phi [? ?]]. rewrite H. exists phi; split; trivial.
Qed.
 
Lemma subsumespec_app_right_right l k1 k2 i
          (LK: subsumespec (find_id i l) (find_id i k2))
          (Hi: find_id i k1= None):
      subsumespec (find_id i l) (find_id i (k1++k2)).
Proof.
  red. rewrite ! find_id_app_char, Hi. (* specialize (LK i).*) destruct (find_id i l); trivial.
Qed.

Lemma subsumespec_app_left l1 l2 k i
          (LK1: subsumespec (find_id i l1) (find_id i k)) 
          (LK2: find_id i l1 = None -> subsumespec (find_id i l2) (find_id i k)):
      subsumespec (find_id i (l1++l2)) (find_id i k).
Proof.
  red. rewrite ! find_id_app_char. (* specialize (LK1 i). specialize (LK2 i).*)
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
Record Component {Espec:OracleKind}
      (E Imports: funspecs) (p: QP.program Clight.function) (Exports: funspecs) (GP: globals -> mpred) (G: funspecs) := {
  Comp_prog_OK: QPprogram_OK p;
  Comp_Imports_external: forall i, In i (map fst Imports) -> 
                         exists f ts t cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc));

  Comp_cs: compspecs := compspecs_of_QPcomposite_env _ (proj2 Comp_prog_OK);
  Comp_ExternsImports_LNR: list_norepet (map fst (E++Imports));

  Comp_Exports_LNR: list_norepet (map fst Exports);

  (*VSTexternals are External functions in CompCert*)
  Comp_Externs: forall i, In i (map fst E) -> 
                exists f ts t cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc));

  Comp_G_dom: forall i, In i (IntIDs p ++ (map fst E)) <-> In i (map fst G);
  Comp_G_LNR: list_norepet (map fst G);
  Comp_G_E: forall i, In i (map fst E) -> find_id i E = find_id i G;
  Comp_G_justified: forall i phi fd,
                    PTree.get i (QP.prog_defs p) = Some (Gfun fd) ->
                    find_id i G = Some phi ->
                    @SF Espec Comp_cs (QPvarspecs p) (QPglobalenv p) (Imports ++ G) i fd phi;

  Comp_G_Exports: forall i phi (E: find_id i Exports = Some phi), 
                  exists phi', find_id i G = Some phi' /\ funspec_sub phi' phi;

  Comp_MkInitPred: forall gv,   globals_ok gv -> InitGPred (Vardefs p) gv |-- GP gv
}.

Definition Comp_prog {Espec E Imports p Exports GP G} (c:@Component Espec E Imports p Exports GP G):= p.
Definition Comp_G {Espec E Imports p Exports GP G} (c:@Component Espec E Imports p Exports GP G):= G.

Definition VSU {Espec} E Imports p Exports GP:=
  sigT (fun G => @Component Espec E Imports p Exports GP G).
 
Arguments Comp_Imports_external {Espec E Imports p Exports GP G} c.
Arguments Comp_prog_OK {Espec E Imports p Exports GP G} c.
Arguments Comp_cs {Espec E Imports p Exports GP G} c.
Arguments Comp_ExternsImports_LNR {Espec E Imports p Exports GP G} c.
Arguments Comp_Exports_LNR {Espec E Imports p Exports GP G} c.
Arguments Comp_Externs {Espec E Imports p Exports GP G} c.
Arguments Comp_G_dom {Espec E Imports p Exports GP G} c.
Arguments Comp_G_LNR {Espec E Imports p Exports GP G} c.
Arguments Comp_G_justified {Espec E Imports p Exports GP G} c.
Arguments Comp_G_Exports {Espec E Imports p Exports GP G} c.
Arguments Comp_G_E {Espec E Imports p Exports GP G} c.
Arguments Comp_MkInitPred {Espec E Imports p Exports GP G} c.

Section Component.
Variable Espec: OracleKind.
Variable E Imports: funspecs.
Variable p: QP.program Clight.function.
Variable Exports: funspecs.
Variable GP: globals -> mpred.
Variable G: funspecs.

Variable c: @Component Espec E Imports p Exports GP G.

Lemma Comp_Imports_LNR: list_norepet (map fst Imports).
Proof.
  specialize (Comp_ExternsImports_LNR c). rewrite map_app.
  apply list_norepet_append_right.
Qed. 

Lemma Comp_Externs_LNR: list_norepet (map fst E).
Proof.
  specialize (Comp_ExternsImports_LNR c). rewrite map_app.
  apply list_norepet_append_left.
Qed.

Lemma Comp_E_in_G_find: forall i phi, find_id i E = Some phi -> find_id i (Comp_G c) = Some phi.
Proof. intros. rewrite <- (Comp_G_E c); trivial. apply find_id_In_map_fst in H; trivial. Qed.

Lemma Comp_E_in_G: forall {i}, In i (map fst E) -> In i (map fst (Comp_G c)).
Proof. intros. apply In_map_fst_find_id in H. destruct H.
  apply Comp_E_in_G_find in H. apply find_id_In_map_fst in H; trivial. apply Comp_Externs_LNR.
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
  specialize Comp_Externs_LNR; specialize Comp_LNR_Interns; intros.
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
  intros. apply (Comp_G_Exports c) in H. destruct H as [psi [H _]].
  apply Comp_G_in_Fundefs' in H; trivial.
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
Proof. specialize (Comp_ExternsImports_LNR c). rewrite map_app, list_norepet_app; intros X; apply X. Qed.

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
  apply (Comp_G_LNR c).
  apply Comp_G_disjoint_from_Imports.
Qed.

Lemma Comp_G_disjoint_from_Imports_find_id {i phi} (Hi: find_id i Imports = Some phi): 
      find_id i (Comp_G c) = None.
Proof. apply (list_disjoint_map_fst_find_id1 Comp_G_disjoint_from_Imports _ _ Hi). Qed.

Lemma Comp_entail {GP'} (H: forall gv, GP gv |-- GP' gv):
      @Component Espec E Imports p Exports GP' G.
Proof. intros. destruct c. econstructor; try assumption.
apply Comp_G_justified0.
 intros; eapply derives_trans. apply Comp_MkInitPred0; auto. cancel.
Qed.

Lemma Comp_entail_starTT:
      @Component Espec E Imports p Exports (GP * TT)%logic G.
Proof. intros. apply Comp_entail. intros; simpl; apply sepcon_TT. Qed.

Lemma Comp_entail_TT:
      @Component Espec E Imports p Exports TT G.
Proof. intros. eapply Comp_entail. intros; simpl. apply TT_right. Qed.

Lemma Comp_entail_split {GP1 GP2} (H: forall gv, GP gv |-- (GP1 gv * GP2 gv)%logic):
      @Component Espec E Imports p Exports (fun gv => GP1 gv * TT)%logic G.
Proof. intros. eapply Comp_entail. intros; simpl.
  eapply derives_trans. apply H. cancel.
Qed.

Lemma Comp_Imports_sub Imports' (HI1: map fst Imports' = map fst Imports)
      (HI2: Forall2 funspec_sub (map snd Imports') (map snd Imports)): 
      @Component Espec E Imports' p Exports GP G.
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
  assert (AUX2: forall V i, sub_option ((make_tycontext_g V (Imports ++ Comp_G c)) ! i)
                                     ((make_tycontext_g V (Imports' ++ Comp_G c)) ! i)).
  { intros. specialize (AUX1 i).
    remember ((make_tycontext_g V (Imports ++ Comp_G c)) ! i) as q; symmetry in Heqq; destruct q; simpl; trivial.
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
+ apply (Comp_MkInitPred c).
Qed.

(*Together with Lemma  Comp_Exports_suboption, this lemma means we can abstract or hide exports*)
Lemma Comp_Exports_sub1 Exports' (HE1: map fst Exports' = map fst Exports)
      (HE2: Forall2 funspec_sub (map snd Exports) (map snd Exports')):
      @Component Espec E Imports p Exports' GP G.
Proof.
  eapply Build_Component; try apply c.
+ rewrite HE1; apply c. 
+ intros i phi Hi. rename phi into phi'.
  assert (X: exists phi, find_id i Exports = Some phi /\ funspec_sub phi phi').
  { clear - HE1 HE2 Hi. eapply find_funspec_sub; eassumption. }
  destruct X as [phi [Phi PHI]].
  destruct (Comp_G_Exports c _ _ Phi) as [psi [Psi PSI]].
  exists psi; split; [ trivial | eapply funspec_sub_trans; eassumption ].
+apply (Comp_MkInitPred c).
Qed.

Lemma Comp_Exports_sub2 Exports' (LNR: list_norepet (map fst Exports'))
      (HE2: forall i, sub_option (find_id i Exports') (find_id i Exports)):
      @Component Espec E Imports p Exports' GP G.
Proof.
  eapply Build_Component (*with (Comp_G c)*); try apply c; trivial.
+ intros i phi' Hi. specialize (HE2 i). rewrite Hi in HE2; simpl in HE2.
  apply c; trivial.
+apply (Comp_MkInitPred c).
Qed.

Definition funspecs_sqsub Exp Exp' :=
  forall i phi', find_id i Exp' = Some phi' ->
         exists phi, find_id i Exp = Some phi /\ funspec_sub phi phi'.

Lemma Comp_Exports_sub Exports' (LNR: list_norepet (map fst Exports'))
      (HE2: funspecs_sqsub Exports Exports'):
      @Component Espec E Imports p Exports' GP G.
Proof.
  eapply Build_Component (*with (Comp_G c)*); try apply c; trivial.
  intros i phi' Hi. destruct (HE2 _ _ Hi) as [phi [H1 H2]].
  apply (Comp_G_Exports c) in H1; destruct H1 as [psi [H3 H4]].
  exists psi; split; trivial. eapply funspec_sub_trans; eassumption.
 apply (Comp_MkInitPred c).
Qed.

End Component.

Arguments Comp_G_LNR {Espec E Imports p Exports GP G} c.
Arguments Comp_ctx_LNR {Espec E Imports p Exports GP G} c.
Arguments Comp_G_disjoint_from_Imports {Espec E Imports p Exports GP G} c.
Arguments Comp_G_disjoint_from_Imports_find_id {Espec E Imports p Exports GP G} c.
Arguments Comp_Interns_disjoint_from_Imports {Espec E Imports p Exports GP G} c.
Arguments Comp_Exports_in_progdefs {Espec E Imports p Exports GP G} c.

Arguments Comp_Externs_LNR {Espec E Imports p Exports GP G} c.
Arguments Comp_Imports_in_Fundefs {Espec E Imports p Exports GP G} c.
Arguments Comp_Exports_in_Fundefs {Espec E Imports p Exports GP G} c.
Arguments Comp_Imports_in_progdefs {Espec E Imports p Exports GP G} c.
Arguments Comp_Exports_in_progdefs {Espec E Imports p Exports GP G} c.

Arguments Comp_G_intern {Espec E Imports p Exports GP G} c.
Arguments Comp_G_extern {Espec E Imports p Exports GP G} c.

Arguments Comp_Imports_LNR {Espec E Imports p Exports GP G} c.
Arguments LNR_Internals_Externs {Espec E Imports p Exports GP G} c.
Arguments Comp_G_in_Fundefs {Espec E Imports p Exports GP G} c.
Arguments Comp_G_in_Fundefs' {Espec E Imports p Exports GP G} c.
Arguments Comp_E_in_G {Espec E Imports p Exports GP G} c.
Arguments Comp_E_in_G_find {Espec E Imports p Exports GP G} c.
Arguments Comp_G_elim {Espec E Imports p Exports GP G} c.
Arguments Comp_G_in_progdefs {Espec E Imports p Exports GP G} c.
Arguments Comp_G_in_progdefs' {Espec E Imports p Exports GP G} c.
Arguments Comp_Imports_sub {Espec E Imports p Exports GP G} c.
Arguments Comp_Exports_sub {Espec E Imports p Exports GP G} c.
Arguments Comp_entail {Espec E Imports p Exports GP G} c.

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
        (*     (SIG: funsigs_match (funsig_of_funspec phi1) (funsig_of_funspec phi2) = true)*)
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
    typesig_of_funspec phi1 = typesig_of_funspec phi2
    (*funsigs_match (funsig_of_funspec phi1) (funsig_of_funspec phi2) = true *)/\
    callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
  (*(pLNR1: params_LNR (find_id i l1))*):
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

Lemma HContexts {Espec
      E1 Imports1 Exports1 E2 Imports2 Exports2 p1 p2 p GP1 GP2 G1 G2}
      (c1: @Component Espec E1 Imports1 p1 Exports1 GP1 G1)
      (c2: @Component Espec E2 Imports2 p2 Exports2 GP2  G2)
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

Lemma cenv_cspecs_sub: (* Not true *)
 forall cs cs', cenv_sub (@cenv_cs cs) (@cenv_cs cs') -> 
cspecs_sub cs cs'.
Proof.
intros.
split; auto.
split; hnf; simpl.
intros.
hnf. destruct ((@ha_env_cs cs) ! i) eqn:?H; auto.
specialize (H i). hnf in H.
destruct (proj2 (@ha_env_cs_complete cs i)) as [co ?].
eauto.
rewrite H1 in H.
pose proof (@ha_env_cs_consistent cs i co z H1 H0).
destruct (proj1 (@ha_env_cs_complete cs' i)).
eauto.
pose proof (@ha_env_cs_consistent cs' i co x H H3).
Abort.

Section ComponentJoin.
Variable Espec: OracleKind.
Variable E1 Imports1 Exports1 G1 E2 Imports2 Exports2 G2: funspecs.
Variable p1 p2: QP.program Clight.function.
Variable GP1 GP2: globals -> mpred.
Variable c1: @Component Espec E1 Imports1 p1 Exports1 GP1 G1.
Variable c2: @Component Espec E2 Imports2 p2 Exports2 GP2 G2.

Variable p: QP.program Clight.function.
Variable Linked : QPlink_progs p1 p2 = Errors.OK p.

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
Variable SC1: forall i phiI, find_id i Imports2 = Some phiI -> In i (map fst E1 ++ IntIDs p1) ->
              exists phiE, find_id i Exports1 = Some phiE /\ funspec_sub phiE phiI.

(*same comment here*)
Variable SC2: forall i phiI, find_id i Imports1 = Some phiI -> In i (map fst E2 ++ IntIDs p2) ->
                          exists phiE, find_id i Exports2 = Some phiE /\ funspec_sub phiE phiI.

Variable HImports: forall i phi1 phi2, find_id i Imports1 = Some phi1 -> find_id i Imports2 = Some phi2 -> phi1=phi2.

Definition Imports := 
                     filter (fun x => negb (in_dec ident_eq (fst x) (map fst E2 ++ IntIDs p2))) Imports1 ++
                     filter (fun x => negb (in_dec ident_eq (fst x) (map fst E1 ++ IntIDs p1 ++ map fst Imports1))) Imports2.

Definition Exports := G_merge Exports1 Exports2.

Lemma LNR_Imports: list_norepet (map fst Imports).
Proof. unfold Imports. subst. clear - c1 c2. rewrite map_app, list_norepet_app; split3.
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

Lemma Imports_in_Fundefs: forall x, In x (map fst Imports) ->
     is_funct_in x p1 \/ is_funct_in x p2.
Proof. unfold Imports. clear - c1 c2; intros. 
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

Lemma Exports_sqsub1: funspecs_sqsub Exports Exports1.
Proof.
  unfold Exports.
  clear - c1 c2 FundefsMatch Linked.
  subst; apply G_merge_sqsub1. intros; split.

+ apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
   apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]].
  specialize (HC i _ _ Hpsi1 Hpsi2). 
  clear - Sub1 Sub2.
  destruct psi1; destruct phi1. destruct Sub1 as [[? ?] _]; subst; simpl.
  destruct psi2; destruct phi2. destruct Sub2 as [[? ?] _]; subst; simpl. trivial.
+ apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
  apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]].
  apply funspec_sub_cc in Sub1.
  apply funspec_sub_cc in Sub2. 
  rewrite <- Sub1, <- Sub2; clear Sub1 Sub2.
  apply (Calling_conventions_match Hpsi1 Hpsi2).
Qed.

Lemma Exports_sqsub2: funspecs_sqsub Exports Exports2.
Proof.
  unfold Exports.
  clear - c1 c2 Linked FundefsMatch.
  subst; apply G_merge_sqsub2; [ apply (Comp_Exports_LNR c2) | intros; split ].
+ apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
  apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]]. 
  specialize (HC i _ _ Hpsi1 Hpsi2). 
  clear - Sub1 Sub2.
  destruct psi1; destruct phi1. destruct Sub1 as [[? ?] _]; subst; simpl.
  destruct psi2; destruct phi2. destruct Sub2 as [[? ?] _]; subst; simpl. trivial.
+ apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
  apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]].
  apply funspec_sub_cc in Sub1.
  apply funspec_sub_cc in Sub2. 
  rewrite <- Sub1, <- Sub2; clear Sub1 Sub2.
  apply (Calling_conventions_match Hpsi1 Hpsi2).
Qed.

Lemma Exports_sqsub3 X
      (H1: funspecs_sqsub X Exports1) (H2: funspecs_sqsub X Exports2):
funspecs_sqsub X Exports.
Proof. clear - H1 H2 c1 c2 Linked FundefsMatch.
  unfold Exports; apply G_merge_sqsub3; trivial.
+  apply (Comp_Exports_LNR c2).
+ intros; split.
  - apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
    apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]]. 
    specialize (HC i _ _ Hpsi1 Hpsi2). 
    clear - Sub1 Sub2.
    destruct psi1; destruct phi1. destruct Sub1 as [[? ?] _]; subst; simpl.
    destruct psi2; destruct phi2. destruct Sub2 as [[? ?] _]; subst; simpl. trivial.
  - apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
    apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]].
    apply funspec_sub_cc in Sub1.
    apply funspec_sub_cc in Sub2. 
    rewrite <- Sub1, <- Sub2; clear Sub1 Sub2.
    apply (Calling_conventions_match Hpsi1 Hpsi2).
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
  destruct v, v0.
  match type of H8 with  (if ?A then _ else _) = _ => destruct A eqn:?H; inv H8 end; auto.
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

Lemma ComponentJoin:
   @Component Espec (G_merge E1 E2) Imports p Exports ((fun gv => GP1 gv * GP2 gv)%logic) (G_merge (Comp_G c1) (Comp_G c2)).
Proof.
  set (E := G_merge E1 E2).
  assert (LMR_Imp:= LNR_Imports).
  assert (LMR_Exp:= LNR_Exports).
  set (G := G_merge (Comp_G c1) (Comp_G c2)).

  assert (DOM_G: forall i, In i (map fst G) ->
          In i (map fst (Comp_G c1 ++ Comp_G c2))).
  { intros. subst G. rewrite G_merge_dom, map_app in H.
    rewrite map_app. apply in_app_or in H. apply in_or_app.
    destruct H.
    + left; trivial. 
    + apply list_in_map_inv in H. destruct H as [[j phi] [JJ J]]; simpl in JJ; subst j.
      apply filter_In in J; destruct J as [J1 J2]. apply (in_map fst) in J1; right; trivial. } 

  assert (G_in_Fundefs: forall i, 
          In i (map fst G) -> is_funct_in i p1 \/ is_funct_in i p2).
  { subst G; clear - c1 c2; intros. apply G_merge_InDom in H; [  | apply (Comp_G_LNR c1)].
    destruct H as [H | H].
    apply Comp_G_in_Fundefs in H. destruct H. left; hnf; rewrite H; auto.
    destruct H.
    apply Comp_G_in_Fundefs in H0. destruct H0. right; hnf; rewrite H0; auto. }

  assert (LNR_E_Imports: list_norepet (map fst (E ++ Imports))).
  { unfold E; unfold Imports.
    rewrite map_app, list_norepet_app; split3; trivial.
    - unfold G_merge. rewrite map_app, list_norepet_app; split3. 
      * rewrite G_merge_aux_dom. apply (Comp_Externs_LNR c1).
      * apply list_norepet_map_fst_filter. apply (Comp_Externs_LNR c2).
      * rewrite G_merge_aux_dom. do 5 intros ?; subst. clear - c1 H H0.
        apply (list_in_map_inv) in H0. destruct H0 as [[j phi] [J Phi]]; simpl in J; subst j.
        apply filter_In in Phi; destruct Phi.
        apply In_map_fst_find_id in H. destruct H as [psi Psi]. rewrite Psi in H1; discriminate.
        apply (Comp_Externs_LNR c1).
    - unfold G_merge. rewrite 2 map_app. apply list_disjoint_app_R; apply list_disjoint_app_L.
      * clear - c1. simpl. rewrite G_merge_aux_dom. specialize (Comp_ExternsImports_LNR c1). rewrite map_app, list_norepet_app.
        intros [? [? ?]]. eapply list_disjoint_mono. apply H1. 2: trivial. 
        clear.  intros. apply in_map_iff. apply in_map_iff in H. destruct H as [[j phi] [J PHI]]. simpl in J; subst.
         apply filter_In in PHI. destruct PHI. exists (x,phi); split; trivial.
      * clear. do 5 intros ?; subst.  apply in_map_iff in H. destruct H as [[j phi] [J PHI]]. simpl in J; subst. 
        apply in_map_iff in H0. destruct H0 as [[j psi] [J PSI]]. simpl in J; subst.
        apply filter_In in PHI; destruct PHI as [PHI1 PHI2]. apply filter_In in PSI; destruct PSI as [PSI1 PSI2]. simpl in *. 
        destruct (in_dec ident_eq y (map fst E2 ++IntIDs p2)); simpl in *. discriminate. 
        elim n. apply (in_map fst) in PHI1. apply in_or_app. left. apply PHI1. 
      * clear. rewrite G_merge_aux_dom.
        do 5 intros ?; subst. apply in_map_iff in H0. destruct H0 as [[j phi] [J PHI]]. simpl in J; subst.
         apply filter_In in PHI. simpl in PHI. destruct PHI. apply negb_true_iff in H1. 
         destruct (in_dec ident_eq y (map fst E1 ++ IntIDs p1 ++ map fst Imports1)); simpl in H1. discriminate.
         apply n. apply in_or_app. left; trivial.
      * clear - c2. specialize (Comp_ExternsImports_LNR c2). rewrite map_app, list_norepet_app. intros [? [? ?]]. 
        eapply list_disjoint_mono. apply H1.
        + clear. intros. apply in_map_iff. apply in_map_iff in H. destruct H as [[j phi] [J PHI]]. simpl in J; subst.
          apply filter_In in PHI. destruct PHI. exists (x,phi); split; trivial.
        + clear. intros. apply in_map_iff. apply in_map_iff in H. destruct H as [[j phi] [J PHI]]. simpl in J; subst.
          apply filter_In in PHI. destruct PHI. exists (x,phi); split; trivial. }

  assert (LNR_G: list_norepet (map fst G)).
  { subst G; clear.
    apply G_merge_LNR; [ apply (Comp_G_LNR c1) | apply (Comp_G_LNR c2)]. }

  assert (Imports_G_disjoint: list_disjoint (map fst Imports) (map fst G)).
  { clear; unfold Imports; subst G. do 5 intros ?; subst.
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
        - apply Comp_G_elim in HH1. destruct HH1. left; apply H0. destruct H0 as [? [? [f Hf]]]. right.
          apply in_or_app. left; trivial.
        - apply in_map_fst in H; elim ((Comp_G_disjoint_from_Imports c2) i i); trivial. }

  specialize (Comp_G_justified c2); intros JUST2. specialize (Comp_G_justified c1); intros JUST1.

assert (Condition1: forall i, In i (map fst Imports) ->
        exists (f : external_function) (ts : typelist) (t : type) (cc : calling_convention),
        PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc))). 
{ unfold Imports; clear - c1 c2 Linked. intros. rewrite map_app in H. apply in_app_or in H; destruct H.
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
    * eauto. }

assert (Condition2: forall i : ident, In i (map fst E) ->
        exists ef ts t cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External ef ts t cc))).
{ intros; unfold E. 
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
  - apply (Comp_Externs_LNR c1). }

assert ( SUBSUME1 : forall i : ident,
           subsumespec (find_id i (Imports1 ++ Comp_G c1)) (find_id i (Imports ++ G))).
{ unfold Imports; subst G; intros i. specialize (@Calling_conventions_match i).
  assert (HCi := HC i).
  clear - c1 c2 HCi Externs2_Hyp Externs1_Hyp SC1 SC2 JUST1 JUST2. 
  intros CC. apply subsumespec_app_left; intros.
           { rewrite ! find_id_app_char. 
             remember (find_id i Imports1) as q1; symmetry in Heqq1; destruct q1 as [phi1 |]; simpl; trivial.
             specialize (list_disjoint_map_fst_find_id1 (Comp_G_disjoint_from_Imports c1) _ _ Heqq1); intros.
             rewrite G_merge_None_l; trivial. 2: apply c2.
             rewrite find_id_filter_char, Heqq1 by apply (Comp_Imports_LNR c1); simpl.
             destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)); simpl.
             2: exists phi1; split; [ reflexivity | apply funspec_sub_si_refl; trivial].
             rewrite find_id_filter_char by apply (Comp_Imports_LNR c2); simpl.
             destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)); simpl.
             + apply find_id_None_iff in H.
               remember (find_id i (Comp_G c2)) as w2; symmetry in Heqw2; destruct w2 as [psi2 |].
               - exists psi2; split. destruct (find_id i Imports2); trivial.
                 destruct (SC2 _ _ Heqq1 i0) as [tau2 [Tau2 SubTau]].
                 apply funspec_sub_sub_si. apply @funspec_sub_trans with tau2; trivial.
                 destruct (Comp_G_Exports c2 _ _ Tau2) as [omega [Omega SubOM]].
                 unfold Comp_G in Heqw2; rewrite Heqw2 in Omega; inv Omega; trivial.
               - destruct (SC2 _ _ Heqq1 i0) as [tau2 [TAU Tau]]. 
                 destruct (Comp_G_Exports c2 _ _ TAU) as [omega [Omega OM]].
                 clear - Heqw2 Omega. unfold Comp_G in Heqw2; congruence.
             + destruct (SC2 _ _ Heqq1 i0) as [tau2 [TAU Tau]]. 
               destruct (Comp_G_Exports c2 _ _ TAU) as [omega [Omega OM]]; unfold Comp_G; rewrite Omega.
               specialize (Comp_G_disjoint_from_Imports c2); intros.
               rewrite (list_disjoint_map_fst_find_id2 (Comp_G_disjoint_from_Imports c2) _ _ Omega).
               exists omega; split; trivial. apply funspec_sub_sub_si. apply @funspec_sub_trans with tau2; trivial. }
           { remember (find_id i (Comp_G c1)) as d; symmetry in Heqd; destruct d as [phi1 |]; simpl; trivial.
               rewrite!  find_id_app_char, find_id_filter_None_I; [ | trivial | apply (Comp_Imports_LNR c1) ].
               rewrite find_id_filter_char by apply (Comp_Imports_LNR c2); simpl.
               remember (find_id i Imports2) as w2; symmetry in Heqw2; destruct w2 as [psi2 |]; simpl.
               - destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)); simpl.
                 * rewrite (G_merge_find_id_SomeNone Heqd (list_disjoint_map_fst_find_id1 (Comp_G_disjoint_from_Imports c2) _ _ Heqw2)).
                   eexists; split. reflexivity. apply funspec_sub_si_refl; trivial.
                 * apply find_id_In_map_fst in Heqd. apply (Comp_G_dom c1) in Heqd.
                   elim n; clear - Heqd. rewrite app_assoc. apply in_or_app. left; apply in_app_or in Heqd; apply in_or_app. destruct Heqd; auto.
               - remember (find_id i (Comp_G c2)) as q2; destruct q2 as [phi2 |]; symmetry in Heqq2; simpl; trivial.
                 * destruct (G_merge_find_id_SomeSome Heqd Heqq2) as [phi [BI PHI]].
                   { apply HCi; trivial. }
                   { auto. } 
                   rewrite PHI. exists phi; split; trivial. apply binaryintersection_sub in BI. apply funspec_sub_sub_si.
                   apply BI. 
                 * rewrite G_merge_None_r, Heqd; trivial. exists phi1. split; trivial. apply funspec_sub_si_refl; trivial.
                   apply (Comp_G_LNR c2). }
}

assert ( SUBSUME2 : forall i : ident,
           subsumespec (find_id i (Imports2 ++ Comp_G c2))
             (find_id i (Imports ++ G))). 
    { intros i. specialize (@Calling_conventions_match i).
      intros CC.
      assert (HCi := HC i).
      remember (find_id i (Imports2 ++ Comp_G c2)) as u; symmetry in Hequ; destruct u as [phi2 |]; simpl; [| trivial].
      rewrite find_id_app_char in Hequ.
      unfold Imports. rewrite <- app_assoc, ! find_id_app_char, ! find_id_filter_char; try apply (Comp_Imports_LNR c2) ; try apply (Comp_Imports_LNR c1).
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
                  destruct (Comp_G_Exports c1 _ _ EXP1) as [psi1 [G1i Psi1]].
                  eexists; split. eassumption. apply funspec_sub_sub_si.
                  apply @funspec_sub_trans with phi1; trivial.
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
          apply in_app_or in Hequ; destruct Hequ; auto. }

  assert (LNR4_V1 : list_norepet
                  (map fst (QPvarspecs p1) ++ map fst (Imports ++ G))). {
    clear - Linked Imports_G_disjoint LNR_G LMR_Imp.
    apply list_norepet_app; split3.
    apply QPvarspecs_norepet.
    rewrite map_app.
    apply list_norepet_app; split3; auto.
    rewrite map_app.
    apply list_disjoint_app_R.
    -
     intros i j ? ? ?; subst j.
     apply Imports_in_Fundefs in H0.
     pose proof (QPlink_progs_globdefs _ _ _ Linked).
     apply (merge_PTrees_e i) in H1.
     apply In_map_fst_find_id in H; [ | apply QPvarspecs_norepet].
     destruct H as [g ?].
     apply find_id_QPvarspecs in H.
     destruct H as [v [? ?]].
     unfold is_funct_in in H0.
     rewrite H in *.
     destruct H0; try contradiction.
     destruct ((QP.prog_defs p2) ! i); try contradiction.
     destruct g0; try contradiction.
     destruct H1 as [x [? ?]].
     destruct v; inv H1.
  -
    intros i j ? ? ?. subst j.
    apply G_merge_InDom in H0; [ | apply (Comp_G_LNR c1)].
     apply In_map_fst_find_id in H; [ | apply QPvarspecs_norepet].
     destruct H as [g ?].
     apply find_id_QPvarspecs in H.
     destruct H as [v [? ?]].
    destruct H0 as [?|[? ?]].
    apply Comp_G_in_Fundefs in H0; destruct H0.
    congruence.
    apply Comp_G_in_Fundefs in H2; destruct H2.
     pose proof (QPlink_progs_globdefs _ _ _ Linked).
     apply (merge_PTrees_e i) in H3.
    rewrite H,H2 in H3.
    destruct H3 as [? [? ?]].
    simpl in H3. destruct v; inv H3.
 }
  assert (LNR4_V2 : list_norepet
                  (map fst (QPvarspecs p2) ++ map fst (Imports ++ G))). {
    clear - Linked Imports_G_disjoint LNR_G LMR_Imp.
    apply list_norepet_app; split3.
    apply QPvarspecs_norepet.
    rewrite map_app.
    apply list_norepet_app; split3; auto.
    rewrite map_app.
    apply list_disjoint_app_R.
    -
     intros i j ? ? ?; subst j.
     apply Imports_in_Fundefs in H0.
     pose proof (QPlink_progs_globdefs _ _ _ Linked).
     apply (merge_PTrees_e i) in H1.
     apply In_map_fst_find_id in H; [ | apply QPvarspecs_norepet].
     destruct H as [g ?].
     apply find_id_QPvarspecs in H.
     destruct H as [v [? ?]].
     unfold is_funct_in in H0.
     rewrite H in *.
     destruct H0; try contradiction.
     destruct ((QP.prog_defs p1) ! i); try contradiction.
     destruct g0; try contradiction.
     destruct H1 as [x [? ?]].
    simpl in H1. destruct f; inv H1.
  -
    intros i j ? ? ?. subst j.
    apply G_merge_InDom in H0; [ | apply (Comp_G_LNR c1)].
     apply In_map_fst_find_id in H; [ | apply QPvarspecs_norepet].
     destruct H as [g ?].
     apply find_id_QPvarspecs in H.
     destruct H as [v [? ?]].
    destruct H0 as [?|[? ?]].
    apply Comp_G_in_Fundefs in H0; destruct H0.
     pose proof (QPlink_progs_globdefs _ _ _ Linked).
     apply (merge_PTrees_e i) in H2.
    rewrite H,H0 in H2.
    destruct H2 as [? [? ?]].
    simpl in H2.
    destruct x; inv H2.
    apply Comp_G_in_Fundefs in H2; destruct H2.
    congruence.
   }
  assert (LNR2 : list_norepet
         (map fst (QPvarspecs p) ++ map fst (Imports ++ G))). {
     clear - Linked LNR4_V1 LNR4_V2.
     pose proof (QPlink_progs_globdefs _ _ _ Linked).
     apply list_norepet_app in LNR4_V1; destruct LNR4_V1 as [? [? ?]].
     apply list_norepet_app in LNR4_V2; destruct LNR4_V2 as [? [? ?]].
     apply list_norepet_app; split3; auto.
     apply QPvarspecs_norepet.
     forget (map fst (Imports ++ G)) as IG.
     clear - H H2 H5.
     intros i j ? ? ?. subst j. specialize (H2 i i). specialize (H5 i i).
     apply (merge_PTrees_e i) in H.
     apply In_map_fst_find_id in H0; [ | apply QPvarspecs_norepet].
     destruct H0.
     apply find_id_QPvarspecs in H0.
     destruct H0 as [? [? ?]].
     rewrite H0 in H.
     destruct ( (QP.prog_defs p1) ! i) eqn:?H;
     destruct ( (QP.prog_defs p2) ! i) eqn:?H.
     destruct H as [? [? ?]]. inv H7.
     apply merge_globdef_noGvar in H; auto.
     inv H. 
     apply H2; auto.
     eapply find_id_In_map_fst.
    apply find_id_QPvarspecs. eauto.
     inv H. 
     apply H5; auto.
     eapply find_id_In_map_fst.
    apply find_id_QPvarspecs. eauto.
    inv H.
 }
 assert (LNR3_V1: list_norepet (map fst (QPvarspecs p1) ++ map fst (Imports1 ++ Comp_G c1))).  {
    clear - Linked Imports_G_disjoint LNR_G LMR_Imp.
    apply list_norepet_app; split3.
  - apply QPvarspecs_norepet.
  - rewrite map_app.
    apply list_norepet_app; split3; auto.
    pose proof (Comp_ExternsImports_LNR c1).
    rewrite map_app in H; apply list_norepet_app in H; destruct H as [_ [? _]]; auto.
    apply (Comp_G_LNR c1).
    pose proof (Comp_G_dom c1).
    pose proof (Comp_ExternsImports_LNR c1).
    rewrite map_app in H0; apply list_norepet_app in H0; destruct H0 as [_ [_ ?]].
    clear - H0 H. change (Comp_G c1) with G1 in *.
    assert (H3 := Comp_Imports_external c1).
    intros i j ? ? ?; subst j. specialize (H3 _ H1). destruct H3 as [? [? [? [? ?]]]].
    rewrite <- H in H2; clear H.
    apply in_app_or in H2; destruct H2.
    unfold IntIDs in H.
    apply list_in_map_inv in H. destruct H as [[??][??]]. simpl in *. subst p.
    rewrite filter_In in H2. simpl in H2; destruct H2.
    apply PTree.elements_complete in H.
    rewrite H3 in H. inv H. inv H2.
    apply (H0 i i); auto.
   - rewrite map_app.
    apply list_disjoint_app_R.
     intros i j ? ? ?; subst j.
     apply In_map_fst_find_id in H; try apply QPvarspecs_norepet.
     destruct H as [v H].
     apply find_id_QPvarspecs in H. destruct H as [g [? ?]].
     apply (Comp_Imports_external c1) in H0.
     destruct H0 as [? [? [? [? ?]]]]. congruence.
     intros i j ? ? ?; subst j.
     apply In_map_fst_find_id in H; [ | apply QPvarspecs_norepet].
     destruct H.
     apply find_id_QPvarspecs in H.
     destruct H as [? [? ?]].
     rewrite <- (Comp_G_dom c1) in H0.
    apply in_app_or in H0; destruct H0.
    unfold IntIDs in H0.
    apply list_in_map_inv in H0. destruct H0 as [[j ?][??]]. simpl in *. subst j.
    rewrite filter_In in H2. simpl in H2; destruct H2.
    apply PTree.elements_complete in H0.
    rewrite H in H0. inv H0. inv H2.
    apply (Comp_Externs c1) in H0.
     destruct H0 as [? [? [? [? ?]]]]. congruence.
 }
 assert (LNR3_V2: list_norepet (map fst (QPvarspecs p2) ++ map fst (Imports2 ++ Comp_G c2))).  {
    clear - Linked Imports_G_disjoint LNR_G LMR_Imp.
    apply list_norepet_app; split3.
  - apply QPvarspecs_norepet.
  - rewrite map_app.
    apply list_norepet_app; split3; auto.
    pose proof (Comp_ExternsImports_LNR c2).
    rewrite map_app in H; apply list_norepet_app in H; destruct H as [_ [? _]]; auto.
    apply (Comp_G_LNR c2).
    pose proof (Comp_G_dom c2).
    pose proof (Comp_ExternsImports_LNR c2).
    rewrite map_app in H0; apply list_norepet_app in H0; destruct H0 as [_ [_ ?]].
    clear - H0 H. change (Comp_G c2) with G2 in *.
    assert (H3 := Comp_Imports_external c2).
    intros i j ? ? ?; subst j. specialize (H3 _ H1). destruct H3 as [? [? [? [? ?]]]].
    rewrite <- H in H2; clear H.
    apply in_app_or in H2; destruct H2.
    unfold IntIDs in H.
    apply list_in_map_inv in H. destruct H as [[??][??]]. simpl in *. subst p.
    rewrite filter_In in H2. simpl in H2; destruct H2.
    apply PTree.elements_complete in H.
    rewrite H3 in H. inv H. inv H2.
    apply (H0 i i); auto.
   - rewrite map_app.
    apply list_disjoint_app_R.
     intros i j ? ? ?; subst j.
     apply In_map_fst_find_id in H; try apply QPvarspecs_norepet.
     destruct H as [v H].
     apply find_id_QPvarspecs in H. destruct H as [g [? ?]].
     apply (Comp_Imports_external c2) in H0.
     destruct H0 as [? [? [? [? ?]]]]. congruence.
     intros i j ? ? ?; subst j.
     apply In_map_fst_find_id in H; [ | apply QPvarspecs_norepet].
     destruct H.
     apply find_id_QPvarspecs in H.
     destruct H as [? [? ?]].
     rewrite <- (Comp_G_dom c2) in H0.
    apply in_app_or in H0; destruct H0.
    unfold IntIDs in H0.
    apply list_in_map_inv in H0. destruct H0 as [[j ?][??]]. simpl in *. subst j.
    rewrite filter_In in H2. simpl in H2; destruct H2.
    apply PTree.elements_complete in H0.
    rewrite H in H0. inv H0. inv H2.
    apply (Comp_Externs c2) in H0.
     destruct H0 as [? [? [? [? ?]]]]. congruence.
 }
 assert (HV1 : forall (i : ident) (phi : type),
      find_id i (QPvarspecs p1) = Some phi -> find_id i (QPvarspecs p) = Some phi). {
  clear - Linked.
  intros.
  apply QPlink_progs_globdefs in Linked.
  apply (merge_PTrees_e i) in Linked.
  rewrite find_id_QPvarspecs in H.
  rewrite find_id_QPvarspecs.
  destruct H as [g [? ?]]; exists g; split; auto.
  rewrite H in Linked.
  destruct ( (QP.prog_defs p2) ! i). destruct Linked as [? [? ?]].
  unfold merge_globdef in H1. destruct g,g0; inv H1. destruct v; inv H4.
  auto.
} 
 assert (HV2 : forall (i : ident) (phi : type),
      find_id i (QPvarspecs p2) = Some phi -> find_id i (QPvarspecs p) = Some phi). {
  clear - Linked.
  intros.
  apply QPlink_progs_globdefs in Linked.
  apply (merge_PTrees_e i) in Linked.
  rewrite find_id_QPvarspecs in H.
  rewrite find_id_QPvarspecs.
  destruct H as [g [? ?]]; exists g; split; auto.
  rewrite H in Linked.
  destruct ( (QP.prog_defs p1) ! i). destruct Linked as [? [? ?]].
  unfold merge_globdef in H1. destruct g0,g; inv H1. destruct f; inv H4.
  destruct v; inv H4. auto.
}
assert (TypesOfFunspecs1: forall i, sub_option (make_tycontext_g (QPvarspecs p1) (Imports1 ++ Comp_G c1)) ! i
  (make_tycontext_g (QPvarspecs p) (Imports ++ G)) ! i).
{
 subst G; clear - HV1 LNR3_V1 LNR4_V1 LNR2 SUBSUME1 Linked. intros i.
  rewrite 2 semax_prog.make_context_g_char, 2 make_tycontext_s_find_id; trivial.
  specialize (SUBSUME1 i). red in SUBSUME1. destruct (find_id i (Imports1 ++ Comp_G c1)); simpl.
  + destruct SUBSUME1 as [psi2 [PHI2 Sub]]. rewrite PHI2.
    exploit (Sub (compcert_rmaps.RML.empty_rmap 0)); [ trivial | intros FS].
    apply type_of_funspec_sub_si in FS; rewrite FS; trivial.
  +
    destruct  (find_id i (QPvarspecs p1)) eqn:Heqw; auto. simpl.
    rewrite (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V1 i _ Heqw).
    apply HV1; trivial.
 }
assert (TypesOfFunspecs2: forall i, sub_option (make_tycontext_g (QPvarspecs p2) (Imports2 ++ Comp_G c2)) ! i
  (make_tycontext_g (QPvarspecs p) (Imports ++ G)) ! i).
{ subst G; clear - SUBSUME2 LNR3_V2 LNR4_V2 LNR2 HV2. intros i.
  rewrite 2 semax_prog.make_context_g_char, 2 make_tycontext_s_find_id; trivial.
  specialize (SUBSUME2 i). red in SUBSUME2. destruct (find_id i (Imports2 ++ Comp_G c2)); simpl.
  + destruct SUBSUME2 as [psi2 [PHI2 Sub]]. rewrite PHI2.
    exploit (Sub (compcert_rmaps.RML.empty_rmap 0)); [ trivial | intros FS].
    apply type_of_funspec_sub_si in FS; rewrite FS; trivial.
  + remember (find_id i (QPvarspecs p2)) as w; symmetry in Heqw; destruct w as [phi |]; simpl; trivial.
    rewrite (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V2 _ _ Heqw).
    apply HV2; trivial.
}
assert (OKp:= QPlink_progs_OK _ _ _ Linked (Comp_prog_OK c1) (Comp_prog_OK c2)).

destruct  (linked_compspecs' _ _ _
                   (proj2 (Comp_prog_OK c1))
                   (proj2 (Comp_prog_OK c2))
                   Linked)
 as [_ [CS1 CS2]].
 apply (cspecs_sub_of_QPsub _ _ (proj2 (Comp_prog_OK c1)) (proj2 OKp) ) in CS1.
 apply (cspecs_sub_of_QPsub _ _ (proj2 (Comp_prog_OK c2)) (proj2 OKp)) in CS2.
eapply Build_Component; trivial.
+ intros. subst G; unfold E. split; intros. 
  - apply G_merge_InDom; [ apply c1 | apply in_app_or in H; destruct H].
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

+ subst G; unfold E; intros. assert (FP := Linked_Functions_preserved _ _ _ Linked i); hnf in FP.
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
+ (*SF*) subst G. intros. clear Condition1 Condition2.
  assert (HCi := HC i).
  assert (FP := Linked_Functions_preserved _ _ _ Linked i). hnf in FP. specialize (FundefsMatch i).
  apply G_merge_find_id_Some in H0. 2: apply (Comp_G_LNR c2).
  remember (find_id i (Comp_G c1)) as q1; symmetry in Heqq1; destruct q1 as [phi1 |].
  - subst phi; 
     clear - c1 c2 (*CS1 CS2*) HCi LNR4_V1 LNR4_V2 HV1 HV2 Heqq1 JUST1 JUST2 H 
            SUBSUME1 SUBSUME2 TypesOfFunspecs1 TypesOfFunspecs2
            Externs1_Hyp Externs2_Hyp FP FundefsMatch.
    exploit (Comp_G_in_Fundefs' c1). apply Heqq1. intros [fd1 FD1].
    specialize (JUST1 _ _ _ FD1 Heqq1).
    specialize (SF_subsumespec JUST1 _ (QPvarspecs p) SUBSUME1 HV1 (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V1) (Comp_ctx_LNR c1)); clear JUST1 SUBSUME1; intros SF1.
    remember (find_id i (Comp_G c2)) as q2; symmetry in Heqq2; destruct q2 as [phi2 |].
    * exploit (Comp_G_in_Fundefs' c2). apply Heqq2. intros [fd2 FD2].
      specialize (JUST2 _ _ _ FD2 Heqq2).
      specialize (SF_subsumespec JUST2 _  (QPvarspecs p) SUBSUME2 HV2 (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V2) (Comp_ctx_LNR c2)); clear JUST2 SUBSUME2; intros SF2.
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
         --  instantiate (1:=OKp).
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
               destruct FundefsMatch as (*[SIGs*) [psi2 PSI2](*]*).
               rewrite FP in H. inv H. simpl.
               apply (InternalInfo_envs_sub CS2 (QPglobalenv p2)); [ apply SF2 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.
          -- clear FundefsMatch Heqw1. contradiction FP.
          -- clear FundefsMatch Heqw1.
             rewrite FP in H. inv H. simpl.
             apply (InternalInfo_envs_sub CS2 (QPglobalenv p2)); [ apply SF2 | clear - OKp FP].
               apply QPfind_funct_ptr_exists; auto.

+ (*TODO: clean up this proof*)
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
      ++ subst phi. destruct (Comp_G_Exports c1 _ _ Heqq1) as [tau1 [Tau1 TAU1]].
         unfold Comp_G in Hequ1; rewrite Hequ1 in Tau1; inv Tau1.
         remember (find_id i Exports2) as q2; symmetry in Heqq2; destruct q2 as [psi2 |].

         2: solve [simpl; apply @funspec_sub_trans with tau1; trivial ].

         destruct (Comp_G_Exports c2 _ _ Heqq2) as [tau2 [Tau2 TAU2]].
         unfold Comp_G in Hequ2; rewrite Hequ2 in Tau2; inv Tau2.

         assert (SigsPsi: typesig_of_funspec psi1 =typesig_of_funspec psi2).
         { clear - SigsPhi TAU1 TAU2. destruct tau1; destruct tau2.
           destruct psi1; destruct TAU1 as [AA1 _].
           destruct psi2; destruct TAU2 as [AA2 _]. simpl in *.
           destruct AA1; destruct AA2; subst; trivial. }
         assert (CCPsi: callingconvention_of_funspec psi1 = callingconvention_of_funspec psi2).
         { clear - CCPhi TAU1 TAU2. apply funspec_sub_cc in TAU1. apply funspec_sub_cc in TAU2. 
           rewrite <- TAU1, <- TAU2; trivial. }
         destruct (G_merge_find_id_SomeSome Heqq1 Heqq2 SigsPsi CCPsi) as [tau' [BI TAU']].
         simpl. rewrite BI. clear - BI Phi1' Phi2' TAU1 TAU2.
         apply (BINARY_intersection_sub3 _ _ _ BI); clear BI.
         apply @funspec_sub_trans with tau1; trivial.
         apply @funspec_sub_trans with tau2; trivial.
      ++ destruct (Comp_G_Exports c2 _ _ Hi) as [tau2 [Tau2 TAU2]].
         unfold Comp_G in Hequ2; rewrite Hequ2 in Tau2; inv Tau2.
         apply @funspec_sub_trans with tau2; trivial.

    * rewrite (G_merge_find_id_SomeNone Hequ1 Hequ2).
      remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
      ++ subst. eexists; split. reflexivity.
         destruct (Comp_G_Exports c1 _ _ Heqq1) as [psi [Psi PSI]]. unfold Comp_G in Hequ1; rewrite Hequ1 in Psi. inv Psi.
         eapply funspec_sub_trans. apply PSI.
         apply type_of_funspec_sub in PSI.
         clear - Heqq1 Hequ2 c2 PSI. remember (find_id i Exports2) as w; symmetry in Heqw; destruct w as [psi2 |].
         -- destruct (Comp_G_Exports c2 _ _ Heqw) as [phi2 [? ?]].
            unfold Comp_G in Hequ2; congruence.
         -- simpl. apply funspec_sub_refl; trivial.
      ++ eexists; split. reflexivity.
         apply (Comp_G_Exports c2) in Hi. destruct Hi as [? [? _]]. unfold Comp_G in Hequ2; congruence. 
  - remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
    * destruct (Comp_G_Exports c1 _ _ Heqq1) as [psi [Psi PSI]].  unfold Comp_G in Hequ1; congruence.
    * destruct (Comp_G_Exports c2 _ _ Hi) as [psi2 [Psi2 PSI2]]. unfold Comp_G in *.
      rewrite (G_merge_find_id_NoneSome Hequ1 Psi2).
      eexists; split. reflexivity. trivial. apply (Comp_G_LNR c2).
+ 
    intros.
  eapply derives_trans. 
  2: apply sepcon_derives; [ apply (Comp_MkInitPred c1 gv) | apply (Comp_MkInitPred c2 gv)]; auto.
  apply InitGPred_join; auto.
Qed.

End ComponentJoin.

Definition VSULink_Imports 
 {Espec E1 Imports1 p1 Exports1 GP1 E2 Imports2 p2 Exports2 GP2}
  (vsu1: @VSU Espec E1 Imports1 p1 Exports1 GP1)
  (vsu2: @VSU Espec E2 Imports2 p2 Exports2 GP2)  := 
      filter (fun x => negb (in_dec ident_eq (fst x) (map fst E2 ++ IntIDs p2))) Imports1 ++
      filter (fun x => negb (in_dec ident_eq (fst x) (map fst E1 ++ IntIDs p1 ++ map fst Imports1))) Imports2.

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
  exists  (G_merge (Comp_G (projT2 vsu1)) (Comp_G (projT2 vsu2))).
  apply ComponentJoin; trivial.
Qed.

Lemma SF_ctx_subsumption {Espec} V G ge i fd phi cs
  (HSF:  @SF Espec cs V ge G i fd phi)
  (LNR_G: list_norepet (map fst G)) G' V' ge' cs'
  (SubCS: cspecs_sub cs cs')
  (FD: genv_find_func ge' i fd)
  (SubFG: forall j, sub_option (make_tycontext_g V G) ! j (make_tycontext_g V' G') ! j)
  (SubG: forall j : ident, subsumespec (find_id j G) (find_id j G')):
  @SF Espec cs' V' ge' G' i fd phi.
Proof.
  destruct fd; simpl.
 + eapply InternalInfo_subsumption.
    4: eapply (@InternalInfo_envs_sub cs cs' SubCS); eassumption.
    assumption. assumption. assumption. 
 + eapply ExternalInfo_envs_sub; eassumption.
Qed.

Lemma SF_ctx_extensional {Espec} V G ge i fd cs phi (HSF:  @SF Espec cs V ge G i fd phi)
  (LNR_G: list_norepet (map fst G)) G'
  (GG': forall j, find_id j G = find_id j G'):
  @SF Espec cs V ge G' i fd phi.
Proof.
  destruct fd; simpl; [ | apply HSF].
  eapply InternalInfo_subsumption; [ | | eassumption | eassumption].
  + intros j; red. remember ((make_tycontext_g V G) ! j) as q; destruct q; simpl; trivial.
    symmetry in Heqq. 
    specialize (semax_prog.make_tycontext_s_g V G j). 
    specialize (semax_prog.make_tycontext_s_g V G' j).
    rewrite 2 make_tycontext_s_find_id, GG'. intros.
    remember (find_id j G') as w; destruct w.
    * rewrite (H _ (eq_refl _)). rewrite (H0 _ (eq_refl _)) in Heqq; trivial.
    * clear H H0; symmetry in Heqw. specialize (GG' j); rewrite Heqw in GG'.
      rewrite semax_prog.make_tycontext_g_G_None by trivial. 
      rewrite semax_prog.make_tycontext_g_G_None in Heqq; trivial.
  + intros j; rewrite GG'. apply subsumespec_refl.
Qed.

Record CanonicalComponent {Espec} Externs Imports p Exports GP G:= {
  CC_component :> @Component Espec Externs Imports p Exports GP G;
  CC_canonical: map fst (Comp_G CC_component) = 
                map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ map fst Externs))
                        (PTree.elements (QP.prog_defs p)))
}.

Lemma CanonicalComponent_entail {Espec E Imp p Exp G} GP1 GP2 : 
      @CanonicalComponent Espec E Imp p Exp GP1 G ->
       (forall gv, GP1 gv |-- GP2 gv) -> 
      @CanonicalComponent Espec E Imp p Exp GP2 G.
Proof.
  intros. destruct H as [C X]. 
  apply (Build_CanonicalComponent _ _ _ _ _ _ _ (Comp_entail C _ H0) X).
Qed.

Fixpoint order {A} (G:list (ident * A)) (l:list ident): option (list (ident *A)) :=
  match l with
    nil => Some nil
  | i::l' => match order G l', find_id i G with 
            | Some G', Some a => Some ((i,a)::G') 
            | _, _ => None
             end
  end.

Lemma order_i {A} G: forall l (LNRG: list_norepet (map fst G))
  (Hl: forall i, In i l -> In i (map fst G)),
  exists G', @order A G l = Some G'.
Proof.
  induction l; simpl; intros.
+ exists nil; trivial.
+ destruct IHl as [G' HG']; trivial. intuition.
  exploit (Hl a); [ left; trivial | intros].
  apply In_map_fst_find_id in H; [destruct H as [b Hb] | trivial].
  rewrite HG', Hb. eexists; reflexivity.
Qed.

Lemma order_i' {A} G l (LNRG: list_norepet (map fst G))
  (Hl: forall i, In i l -> In i (map fst G)): ~ @order A G l = None.
Proof. destruct (order_i G l); trivial. congruence. Qed.

Lemma order_dom {A G}: forall {l G'}, @order A G l = Some G' -> l = map fst G'.
Proof.
  induction l; simpl; intros. inv H; trivial.
  remember (order G l) as p; destruct p; try inv H.
  remember (find_id a G) as q. destruct q; inv H1.
  simpl. f_equal; auto.
Qed.

Lemma order_sound {A G}: forall {l G'}, @order A G l = Some G' -> 
      forall i phi, find_id i G' = Some phi -> find_id i G = Some phi.
Proof.
  induction l; simpl; intros. inv H. inv H0.
  remember (order G l) as p; destruct p as [GG' |]; [ symmetry in Heqp | inv H].
  remember (find_id a G) as q. destruct q as [psi |]; inv H. symmetry in Heqq.
  simpl in H0. if_tac in H0; subst.
  + inv H0. rewrite Heqq; trivial.
  + apply (IHl GG'); trivial.
Qed.

Lemma order_complete {A G l G'}: @order A G l = Some G' -> list_norepet l ->
      (forall i, In i (map fst G) -> In i l) ->
      forall i phi, find_id i G = Some phi -> find_id i G' = Some phi.
Proof.
  intros. exploit (H1 i). apply find_id_In_map_fst in H2; trivial. clear H1; intros.
  specialize (order_dom H); intros; subst.
  apply In_map_fst_find_id in H1; [ destruct H1 | trivial].
  rewrite (order_sound H _ _ H1) in H2. inv H2; trivial.
Qed. 

Lemma order_SOC {A G l G'}: @order A G l = Some G' -> list_norepet l ->
      (forall i, In i (map fst G) -> In i l) ->
      forall i, find_id i G = find_id i G'.
Proof.
  intros. specialize (order_sound H i); specialize (order_complete H H0 H1 i); clear; intros.
  destruct (find_id i G); destruct (find_id i G'); trivial. intuition.
  elim (H _ (eq_refl _)); trivial. elim (H0 _ (eq_refl _)); trivial.
Qed.

Definition keep_fun {F} (externs: list ident) (ig: ident * globdef (fundef F) type) : bool :=
 match ig with
 | (_,Gvar _) => true 
 | (i, Gfun (Internal _)) => true
 | (i, Gfun (External _ _ _ _)) => in_dec ident_eq i externs
 end.

Fixpoint PTree_filter' {A} (f: positive * A -> bool) (i: positive) (m: PTree.t A) : PTree.t A  :=
  match m with
  | PTree.Leaf => PTree.Leaf
  | PTree.Node  l (Some x) r => 
      PTree.Node (PTree_filter' f (xO i) l)
                   (if f (i,x) then (Some x) else None)
                   (PTree_filter' f (xI i) l)
  | PTree.Node l None r => 
      PTree.Node (PTree_filter' f (xO i) l) None (PTree_filter' f (xI i) l)
  end.

Definition PTree_filter {A} (f: positive * A -> bool)  := 
  PTree_filter' f xH.

Definition prune_QPprogram {F} (p: QP.program F) (externs: list ident) : QP.program F :=
 {| QP.prog_builtins := p.(QP.prog_builtins);
     QP.prog_defs := PTree_filter (keep_fun externs) p.(QP.prog_defs);
     QP.prog_public := p.(QP.prog_public);
     QP.prog_main := p.(QP.prog_main);
     QP.prog_comp_env := p.(QP.prog_comp_env)
 |}.

Record CanonicalComponent_M {Espec} Externs Imports p Exports GP G:= {
  CCM_G: funspecs;
  CCM_component :> @CanonicalComponent Espec Externs Imports p Exports GP CCM_G;
  CCM_main: find_id (QP.prog_main p) CCM_G = find_id (QP.prog_main p) G
}.

(*
Lemma Comp_to_CanComp {Espec Ext Imp p Exp GP G} (C: @Component Espec Ext Imp p Exp GP G):
     In (QP.prog_main p) (IntIDs p ++ map fst Ext) ->
      @CanonicalComponent_M Espec Ext Imp (prune_QPprogram p (map fst Ext)) Exp GP G.
Proof.
  intro Hmain.
  set (p' := prune_QPprogram p (map fst Ext)).
  remember (order G (map fst (QPprog_funct p'))) as Gopt.
  destruct Gopt as [GG |]; symmetry in HeqGopt.
-
  exists GG.
 +
  assert (Comp: Component Ext Imp p' Exp GP GG). {
    assert (C_Imports_external : forall i : ident,
                         In i (map fst Imp) ->
                         exists
                           (f : external_function) 
                         (ts : typelist) (t : type) 
                         (cc : calling_convention),
                           (QP.prog_defs p') ! i =
                           Some (Gfun (External f ts t cc))). {
   admit.
  }
    assert (C_Externs: forall i : ident,
     In i (map fst Ext) ->
     exists f ts t cc, (QP.prog_defs p') ! i = Some (Gfun (External f ts t cc))).
   admit.
     assert (C_G_dom: forall i : ident,
          In i (IntIDs p' ++ map fst Ext) <-> In i (map fst GG)).
    admit.
     assert (C_G_LNR: list_norepet (map fst GG)).
  { rewrite <- (order_dom HeqGopt). 
    admit.
  }
     assert (C_G_E: forall i, In i (map fst Ext) -> find_id i Ext = find_id i GG).
    admit.
     assert (C_G_justified : forall i phi fd,
                       (QP.prog_defs p') ! i = Some (Gfun fd) ->
                       find_id i GG = Some phi ->
                       @SF Espec (Comp_cs C) (QPvarspecs p') (QPglobalenv p') (Imp ++ GG) i fd phi).
     admit.
     assert (C_G_Exports : forall i phi,
                     find_id i Exp = Some phi ->
                     exists phi' : funspec,
                       find_id i GG = Some phi' /\
                       funspec_sub phi' phi).
     admit. 
     assert (C_MkInitPred : forall gv : globals,
                      globals_ok gv ->
                      InitGPred (Vardefs p') gv |-- GP gv). {
     admit.
  } 
     apply (Build_Component Espec Ext Imp p' Exp GP GG). C_Imports_external (Comp_cs C)).
     apply (Comp_cs_OK C).
     apply (Comp_ExternsImports_LNR C).
     apply (Comp_Exports_LNR C).
     apply C_Externs.
     apply C_G_dom.
     apply C_G_LNR.
     apply C_G_E. 
     apply C_G_justified. 
     apply C_G_Exports. 
     apply C_MkInitPred.
  } 
 apply (Build_CanonicalComponent _ _ _ _ _ _ _ Comp).
 change (Comp_G Comp) with GG.
 rewrite <- (order_dom HeqGopt); clear HeqGopt.
 unfold QPprog_funct.
  admit.
 +
  admit.
-
 apply order_i' in HeqGopt. contradiction. apply C.
  clear - C. intros i H'.  apply (Comp_G_dom C).
 admit.
Abort.

*)

Lemma Comp_to_CanComp {Espec Ext Imp p Exp GP G} (C: @Component Espec Ext Imp p Exp GP G):
      @CanonicalComponent_M Espec Ext Imp p Exp GP G.
Proof.
  assert (HG: G = Comp_G C). reflexivity.
  remember (order (Comp_G C) 
                  (map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ (map fst Ext))) 
                     (PTree.elements (QP.prog_defs p))))) as Gopt.
  destruct Gopt as [GG |]; symmetry in HeqGopt.
+ specialize (LNR_Internals_Externs C); intros LNR_IEc.
  assert (X6: forall i : ident, In i (IntIDs p ++ map fst Ext) <-> In i (map fst GG)).
  { intros. rewrite <- (order_dom HeqGopt).
    remember  (PTree.elements (QP.prog_defs p)) as l. remember (IntIDs p ++ map fst Ext) as l'.
    assert (forall j, In j l' -> In j (map fst l)).
    { subst. clear -C. intros. apply C in H. destruct (Comp_G_in_progdefs C j H).
       apply PTree_In_fst_elements. eauto. }
    clear - H.
    split; intros. 
    + specialize (H _ H0). apply in_map_iff in H. destruct H as [[j d] [J HJ]]; simpl in *; subst.
      apply in_map_iff. exists (i,d); simpl; split; trivial. apply filter_In; simpl. split; trivial.
      destruct (in_dec ident_eq i l'); trivial. contradiction.
    + apply in_map_iff in H0. destruct H0 as [[j d] [J HJ]]; simpl in *; subst.
      apply filter_In in HJ; simpl in HJ; destruct HJ. 
      destruct (in_dec ident_eq i l'); trivial. discriminate. }
  assert (X7: list_norepet (map fst GG)).
  { rewrite <- (order_dom HeqGopt). apply list_norepet_map_fst_filter.
    apply PTree.elements_keys_norepet. }
  assert (Y: forall i, find_id i (Comp_G C) = find_id i GG).
  { clear - HeqGopt X6. apply (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. 
    apply PTree.elements_keys_norepet.
    intros. rewrite (order_dom HeqGopt). apply X6. apply C. trivial. }
  assert (X8: forall i, In i (map fst Ext) -> find_id i Ext = find_id i GG).
  { intros. rewrite (Comp_G_E C _ H); trivial. }

  assert (X1: forall i, In i (map fst Imp) ->
      exists
        (f : external_function) (ts : typelist) (t : type) (cc : calling_convention),
        PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc))) by apply C.

  assert (X3: list_norepet (map fst (Ext ++ Imp))) by apply C.

  assert (X4: list_norepet (map fst Exp)) by apply C.
  assert (X5: forall i, In i (map fst Ext) -> exists f ts t cc,
    PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc))) by apply C.

  assert (X9: forall i phi fd,
    PTree.get i (QP.prog_defs p) = Some (Gfun fd) -> find_id i GG = Some phi -> 
   @SF Espec (Comp_cs C) (QPvarspecs p) (QPglobalenv p) (Imp ++ GG) i fd phi).
  { intros.
    eapply SF_ctx_extensional. 
    + rewrite <- Y in H0; apply (Comp_G_justified C _ phi _ H H0).
    + apply (Comp_ctx_LNR C).
    + intros j. rewrite 2 find_id_app_char, Y; trivial. }

  assert (X10: forall i phi, find_id i Exp = Some phi -> 
          exists phi', find_id i GG = Some phi' /\ funspec_sub phi' phi).
  { intros. destruct (Comp_G_Exports C _ _ H) as [phi' [Phi' Sub]].
    exists phi'; split; trivial. rewrite <- (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply PTree.elements_keys_norepet.
    intros. rewrite (order_dom HeqGopt). apply X6. apply C. trivial. }

  remember (@Build_Component Espec Ext Imp p Exp GP GG
  (Comp_prog_OK C) X1 X3 X4 X5 X6 X7 X8 X9 X10
          (Comp_MkInitPred C)) as cc.
  exists GG.
  - apply Build_CanonicalComponent with cc.
         subst cc; simpl. symmetry; apply (order_dom HeqGopt).
  - rewrite HG, Y; trivial.
+ apply order_i' in HeqGopt. contradiction. apply C. unfold Comp_G in *.
  clear - C. intros.
  apply (Comp_G_dom C). apply in_map_iff in H. destruct H as [[j d] [J HJ]]. simpl in J; subst.
  apply filter_In in HJ; simpl in HJ; destruct HJ.
  destruct (in_dec ident_eq i (IntIDs p ++ map fst Ext)). trivial. inv H0.
Qed.

Lemma CanonicalComponent_M_entail {Espec E Imp p Exp G} GP1 GP2 : 
      @CanonicalComponent_M Espec E Imp p Exp GP1 G -> (forall gv, GP1 gv |-- GP2 gv) -> 
      @CanonicalComponent_M Espec E Imp p Exp GP2 G.
Proof.
  intros. eapply Build_CanonicalComponent_M. apply (CanonicalComponent_entail _ _ X H). apply X.
Defined.

Definition CanonicalVSU {Espec} E Imports p Exports GP :=
  sigT (fun G => @CanonicalComponent_M Espec E Imports p Exports GP G).

Lemma VSU_to_CanonicalVSU {Espec Ext Imp p Exp GP} 
        (vsu: @VSU Espec Ext Imp p Exp GP):
      @CanonicalVSU Espec Ext Imp p Exp GP.
Proof.
  destruct vsu as [GG c]. remember (Comp_to_CanComp c) as CC. destruct CC as [G C M]. clear HeqCC.
  exists GG. econstructor. apply C. trivial.
Qed.

Lemma CanonicalVSU_entail {Espec E Imp p Exp} GP1 GP2 : 
      @CanonicalVSU Espec E Imp p Exp GP1 -> (forall gv, GP1 gv |-- GP2 gv) -> 
      @CanonicalVSU Espec E Imp p Exp GP2.
Proof. intros. destruct X as [G C].
  exists G. apply (CanonicalComponent_M_entail _ _ C H).
Qed.

Inductive semaxfunc {Espec} {cs : compspecs} (V : varspecs) (G : funspecs) (ge : Genv.t Clight.fundef type):
  list (ident * Clight.fundef) -> funspecs -> Prop :=
  semaxfunc_nil: @semaxfunc Espec cs V G ge nil nil

| semaxfunc_cons: forall (fs : list (ident * Clight.fundef)) (id : ident) (f : function) phi (G' : funspecs),
  semaxfunc_InternalInfo cs V G ge id f phi ->
  negb (id_in_list id (map fst fs)) = true ->
  @semaxfunc Espec cs V G ge fs G' ->
  @semaxfunc Espec cs V G ge ((id, Internal f) :: fs) ((id, phi) :: G')

| semaxfunc_cons_ext: forall (fs : list (ident * Clight.fundef)) (id : ident) 
    (ef : external_function) (argsig : typelist) (retsig : type) (G' : funspecs) (cc : calling_convention)
    phi,
   semaxfunc_ExternalInfo Espec ge id ef argsig retsig cc phi ->
   id_in_list id (map fst fs) = false ->
  @semaxfunc Espec cs V G ge fs G' ->
  @semaxfunc Espec cs V G ge ((id, External ef argsig retsig cc) :: fs)
    ((id, phi) :: G').

Lemma semaxfunc_sound {Espec cs V G ge funs G'} 
  (SF: @semaxfunc Espec cs V G ge funs G'):
  @semax_func Espec V G cs ge funs G'.
Proof.
  induction SF.
+ apply semax_func_nil.
+ destruct H as [? [? [? [? [? [b [? ?]]]]]]]; destruct phi.
  eapply semax_func_cons; try eassumption.
  rewrite H0; simpl; trivial.
+ destruct phi; destruct t. destruct H as [? [? [? [? [? [? [H1 [H2 [H3 H4]]]]]]]]].
  subst.
  eapply semax_func_cons_ext; try eassumption; trivial.
Qed.

Lemma semaxfunc_cons_int_vacuous {Espec} {cs : compspecs} (V : varspecs) (G : funspecs) ge: forall
    (fs : list (ident * Clight.fundef)) (id : ident) ifunc
    (b : block) G'
  (ID: id_in_list id (map fst fs) = false)
  (ID2: id_in_list id (map fst G) = true)
  (GfsB: Genv.find_symbol ge id = Some b)
  (GffpB: Genv.find_funct_ptr ge b = Some (Internal ifunc))
  (CTvars: Forall (fun it : ident * type => complete_type cenv_cs (snd it) = true) (fn_vars ifunc))
  (LNR_PT: list_norepet (map fst (fn_params ifunc) ++ map fst (fn_temps ifunc)))
  (LNR_Vars: list_norepet (map fst (fn_vars ifunc)))
  (VarSizes: semax.var_sizes_ok cenv_cs (fn_vars ifunc))
  (Sfunc: @semaxfunc Espec cs V G ge fs G'),
  @semaxfunc Espec cs V G ge ((id, Internal ifunc) :: fs)
    ((id, vacuous_funspec (Internal ifunc)) :: G').
Proof.
intros.
eapply semaxfunc_cons; try eassumption.
+ repeat split; simpl; trivial.
  - rewrite ID2. simpl. unfold semax_body_params_ok.
    apply compute_list_norepet_i in LNR_PT. rewrite LNR_PT.
    apply compute_list_norepet_i in LNR_Vars. rewrite LNR_Vars. trivial.
  - destruct ifunc; simpl; trivial.
  - destruct ifunc; simpl; trivial.
  - intros ? ? Impos. inv Impos.
  - exists b; split; trivial.
+ rewrite ID; trivial.
Qed.

Lemma semaxfunc_cons_ext_vacuous:
     forall {Espec: OracleKind} (V : varspecs) (G : funspecs) (cs : compspecs) ge
         (fs : list (ident * Clight.fundef)) (id : ident) (ef : external_function)
         (argsig : typelist) (retsig : type)
         (G' : funspecs) cc b,
       (id_in_list id (map fst fs)) = false ->
       ef_sig ef =
       {|
         sig_args := typlist_of_typelist argsig;
         sig_res := rettype_of_type retsig;
         sig_cc := cc_of_fundef (External ef argsig retsig cc) |} ->
       (*new*) Genv.find_symbol ge id = Some b ->
       (*new*) Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
       @semaxfunc Espec cs V G ge fs G' ->
       @semaxfunc Espec cs V G ge ((id, External ef argsig retsig cc) :: fs)
         ((id, vacuous_funspec (External ef argsig retsig cc)) :: G').
Proof.
intros.
eapply (@semaxfunc_cons_ext Espec cs V G ge fs id ef argsig retsig); trivial.
repeat split; trivial.
* rewrite <-(typelist2list_arglist _ 1). reflexivity.
* right. clear. hnf. intros. simpl in X; inv X.
* intros. simpl. apply andp_left1, FF_left.
* apply semax_external_FF.
* exists b; split; trivial.
Qed.

Lemma SF_semaxfunc {Espec V cs ge} G: forall funs GG
      (HSF: forall i phi fd, find_id i funs = Some fd -> 
            find_id i GG = Some phi -> @SF Espec cs V ge G i fd phi)
      (LNR: list_norepet (map fst funs))
      (DOM: map fst funs = map fst GG),
  semaxfunc V G ge funs GG.
Proof.
  induction funs; intros.
+ destruct GG; inv DOM. constructor.
+ destruct GG; inv DOM.
  destruct p as [i phi]; destruct a as [j fd]; simpl in *; subst. inv LNR.
  exploit (IHfuns GG); trivial; clear IHfuns.
  { intros. apply HSF; rewrite if_false; trivial;
    apply find_id_In_map_fst in H; congruence. }
  specialize (HSF i phi fd). rewrite 2 if_true in HSF by trivial.
  specialize (HSF (eq_refl _) (eq_refl _)).
  apply id_in_list_false_i in H2. intros.
  destruct fd; simpl in HSF; econstructor; trivial.
  rewrite H2; trivial.
Qed.

Lemma remove_elim {A f y}: forall (l:list A) x, In x (remove f y l) -> In x l.
Proof. 
  induction l; simpl; intros. contradiction.
  destruct (f y a); subst. right; apply (IHl _ H).
  destruct H. left; trivial. right; apply (IHl _ H).
Qed.

Lemma filter_prog_funct_defs {f g} {p: QP.program function}
      (GF: forall i x, f (i,x) = g (i, Gfun x))
      (HG: forall i v, PTree.get i (QP.prog_defs p) = Some (Gvar v) -> g (i, Gvar v) = false):
      map fst (filter f (QPprog_funct p)) = map fst (filter g (PTree.elements (QP.prog_defs p))).
Proof.
  unfold prog_funct. unfold QPprog_funct.
  pose proof (PTree.elements_keys_norepet (QP.prog_defs p)).
  assert (HG': forall i v, In (i, Gvar v) (PTree.elements (QP.prog_defs p)) -> g (i, Gvar v) = false).
    intros. apply PTree.elements_complete in H0; auto.
  clear HG.
 forget (PTree.elements (QP.prog_defs p)) as l.
  induction l; simpl. trivial.
  destruct a as [i d]. destruct d; simpl.
  + rewrite GF. inv H.
    destruct (g (i, Gfun f0)); simpl; f_equal; apply IHl; auto;
    intros; apply HG'; simpl; auto. 
  + inv H. rewrite HG'; simpl; auto. apply IHl; auto.
    intros; apply HG'; simpl; auto.
Qed.

Lemma Canonical_semaxfunc {Espec E} p Exp GP G
      (c: @CanonicalComponent Espec E nil p Exp GP G):
   @semaxfunc Espec (Comp_cs c) (QPvarspecs p) (Comp_G c) (QPglobalenv p) 
             (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ map fst E)) 
                     (QPprog_funct p))
             G.
Proof.
  specialize (Comp_G_justified c); intros. destruct c as [c DOM]; simpl.
  simpl in *.
  assert (LNRfuncs: list_norepet (map fst (QPprog_funct p))). {
    clear.
    unfold QPprog_funct.
    pose proof (PTree.elements_keys_norepet (QP.prog_defs p)).
    induction (PTree.elements (QP.prog_defs p)).
    constructor. 
    destruct a. destruct g; simpl in *.
    inv H. constructor; auto.
    clear - H2. contradict H2. induction l; simpl; auto. destruct a. destruct g; simpl in *; auto. destruct H2; auto; right. inv H; auto.
  }
  apply SF_semaxfunc.
+ intros. apply find_id_filter_Some in H0; trivial.
   destruct H0. apply H; auto.
   clear - H0.
   unfold QPprog_funct in *. 
   rewrite <- find_id_elements.
    pose proof (PTree.elements_keys_norepet (QP.prog_defs p)).
    induction  (PTree.elements (QP.prog_defs p)).
    inv H0.
    destruct a. destruct g; simpl in *. if_tac. congruence.
    apply IHl; auto. inv H; auto.
    if_tac. subst p0. elimtype False; clear - H0 H.
    inv H. apply H3; clear H3 H4. induction l; simpl in *. inv H0. destruct a. destruct g; auto.
    simpl in *. if_tac in H0; auto. apply IHl; auto. inv H; auto.
+ apply list_norepet_map_fst_filter; auto.
+ unfold Comp_G in *. rewrite DOM; clear DOM H LNRfuncs.
  apply filter_prog_funct_defs; intros; simpl. trivial.
  destruct (in_dec ident_eq i (IntIDs p ++ map fst E)); simpl; trivial.
  apply in_app_or in i0; destruct i0.
  - destruct (IntIDs_e H0) as [f Hf]; trivial. congruence.
  - apply (Comp_Externs c) in H0. destruct H0 as [ef [tys [rt [cc Hf]]]].
    congruence.
Qed.

Lemma filter_true {A f}: forall (l:list A) (Hf: forall i, In i l -> f i=true),
      filter f l = l.
Proof.
  induction l; simpl; intros; auto. rewrite (Hf a).
  rewrite IHl; trivial. intros. apply Hf. right; trivial. left; trivial.
Qed.

Lemma Canonical_semax_func {Espec E p Exp GP G}
      (c: @CanonicalComponent Espec  E nil p Exp GP G)
      (HE: map fst E =
           map fst (filter (fun x  => negb (isInternal (Gfun (snd x)))) (QPprog_funct p))):
      @semax_func Espec (QPvarspecs p) (Comp_G c) (Comp_cs c) (QPglobalenv p) (QPprog_funct p) (Comp_G c).
Proof.
  apply semaxfunc_sound.
  specialize (Canonical_semaxfunc _ _ _ _ c).
  rewrite filter_true; trivial.
  rewrite HE; clear; intros. 
  destruct (in_dec ident_eq (fst i)
    (IntIDs p ++ map fst
       (filter (fun x => negb (isInternal (Gfun (snd x)))) (QPprog_funct p))) ); simpl; trivial.
  elim n; clear n. destruct i as [i d]; simpl. unfold IntIDs, prog_funct in *.
  unfold QPprog_funct in *.
  forget (PTree.elements (QP.prog_defs p)) as l. clear p.
  induction l; simpl in *; trivial.
  destruct a as [j a]; simpl in *. destruct a; simpl in *; [|auto].
  destruct f; simpl in *.
  + destruct H; [ inv H; left; trivial | right; auto].
  + destruct H.
    - inv H; simpl. apply in_or_app. right; left; trivial.
    - apply in_or_app. specialize (IHl H); apply in_app_or in IHl.
      destruct IHl; [ left; trivial | right; right; trivial].
Qed.

(*******************Material related to automation *****************************)


Inductive SF_internal C V (ge : Genv.t Clight.fundef type) G id f phi:=
_SF_internal:
  (id_in_list id (map fst G) && semax_body_params_ok f)%bool = true ->
  Forall (fun it : ident * type => complete_type (@cenv_cs C)(snd it) = true) (fn_vars f) ->
  var_sizes_ok (*cenv_cs*) (fn_vars f) ->
  fn_callconv f = callingconvention_of_funspec phi ->
  semax_body V G f (id, phi) -> genv_find_func ge id (Internal f) ->
  SF_internal C V ge G id f phi.

Lemma SF_internal_sound {Espec cs V} {ge : Genv.t Clight.fundef type} G i f phi:
  SF_internal cs V ge G i f phi -> @SF Espec cs V ge G i (Internal f) phi.
Proof. simpl; intros. inv H. red. intuition. Qed.

Ltac findentry := repeat try first [ left; reflexivity | right].

Ltac finishComponent :=
    intros i phi E; simpl in E;
    repeat (if_tac in E;
            [inv E; eexists; split; [ reflexivity
                                    | try solve [apply funspec_sub_refl]]
            | ]);
    try solve [discriminate].

Ltac lookup_tac := 
    intros H;
    repeat (destruct H; [ repeat ( first [ solve [left; trivial] | right]) | ]); try contradiction.

Lemma semax_vacuous:
 forall cs Espec Delta pp frame c post,
  @semax cs Espec Delta (fun rho => (close_precondition pp) FF rho * frame rho)%logic
      c post.
Proof.
intros.
eapply semax_pre; [ | apply semax_ff].
apply andp_left2.
intro rho.
rewrite sepcon_comm.
apply sepcon_FF_derives'.
unfold close_precondition.
apply exp_left; intro.
apply andp_left2.
unfold FF; simpl.
auto.
Qed.

Ltac SF_vacuous :=
   match goal with |- SF _ _ _ (vacuous_funspec _) => idtac end;
   repeat (split; [solve[constructor] | ]);
  split; [ | eexists; split; compute; reflexivity];
  split3; [reflexivity | reflexivity | intros ];
  apply semax_vacuous.

Lemma compspecs_ext:
 forall cs1 cs2 : compspecs,
 @cenv_cs cs1 = @cenv_cs cs2 ->
 @ha_env_cs cs1 = @ha_env_cs cs2 ->
 @la_env_cs cs1 = @la_env_cs cs2 ->
 cs1 = cs2.
Proof.
intros.
destruct cs1,cs2.
simpl in *; subst.
f_equal; apply proof_irr.
Qed.

Record compositeData :=
  { cco_su : struct_or_union;
    cco_members : members;
    cco_attr : attr;
    cco_sizeof : Z;
    cco_alignof : Z;
    cco_rank : nat }.

Definition getCompositeData (c:composite):compositeData. destruct c.
apply (Build_compositeData co_su co_members co_attr co_sizeof co_alignof co_rank).
Defined.

Lemma composite_env_ext:
 forall ce1 ce2, 
 PTree.map1 getCompositeData ce1 =
 PTree.map1 getCompositeData ce2 ->
 ce1 = ce2.
Proof.
induction ce1; destruct ce2; simpl; intros; auto; try discriminate.
inv H.
f_equal; auto.
destruct o,o0; inv H2; auto.
clear - H0.
f_equal.
destruct c,c0; inv H0; simpl in *; subst; f_equal; apply proof_irr.
Qed.

Definition QPprog {cs: compspecs} (p: Clight.program) :=
  QPprogram_of_program p ha_env_cs la_env_cs.

Definition compspecs_of_QPprogram (prog: Clight.program)
          ha_env la_env OK :=
compspecs_of_QPcomposite_env
  (QP.prog_comp_env
     (QPprogram_of_program prog ha_env la_env)) OK.

Lemma compspecs_eq_of_QPcomposite_env:
forall cs (prog: Clight.program) OK,
 PTree.map1 getCompositeData (@cenv_cs cs) =
 PTree.map1 getCompositeData (prog_comp_env prog) ->
 PTree_samedom  (@cenv_cs cs) (@ha_env_cs cs) ->
 PTree_samedom  (@cenv_cs cs) (@la_env_cs cs) ->
 cs = compspecs_of_QPprogram prog (@ha_env_cs cs) (@la_env_cs cs) OK.
Proof.
intros.
assert (@cenv_cs cs = prog_comp_env prog)
 by (apply composite_env_ext; auto).
destruct OK as [? [? [? [? [? [? ?]]]]]].
simpl.
apply compspecs_ext; simpl.
clear - H0 H1 H2.
unfold QPprogram_of_program in x.
simpl in x.
forget (prog_comp_env prog) as ce.
clear prog.
subst ce.
rewrite composite_env_of_QPcomposite_env_of_composite_env. auto.
apply PTree_samedom_domain_eq; auto.
apply PTree_samedom_domain_eq; auto.
unfold QPcomposite_env_of_composite_env.
rewrite PTree_map1_map3.
symmetry; apply PTree_map3_2; rewrite <- H2; auto.
unfold QPcomposite_env_of_composite_env.
rewrite PTree_map1_map3.
symmetry; apply PTree_map3_3; rewrite <- H2; auto.
Qed.

Lemma QPcompspecs_OK_i':
 forall (cs: compspecs) ce ha la, 
 ce = @cenv_cs cs ->
 ha = @ha_env_cs cs ->
 la = @la_env_cs cs ->
 @PTree_samedom composite Z ce ha->
 @PTree_samedom composite legal_alignas_obs ce la ->
 QPcompspecs_OK
    (QPcomposite_env_of_composite_env ce ha la).
Proof.
intros.
subst.
apply QPcompspecs_OK_i; auto.
Qed.

Ltac decompose_in_elements H :=
match type of H with
 | (?i,_)=_ \/ _ => 
   destruct H as [H|H];
   [let j := eval compute in i in change i with j in H;
                injection H; clear H; intros; subst 
  | decompose_in_elements H ]
 | False => contradiction H
 | _ => idtac
 end.

Fixpoint fold_ident {A} (i: positive) (al: list (ident * A)) : ident :=
 match al with
 | (j,_)::al' => if Pos.eqb i j then j else fold_ident i al'
 | nil => i
end.

Ltac mkComponent prog :=
 let p := fresh "p" in
 match goal with |- @Component _ _ _ ?pp _ _ _ => set (p:=pp) end;
 let HA := fresh "HA" in 
   assert (HA: PTree_samedom cenv_cs ha_env_cs) by repeat constructor;
 let LA := fresh "LA" in 
   assert (LA: PTree_samedom cenv_cs la_env_cs) by repeat constructor;
 let OK := fresh "OK" in
 assert (OK: QPprogram_OK p);
 [split; [apply compute_list_norepet_e; reflexivity | ];
   simpl;
   simple apply (QPcompspecs_OK_i' _);
   [ apply composite_env_ext; repeat constructor | reflexivity | reflexivity | assumption | assumption ]
 | ];
 assert (CSeq: _ = compspecs_of_QPcomposite_env 
                 (QP.prog_comp_env (QPprogram_of_program prog ha_env_cs la_env_cs))
                     (proj2 OK))
   by (apply compspecs_eq_of_QPcomposite_env;
          [reflexivity | assumption | assumption]);
 change (QPprogram_of_program prog ha_env_cs la_env_cs) with p in CSeq;
 exists OK;
  [ let i := fresh in let H := fresh in 
    intros i H; 
    first [ repeat (destruct H; [subst; do 4 eexists; findentry; reflexivity  |]); contradiction
          | (*fail 99 "SC1"*)idtac ]
  | apply compute_list_norepet_e; reflexivity
  | apply compute_list_norepet_e; reflexivity
  | let i := fresh in let H := fresh in 
    intros i H; first [ solve contradiction | simpl in H];
    repeat (destruct H; [ subst; do 4 eexists; reflexivity |]); try contradiction
  | intros; simpl; split; trivial; try solve [lookup_tac]
  | apply compute_list_norepet_e; reflexivity
  | let i := fresh in let H := fresh in 
    intros i H; first [ solve contradiction | simpl in H];
    repeat (destruct H; [ subst; reflexivity |]); try contradiction
  |   let i := fresh "i" in let H := fresh in let H0 := fresh in 
    let phi := fresh "phi" in let fd := fresh "fd" in 
    intros i phi fd H H0;
    apply PTree.elements_correct in H;
    simpl in H;
    decompose_in_elements H;
    inv H0;
    try SF_vacuous;
    clear - CSeq;
    match goal with |- SF _ ?i _ _ =>
      let j := constr:(fold_ident i prog.(prog_defs)) in
      let j := eval red in j in let j := eval simpl in j in 
       change i with j
    end
  | finishComponent
  | first [ solve [intros; apply derives_refl] | solve [intros; reflexivity] | solve [intros; simpl; cancel] | idtac]
  ].


Ltac mkVSU prog internal_specs := 
 lazymatch goal with |- VSU _ _ _ _ _ => idtac
  | _ => fail "mkVSU must be applied to a VSU goal"
 end;
 exists internal_specs;
 mkComponent prog.

(*
 Ltac findentry_cautious := cbv.

 Ltac mkComponent_cautious :=
  eapply Build_Component;
   [ intros i H; (first
      [ repeat (destruct H; [ subst; do 4 eexists; findentry_cautious; reflexivity |  ]); contradiction | idtac ])
   | apply compute_list_norepet_e; reflexivity
   | apply compute_list_norepet_e; reflexivity
   | apply compute_list_norepet_e; reflexivity
   | intros i H; (first [ solve ltac:(contradiction) | simpl in H ]);
      repeat (destruct H; [ subst; do 4 eexists; reflexivity |  ]); try contradiction
   | intros; (*simpl*)cbv; split; trivial; try (solve [ lookup_tac ])
   | apply compute_list_norepet_e; reflexivity
   | intros i H; (first [ solve ltac:(contradiction) | simpl in H ]); repeat (destruct H; [ subst; reflexivity |  ]);
      try contradiction
   | intros i phi fd H H0; simpl in H0;
     repeat (if_tac in H0; [ inv H0; cbv in H; inv H |  ]); try discriminate
     (*.intros i phi fd H H0; simpl in H; repeat (if_tac in H; [ inv H; inv H0 |  ]; try discriminate)*)
   | finishComponent
   | intros; (first [ solve [ apply derives_refl ] | solve [ reflexivity ] | solve [ simpl; cancel ] | idtac ]) ].
*)

Ltac solve_SF_internal P :=
  apply SF_internal_sound; eapply _SF_internal;
   [  reflexivity 
   | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
   | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
   | reflexivity
   | match goal with OK: QPprogram_OK _, CSeq: @eq compspecs _ _ |- _ =>
       rewrite <- CSeq;
       clear CSeq OK
     end;
     apply P
   | eexists; split; [ LookupID | LookupB ]
   ].

(*slightly slower*)
Ltac solve_SF_external_with_intuition B :=
   first [simpl; split; intuition; [ try solve [entailer!] | try apply B | eexists; split; cbv; reflexivity ] | idtac].

(*Slightly faster*)
Ltac solve_SF_external B :=
  first [ split3;
            [ reflexivity 
            | reflexivity 
            | split3;
                [ reflexivity
                | reflexivity
                | split3;
                   [ left; trivial
                   | clear; intros ? ? ? ?; try solve [entailer!];
                     repeat match goal with |- (let (y, z) := ?x in _) _ && _ |--  _ =>
                                     destruct x as [y z]
                     end
                    | split; [ try apply B | eexists; split; cbv; reflexivity ]
            ] ] ]
        | idtac ].

Fixpoint FDM_entries (funs1 funs2 : list (ident * fundef function)): option (list (ident * fundef function * fundef function)) :=
  match funs1 with
    nil => Some nil
  | (i, fd1) :: funs => match find_id i funs2 with 
                           None => FDM_entries funs funs2 
                         | Some fd2 => match FDM_entries funs funs2 with
                                         None => None
                                       | Some l => Some ((i, fd1, fd2) :: l)
                                       end
                        end
  end.

Definition check_FDM_entry (Imports1 Imports2:funspecs)  x :=
  match x with (i, fd1, fd2) =>
   match fd1, fd2 with
      Internal _, Internal _ => fd1 = fd2
    | Internal _, External _ _ _ _ => match find_id i Imports2 with
                                        None => False
                                      | Some phi2 => signature_of_fundef fd1 = signature_of_fundef fd2
                                      end
    | External _ _ _ _, Internal _ => match find_id i Imports1 with
                                        None => False
                                      | Some phi1 => signature_of_fundef fd1 = signature_of_fundef fd2
                                      end
    | External _ _ _ _, External _ _ _ _ => fd1 = fd2
   end
  end.

Lemma FDM {p1 p2 Imports1 Imports2}: forall entries,
  FDM_entries (QPprog_funct p1) (QPprog_funct p2) = Some entries ->
  Forall (check_FDM_entry Imports1 Imports2) entries ->
  Fundefs_match p1 p2 Imports1 Imports2.
Proof. 
  intros.
  hnf; intros.
  unfold QPprog_funct in H.
  rewrite <- find_id_elements in H1, H2.
  forget (PTree.elements (QP.prog_defs p1)) as d1.
  forget (PTree.elements (QP.prog_defs p2)) as d2.
  clear p1 p2.
  revert d2 H2 entries H H0; induction d1 as [|[j [?|?]]]; simpl; intros.
  -
   inv H. inv H1.
  -
    simpl in H1.
    if_tac in H1.
    +
      subst j. inv H1.
      assert (find_id i (QPprog_funct' d2) = Some fd2). {
         clear - H2.
         induction d2 as [|[??]]; simpl in *. inv H2.
         if_tac in H2. inv H2. simpl. rewrite if_true by auto. auto.
         apply IHd2 in H2. destruct g. simpl. rewrite if_false by auto; auto. auto.
      }
      rewrite H1 in H.
      destruct (FDM_entries (QPprog_funct' d1) (QPprog_funct' d2)) eqn:?H; inv H.
      inv H0. hnf in H5.
      destruct fd1, fd2; auto.
      destruct (find_id i Imports2) eqn:?H; try contradiction; eauto.
      destruct (find_id i Imports1) eqn:?H; try contradiction; eauto.
   +
       specialize (IHd1 H1).
       destruct (find_id j (QPprog_funct' d2)) eqn:?H.
     *
       destruct (FDM_entries (QPprog_funct' d1) (QPprog_funct' d2)) eqn:?H; inv H.
       inv H0. eapply IHd1; eauto.
     * eapply IHd1;  eauto.
  -
    simpl in H1.
    if_tac in H1. inv H1.
    eapply IHd1; eauto.
Qed.

(*
Lemma FDM_complete {p1 p2 Imports1 Imports2}
  (FM: Fundefs_match p1 p2 Imports1 Imports2) 
(*  (LNRp1:list_norepet (map fst (prog_defs p1))) *):
  exists entries,
  FDM_entries (QPprog_funct p1) (QPprog_funct p2) = Some entries /\
  Forall (check_FDM_entry Imports1 Imports2) entries.
Proof. rewrite Fundefs_match_eq in FM. 
  remember (QPprog_funct p1) as funs1.
  assert (LNR1: list_norepet (map fst funs1)).
  {subst. clear. unfold QPprog_funct.
   pose proof (PTree.elements_keys_norepet (QP.prog_defs p1)).
   induction (PTree.elements (QP.prog_defs p1)). constructor.
   inv H. destruct a,g; simpl; auto. constructor; auto.
  contradict H2. clear - H2; induction l; simpl in *; auto.
   destruct a,g; simpl in *; auto. destruct H2; auto.
  }
  forget (QPprog_funct p2) as funs2.
  clear Heqfuns1 p1 p2. generalize dependent funs2.
  induction funs1; simpl; intros.
- exists nil. split; auto.
- destruct a as [i fi1]. inv LNR1.
  remember (find_id i funs2) as I2; destruct I2; [ symmetry in HeqI2 | ].
  2:{ apply IHfuns1; clear IHfuns1; trivial. intros.
      apply (FM i0); trivial. rewrite if_false; trivial. congruence. }
  rename f into fi2.
  assert (FMi := FM i). rewrite if_true in FMi by trivial.
  specialize (FMi _ _ (eq_refl _) HeqI2).
  destruct (IHfuns1 H2 funs2) as [l [L1 L2]]; clear IHfuns1.
  + clear FMi. intros. apply (FM i0); trivial. rewrite if_false; trivial.
    apply assoclists.find_id_None_iff in H1. congruence.
  + clear FM. rewrite L1. eexists; split. reflexivity. constructor; trivial.
    simpl. destruct fi1; destruct fi2; trivial.
    * destruct FMi as [? [phi2 X]]; rewrite X; trivial. 
    * destruct FMi as [? [phi2 X]]; rewrite X; trivial.
Qed.

*)

Fixpoint FP_entries1 (funs1 funs2 funs: list (ident * fundef function)):=
  match funs1 with
    nil => Some nil
  | (i, Internal f1) :: funs1' => match find_id i funs with 
                                    None => None
                                  | Some fd => match FP_entries1 funs1' funs2 funs with
                                                 None => None
                                               | Some l => Some ((Internal f1,fd)::l)
                                               end
                                  end
  | (i, External ef1 tys1 rt1 cc1) :: funs1' => 
        match find_id i funs2, find_id i funs with
          Some (Internal f2), Some fd => match FP_entries1 funs1' funs2 funs with
                                                 None => None
                                               | Some l => Some ((Internal f2,fd)::l)
                                         end
        | _, Some fd => match FP_entries1 funs1' funs2 funs with
                                                 None => None
                                               | Some l => Some ((External ef1 tys1 rt1 cc1,fd)::l)
                        end
        | _, _ => None
        end
  end.

Definition Functions_preserved_A (funs1 funs2 funs: list (ident * fundef function)) i:=
         match find_id i funs1, find_id i funs2 with
           Some (Internal f1), _ => find_id i funs = Some (Internal f1)
         | _, Some (Internal f2) => find_id i funs = Some (Internal f2)
         | Some (External ef1 tys1 rt1 cc1), _ =>
               find_id i funs = Some (External ef1 tys1 rt1 cc1)
         | _, Some (External ef2 tys2 rt2 cc2) =>
               find_id i funs = Some (External ef2 tys2 rt2 cc2)
         | None, None => True
         end.

Lemma FP_entries1_soundA: forall {funs1 funs2 funs entries}
      (FP: FP_entries1 funs1 funs2 funs = Some entries) 
      (HE: Forall (fun x => fst x = snd x) entries),
  forall i fd, find_id i funs1 = Some fd -> Functions_preserved_A funs1 funs2 funs i.
Proof. intros funs1 .
  unfold Functions_preserved_A. induction funs1; simpl; intros. inv H.
  destruct a as [j f1j]. if_tac; subst.
  { inv H. clear IHfuns1. destruct fd.
    + remember (find_id j funs) as q; destruct q; [ | discriminate].
      destruct (FP_entries1 funs1 funs2 funs); inv FP. inv HE. simpl in H1. subst; trivial.
    + remember (find_id j funs2) as w; destruct w; symmetry in Heqw.
      - destruct f. 
        * remember (find_id j funs) as q; destruct q; [ | discriminate]. 
          destruct (FP_entries1 funs1 funs2 funs); inv FP. inv HE. simpl in H1. subst; trivial.
        * remember (find_id j funs) as q; destruct q; [ | discriminate]. 
          destruct (FP_entries1 funs1 funs2 funs); inv FP. inv HE. simpl in H1. subst; trivial.
      - remember (find_id j funs) as q; destruct q; [ | discriminate]. 
        destruct (FP_entries1 funs1 funs2 funs); inv FP. inv HE. simpl in H1. subst; trivial. }
  destruct f1j. 
  + remember (find_id j funs) as q; destruct q; [symmetry in Heqq | discriminate]. 
    remember (FP_entries1 funs1 funs2 funs) as t; destruct t; inv FP. symmetry in Heqt.
    inv HE. simpl in H3. subst. rewrite H.
    specialize (IHfuns1 _ _ _ Heqt H4 _ _ H). rewrite H in IHfuns1. trivial.
  + rewrite H. 
    remember (find_id j funs2) as r; destruct r; symmetry in Heqr.
    - destruct f.
      * remember (find_id j funs) as q; destruct q; [symmetry in Heqq | discriminate].
        remember (FP_entries1 funs1 funs2 funs) as u; destruct u; inv FP. symmetry in Hequ.
        inv HE. simpl in H3. subst.
        specialize (IHfuns1 _ _ _ Hequ H4 _ _ H). rewrite H in IHfuns1. trivial.
      * remember (find_id j funs) as q; destruct q; [symmetry in Heqq | discriminate].
        remember (FP_entries1 funs1 funs2 funs) as u; destruct u; inv FP. symmetry in Hequ.
        inv HE. simpl in H3. subst.
        specialize (IHfuns1 _ _ _ Hequ H4 _ _ H). rewrite H in IHfuns1. trivial.
    - remember (find_id j funs) as q; destruct q; [symmetry in Heqq | discriminate].
        remember (FP_entries1 funs1 funs2 funs) as u; destruct u; inv FP. symmetry in Hequ.
        inv HE. simpl in H3. subst.
        specialize (IHfuns1 _ _ _ Hequ H4 _ _ H). rewrite H in IHfuns1. trivial.
Qed.  

Fixpoint FP_entries2 (funs2 funs: list (ident * fundef function)):=
  match funs2 with
    nil => Some nil
  | (i, fd2) :: funs2' => match find_id i funs with 
                                    None => None
                                  | Some fd => match FP_entries2 funs2' funs with
                                                 None => None
                                               | Some l => Some ((fd2,fd)::l)
                                               end
                                  end
  end.

Lemma FP_entries2_soundA: forall {funs2 funs1 funs entries}
      (FP: FP_entries2 funs2 funs = Some entries) 
      (HE: Forall (fun x => fst x = snd x) entries),
  forall i fd, find_id i funs1 = None -> find_id i funs2 = Some fd ->Functions_preserved_A funs1 funs2 funs i.
Proof. 
  unfold Functions_preserved_A. induction funs2; simpl; intros. inv H0.
  destruct a as [j f2j]. rewrite H. if_tac; subst.
  { inv H0. clear IHfuns2.
    remember (find_id j funs) as q; destruct q; [ | discriminate].
    destruct (FP_entries2 funs2 funs); inv FP. inv HE. simpl in H2. subst.
    destruct f; trivial. }
  rewrite H0.
  remember (find_id j funs) as q; destruct q; [symmetry in Heqq | discriminate]. 
  remember (FP_entries2 funs2 funs) as t; destruct t; inv FP. symmetry in Heqt.
  inv HE. simpl in H4. subst.
  specialize (IHfuns2 _ _ _ Heqt H5 _ _ H H0). rewrite H, H0 in IHfuns2; trivial.
Qed.

Lemma FP_entries2_soundA': forall {funs2 funs1 funs entries}
      (FP: FP_entries2 (filter (fun x => (negb (in_dec peq (fst x) (map fst funs1)))) funs2) funs = Some entries) 
      (HE: Forall (fun x => fst x = snd x) entries),
  forall i fd, find_id i funs1 = None -> find_id i funs2 = Some fd ->Functions_preserved_A funs1 funs2 funs i.
Proof. 
  unfold Functions_preserved_A. induction funs2; simpl; intros. inv H0.
  destruct a as [j f2j]. simpl in FP. rewrite H. if_tac; subst.
  { inv H0. clear IHfuns2. destruct (in_dec peq j (map fst funs1)); simpl in FP.
    1: apply assoclists.find_id_None_iff in H; contradiction.
    remember (find_id j funs) as q; destruct q; [ | discriminate].
    destruct (FP_entries2 (filter (fun x : positive * fundef function => negb (in_dec peq (fst x) (map fst funs1))) funs2) funs); inv FP.
    inv HE. simpl in H2. subst.
    destruct f; trivial. }
  rewrite H0. simpl in FP.
  destruct (negb (in_dec peq j (map fst funs1))).
  + inv FP.
    remember (find_id j funs) as q; destruct q; [symmetry in Heqq | discriminate]. 
    remember (FP_entries2 (filter (fun x : positive * fundef function => negb (in_dec peq (fst x) (map fst funs1))) funs2) funs) as t; destruct t; inv H3.
    symmetry in Heqt.
    inv HE. simpl in H4. subst.
    specialize (IHfuns2 _ _ _ Heqt H5 _ _ H H0). rewrite H, H0 in IHfuns2; trivial.
  + specialize (IHfuns2 _ _ _ FP HE _ _ H H0). rewrite H, H0 in IHfuns2; trivial.
Qed.

Definition FP_entries_inv ids1 ids2 ids:=
  forallb (fun i => in_dec peq i (ids1++ids2)) ids.

Definition FP_entries_inv_sound {ids}: forall {ids1 ids2} (H:FP_entries_inv ids1 ids2 ids = true),
  forall i, In i ids -> In i ids1 \/ In i ids2.
Proof.
  induction ids; simpl; intros. contradiction.
  apply andb_true_iff in H; destruct H. destruct H0; subst. 2: auto.
  apply in_app_or. forget (ids1 ++ ids2) as l. clear - H. destruct (in_dec peq i l); trivial; inv H.
Qed.

Lemma semaxfunc_Ext_elim {Espec cs V G ge funs specs} (Sfunc: @semaxfunc Espec cs V G ge funs specs):
   forall i ef argsig retsig cc phi, 
          find_id i funs = Some (External ef argsig retsig cc) ->
          find_id i specs = Some phi ->
   @semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi.
Proof. induction Sfunc; simpl; intros; try discriminate.
+ if_tac in H1; subst; try discriminate; auto.
+ if_tac in H1; subst; inv H1; inv H2; auto.
Qed. 

Lemma semaxfunc_Int_elim {Espec cs V G ge funs specs} (Sfunc: @semaxfunc Espec cs V G ge funs specs):
   forall i f phi, 
          find_id i funs = Some (Internal f) ->
          find_id i specs = Some phi ->
   @semaxfunc_InternalInfo cs V G ge i f phi.
Proof. induction Sfunc; simpl; intros; try discriminate.
+ if_tac in H1; subst. inv H1; inv H2; auto. auto.
+ if_tac in H1; subst. discriminate. auto.
Qed.
 
Lemma semaxfunc_elim {Espec cs V G ge funs specs} (Sfunc: @semaxfunc Espec cs V G ge funs specs) i:
   match find_id i funs, find_id i specs with
     Some (Internal f), Some phi => @semaxfunc_InternalInfo cs V G ge i f phi
   | Some (External ef argsig retsig cc), Some phi => @semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi
   | _, _ => True
end.
Proof. induction Sfunc; simpl; intros; trivial.
if_tac; subst; trivial.
if_tac; subst; trivial.
Qed.

Lemma delete_id_elim{A}: forall {G i x GG}, 
      @delete_id A i G = Some (x, GG) ->
      exists n, G = firstn n GG ++ (i, x) :: skipn n GG.
Proof. induction G; simpl; intros. inv H. destruct a as [j b].
destruct (ident_eq i j); subst.
+ inv H. exists O; simpl; trivial.
+ specialize (IHG i). destruct (delete_id i G); [ | inv H].
   destruct p; inv H. destruct (IHG _ _ (eq_refl _)) as [k K]; clear IHG.
   subst. exists (S k); simpl; trivial.
Qed.

Module FunspecOrder <: Orders.TotalLeBool.
  Definition t := (ident * funspec)%type.
  Definition leb := fun x y : (ident * funspec)=> Pos.leb (fst x) (fst y).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.  intros. unfold leb. 
    pose proof (Pos.leb_spec (fst a1) (fst a2)).
    pose proof (Pos.leb_spec (fst a2) (fst a1)).
    inv H; inv H0; auto.
    clear - H2 H3. 
    pose proof (Pos.lt_trans _ _ _ H2 H3).
    apply Pos.lt_irrefl in H. contradiction.
  Qed.
End FunspecOrder.
Module SortFunspec := Mergesort.Sort(FunspecOrder).

Require Import VST.veric.initial_world.

Lemma perm_In_map_fst {A}: forall {G:list (ident*A)} {G'} (P: Permutation G G') i,
      In i (map fst G') -> In i (map fst G).
Proof. intros G G' P. induction P; simpl; intros; trivial.
+ destruct x; simpl in *; intros.
  destruct H; [ left; trivial | right; auto].
+ destruct H as [? | [? | ?]]. right; left; trivial. left; trivial. right; right; trivial.
+ apply IHP1. apply IHP2; trivial.
Qed.
 
Lemma perm_LNR {A}: forall {G:list (ident * A)} {G'} (P: Permutation G G')
      (LNR: list_norepet (map fst G)),
      list_norepet (map fst G').
Proof. intros G G' P. induction P; simpl; intros; trivial; auto.
+ destruct x. inv LNR. constructor; eauto. simpl.
  intros N. apply H1. apply (perm_In_map_fst P); trivial.
+ inv LNR. inv H2. constructor.
  - intros N. destruct N; auto. rewrite H in *; apply H1; left; trivial.
  - constructor; trivial. intros N. apply H1. right; trivial.
Qed.

Lemma perm_find_id {A}: forall (G:list (ident * A)) G' (P: Permutation G G')
      (LNR: list_norepet (map fst G)) i,
      find_id i G = find_id i G'.
Proof. intros G G' P. induction P; simpl; intros; trivial.
+ destruct x. inv LNR. rewrite IHP; trivial.
+ destruct y. destruct x; simpl in *. inv LNR. inv H2.
  destruct (Memory.EqDec_ident i i0); subst; trivial.
  rewrite if_false; trivial. intros N; subst. apply H1; left; trivial.
+ rewrite IHP1; trivial. apply IHP2.
  apply (perm_LNR P1); trivial.
Qed.

Lemma sort_In_map_fst_i {G i}:
      In i (map fst G) -> In i (map fst (SortFunspec.sort G)).
Proof.
intros; eapply perm_In_map_fst; try eassumption.
apply Permutation_sym. apply SortFunspec.Permuted_sort.
Qed.

Lemma sort_In_map_fst_e {G i}:
      In i (map fst (SortFunspec.sort G)) -> In i (map fst G).
Proof.
intros; eapply perm_In_map_fst; try eassumption.
apply SortFunspec.Permuted_sort.
Qed.

Lemma sort_In_map_fst {G i}:
      In i (map fst G) <-> In i (map fst (SortFunspec.sort G)).
Proof.
split; intros; [ apply sort_In_map_fst_i | apply sort_In_map_fst_e]; trivial.
Qed. 

Lemma LNR_sort_i {G}: list_norepet (map fst G) ->
      list_norepet (map fst (SortFunspec.sort G)).
Proof.
intros; eapply perm_LNR; try eassumption.
apply SortFunspec.Permuted_sort.
Qed.

Lemma LNR_sort_e {G}:
      list_norepet (map fst (SortFunspec.sort G))
      -> list_norepet (map fst G).
Proof.
intros; eapply perm_LNR; try eassumption.
apply Permutation_sym. apply SortFunspec.Permuted_sort.
Qed.

Lemma sort_LNR {G}: list_norepet (map fst G) <->
      list_norepet (map fst (SortFunspec.sort G)).
Proof.
split; intros; eapply perm_LNR; try eassumption.
apply SortFunspec.Permuted_sort.
apply Permutation_sym. apply SortFunspec.Permuted_sort.
Qed.

Lemma sort_find_id {G i} (LNR: list_norepet (map fst G)) :
      find_id i G = find_id i (SortFunspec.sort G).
Proof.
apply perm_find_id; trivial.
apply SortFunspec.Permuted_sort.
Qed.

Ltac prove_cspecs_sub := 
   try solve [split3; intros ?i; apply sub_option_get; repeat constructor].

Ltac solve_entry H H0:=
     inv H; inv H0; first [ solve [ trivial ] | split; [ reflexivity | eexists; reflexivity] ].

Definition list_disjoint_id (al bl: list ident) :=
  Forall (fun i => id_in_list i bl = false) al.

Lemma list_disjoint_id_e: 
 forall (al bl: list ident), 
  (list_disjoint_id al bl) ->
  list_disjoint al bl.
Proof.
intros.
induction H.
intros ? ? ? ? ?. inv H.
apply id_in_list_false in H.
apply list_disjoint_cons_l; auto.
Qed.

Ltac LDI_tac := 
   apply Forall_nil ||  (apply Forall_cons; [ reflexivity | LDI_tac ]).

Ltac LNR_tac := apply compute_list_norepet_e; reflexivity.

Ltac list_disjoint_tac := (*red; simpl; intros; contradiction.*)
     apply list_norepet_append_inv; LNR_tac.

Ltac ExternsHyp_tac := first [ reflexivity | idtac ].

Inductive Identifier_not_found: ident -> funspecs -> Prop := .
Inductive Funspecs_must_match (i: ident) (f1 f2: funspec):  Prop := 
mk_Funspecs_must_match: f1=f2 -> Funspecs_must_match i f1 f2.

Fixpoint SC_test (ids: list ident) (fds1 fds2: funspecs) : Prop :=
 match fds1 with
 | (i,fd)::fds' => if id_in_list i ids
                         then match initial_world.find_id i fds2 with
                                 | Some fd2 => Funspecs_must_match i fd fd2 
                                 | None => Identifier_not_found i fds2
                                 end /\ SC_test ids fds' fds2
                         else SC_test ids fds' fds2
 | nil => True
 end.

Lemma SC_lemma: forall (ids: list ident) (fds1 fds2: funspecs),
 SC_test ids fds1 fds2 ->
(forall (i:ident) (phi1: funspec),
  initial_world.find_id i fds1 = Some phi1 ->
  In i ids ->
  exists phi2 : funspec, 
  initial_world.find_id i fds2 = Some phi2 /\ funspec_sub phi2 phi1).
Proof.
intros ? ? ?.
induction fds1 as [|[i?]]; simpl; intros.
inv H0.
if_tac in H0.
subst i0; inv H0.
rewrite assoclists.id_in_list_true_i in H by auto.
destruct H.
destruct (initial_world.find_id i fds2) eqn:?H.
inv H.
exists f; split; auto.
apply funspec_sub_refl.
inv H.
destruct (id_in_list i ids) eqn:?H.
destruct H.
destruct (initial_world.find_id i fds2) eqn:?H.
eauto.
eauto.
eauto.
Qed.

Lemma VSULink': 
    forall Espec E1 Imports1 p1 Exports1 E2 Imports2 p2 Exports2
         GP1 GP2
         (vsu1 : @VSU Espec E1 Imports1 p1 Exports1 GP1)
         (vsu2 : @VSU Espec E2 Imports2 p2 Exports2 GP2)
         E Imports p Exports,
       E = G_merge E1 E2 ->
       Imports = VSULink_Imports vsu1 vsu2 ->
       Exports = G_merge Exports1 Exports2 ->
       QPlink_progs p1 p2 = Errors.OK p ->
       Fundefs_match p1 p2 Imports1 Imports2 ->
       list_disjoint_id (map fst E1) (IntIDs p2) ->
       list_disjoint_id (map fst E2) (IntIDs p1) ->
       SC_test (map fst E1 ++ IntIDs p1) Imports2 Exports1 ->
       SC_test (map fst E2 ++ IntIDs p2) Imports1 Exports2 ->
       (forall (i : ident) (phi1 phi2 : funspec),
        initial_world.find_id i Imports1 = Some phi1 ->
        initial_world.find_id i Imports2 = Some phi2 ->
        phi1 = phi2) ->
       VSU E Imports p Exports (GP1 * GP2)%logic.
Proof.
intros.
subst.
eapply VSULink; try eassumption.
apply list_disjoint_id_e; auto.
apply list_disjoint_id_e; auto.
apply SC_lemma; auto.
apply SC_lemma; auto.
Qed.

Ltac SC_tac :=
clear; simpl; repeat apply conj; try apply Logic.I;
((constructor; reflexivity) 
|| match goal with |- Funspecs_must_match ?i _ _ =>
     fail "funspecs don't match at identifier" i
    end).

Ltac HImports_tac := simpl;
  let i := fresh "i" in 
   intros i ? ? H1 H2;
  repeat (if_tac in H1; subst; simpl in *; try discriminate);
    (congruence || fail "Imports disagree at identifier" i).

Ltac ImportsDef_tac := first [ reflexivity | idtac ].
Ltac ExportsDef_tac := first [ reflexivity | idtac ].
Ltac domV_tac := compute; tauto.

Ltac find_id_subset_tac := simpl; intros ? ? H;
  repeat (if_tac in H; [ inv H; simpl; try reflexivity | ]); discriminate.

Ltac ComponentMerge C1 C2 :=
  eapply (ComponentJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 C2);
[ list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| LNR_tac
| LNR_tac
| prove_cspecs_sub
| prove_cspecs_sub
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
(*| FDM_tac *)
(*| FunctionsPreserved_tac *)
| apply list_disjoint_id_e; LDI_tac
| apply list_disjoint_id_e; LDI_tac
| ExternsHyp_tac
| apply SC_lemma; SC_tac
| apply SC_lemma; SC_tac
| HImports_tac
(*+  HContexts. This is the side condition we'd like to exliminate - it's also
   why we need to define SubjectComponent/ObserverComponent using DEFINED
  simpl; intros.
  repeat (if_tac in H; [ inv H; inv H0 | ]). discriminate.*)
| ImportsDef_tac
| ExportsDef_tac
| LNR_tac
| LNR_tac
| domV_tac
| try (cbv; reflexivity)
| try (cbv; reflexivity)
| try (cbv; reflexivity) 
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
].

Lemma VSU_ext {Espec E Imp p Exp GP1 GP2}:
      @VSU Espec E Imp p Exp GP1 -> GP1=GP2 ->
      @VSU Espec E Imp p Exp GP2.
Proof. intros; subst; trivial. Qed.

Ltac compute_QPlink_progs := 
match goal with |- ?A = _ => 
  let p1 := eval hnf in A in
  lazymatch p1 with
 | Errors.Error ?m => fail m
 | Errors.OK ?p' => instantiate (1:=@abbreviate _ p'); reflexivity
 | _ => fail "could not reduce QPlink_prog to hnf"
 end
end.

Ltac FDM_tac := 
  solve [eapply FDM; [ reflexivity | repeat constructor]];
  fail "FDM_tac failed".

Ltac VSULink_tac := 
eapply VSULink;
[ compute_QPlink_progs
| FDM_tac
| list_disjoint_tac
| list_disjoint_tac
| apply SC_lemma; SC_tac
| apply SC_lemma; SC_tac
| HImports_tac].

Ltac red_until_NDmk_funspec x :=
 match x with
 | NDmk_funspec _ _ _ _ _ => constr:(x)
 | _ => let x := eval red in x in red_until_NDmk_funspec x
 end.

Ltac simplify_funspecs G :=
  let x := eval hnf in G in 
 lazymatch x with
 | nil => constr:(x)
 | ?ia :: ?al => let al := simplify_funspecs al in
                       let ia := eval hnf in ia in
                       match ia with pair  ?i ?a =>
                             let b := red_until_NDmk_funspec a in
                              constr:( (i,@abbreviate _ b)::al )
                       end
 end.

Definition VSU_E {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := E.
Definition VSU_Exports {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := Exports.
Definition VSU_prog {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := p.
Definition VSU_Espec {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := Espec.
Definition VSU_GP {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP) := GP.

Ltac VSULink_type v1 v2 :=
  let Espec := constr:(VSU_Espec v1) in
  let Espec := eval unfold VSU_Espec in Espec in
  let GP := constr:(sepcon (VSU_GP v1) (VSU_GP v2)) in
  let GP := eval unfold VSU_GP in GP in 
  let E := constr:(G_merge (VSU_E v1) (VSU_E v2)) in
  let E := simplify_funspecs E in
  let Imports := constr:(VSULink_Imports v1 v2) in
  let Imports := simplify_funspecs Imports in
  let Exports := constr:(G_merge (VSU_Exports v1) (VSU_Exports v2)) in
  let Exports := simplify_funspecs Exports in
  let p' :=  constr:(QPlink_progs (VSU_prog v1) (VSU_prog v2)) in
  let p'' := eval vm_compute in p' in
  let p := lazymatch p'' with
               | Errors.OK ?p => constr:(@abbreviate _ p)
               | Errors.Error ?m => fail "QPlink_progs failed:" m
               end in
   constr:(@VSU Espec E Imports p Exports GP).

Ltac linkVSUs v1 v2 :=
  let t := VSULink_type v1 v2 in
 match t with @VSU ?Espec ?E ?Imports ?p ?Exports ?GP =>
   apply (VSULink' Espec _ _ _ _ _ _ _ _ _ _ v1 v2 E Imports p Exports)
  end;
  [ reflexivity | reflexivity | reflexivity | reflexivity
  | clear; FDM_tac
  | clear;  LDI_tac || fail "Externs of vsu1 overlap with Internals of vsu2"
  | clear;  LDI_tac || fail "Externs of vsu2 overlap with Internals of vsu1"
  | SC_tac
  | SC_tac
  | clear; HImports_tac
  ].

Definition VSU_of_Component {Espec E Imports p Exports GP G}
          (c: @Component Espec E Imports p Exports GP G) : 
             @VSU Espec E Imports p Exports GP :=
  existT _ G c.

Lemma progfunct_eq:SeparationLogic.prog_funct = prog_funct.
Proof. reflexivity. Qed.

Lemma augment_funspecs_find_id_None i: forall p G,
      find_id i G = None-> 
      find_id i (prog_funct p) = None ->
      find_id i (augment_funspecs p G) = None.
Proof.
  intros p. unfold augment_funspecs; rewrite progfunct_eq. forget (prog_funct p) as l. clear p.
  induction l; simpl; intros G.
+ intros. destruct G; simpl; intros; trivial.
+ destruct a as [j phi]; if_tac; subst; intros; try discriminate.
  remember (delete_id j G) as d; symmetry in Heqd; destruct d.
  - destruct p as [f GG]. specialize (IHl GG).
    destruct (augment_funspecs' l GG); trivial.
    simpl. rewrite if_false by trivial. apply IHl; trivial. 
    specialize (delete_id_elim Heqd) as [n N]. subst. clear - H0 H.
    rewrite assoclists.find_id_app_char in H0.
    rewrite <- (firstn_skipn n GG).
    rewrite assoclists.find_id_app_char.
    destruct (find_id i (firstn n GG)); trivial.
    simpl in H0. rewrite if_false in H0; trivial.
  - specialize (IHl G). destruct (augment_funspecs' l G); simpl; trivial.
    rewrite if_false; trivial. auto.
Qed.

Lemma augment_funspecs_eq: forall p G, map fst G = map fst (prog_funct p) ->
  (augment_funspecs p G) = G.
Proof. intros.
unfold augment_funspecs. rewrite progfunct_eq.
forget (prog_funct p) as fds.
clear p.
revert G H; induction fds; destruct G; simpl; intros; inv H. trivial.
destruct a.
destruct p.
simpl in H1; subst i0.
rewrite if_true by auto.
specialize (IHfds G H2).
destruct (augment_funspecs' fds G) as [G' | ] eqn:?H.
2:{ destruct G; inv IHfds. destruct fds; inv H2. inv H. }
subst; trivial.
Qed.

(*Now trivial*)
Lemma augment_funspecs_sub: forall p G, map fst G = map fst (prog_funct p) ->
Forall2 (fun fs1 fs2 : ident * funspec => fst fs1 = fst fs2 /\ funspec_sub (snd fs1) (snd fs2)) G
  (augment_funspecs p G).
Proof. intros.
unfold augment_funspecs. rewrite progfunct_eq.
forget (prog_funct p) as fds.
clear p.
revert G H; induction fds; destruct G; simpl; intros; inv H.
constructor.
destruct a.
destruct p.
simpl in H1; subst i0.
rewrite if_true by auto.
specialize (IHfds G H2).
destruct (augment_funspecs' fds G) as [G' | ] eqn:?H.
2:{ destruct G; inv IHfds. destruct fds; inv H2. inv H. }
constructor.
split; auto.
simpl.
apply funspec_sub_refl.
auto.
Qed.

Record LinkedProgVSU {Espec} E Imports p Exports GP := {
  LP_G: funspecs;
  LP_C: @CanonicalComponent Espec E Imports p Exports GP LP_G;
  LP_main: exists phi, find_id (QP.prog_main p) LP_G = Some phi /\
                      find_id (QP.prog_main p) Exports = Some phi
}.

Lemma LP_VSU_ext {Espec E Imp p Exp GP1 GP2}:
      @LinkedProgVSU Espec E Imp p Exp GP1 -> GP1=GP2 ->
      @LinkedProgVSU Espec E Imp p Exp GP2.
Proof. intros; subst; trivial. Qed.

Lemma LP_VSU_entail {Espec E Imp p Exp} GP1 GP2 : 
      @LinkedProgVSU Espec E Imp p Exp GP1 -> (forall gv, GP1 gv |-- GP2 gv) -> 
      @LinkedProgVSU Espec E Imp p Exp GP2.
Proof.
 intros. destruct X as [G C M].
 apply (Build_LinkedProgVSU _ _ _ _ _ _ _ (CanonicalComponent_entail _ _ C H) M).
Qed.

Definition G_of_CanonicalVSU {Espec E Imports p Exports GP}
     (vsu: @CanonicalVSU Espec E Imports p Exports GP): funspecs.
destruct vsu as [G CCM]. destruct CCM as [GG CC M]. apply GG. Defined. 

Lemma G_of_CanonicalVSU_char {Espec E Imports p Exports GP}
        (vsu: @CanonicalVSU Espec E Imports p Exports GP):
     map fst (G_of_CanonicalVSU vsu) = 
                map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ map fst E))
                        (PTree.elements (QP.prog_defs p))).
Proof. destruct vsu as [G CCM]. simpl. destruct CCM as [GG CC M].
 destruct CC. unfold Comp_G in *. trivial. Qed.

Lemma G_of_CanoncialVSU_justified {Espec E Imports p Exports GP}
       (vsu: @CanonicalVSU Espec E Imports p Exports GP):
       forall (i : ident) (phi : funspec) (fd : fundef function),
       initial_world.find_id i (QPprog_funct p) = Some fd ->
       initial_world.find_id i (G_of_CanonicalVSU vsu) = Some phi -> 
       @SF Espec (Comp_cs (projT2 vsu)) (QPvarspecs p)
             (@QPglobalenv function p) 
             (Imports ++ (G_of_CanonicalVSU vsu)) i fd phi.
Proof. intros. destruct vsu as [G ?]. 
 apply  (Comp_G_justified c).
-
 clear - H. simpl in *.
 unfold QPprog_funct in H.
 rewrite <- find_id_elements.
 pose proof (PTree.elements_keys_norepet (QP.prog_defs p)).
 induction  (PTree.elements (QP.prog_defs p)).
 inv H.
 inv H0.
 destruct a,g.
 simpl in *.
 if_tac; subst. inv H; auto.
 auto.
 simpl in *. if_tac; auto. subst.
 contradiction H3. clear - H.
 induction l. inv H. destruct a,g; simpl in *; auto.
 if_tac in H; auto; right; auto.
- apply H0.
Qed.

Lemma LNR_G_of_CanoncialVSU {Espec E Imports p Exports GP}
         (vsu: @CanonicalVSU Espec E Imports p Exports GP):
      list_norepet (map fst (G_of_CanonicalVSU vsu)).
Proof. intros. destruct vsu. apply (Comp_G_LNR c). Qed.

Lemma LNR_progdefs_progfunct {F} {p: program F}: list_norepet (map fst (prog_defs p)) -> 
      list_norepet (map fst (prog_funct p)).
Proof. apply initialize.list_norepet_prog_funct'. Qed.

Definition ExtIDs (p: Ctypes.program function): list ident := 
  map fst ((filter (fun x => negb (isInternal (snd x)))) (prog_defs p)).

Lemma MkInitPred_of_CanonicalVSU {Espec E Imports p Exports GP} 
       (vsu: @CanonicalVSU Espec E Imports p Exports GP):
      forall gv, globals_ok gv -> InitGPred (Vardefs p) gv |-- GP gv.
Proof. destruct vsu as [G [GG CC M]]. apply (Comp_MkInitPred CC). Qed.

Lemma global_is_headptr g i: isptr (globals_of_env g i) -> headptr (globals_of_env g i).
Proof. unfold globals_of_env, headptr; simpl.
  destruct (Map.get (ge_of g) i); simpl; intros; [ exists b; trivial | contradiction].
Qed.

Lemma align_compatible_tint_tuint {cs b}: @align_compatible cs tint (Vptr b Ptrofs.zero) =
                @align_compatible cs tuint (Vptr b Ptrofs.zero).
Proof.
  unfold align_compatible. apply prop_ext; split; intros.
+ inv H. econstructor. reflexivity. simpl. apply Z.divide_0_r. 
+ inv H. econstructor. reflexivity. simpl. apply Z.divide_0_r.
Qed.

Lemma semax_body_Gmerge1 {cs} V G1 G2 f iphi (SB: @semax_body V G1 cs f iphi)
  (G12: forall i phi1 phi2, find_id i G1 = Some phi1 -> find_id i G2 = Some phi2 ->
        typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
        callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
   (LNR: list_norepet (map fst V ++ map fst (G_merge G1 G2))):
   @semax_body V (G_merge G1 G2) cs f iphi.
Proof. 
assert (LNR_VG1: list_norepet (map fst V ++ map fst G1)). 
{ clear - LNR. apply list_norepet_append_inv in LNR; destruct LNR as [? [? ?]].
  apply list_norepet_append; trivial.
  + rewrite (@G_merge_dom G1 G2), map_app in H0.
    apply list_norepet_append_inv in H0; apply H0.
  + eapply list_disjoint_mono. apply H1. 2: trivial.
    intros. rewrite (@G_merge_dom G1 G2), map_app. apply in_or_app. left; trivial. }
assert (LNR_G1: list_norepet (map fst G1)). 
{ clear - LNR_VG1. apply list_norepet_append_inv in LNR_VG1; apply LNR_VG1. }
assert (D1: forall j t, find_id j V = Some t -> find_id j G1 = None).
{ clear - LNR. intros.
  apply (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR) in H.
  apply find_id_None_iff. apply find_id_None_iff in H. intros N; apply H; clear H.
  rewrite (@G_merge_dom G1 G2), map_app. apply in_or_app. left; trivial. }
assert (D2: forall j t, find_id j V = Some t -> find_id j G2 = None).
{ clear - LNR LNR_G1. intros.
  apply (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR) in H.
  apply find_id_None_iff. apply find_id_None_iff in H. intros N; apply H; clear H.
  apply G_merge_InDom; trivial.
  destruct (in_dec ident_eq j (map fst G1)). left; trivial. right; split; trivial. }
eapply semax_body_subsumespec. eassumption.
2: intros; apply subsumespec_G_merge_l; eauto.
intros. red. specialize (D1 i); specialize (D2 i).
remember (find_id i V) as q; destruct q; symmetry in Heqq. 
+ erewrite 2 semax_prog.make_context_g_mk_findV_mk; try eassumption.
  trivial.
+ remember ((make_tycontext_g V G1) ! i) as w; symmetry in Heqw; destruct w; trivial.
  specialize (G12 i).
  remember (find_id i G1) as a; symmetry in Heqa; destruct a.
  - erewrite semax_prog.make_tycontext_s_g in Heqw.
    2:  rewrite make_tycontext_s_find_id; eassumption. 
    inv Heqw.
    remember (find_id i G2) as b; symmetry in Heqb; destruct b.
    * destruct (G12 _ _ (eq_refl _) (eq_refl _)); clear G12.
      destruct (G_merge_find_id_SomeSome Heqa Heqb H H0) as [psi [Psi PSI]].
      apply funspectype_of_binary_intersection in Psi; destruct Psi.
      erewrite semax_prog.make_tycontext_s_g.
      2: rewrite make_tycontext_s_find_id; eassumption.
      rewrite H1; trivial. 
    * apply (G_merge_find_id_SomeNone Heqa) in Heqb.
      erewrite semax_prog.make_tycontext_s_g.
      2: rewrite make_tycontext_s_find_id; eassumption.
      trivial.
  - rewrite (semax_prog.make_tycontext_g_G_None _ _ _ Heqa) in Heqw; congruence.
Qed.

Lemma semax_body_Gmerge2 {cs} V G1 G2 f iphi (SB:@semax_body V G2 cs f iphi)
  (G12: forall i phi1 phi2, find_id i G1 = Some phi1 -> find_id i G2 = Some phi2 ->
        typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
        callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
   (LNR_VG1: list_norepet (map fst V ++ map fst G1)) 
   (LNR_VG2: list_norepet (map fst V ++ map fst G2)):
   @semax_body V (G_merge G1 G2) cs f iphi.
Proof.
assert (LNR: list_norepet (map fst V ++ map fst (G_merge G1 G2))).
{ apply list_norepet_append_inv in LNR_VG1; destruct LNR_VG1 as [? [? ?]].
  apply list_norepet_append_inv in LNR_VG2; destruct LNR_VG2 as [? [? ?]].
  apply list_norepet_append; trivial.
  + apply G_merge_LNR; trivial.
  + intros ? ? ? ?. apply G_merge_InDom in H6; trivial.
    destruct H6 as [Y | [YY Y]]. apply H1; trivial. apply H4; trivial. }
assert (LNR_G1: list_norepet (map fst G1)). 
{ clear - LNR_VG1. apply list_norepet_append_inv in LNR_VG1; apply LNR_VG1. }
assert (D1: forall j t, find_id j V = Some t -> find_id j G1 = None).
{ clear - LNR. intros.
  apply (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR) in H.
  apply find_id_None_iff. apply find_id_None_iff in H. intros N; apply H; clear H.
  rewrite (@G_merge_dom G1 G2), map_app. apply in_or_app. left; trivial. }
assert (D2: forall j t, find_id j V = Some t -> find_id j G2 = None).
{ clear - LNR LNR_G1. intros.
  apply (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR) in H.
  apply find_id_None_iff. apply find_id_None_iff in H. intros N; apply H; clear H.
  apply G_merge_InDom; trivial.
  destruct (in_dec ident_eq j (map fst G1)). left; trivial. right; split; trivial. }
assert (LNR_G2: list_norepet (map fst G2)). 
{ clear - LNR_VG2. apply list_norepet_append_inv in LNR_VG2; apply LNR_VG2. }

eapply semax_body_subsumespec. eassumption.
2: intros; apply subsumespec_G_merge_r; eauto.
intros. red. specialize (D1 i); specialize (D2 i).
remember (find_id i V) as q; destruct q; symmetry in Heqq. 
+ erewrite 2 semax_prog.make_context_g_mk_findV_mk; try eassumption.
  trivial.
+ remember ((make_tycontext_g V G2) ! i) as w; symmetry in Heqw; destruct w; trivial.
  specialize (G12 i).
  remember (find_id i G2) as a; symmetry in Heqa; destruct a.
  - erewrite semax_prog.make_tycontext_s_g in Heqw.
    2:  rewrite make_tycontext_s_find_id; eassumption. 
    inv Heqw.
    remember (find_id i G1) as b; symmetry in Heqb; destruct b.
    * destruct (G12 _ _ (eq_refl _) (eq_refl _)); clear G12.
      destruct (G_merge_find_id_SomeSome Heqb Heqa H H0) as [psi [Psi PSI]].
      apply funspectype_of_binary_intersection in Psi; destruct Psi.
      erewrite semax_prog.make_tycontext_s_g.
      2: rewrite make_tycontext_s_find_id; eassumption.
      rewrite H2; trivial. 
    * apply (G_merge_find_id_NoneSome Heqb) in Heqa; trivial.
      erewrite semax_prog.make_tycontext_s_g.
      2: rewrite make_tycontext_s_find_id; eassumption.
      trivial.
  - rewrite (semax_prog.make_tycontext_g_G_None _ _ _ Heqa) in Heqw; congruence.
Qed.

(*** Andrew's new stuff: *)

Lemma globs_to_globvars:
 forall prog rho, 
  Forall (fun ig => isptr (globals_of_env rho (fst ig))) (QPprog_vars prog) ->
 globvars2pred (globals_of_env rho) (QPprog_vars prog)
  |-- InitGPred (Vardefs prog) (globals_of_env rho).
Proof.
intros.
unfold globvars2pred.
unfold QPprog_vars, Vardefs in *.
induction (PTree.elements (QP.prog_defs prog)).
simpl.
apply derives_refl.
simpl.
destruct a.
unfold isGvar.
simpl.
destruct g; simpl.
simpl in H.
apply IHl; auto.
rewrite InitGPred_consD.
simpl in H. inv H.
simpl in H2.
apply sepcon_derives; auto.
clear IHl.
unfold globs2pred, globvar2pred.
simpl.
rewrite prop_true_andp by (apply global_is_headptr; auto).
destruct (gvar_volatile v).
apply derives_refl.
clear H3 H2.
forget (globals_of_env rho p) as g.
change (initialize.readonly2share (gvar_readonly v))
  with (readonly2share (gvar_readonly v)).
forget (readonly2share (gvar_readonly v)) as sh.
revert g; induction (gvar_init v); intros; simpl; auto.
Qed.

Definition main_pre {Z: Type} (prog: QP.program function) (ora: Z) : globals -> argsEnviron -> mpred :=
 (fun gv rho => 
  !! (gv = initialize.genviron2globals (fst rho) /\ snd rho = []) &&
   (globvars2pred gv (QPprog_vars prog) * has_ext ora))%logic.

Definition main_pre_old {Z : Type} (prog : QP.program function) (ora : Z) 
  (gv : globals) (rho : environ) :=
 !! (gv = globals_of_env rho) &&
   (globvars2pred gv (QPprog_vars prog) * has_ext ora)%logic.

(* Don't use this! 
Lemma close_precondition_main {Z p ora gv}:
close_precondition nil (@main_pre Z p ora gv) = @main_pre_old Z p ora gv.
Proof.
unfold close_precondition; extensionality rho.
unfold main_pre, main_pre_old; simpl snd. 
forget (QPprog_vars p) as vars. clear p.
remember (globvars2pred gv vars) as G.
apply pred_ext.
+ apply exp_left. intros vals. normalize.
+ Exists (@nil val). 
  apply andp_right. apply prop_right; split; [trivial | constructor].
  clear HeqG. normalize. rewrite prop_true_andp; auto.
Qed.
*)

Lemma main_pre_InitGpred:
 forall globs (Espec: OracleKind) (cs: compspecs)  Delta prog1 prog2 Z (ext:Z) (gv: globals) R c Post
  (H1: globals_ok gv -> InitGPred (Vardefs prog1) gv |-- globs)
  (H: Vardefs prog1 = Vardefs prog2)
  (H0: Forall (fun ig : ident * _ => isSome ((glob_types Delta) ! (fst ig))) (QPprog_vars prog2))
  (H2: semax Delta (sepcon (PROP ( )  LOCAL (gvars gv)  SEP (globs; has_ext ext)) R) c Post),
  semax Delta (sepcon (close_precondition nil (@main_pre Z prog2 ext gv)) R) c Post.
Proof.
intros.
rewrite H in H1. clear H prog1. rename H1 into H.
eapply semax_pre; [ | apply H2]; clear H2.
unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
intro rho.
unfold close_precondition.
simpl. unfold_lift.
normalize.
clear H2 H3.
rewrite prop_true_andp.
2:{ split; auto. hnf. reflexivity. }
apply sepcon_derives; auto.
apply sepcon_derives; auto.
eapply derives_trans; [ | apply H]; clear H.
2:{
clear. intro i.
unfold initialize.genviron2globals.
destruct (Map.get (ge_of rho) i); auto.
left; eexists; eauto.
}
unfold Vardefs, InitGPred.
unfold SeparationLogic.prog_vars.
clear - H0 H1.
unfold QPprog_vars in *.
induction (PTree.elements (QP.prog_defs prog2)); simpl.
auto.
destruct a.
simpl in H0.
destruct g; simpl; auto.
inv H0.
apply sepcon_derives; auto.
rewrite prop_true_andp; auto.
clear - H1 H3.
destruct H1 as [_ [_ ?]].
simpl in *.
specialize (H p).
destruct ((glob_types Delta) ! p); inv H3.
specialize (H _ (eq_refl _)) as [b ?].
unfold initialize.genviron2globals.
rewrite H.
exists b; auto.
Qed.

Definition VSU_MkInitPred {Espec E Imports p Exports GP} 
  (vsu: @VSU Espec E Imports p Exports GP) 
  (gv: globals) : globals_ok gv -> InitGPred (Vardefs p) gv |-- (GP gv) :=
  Comp_MkInitPred (projT2 vsu) gv.

Ltac report_failure :=
 match goal with |- ?G => fail 99 "expand_main_pre_new failed with goal" G end.

Ltac unfold_all R :=
 match R with
 | sepcon ?a ?ar => let b := unfold_all a in
                      let br := unfold_all ar in
                      constr:(sepcon b br)
 | ?a => let x := eval unfold a in a in unfold_all x
 | ?a => constr:(a)
 end.

Ltac expand_main_pre_VSU :=
  match goal with
  | vsu: VSU _ _ _ _ _ |- _ => 
    eapply main_pre_InitGpred; 
        [ try apply (VSU_MkInitPred vsu); report_failure
        | try reflexivity; report_failure
        | try solve [repeat constructor]; report_failure
        |  ];
     clear vsu;
     match goal with
      |- semax _ (PROPx _ (LOCALx _ (SEPx ((emp * emp * ?R) _ :: _))) * _)%logic _ _ =>
        let x := unfold_all R in change R with x
     end
  | vsu: VSU _ _ _ _ _ |- _ =>  report_failure
  | |- _ => expand_main_pre_old
  end.

Ltac expand_main_pre ::= 
   expand_main_pre_VSU.

Ltac start_function2 ::=
  first [ erewrite compute_close_precondition_eq; [ | reflexivity | reflexivity]
        | rewrite close_precondition_main
        | match goal with |- semax (func_tycontext _ ?V ?G _) 
              (close_precondition _ (main_pre _ _ _) * _)%logic _ _ =>
                  let x := eval hnf in V in change V with x 
          end
        ].

Fixpoint vardefs_to_globvars (vdefs: list (ident * globdef (fundef function) type)) :
    list (ident * globvar type) :=
 match vdefs with
 | (i, Gfun _)::r => vardefs_to_globvars r
 | (i, Gvar v)::r => (i,v) :: vardefs_to_globvars r
 | nil => nil
 end.

Definition vardefs_tycontext (vdefs: list (ident * globdef (fundef function) type)) : tycontext :=
  make_tycontext nil nil nil Tvoid 
   (map (fun iv => (fst iv, gvar_info (snd iv))) (vardefs_to_globvars vdefs))
  nil nil.



Lemma InitGPred_process_globvars:
  forall Delta al gv (R: globals -> mpred),
  Delta = vardefs_tycontext al ->
  ENTAIL Delta, globvars_in_process gv nil emp (vardefs_to_globvars al) |-- lift0 (R gv) ->
  globals_ok gv ->
  InitGPred al gv |-- R gv.
Proof.
intros until 2. intro Hgv; intros.
unfold globvars_in_process in H0.
simpl fold_right_sepcon in H0.
rewrite sepcon_emp, emp_sepcon in H0. 
pose (rho := 
 mkEnviron 
  (fun i => match gv i with Vptr b _ => Some b | _ => None end)
  (Map.empty (block * type))
  (Map.empty val)).
eapply derives_trans; [ | apply (H0 rho)].
clear R H0; subst Delta.
unfold local, lift1.
simpl.
normalize.
subst rho.
unfold tc_environ, typecheck_environ.
simpl.
rewrite prop_and.
rewrite <- and_assoc.
rewrite prop_and.
rewrite prop_true_andp.
-
apply andp_right.
*
apply derives_trans with
(!! (Forall (fun x : (ident * globdef (fundef function) type) => let (i, d) := x in
      match d with Gfun _ => True | Gvar v => headptr (gv i) end) al)).
+
apply derives_trans with (TT * InitGPred al gv)%logic. cancel.
induction al.
apply prop_right; constructor.
rewrite InitGPred_consD.
unfold globs2pred.
destruct a. destruct g.
rewrite emp_sepcon; auto.
eapply derives_trans; [apply IHal |].
apply prop_derives. intros. constructor; auto.
normalize.
rewrite <- sepcon_assoc.
eapply derives_trans; [ eapply derives_trans; [ | apply IHal] | ].
cancel.
clear IHal.
apply prop_derives.
intros. constructor; auto.
+
apply andp_right; apply prop_derives; intros.
 --
induction al; simpl.
hnf; intros. rewrite PTree.gempty in H0; inv H0.
inv H.
specialize (IHal H3). clear H3.
destruct a. destruct g.
auto.
simpl.
intros ? ?.
specialize (IHal id t).
intros.
destruct (eq_dec id i).
subst id.
rewrite PTree.gss in H.
inv H.
unfold Map.get.
destruct H2. rewrite H. eauto.
rewrite PTree.gso in H by auto.
specialize (IHal H).
destruct IHal as [b ?]; exists b.
unfold Map.get in *.
destruct (Memory.EqDec_ident i id); try congruence.
 --
unfold gvars_denote.
simpl ge_of.
extensionality i.
unfold Map.get.
specialize (Hgv i).
destruct Hgv as [[b' Hgv] | Hgv];
rewrite Hgv; auto.
*
induction al; simpl. 
rewrite InitGPred_nilD. auto.
rewrite InitGPred_consD.
rewrite fold_right_map in IHal.
rewrite fold_right_map.
destruct a. destruct g.
simpl. rewrite emp_sepcon; auto.
simpl.
normalize.
apply sepcon_derives; auto.
-
split.
hnf; intros. rewrite PTree.gempty in H; inv H.
hnf; intros.
split; intros. rewrite PTree.gempty in H; inv H.
destruct H. unfold Map.get, Map.empty in H.  inv H. 
Qed.

Lemma finish_process_globvars' :
 forall gv (done: list mpred) (R: mpred), 
  fold_right_sepcon done |-- R -> 
globvars_in_process gv done emp nil |-- lift0 R.
Proof.
intros.
intro rho.
unfold globvars_in_process, globvars2pred, lift0. simpl.
normalize.
Qed.

Lemma globals_ok_isptr_headptr:
  forall gv i, globals_ok gv -> isptr (gv i) -> headptr (gv i).
Proof.
intros.
destruct (H i); auto.
rewrite H1 in H0; contradiction.
Qed.

Hint Resolve globals_ok_isptr_headptr: core.

Lemma globals_ok_genviron2globals:
  forall g,  globals_ok (initialize.genviron2globals g).
Proof.
intros. intro i; simpl. unfold initialize.genviron2globals.
destruct (Map.get g i); auto.
left; eexists; eauto.
Qed.

Hint Resolve globals_ok_genviron2globals : core.

Definition VSU_initializer {cs: compspecs} (prog: Clight.program) (Gpred: globals -> mpred) :=
 forall gv, globals_ok gv -> InitGPred (Vardefs (QPprog prog)) gv |-- Gpred gv.

Ltac InitGPred_tac :=
intros ? ?;
eapply InitGPred_process_globvars; auto;
let Delta := fresh "Delta" in let Delta' := fresh "Delta'" in 
set (Delta' := vardefs_tycontext _);
set (Delta := @abbreviate tycontext Delta');
change Delta' with Delta;
hnf in Delta'; simpl in Delta'; subst Delta';
simpl vardefs_to_globvars;
eapply derives_trans; [process_globals | ];
clear Delta;
apply finish_process_globvars'; unfold fold_right_sepcon at 1;
repeat change_mapsto_gvar_to_data_at.

Ltac QPprog p := 
  let q := constr:(QPprog p) in
  let q := eval hnf in q in
  let q := eval simpl in q in
  exact (@abbreviate _ q).
