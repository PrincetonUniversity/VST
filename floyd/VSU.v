Require Import VST.floyd.proofauto.
Require Import VST.veric.Clight_initial_world.
Require Import VST.floyd.assoclists.

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
(*
Lemma InternalInfo_envs_sub {CS CS'} (CSUB: cspecs_sub CS CS') ge ge'
  (Gfs: forall i b, Genv.find_symbol ge i = Some b -> exists b', Genv.find_symbol ge' i=Some b')
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
  V G  i f phi (H : semaxfunc_InternalInfo CS V G ge i f phi):
semaxfunc_InternalInfo CS' V G ge' i f phi.
Proof. 
  destruct H as [b [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 Hb7]]]]]]].
  destruct(Gfs _ _ Hb5) as [b' B']. exists b'. repeat split; try assumption.
  - destruct CSUB as [CSE _]. clear - CSE Hb2. induction Hb2; constructor; trivial.
    apply (@semax.complete_type_cenv_sub _ _ CSE _ H).
  - destruct CSUB as [CSE _]. clear - CSE Hb2 Hb3. unfold var_sizes_ok in *.
    induction Hb3; trivial. inv Hb2. constructor. 2: eauto.
    rewrite (@expr_lemmas4.cenv_sub_sizeof _ _ CSE); trivial.
  - specialize (Gfs i); rewrite Hb5 in Gfs. apply Gfs.
  - specialize (Gffp b); rewrite Hb6 in Gffp; apply Gffp.
  - apply (semax_body_cenv_sub CSUB); trivial.
Qed.*)

Lemma InternalInfo_envs_sub {CS CS'} (CSUB: cspecs_sub CS CS') ge ge'
  (*(Hge: forall i f, genv_find_func ge i (Internal f) -> genv_find_func ge' i (Internal f))*)
  V G  i f phi (H : semaxfunc_InternalInfo CS V G ge i f phi) (FFunc: genv_find_func ge' i (Internal f)):
semaxfunc_InternalInfo CS' V G ge' i f phi.
Proof. 
  destruct H as [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 Hb6]]]]]. (*clear Hge.*)
  repeat split; try assumption.
  - destruct CSUB as [CSE _]. clear - CSE Hb2. induction Hb2; constructor; trivial.
    apply (@semax.complete_type_cenv_sub _ _ CSE _ H).
  - destruct CSUB as [CSE _]. clear - CSE Hb2 Hb3. unfold var_sizes_ok in *.
    induction Hb3; trivial. inv Hb2. constructor. 2: eauto.
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
  (*(Hge: forall i ef tys rt cc, genv_find_func ge i (External ef tys rt cc) -> genv_find_func ge' i (External ef tys rt cc))*)
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

Definition IntIDs (p: Ctypes.program function): list ident := 
  map fst ((filter (fun x => isInternal (snd x))) (prog_defs p)).

Lemma IntIDs_elim {i p}: In i (IntIDs p) -> exists f, In (i, Gfun (Internal f)) (prog_defs p).
Proof. unfold IntIDs; forget (prog_defs p) as l. 
  induction l; simpl; intros. contradiction.
  destruct a; simpl in *.
  destruct g; simpl in *.
+ destruct f.
  - simpl in H. destruct H; subst. eexists; left; reflexivity.
     apply IHl in H; destruct H. exists x; right; trivial.
   - apply IHl in H; destruct H. exists x; right; trivial.
+ apply IHl in H; destruct H. exists x; right; trivial.
Qed.

Lemma IntIDs_e {i p}: In i (IntIDs p) -> list_norepet (map fst (prog_defs p)) ->
      exists f, find_id i (prog_defs p) = Some ( Gfun (Internal f)).
Proof. intros. apply IntIDs_elim in H. destruct H. exists x. apply find_id_i; trivial. Qed.

Lemma IntIDs_intro {i p f}: In (i, Gfun (Internal f)) (prog_defs p) -> In i (IntIDs p).
Proof. unfold IntIDs; forget (prog_defs p) as l. 
  induction l; simpl; intros. contradiction.
  destruct a; simpl in *.
  destruct g; simpl in *.
+ destruct H.
  - inv H; simpl. left; trivial.
  - apply IHl in H; clear IHl. 
    destruct f0; simpl; trivial. right; trivial.
+ destruct H. congruence. auto. 
Qed.

Lemma IntIDs_i {i p f}: find_id i (prog_defs p) = Some (Gfun (Internal f)) -> In i (IntIDs p).
Proof. intros. apply find_id_e in H. eapply IntIDs_intro. eassumption. Qed.

Lemma Fundef_of_Gfun {i p f}: find_id i (prog_defs p) = Some (Gfun f) ->
      find_id i (prog_funct p) = Some f.
Proof.
  unfold prog_funct. forget (prog_defs p) as l.
  induction l; simpl; intros. inv H.
  destruct a. destruct g; simpl. if_tac; subst. inv H; trivial. auto. if_tac in H. inv H. auto.
Qed.

Lemma in_map_fst_prog_funct' {F V i l}: In i (map fst (@prog_funct' F V l)) -> 
      In i (map fst l).
Proof.
  induction l; simpl; trivial.
  destruct a. destruct g; simpl; intros. destruct H; subst; [ left; trivial | right; eauto].
  right; eauto.
Qed.
Lemma in_map_fst_fundefs {i p}: In i (map fst (prog_funct p)) -> In i (map fst (prog_defs p)).
Proof. apply in_map_fst_prog_funct'. Qed.

Lemma Gfun_of_Fundef {i p fd}: 
      find_id i (prog_funct p) = Some fd -> list_norepet (map fst (prog_defs p)) ->
      find_id i (prog_defs p) = Some (Gfun fd).
Proof. unfold prog_funct. forget (prog_defs p) as l.
  induction l; simpl; intros. discriminate.
  destruct a. inv H0. destruct g; simpl in *.
+ if_tac; subst. inv H; trivial. auto.
+ rewrite if_false. auto. specialize (IHl H H4). apply find_id_In_map_fst in IHl.
  congruence.
Qed.

Lemma Fundef_of_Gvar {i p v}: find_id i (prog_defs p) = Some (Gvar v) -> 
      list_norepet (map fst (prog_defs p)) -> find_id i (prog_funct p) = None.
Proof.
  unfold prog_funct. forget (prog_defs p) as l.
  induction l; simpl; intros; trivial.
  destruct a. simpl in H0; inv H0. destruct g; simpl.
  + if_tac; subst. inv H. eauto.
  + if_tac in H; [ subst | eauto]. inv H.
    apply find_id_None_iff. intros N.
    apply in_map_fst_prog_funct' in N. congruence.
Qed.

Definition SF {Espec cs V ge} G (i:ident) (fd:Clight.fundef) (phi:funspec) :=
  match fd with
    Internal f => semaxfunc_InternalInfo cs V G ge i f phi
  | External ef argsig retsig cc => semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi
  end.

Definition isGvar (x: ident * globdef (fundef function) type) := 
           match (snd x) with Gvar v => true | _ => false end.

Definition Vardefs (p: Clight.program) := filter isGvar (prog_defs p).
(*
Definition globvar2pred': globals -> ident * globvar type -> globals -> mpred := initialize.gv_globvar2pred.

Definition globs2pred' (gv1: globals) (x: ident * globdef (fundef function) type) (gv2: globals): mpred :=
  match x with (i, d) => match d with
                           Gfun _ => emp
                         | Gvar v => !!(headptr (gv2 i)) && globvar2pred' gv1 (i,v) gv2
                         end
  end.

Lemma globvar2pred_char gv idv rho: globvar2pred gv idv rho = globvar2pred' gv idv (globals_of_genv (ge_of rho)).
apply initialize.globvar2pred_char_gv. Qed.*)

Definition globs2pred (gv1: globals) (x: ident * globdef (fundef function) type) (gv2: globals): mpred :=
  match x with (i, d) => match d with
                           Gfun _ => emp
                         | Gvar v => !!(headptr (gv2 i)) && initialize.gv_globvar2pred gv1 (i,v) gv2
                         end
  end.

Definition InitGPred (V:list (ident * globdef (fundef function) type)) (gv: globals) :mpred := 
   fold_right sepcon emp (map (globs2pred gv) V) gv.

(*V should be the varspecs of p, and cs the compspecs* 
VSTexterns, "E": Syscalls, functions implemented in assembly... These functions are represented
  as GFun(external ...) in Clight, but nevertheless should be in G (and hence 
  should be justified by a semaxfunc - in fact by a semax_func_extern. Since they are in G
  they may be in Exports, too. -*)
Record Component {Espec:OracleKind} {V:varspecs} {cs:compspecs}
      (E Imports: funspecs) (p: Clight.program) (Exports: funspecs) (GP: globals -> mpred) (G: funspecs) := {
  Comp_Imports_external: forall i, In i (map fst Imports) -> 
                         exists f ts t cc, find_id i (prog_defs p) = Some (Gfun (External f ts t cc));

  Comp_p_LNR: list_norepet (map fst (prog_defs p)); 
  Comp_ExternsImports_LNR: list_norepet (map fst (E++Imports));

  Comp_Exports_LNR: list_norepet (map fst Exports);

  (*VSTexternals are External functions in CompCert*)
  Comp_Externs: forall i, In i (map fst E) -> 
                exists f ts t cc, find_id i (prog_defs p) = Some (Gfun (External f ts t cc));

  Comp_G_dom: forall i, In i (IntIDs p ++ (map fst E)) <-> In i (map fst G);
  Comp_G_LNR: list_norepet (map fst G);
  Comp_G_E: forall i, In i (map fst E) -> find_id i E = find_id i G;

  Comp_G_justified: forall i phi fd,
                    find_id i (prog_funct p) = Some fd ->
                    find_id i G = Some phi ->
                    @SF Espec cs V (Genv.globalenv p) (Imports ++ G) i fd phi;

  Comp_G_Exports: forall i phi (E: find_id i Exports = Some phi), 
                  exists phi', find_id i G = Some phi' /\ funspec_sub phi' phi;

  (*Comp_InitPred: globals -> mpred;*)
  Comp_MkInitPred: forall gv, InitGPred (Vardefs p) gv |-- (*Comp_InitPred*)(GP gv(* * TT*))%logic
}.

Definition Comp_G {Espec V cs E Imports p Exports GP G} (c:@Component Espec V cs E Imports p Exports GP G):= G.

Definition VSU {Espec V cs} E Imports p Exports GP:=
  sigT (fun G => @Component Espec V cs E Imports p Exports GP G).

Arguments Comp_Imports_external {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_p_LNR {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_ExternsImports_LNR {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Exports_LNR {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Externs {Espec V cs E Imports p Exports GP G} c.
(*Arguments Comp_G {Espec V cs E Imports p Exports} c.*)
Arguments Comp_G_dom {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_LNR {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_justified {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_Exports {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_E {Espec V cs E Imports p Exports GP G} c.
(*Arguments Comp_InitPred {Espec V cs E Imports p Exports GP G} c.*)
Arguments Comp_MkInitPred {Espec V cs E Imports p Exports GP G} c.

Section Component.
Variable Espec: OracleKind.
Variable V: varspecs.
Variable cs: compspecs.
Variable E Imports: funspecs.
Variable p: Clight.program.
Variable Exports: funspecs.
Variable GP: globals -> mpred.
Variable G: funspecs.

Variable c: @Component Espec V cs E Imports p Exports GP G.

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
  eapply sublist_norepet. 2: apply (Comp_p_LNR c). unfold IntIDs.
  remember (prog_defs p) as l; clear.
  induction l; simpl; intros. constructor.
  destruct a; simpl. destruct g; [destruct f |]; subst; constructor; auto.
Qed.

Lemma LNR_Internals_Externs: list_norepet (IntIDs p ++ map fst E).
Proof.
  specialize (Comp_p_LNR c); specialize Comp_Externs_LNR; specialize Comp_LNR_Interns; intros.
  apply list_norepet_app; split3; trivial.
  do 5 intros ?; subst.
  apply (Comp_Externs c) in H3. destruct H3 as [ef [tys [rt [cc Hy]]]].
  apply IntIDs_e in H2; [destruct H2 | trivial]. congruence.
Qed.

Lemma Comp_G_intern {i} (Hi: In i (map fst (Comp_G c))):
      ( ~ In i (map fst E)) <->
      ( exists f, find_id i (prog_defs p) = Some (Gfun (Internal f)) ).
Proof. 
  apply list_in_map_inv in Hi. destruct Hi as [[ii phi] [H Hi]]; simpl in H; subst ii.
  apply in_map_fst in Hi. rewrite <- (Comp_G_dom c) in Hi.
  apply in_app_or in Hi; destruct Hi.
+ split; intros.
  - apply IntIDs_e in H; [ destruct H | apply c].
    rewrite H. exists x; trivial.
  - destruct H0. intros N. specialize LNR_Internals_Externs.
    rewrite list_norepet_app; intros [? [? X]]. apply (X i i); trivial.
+ split; intros. contradiction.
  destruct H0 as [f Hf]. apply (Comp_Externs c) in H. destruct H as [? [? [? [? ?]]]]. congruence.
Qed.

Lemma Comp_G_extern {i} (Hi: In i (map fst (Comp_G c))):
      (In i (map fst E)) <->
      exists ef tys rt cc, find_id i (prog_defs p) = Some (Gfun (External ef tys rt cc)).
Proof. 
  apply list_in_map_inv in Hi. destruct Hi as [[ii phi] [H Hi]]; simpl in H; subst ii.
  apply in_map_fst in Hi. rewrite <- (Comp_G_dom c) in Hi.
  apply in_app_or in Hi; destruct Hi.
+ split; intros.
  - specialize LNR_Internals_Externs.
    rewrite list_norepet_app; intros [? [? X]]. elim (X i i); trivial.
  - apply IntIDs_e in H; [destruct H | apply c]. destruct H0 as [ef [tys [rt [cc He]]]]; congruence.
+ split; intros; trivial.
  apply c in H; trivial.
Qed.

Lemma Comp_G_elim {i} (Hi: In i (map fst (Comp_G c))):
      (In i (map fst E) /\ exists ef tys rt cc, find_id i (prog_defs p) = Some (Gfun (External ef tys rt cc)))
    \/ ((~In i (map fst E)) /\ In i (IntIDs p) /\ exists f, find_id i (prog_defs p) = Some (Gfun (Internal f))).
Proof.
  destruct (in_dec ident_eq i (map fst E)).
+ left. split; trivial. apply (Comp_G_extern Hi); trivial.
+ right; split; trivial. apply (Comp_G_intern Hi) in n. split; trivial.
  destruct n. apply IntIDs_i in H; trivial.
Qed.

Lemma Comp_G_in_Fundefs {i} (Hi: In i (map fst (Comp_G c))):
      exists fd, find_id i (prog_funct p) = Some fd.
Proof. 
  destruct (in_dec ident_eq  i (map fst E)).
+ apply (Comp_G_extern Hi) in i0. destruct i0 as [ef [tys [rt [cc Hef]]]].
  apply Fundef_of_Gfun in Hef; rewrite Hef. eexists; reflexivity.
+ apply (Comp_G_intern Hi) in n. destruct n as [f Hf].
  apply Fundef_of_Gfun in Hf; rewrite Hf. eexists; reflexivity.
Qed.

Lemma Comp_G_in_progdefs' {i phi} (Hi: find_id i (Comp_G c) = Some phi):
      exists fd, find_id i (prog_defs p) = Some (Gfun fd).
Proof. apply find_id_In_map_fst in Hi. 
  apply Comp_G_in_Fundefs in Hi; destruct Hi.
  apply Gfun_of_Fundef in H. exists x; trivial.  apply c.
Qed.

Lemma Comp_G_in_Fundefs' {i phi} (Hi: find_id i (Comp_G c) = Some phi):
      exists fd, find_id i (prog_funct p) = Some fd.
Proof. apply find_id_In_map_fst in Hi. apply Comp_G_in_Fundefs; trivial. Qed.

Lemma Comp_G_in_progdefs {i} (Hi: In i (map fst (Comp_G c))):
      exists fd, find_id i (prog_defs p) = Some (Gfun fd).
Proof.
  apply Comp_G_elim in Hi.
  destruct Hi as [[HE [ef [tys [rt [cc H]]]]] | [HE [INT [f H]]]]; rewrite H; eexists; reflexivity.
Qed.

Lemma Comp_Imports_in_Fundefs {i phi}: find_id i Imports = Some phi ->
      exists f , find_id i (prog_funct p) = Some f.
Proof.
  specialize (Comp_Imports_external c); intros. apply find_id_e in H0. apply in_map_fst in H0.
  destruct (H _ H0) as [f [ts [t [cc Hf]]]]; clear H. eexists; apply (Fundef_of_Gfun Hf).
Qed.

Lemma Comp_Exports_in_Fundefs {i phi}: find_id i Exports = Some phi ->
      exists f , find_id i (prog_funct p) = Some f.
Proof.
  intros. apply (Comp_G_Exports c) in H. destruct H as [psi [H _]].
  apply Comp_G_in_Fundefs' in H; trivial.
Qed.

Lemma Comp_Imports_in_progdefs {i}: In i (map fst(Imports)) -> In i (map fst (prog_defs p)).
Proof.
  specialize (Comp_Imports_external c); intros.
  destruct (H _ H0) as [f [ts [t [cc Hf]]]]; clear H.
  apply find_id_In_map_fst in Hf; trivial.
Qed.

Lemma Comp_Exports_in_progdefs {i}: In i (map fst(Exports)) -> In i (map fst (prog_defs p)).
Proof.
  intros. apply In_map_fst_find_id in H; [ destruct H | apply c].
  apply Comp_Exports_in_Fundefs in H. destruct H.
  apply find_id_In_map_fst in H. apply in_map_fst_fundefs. trivial.
Qed.

Lemma Comp_Imports_ExternalFundefs {i phi}: find_id i Imports = Some phi ->
      exists ef tys rt cc, find_id i (prog_defs p) = Some (Gfun (External ef tys rt cc)).
Proof.
  specialize (Comp_Imports_external c); intros. apply find_id_In_map_fst in H0.
  apply (H _ H0). (* as [f [ts [t [cc Hf]]]]; clear H.
  apply find_id_Externals_i in Hf. do 4 eexists; apply Hf.*)
Qed.

Lemma Comp_Interns_disjoint_from_Imports: list_disjoint (IntIDs p) (map fst Imports).
Proof.
  intros x y X Y.
  apply (Comp_Imports_external c) in Y. destruct Y as [f [ef [ts [t FE]]]].
  apply list_in_map_inv in X. destruct X as [[j fd] [J FD]]; simpl in J; subst j.
  apply filter_In in FD.  simpl in FD; destruct FD. unfold isInternal in H0.
  apply find_id_i in H. intros ?; subst. rewrite H in FE. inv FE.  congruence. apply c.
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
(*
Lemma Comp_Interns_disjoint_from_Imports_find_id {i phi} (Hi: find_id i Imports = Some phi): 
      find_id i (InternalFundefs (prog_defs p)) = None.
Proof.
  specialize Comp_Interns_disjoint_from_Imports; intros D_ImpInt2.
  remember (find_id i (InternalFundefs (prog_defs p))) as u; destruct u; [symmetry in Hequ | trivial].
  apply find_id_e in Hequ. apply InternalFundefs_D in Hequ; destruct Hequ as [g [G Hg]]; subst.
  apply InternalFundefs_char in Hg. apply in_map_fst in Hg. apply find_id_In_map_fst in Hi.
  elim (D_ImpInt2 i i); trivial.
Qed.
*)
Lemma Comp_G_disjoint_from_Imports_find_id {i phi} (Hi: find_id i Imports = Some phi): 
      find_id i (Comp_G c) = None.
Proof. apply (list_disjoint_map_fst_find_id1 Comp_G_disjoint_from_Imports _ _ Hi). Qed.

Lemma Comp_entail {GP'} (H: forall gv, GP gv |-- GP' gv):
      @Component Espec V cs E Imports p Exports GP' G.
Proof. intros. destruct c. econstructor; trivial.
 intros; eapply derives_trans. apply Comp_MkInitPred0. cancel.
Qed.

Lemma Comp_entail_starTT:
      @Component Espec V cs E Imports p Exports (GP * TT)%logic G.
Proof. intros. apply Comp_entail. intros; simpl; apply sepcon_TT. Qed.

Lemma Comp_entail_TT:
      @Component Espec V cs E Imports p Exports TT G.
Proof. intros. eapply Comp_entail. intros; simpl. apply TT_right. Qed.

Lemma Comp_entail_split {GP1 GP2} (H: forall gv, GP gv |-- (GP1 gv * GP2 gv)%logic):
      @Component Espec V cs E Imports p Exports (fun gv => GP1 gv * TT)%logic G.
Proof. intros. eapply Comp_entail. intros; simpl.
  eapply derives_trans. apply H. cancel.
Qed.

Lemma Comp_Imports_sub Imports' (HI1: map fst Imports' = map fst Imports)
      (HI2: Forall2 funspec_sub (map snd Imports') (map snd Imports)): 
      @Component Espec V cs E Imports' p Exports GP G.
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
  assert (AUX2: forall i, sub_option ((make_tycontext_g V (Imports ++ Comp_G c)) ! i)
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
  eapply Build_Component (*with (Comp_G c)*); subst; try solve [apply c].
+ rewrite HI1; apply c. 
+ rewrite map_app, HI1, <- map_app; apply c.
+ intros. specialize (Comp_G_justified c i _ _ H H0); intros; destruct fd.
  - eapply InternalInfo_subsumption. apply AUX2. apply AUX1. apply Comp_ctx_LNR. apply H1.
  - apply H1.
(*+ intros. clear - HI1 HI2. generalize dependent Imports'. 
  induction Imports; intros; destruct Imports'; inv HI1; simpl; trivial. 
  destruct a; destruct p; simpl in *. inv HI2. 
  destruct (Memory.EqDec_ident i i0); subst; simpl; auto.
  apply funspec_sub_funsigs_match in H4. apply (funsigs_match_LNR1 H4).*)
Qed.

(*Together with Lemma  Comp_Exports_suboption, this lemma means we can abstract or hide exports*)
Lemma Comp_Exports_sub1 Exports' (HE1: map fst Exports' = map fst Exports)
      (HE2: Forall2 funspec_sub (map snd Exports) (map snd Exports')):
      @Component Espec V cs E Imports p Exports' GP G.
Proof.
  eapply Build_Component (*with (Comp_G c)*); try apply c.
+ rewrite HE1; apply c. 
+ intros i phi Hi. rename phi into phi'.
  assert (X: exists phi, find_id i Exports = Some phi /\ funspec_sub phi phi').
  { clear - HE1 HE2 Hi. eapply find_funspec_sub; eassumption. }
  destruct X as [phi [Phi PHI]].
  destruct (Comp_G_Exports c _ _ Phi) as [psi [Psi PSI]].
  exists psi; split; [ trivial | eapply funspec_sub_trans; eassumption ].
Qed.

Lemma Comp_Exports_sub2 Exports' (LNR: list_norepet (map fst Exports'))
      (HE2: forall i, sub_option (find_id i Exports') (find_id i Exports)):
      @Component Espec V cs E Imports p Exports' GP G.
Proof.
  eapply Build_Component (*with (Comp_G c)*); try apply c; trivial.
+ intros i phi' Hi. specialize (HE2 i). rewrite Hi in HE2; simpl in HE2.
  apply c; trivial.
Qed.

Definition funspecs_sqsub Exp Exp' :=
  forall i phi', find_id i Exp' = Some phi' ->
         exists phi, find_id i Exp = Some phi /\ funspec_sub phi phi'.

Lemma Comp_Exports_sub Exports' (LNR: list_norepet (map fst Exports'))
      (HE2: funspecs_sqsub Exports Exports'):
      @Component Espec V cs E Imports p Exports' GP G.
Proof.
  eapply Build_Component (*with (Comp_G c)*); try apply c; trivial.
  intros i phi' Hi. destruct (HE2 _ _ Hi) as [phi [H1 H2]].
  apply (Comp_G_Exports c) in H1; destruct H1 as [psi [H3 H4]].
  exists psi; split; trivial. eapply funspec_sub_trans; eassumption.
Qed.

End Component.

Arguments Comp_G_LNR {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_LNR_Interns {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_ctx_LNR {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_disjoint_from_Imports {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_disjoint_from_Imports_find_id {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Interns_disjoint_from_Imports {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Exports_in_progdefs {Espec V cs E Imports p Exports GP G} c.

Arguments Comp_Externs_LNR {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Imports_in_Fundefs {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Exports_in_Fundefs {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Imports_in_progdefs {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Exports_in_progdefs {Espec V cs E Imports p Exports GP G} c.

Arguments Comp_G_intern {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_extern {Espec V cs E Imports p Exports GP G} c.

(*Arguments Comp_Interns_disjoint_from_Imports_find_id {Espec V cs E Imports p Exports}.*)

Arguments Comp_Imports_LNR {Espec V cs E Imports p Exports GP G} c.
Arguments LNR_Internals_Externs {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_in_Fundefs {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_in_Fundefs' {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_E_in_G {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_E_in_G_find {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_elim {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_in_progdefs {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_G_in_progdefs' {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Imports_sub {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_Exports_sub {Espec V cs E Imports p Exports GP G} c.
Arguments Comp_entail {Espec V cs E Imports p Exports GP G} c.

Section VSU_rules.
Variable Espec: OracleKind.
Variable V: varspecs.
Variable cs: compspecs.
Variable E Imports: funspecs.
Variable p: Clight.program.
Variable Exports: funspecs.
Variable GP: globals -> mpred.
Variable vsu: @VSU Espec V cs E Imports p Exports GP.

Lemma VSU_Imports_sub Imports' (HI1: map fst Imports' = map fst Imports)
      (HI2: Forall2 funspec_sub (map snd Imports') (map snd Imports)): 
      @VSU Espec V cs E Imports' p Exports GP.
Proof. destruct vsu as [G c]. exists G. eapply Comp_Imports_sub; eassumption. Qed.

Lemma VSU_Exports_sub1 Exports' (HE1: map fst Exports' = map fst Exports)
      (HE2: Forall2 funspec_sub (map snd Exports) (map snd Exports')):
      @VSU Espec V cs E Imports p Exports' GP.
Proof. destruct vsu as [G c]. exists G. eapply Comp_Exports_sub1; eassumption. Qed.

Lemma VSU_Exports_sub Exports' (LNR: list_norepet (map fst Exports'))
      (HE2: funspecs_sqsub Exports Exports'):
      @VSU Espec V cs E Imports p Exports' GP.
Proof. destruct vsu as [G c]. exists G. eapply Comp_Exports_sub; eassumption. Qed.

Lemma VSU_entail {GP'} : (forall gv, GP gv |-- GP' gv) -> 
      @VSU Espec V cs E Imports p Exports GP'.
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
(*
Lemma merge_specs_succeed {phi1 phi2}:
      funsig_of_funspec phi1 = funsig_of_funspec phi2 ->
      callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2 ->
  binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2)).
Proof. clear. intros.
  simpl. destruct phi1; destruct phi2; simpl in *. subst f0 c0. 
  rewrite ! if_true; trivial.
Qed.*)
(*
Lemma merge_specs_succeed {phi1 phi2}:
      funsigs_match (funsig_of_funspec phi1) (funsig_of_funspec phi2) = true ->
      callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2 ->
  binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2)).
Proof. intros.
  simpl. destruct phi1; destruct phi2; simpl in *. rewrite H.  subst c0.
  rewrite ! if_true; trivial.
Qed.*)

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
(*             (Sigs: funsig_of_funspec phi1 = funsig_of_funspec phi2)*)
(*             (Sigs: funsigs_match (funsig_of_funspec phi1) (funsig_of_funspec phi2) = true)*)
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

Definition signature_of_fundef (fd: Ctypes.fundef function):signature :=
match fd with
    Internal f => {| sig_args := map typ_of_type (map snd (fn_params f));
                     sig_res := rettype_of_type (fn_return f);
                     sig_cc := fn_callconv f |}
  | External ef tys rt cc => signature_of_type tys rt cc
 end.

Definition Fundefs_match p1 p2 (Imports1 Imports2:funspecs) := 
           forall i fd1 fd2,
                         find_id i (prog_funct p1) = Some fd1 ->
                         find_id i (prog_funct p2) = Some fd2 ->
                         match fd1, fd2 with
                           Internal _, Internal _ => fd1=fd2
                         | Internal _, External _ _ _ _ => signature_of_fundef fd1 = signature_of_fundef fd2 /\
                                                           exists phi2, find_id i Imports2 = Some phi2
                         | External _ _ _ _, Internal _ => signature_of_fundef fd1 = signature_of_fundef fd2 /\
                                                           exists phi1, find_id i Imports1 = Some phi1
                         | External _ _ _ _ , External _ _ _ _  => fd1=fd2
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

Definition Functions_preserved (p1 p2 p: Clight.program) i:=
         match find_id i (prog_funct p1), find_id i (prog_funct p2) with
           Some (Internal f1), _ => find_id i (prog_funct p) = Some (Internal f1)
         | _, Some (Internal f2) => find_id i (prog_funct p) = Some (Internal f2)
         | Some (External ef1 tys1 rt1 cc1), _ =>
               find_id i (prog_funct p) = Some (External ef1 tys1 rt1 cc1)
         | _, Some (External ef2 tys2 rt2 cc2) =>
               find_id i (prog_funct p) = Some (External ef2 tys2 rt2 cc2)
         | None, None => find_id i (prog_funct p) = None
         end.

(*It may be possible to eliminate this condition by modifying the definition
  of binary intersection such that instead of requiring parameter names
  to be identical the names are suitably renamed. Note that equality of the
  argument (and return) types already holds, by the semaxfunc properties inside c1 and c2*)
Lemma HContexts {Espec V1 V2 cs1 cs2 
      E1 Imports1 Exports1 E2 Imports2 Exports2 p1 p2 GP1 GP2 G1 G2}
      (c1: @Component Espec V1 cs1 E1 Imports1 p1 Exports1 GP1 G1)
      (c2: @Component Espec V2 cs2 E2 Imports2 p2 Exports2 GP2  G2)
      (FM: Fundefs_match p1 p2 Imports1 Imports2):
      forall i phi1 phi2,
             find_id i G1 = Some phi1 ->
             find_id i G2 = Some phi2 ->
             (*funsigs_match (funsig_of_funspec phi1) (funsig_of_funspec phi2) = true*)
             typesig_of_funspec phi1 = typesig_of_funspec phi2.
Proof. intros. specialize (FM i).
  specialize (Comp_G_in_Fundefs' c1 _ _ H) as [fd1 FD1].
  specialize (Comp_G_in_Fundefs' c2 _ _ H0) as [fd2 FD2].
  specialize (Comp_G_justified c1 _ _ _ FD1 H); intros SF1.
  specialize (Comp_G_justified c2 _ _ _ FD2 H0); intros SF2.
  rewrite FD1, FD2 in *. specialize (FM _ _ (eq_refl _) (eq_refl _)).
  destruct fd1; destruct fd2; simpl in *.
+ (*II*) inv FM. red in SF1, SF2.
  destruct phi1 as [[? ?] ? ? ? ? ? ?].
  destruct phi2 as [[? ?] ? ? ? ? ? ?]. simpl in *.
  destruct SF1 as [? [? [? [? [[? [? _]] _]]]]].
  destruct SF2 as [? [? [? [? [[? [? _]] _]]]]].
  (*destruct H5 as [? [? ?]]; destruct H10 as [? [? ?]]; subst.
  rewrite eqb_type_refl, H5, H10, Forallb2_refl, 2 compute_list_norepet_i; simpl; trivial.
  intros; apply eqb_type_refl.*)
  rewrite <- H5 in H11; subst l0. rewrite <- H6 in H12; subst t0; trivial.
+ destruct FM as [_ [psi2 Psi2]].
  apply (Comp_G_disjoint_from_Imports_find_id c2) in Psi2; unfold Comp_G in Psi2; congruence. 
+ destruct FM as [_ [psi1 Psi1]].
  apply (Comp_G_disjoint_from_Imports_find_id c1) in Psi1; unfold Comp_G in Psi1; congruence.
+ inv FM.
  destruct phi1 as [[? ?] ? ? ? ? ? ?].
  destruct phi2 as [[? ?] ? ? ? ? ? ?]. simpl in *.
  destruct SF1 as [? [? [? _]]].
  destruct SF2 as [? [? [? _]]]. subst t0 t. rewrite <- H3 in H6; subst; trivial.
Qed.

Section ComponentJoin.
Variable Espec: OracleKind.
Variable V1 V2: varspecs.
Variable cs1 cs2 cs: compspecs. 
Variable E1 Imports1 Exports1 G1 E2 Imports2 Exports2 G2 E Imports Exports: funspecs.
Variable p1 p2 p: Clight.program.
Variable GP1 GP2: globals -> mpred.
Variable c1: @Component Espec V1 cs1 E1 Imports1 p1 Exports1 GP1 G1.
Variable c2: @Component Espec V2 cs2 E2 Imports2 p2 Exports2 GP2 G2.

Variable DisjointVarspecs: list_disjoint (map fst V1) (map fst V2).
Variable HV1p1: list_disjoint (map fst V1) (map fst (prog_funct p1)).
Variable HV1p2: list_disjoint (map fst V1) (map fst (prog_funct p2)).
Variable HV2p1: list_disjoint (map fst V2) (map fst (prog_funct p1)).
Variable HV2p2: list_disjoint (map fst V2) (map fst (prog_funct p2)).
Variable LNR_V1: list_norepet (map fst V1).
Variable LNR_V2: list_norepet (map fst V2).
Variable CS1: cspecs_sub cs1 cs.
Variable CS2: cspecs_sub cs2 cs.

Variable V: varspecs.
Variable HV1: forall i phi, find_id i V1 = Some phi -> find_id i V = Some phi.
Variable HV2: forall i phi, find_id i V2 = Some phi -> find_id i V = Some phi.

Variable FundefsMatch: Fundefs_match p1 p2 Imports1 Imports2.

Variable FP: forall i, Functions_preserved p1 p2 p i.

Definition HC := HContexts c1 c2 FundefsMatch.

(********************Assumptions involving E1 and E2  ********)

Variable Externs1_Hyp: list_disjoint (map fst E1) (IntIDs p2).
Variable Externs2_Hyp: list_disjoint (map fst E2) (IntIDs p1).

Variable ExternsHyp: E = G_merge E1 E2. 

(************************************************************)

(*one could try to weaken this hypothesis by weakening the second condition to In i (IntIDs p1),
  so that it is possible to delay resolving the spec for an extern in case several modules prove (mergaable but different) specs for it. The present cluase forces one to use match with the first spec one finds*)
Variable SC1: forall i phiI, find_id i Imports2 = Some phiI -> In i (map fst E1 ++ IntIDs p1) ->
              exists phiE, find_id i Exports1 = Some phiE /\ funspec_sub phiE phiI.

(*same comment here*)
Variable SC2: forall i phiI, find_id i Imports1 = Some phiI -> In i (map fst E2 ++ IntIDs p2) ->
                          exists phiE, find_id i Exports2 = Some phiE /\ funspec_sub phiE phiI.

Variable HImports: forall i phi1 phi2, find_id i Imports1 = Some phi1 -> find_id i Imports2 = Some phi2 -> phi1=phi2.

Variable ImportsDef: Imports = 
                     filter (fun x => negb (in_dec ident_eq (fst x) (map fst E2 ++ IntIDs p2))) Imports1 ++
                     filter (fun x => negb (in_dec ident_eq (fst x) (map fst E1 ++ IntIDs p1 ++ map fst Imports1))) Imports2.

Variable ExportsDef: Exports = G_merge Exports1 Exports2.

Variable LNRp: list_norepet (map fst (prog_defs p)).

Lemma LNR_Imports: list_norepet (map fst Imports).
Proof. subst. clear - c1 c2. rewrite map_app, list_norepet_app; split3.
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
Proof. subst. clear - c1 c2. rewrite G_merge_dom, map_app, list_norepet_app; split3.
    - apply c1.
    - eapply sublist_norepet. apply sublist_map_fst. apply sublist_filter. apply c2.
    - clear -c1. intros x1 x2 X1 X2 N; subst.
      apply list_in_map_inv in X1; destruct X1 as [[i phi1] [Hi X1]]; simpl in Hi; subst i.
      apply list_in_map_inv in X2; destruct X2 as [[i phi2] [Hi X2]]; simpl in Hi; subst i.
      apply filter_In in X2; destruct X2 as [X2 Y2].
      apply find_id_i in X1. rewrite X1 in Y2. congruence. apply c1.
Qed.

Lemma LNR3_V1: list_norepet (map fst V1 ++ map fst (Imports1 ++ (Comp_G c1))).
Proof.
  apply list_norepet_append; trivial. apply Comp_ctx_LNR. 
  rewrite map_app. apply list_disjoint_app_R.
  + eapply list_disjoint_mono. apply HV1p1. 2: trivial. 
    intros. apply list_in_map_inv in H. destruct H as [[j phi] [Phi PHI]]; simpl in Phi; subst x.
    apply find_id_i in PHI. destruct (Comp_Imports_in_Fundefs c1 _ _ PHI) as [f F].
    apply find_id_e in F. eapply in_map_fst. apply F. apply (Comp_Imports_LNR c1).
  + eapply list_disjoint_mono. apply HV1p1. 2: trivial. 
    intros. apply list_in_map_inv in H. destruct H as [[j phi] [Phi PHI]]; simpl in Phi; subst x.
    apply find_id_i in PHI; [ | apply (Comp_G_LNR c1) ].
    destruct (@Comp_G_in_Fundefs' _ _ _ _ _ _ _ _ _ c1 _ _  PHI) as [f F]. apply find_id_In_map_fst in F; trivial.
Qed.

Lemma LNR3_V2: list_norepet (map fst V2 ++ map fst (Imports2 ++ (Comp_G c2))).
Proof.
  apply list_norepet_append; trivial. apply Comp_ctx_LNR. 
  rewrite map_app. apply list_disjoint_app_R.
  + eapply list_disjoint_mono. apply HV2p2. 2: trivial. 
    intros. apply list_in_map_inv in H. destruct H as [[j phi] [Phi PHI]]; simpl in Phi; subst x.
    apply find_id_i in PHI. destruct (Comp_Imports_in_Fundefs c2 _ _ PHI) as [f F].
    apply find_id_e in F. eapply in_map_fst. apply F. apply (Comp_Imports_LNR c2).
  + eapply list_disjoint_mono. apply HV2p2. 2: trivial. 
    intros. apply list_in_map_inv in H. destruct H as [[j phi] [Phi PHI]]; simpl in Phi; subst x.
    apply find_id_i in PHI; [ | apply (Comp_G_LNR c2) ].
    destruct (Comp_G_in_Fundefs' c2 _ _ PHI) as [f F]. apply find_id_In_map_fst in F; trivial.
Qed.

Lemma Imports_in_Fundefs: forall x, In x (map fst Imports) ->
      In x (map fst (prog_funct p1) ++ map fst (prog_funct p2)).
Proof. subst Imports. clear - c1 c2; intros. 
          specialize (Comp_Imports_in_Fundefs c1) ; intros CIF1.
          specialize (Comp_Imports_in_Fundefs c2) ; intros CIF2.
          rewrite map_app in H.
          apply in_or_app. apply in_app_or in H; destruct H.
          * apply list_in_map_inv in H; destruct H as [[i phi] [Phi PHI]]; simpl in Phi; subst x.
            apply filter_In in PHI; simpl in PHI; destruct PHI. apply find_id_i in H; [ | apply (Comp_Imports_LNR c1)].
            destruct (CIF1 _ _ H) as [f Hf].
            left. apply find_id_e in Hf. apply in_map_fst in Hf; trivial.
          * apply list_in_map_inv in H; destruct H as [[i phi] [Phi PHI]]; simpl in Phi; subst x.
            apply filter_In in PHI; simpl in PHI; destruct PHI. apply find_id_i in H; [ | apply (Comp_Imports_LNR c2)].
            destruct (CIF2 _ _ H) as [f Hf].
            remember (find_id i (prog_funct p1) )as k; symmetry in Heqk; destruct k.
            ++ left. apply find_id_e in Heqk. apply in_map_fst in Heqk. trivial.
            ++ right. apply find_id_In_map_fst in Hf. trivial. 
Qed.

Variable V_LNR: list_norepet (map fst V).
Variable domV: forall i, In i (map fst V) -> In i (map fst V1) \/ In i (map fst V2).

Lemma Calling_conventions_match {i psi1 psi2}
      (Hpsi1: find_id i (Comp_G c1) = Some psi1)
      (Hpsi2 : find_id i (Comp_G c2) = Some psi2):
callingconvention_of_funspec psi1 = callingconvention_of_funspec psi2.
Proof. 
  clear - FundefsMatch c1 c2 Hpsi1 Hpsi2. specialize (FundefsMatch i).
  destruct (Comp_G_elim c1 i).
  { apply find_id_In_map_fst in Hpsi1; trivial. } 
  - destruct H. destruct H0 as [? [? [? [? H0]]]]; apply Fundef_of_Gfun in H0.
    rewrite H0 in *.
    destruct (Comp_G_elim c2 i).
    { apply find_id_In_map_fst in Hpsi2; trivial. } 
    * destruct H1. destruct H2 as [? [? [? [? H2]]]]; apply Fundef_of_Gfun in H2.
      rewrite H2 in *.
      specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch.
      inv FundefsMatch.
      specialize (Comp_G_justified c1 _ _ _ H0 Hpsi1). simpl; intros.
      apply ExternalInfo_cc in H3; rewrite <- H3.
      specialize (Comp_G_justified c2 _ _ _ H2 Hpsi2). simpl; intros.
      apply ExternalInfo_cc in H4; rewrite <- H4; trivial. 
    * destruct H1 as [? [? [? ?]]]. apply Fundef_of_Gfun in H3.
      rewrite H3 in *.
      specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch.
      destruct FundefsMatch as [SIG1 _]. unfold signature_of_type in SIG1. inv SIG1. simpl in *.
      specialize (Comp_G_justified c1 _ _ _ H0 Hpsi1). simpl; intros.
      apply ExternalInfo_cc in H4; rewrite <- H4.
      specialize (Comp_G_justified c2 _ _ _ H3 Hpsi2). simpl; intros.
      apply InternalInfo_cc in H7; rewrite <- H7. trivial.
  - destruct H as [? [? [? ?]]]. apply Fundef_of_Gfun in H1.
    rewrite H1 in *.
    destruct (Comp_G_elim c2 i).
    { apply find_id_In_map_fst in Hpsi2; trivial. } 
    * destruct H2. destruct H3 as [? [? [? [? H3]]]]; apply Fundef_of_Gfun in H3.
      rewrite H3 in *.
      specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch.
      destruct FundefsMatch as [SIG1 _]. unfold signature_of_type in SIG1. inv SIG1. simpl in *.
      specialize (Comp_G_justified c1 _ _ _ H1 Hpsi1). simpl; intros.
      apply InternalInfo_cc in H4; rewrite <- H4.
      specialize (Comp_G_justified c2 _ _ _ H3 Hpsi2). simpl; intros.
      apply ExternalInfo_cc in H7; rewrite <- H7; trivial.
    * destruct H2 as [? [? [? ?]]]. apply Fundef_of_Gfun in H4.
      rewrite H4 in *.
      specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch.
      inv FundefsMatch.
      specialize (Comp_G_justified c1 _ _ _ H1 Hpsi1). simpl; intros.
      apply InternalInfo_cc in H5; rewrite <- H5.
      specialize (Comp_G_justified c2 _ _ _ H4 Hpsi2). simpl; intros.
      apply InternalInfo_cc in H6; rewrite <- H6. trivial.
Qed.

Lemma Exports_sqsub1: funspecs_sqsub Exports Exports1.
Proof.
  clear - c1 c2 (*HContexts*) ExportsDef FundefsMatch.
  subst; apply G_merge_sqsub1. intros; split.
+ apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
  apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]].  
  specialize (HC i _ _ Hpsi1 Hpsi2). 
  clear - Sub1 Sub2 (*HContexts*).
  destruct psi1; destruct phi1. destruct Sub1 as [[? ?] _]; subst; simpl.
  destruct psi2; destruct phi2. destruct Sub2 as [[? ?] _]; subst; simpl. trivial.
  (*intros.
  rewrite funsigs_match_symm in H.
  eapply funsigs_match_trans; [ apply H |]. 
  eapply funsigs_match_trans; eassumption.*)
+ apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
  apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]].
  apply funspec_sub_cc in Sub1.
  apply funspec_sub_cc in Sub2. 
  rewrite <- Sub1, <- Sub2; clear Sub1 Sub2.
  apply (Calling_conventions_match Hpsi1 Hpsi2).
Qed.

Lemma Exports_sqsub2: funspecs_sqsub Exports Exports2.
Proof.
  clear - c1 c2 (*HContexts*) ExportsDef FundefsMatch.
  subst; apply G_merge_sqsub2; [ apply (Comp_Exports_LNR c2) | intros; split ].
+ apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
  apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]]. 
  specialize (HC i _ _ Hpsi1 Hpsi2). 
  clear - Sub1 Sub2 (*HContexts*).
  destruct psi1; destruct phi1. destruct Sub1 as [[? ?] _]; subst; simpl.
  destruct psi2; destruct phi2. destruct Sub2 as [[? ?] _]; subst; simpl. trivial.
  (*intros.
  rewrite  funsigs_match_symm in H.
  eapply funsigs_match_trans; [ apply H |]. 
  eapply funsigs_match_trans; eassumption.*)
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
Proof. clear - H1 H2 c1 c2 (*HContexts*) ExportsDef FundefsMatch.
  subst Exports; apply G_merge_sqsub3; trivial.
+  apply (Comp_Exports_LNR c2).
+ intros; split.
  - apply c1 in H. destruct H as [psi1 [Hpsi1 Sub1]]. 
    apply c2 in H0. destruct H0 as [psi2 [Hpsi2 Sub2]]. 
    specialize (HC i _ _ Hpsi1 Hpsi2). 
    clear - Sub1 Sub2 (*HContexts*).
    destruct psi1; destruct phi1. destruct Sub1 as [[? ?] _]; subst; simpl.
    destruct psi2; destruct phi2. destruct Sub2 as [[? ?] _]; subst; simpl. trivial.
    (*intros.
    rewrite  funsigs_match_symm in H.
    eapply funsigs_match_trans; [ apply H |]. 
    eapply funsigs_match_trans; eassumption.*)
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
      InitGPred (a :: X) gv = (globs2pred gv a gv * InitGPred X gv)%logic.
Proof. clear. reflexivity. Qed.

Lemma InitGPred_middleD Y a gv: forall X,
      InitGPred (Y ++ a :: X) gv = (globs2pred gv a gv * InitGPred Y gv * InitGPred X gv)%logic.
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
      globs2pred gv a gv = EX i v, !! (a=(i,Gvar v) /\ headptr (gv i)) && initialize.gv_globvar2pred gv (i, v) gv.
Proof. clear. unfold globs2pred. destruct a. unfold isGvar; simpl. destruct g; intros. discriminate.
 apply pred_ext. Intros. Exists i v. entailer!.
 Intros ii vv. inv H0. entailer!.
Qed.

Lemma globs2predD_false a gv: false = isGvar a ->
      globs2pred gv a gv = emp.
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
(*
Proof. clear; intros. apply list_disjoint_app_inv in H; destruct H.
  apply list_disjoint_consD in H0; destruct H0. split; trivial.
  apply list_disjoint_app_L; trivial.
Qed.*)

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

Lemma InitGPred_join {gv} VDp1 VDp2 VDp
     (VD1: map fst (filter isGvar VDp1) = map fst V1)
     (VD2: map fst (filter isGvar VDp2) = map fst V2)
     (VD: map fst (filter isGvar VDp) = map fst V)

     (HVardefs1: forall i d, find_id i (filter isGvar VDp1) = Some d -> find_id i (filter isGvar VDp) = Some d)
     (HVardefs2: forall i d, find_id i (filter isGvar VDp2) = Some d -> find_id i (filter isGvar VDp) = Some d):
      InitGPred (filter isGvar VDp) gv
      = (InitGPred (filter isGvar VDp1) gv * InitGPred (filter isGvar VDp2) gv)%logic.
Proof. 
  clear HImports ImportsDef ExportsDef HV1p1 HV2p1 HV1p2 HV2p2 SC1 SC2 Externs1_Hyp Externs2_Hyp ExternsHyp CS1 CS2 FundefsMatch cs1 cs2 c1 c2 E1 Imports1 Exports1 G1 E2 Imports2 Exports2 G2
        FP LNRp p p1 p2 E Imports Exports cs.
  (*unfold Vardefs, prog_funct in *. forget (prog_defs p) as d.
  forget (prog_defs p1) as d1. forget (prog_defs p2) as d2.*)
  revert HVardefs1 HVardefs2 LNR_V2 LNR_V1 HV2 HV1 VD2 VD1 DisjointVarspecs domV VD V_LNR.
  generalize dependent V2. generalize dependent V1.
  generalize dependent V. generalize dependent VDp2. generalize dependent VDp1. clear.
  induction VDp; simpl; intros.
  - symmetry in VD; apply map_eq_nil in VD; subst V.
    assert (V1 = nil).
    { clear - HV1. destruct V1; trivial. destruct p. specialize (HV1 i t); simpl in HV1.
      rewrite if_true in HV1 by trivial. specialize (HV1 (eq_refl _)); discriminate. }
    subst V1. apply map_eq_nil in VD1; rewrite VD1; clear VD1.
    assert (V2 = nil).
    { clear - HV2. destruct V2; trivial. destruct p. specialize (HV2 i t); simpl in HV2.
      rewrite if_true in HV2 by trivial. specialize (HV2 (eq_refl _)); discriminate. }
    subst V2. apply map_eq_nil in VD2; rewrite VD2; clear VD2.
    unfold InitGPred. simpl. (*cancel.*)rewrite emp_sepcon; trivial.
  - remember (isGvar a) as Q1; destruct Q1; [ simpl in * | eapply (IHVDp _ _ V V1 V2); clear IHVDp; trivial ].
    destruct V as [ | [j z] VV]; inv VD; simpl in *.
    inv V_LNR. rewrite InitGPred_consD.
      destruct (domV (fst a)) as  [Hj1 | Hj2]; [ left; trivial | |].
      + (*destruct (In_map_fst_find_id Hj1) as [ tp Tp]; trivial.*)
         rewrite <- VD1 in Hj1. destruct (In_map_fst_find_id Hj1) as [ u U]; trivial. rewrite VD1; trivial.
         destruct a as [i gd]. simpl fst in *; simpl snd in *.
         assert (HVD1 := HVardefs1 i _ U). rewrite if_true in HVD1 by trivial. inv HVD1.
        (* apply in_split in Hj1. destruct Hj1 as [Y [Z YZ]].
 rewrite YZ in *.*)
         destruct (list_in_map_inv _ _ _ Hj1) as [[jj tj] [JJ Tj]]. simpl in JJ; subst jj.
         apply in_split in Tj. destruct Tj as [d1a [d1b App1]]. rewrite App1.
         assert (tj = u).
         { rewrite App1, find_id_app_char in U. remember (find_id i d1a). destruct o.
           - symmetry in Heqo; apply find_id_e in Heqo. apply in_split in Heqo. destruct Heqo as [X1 [X2 XX]].
             subst d1a.  rewrite <- VD1, App1 in LNR_V1. clear- LNR_V1.
             rewrite ! map_app in LNR_V1. simpl in LNR_V1. apply list_norepet_middleD in LNR_V1. destruct LNR_V1; clear LNR_V1.
             elim H. apply in_or_app. left. apply in_or_app. right; left; trivial.
           - simpl in U. rewrite if_true in U by trivial. inv U; trivial. }
         subst tj.
         rewrite InitGPred_middleD. (*cancel*) rewrite ! sepcon_assoc. f_equal.
         assert (filter isGvar (filter isGvar VDp1) = filter isGvar (d1a ++ (i, u) :: d1b)).
         { rewrite App1; trivial. }
         rewrite filter_involutive, filter_app in H.
         rewrite App1 in VD1. destruct (map_app_inv _ _ _ VD1) as [V1a [V1b [HV1a [HV1b UU]]]]; subst V1.
         simpl in HV1b. destruct V1b as [ |v1 V1b]. inv HV1b. simpl in HV1b.
         destruct v1 as [j zz]; simpl in *. inv HV1b. rename H5 into HV1b.

         (*eapply derives_trans. eapply (IHVDp (d1a++d1b) VDp2 VV (V1a++V1b) V2) ; clear IHVDp; trivial.*)
         rewrite (IHVDp (d1a++d1b) VDp2 VV (V1a++V1b) V2); clear IHVDp; trivial.
         (*9: rewrite filter_app, InitGPred_app; trivial.*)
         * rewrite filter_app, InitGPred_app, <- ! sepcon_assoc. f_equal.
             rewrite 2 filter_redundant; trivial.
              intros. apply (filter_In _ _ VDp1). rewrite App1; apply in_or_app. right. right; trivial.
              intros. apply (filter_In _ _ VDp1). rewrite App1; apply in_or_app. left; trivial.
         * intros. rewrite H in HVardefs1. specialize (HVardefs1 i d).
             assert (Hi: i <> j).
             { intros N; subst. clear - App1 VD1 H H0 LNR_V1 HeqQ1 HV1a HV1b .
               apply find_id_In_map_fst in H0. rewrite filter_app, map_app  in H0.
               rewrite <- VD1, map_app in LNR_V1. simpl in LNR_V1.
               apply list_norepet_middleD in LNR_V1; destruct LNR_V1 as [XX YY]; clear LNR_V1.
               clear - XX H0. elim XX; clear XX. apply in_or_app; apply in_app_or in H0; destruct H0.
               - left. apply in_map_iff in H; destruct H as [? [? ?]]; subst. apply filter_In in H0; destruct H0.
                 apply in_map_iff. exists x. split; trivial.
               - right. apply in_map_iff in H; destruct H as [? [? ?]]; subst. apply filter_In in H0; destruct H0.
                 apply in_map_iff. exists x. split; trivial. }
             rewrite if_false in HVardefs1 by trivial. apply HVardefs1. simpl. rewrite <- HeqQ1.
             rewrite find_id_app_char. simpl. rewrite filter_app, find_id_app_char in H0. rewrite if_false; trivial.
         * intros. specialize (HVardefs2 i d H0). rewrite if_false in HVardefs2; trivial.
             intros N; subst. rewrite <- VD1, <- VD2,  map_app  in DisjointVarspecs.
              apply find_id_In_map_fst in H0.
              apply (DisjointVarspecs j j); trivial. apply in_or_app. right; left; trivial.
         * rewrite map_app in *. simpl in LNR_V1. apply semax_prog.list_norepet_cut_middle in LNR_V1; trivial.
         * intros. specialize (HV2 _ _ H0). rewrite if_false in HV2; trivial.
              intros N; subst. rewrite <- VD1, map_app  in DisjointVarspecs.
              apply find_id_In_map_fst in H0.
              apply (DisjointVarspecs j j); trivial. apply in_or_app. right; left; trivial.
         * intros. 
             assert (JI: i <> j).
             { rewrite map_app in LNR_V1. simpl in LNR_V1.
               apply list_norepet_middleD in LNR_V1. clear - LNR_V1 H0. intros N; subst.
               apply LNR_V1. apply find_id_In_map_fst in H0. rewrite map_app in H0; trivial. }
             specialize (HV1 i phi). rewrite if_false in HV1 by trivial.
             apply HV1. rewrite find_id_app_char in *. destruct (find_id i V1a); trivial.
             simpl. rewrite if_false; trivial.
         * rewrite map_app, <- HV1a, <- HV1b, filter_app, map_app. clear - App1.
              rewrite 2 filter_redundant; trivial.
              intros. apply (filter_In _ _ VDp1). rewrite App1; apply in_or_app. right. right; trivial.
              intros. apply (filter_In _ _ VDp1). rewrite App1; apply in_or_app. left; trivial.
         * rewrite map_app in DisjointVarspecs. simpl in DisjointVarspecs. rewrite map_app.
             apply list_disjoint_middleD in DisjointVarspecs. apply  DisjointVarspecs.
         * intros. assert (i<>j) by congruence. rewrite map_app. 
              simpl in domV; destruct (domV i) as [HH | HH]. right; trivial.
              rewrite map_app in HH; simpl in HH.
              apply in_app_or in HH. destruct HH. left; apply in_or_app; left; trivial.
              inv H5. congruence. left; apply in_or_app; right; trivial.
              right; trivial.
         (* * { rewrite 2 filter_redundant; trivial.
              intros. apply (filter_In _ _ VDp1). rewrite App1; apply in_or_app. right. right; trivial.
              intros. apply (filter_In _ _ VDp1). rewrite App1; apply in_or_app. left; trivial. }*)

      + (*symmetric*)
         rewrite <- VD2 in Hj2. destruct (In_map_fst_find_id Hj2) as [ u U]; trivial. rewrite VD2; trivial.
         destruct a as [i gd]. simpl fst in *; simpl snd in *.
         assert (HVD2 := HVardefs2 i _ U). rewrite if_true in HVD2 by trivial. inv HVD2.
         destruct (list_in_map_inv _ _ _ Hj2) as [[jj tj] [JJ Tj]]. simpl in JJ; subst jj.
         apply in_split in Tj. destruct Tj as [d2a [d2b App2]]. rewrite App2.
         assert (tj = u).
         { rewrite App2, find_id_app_char in U. remember (find_id i d2a). destruct o.
           - symmetry in Heqo; apply find_id_e in Heqo. apply in_split in Heqo. destruct Heqo as [X1 [X2 XX]].
             subst d2a.  rewrite <- VD2, App2 in LNR_V2. clear- LNR_V2.
             rewrite ! map_app in LNR_V2. simpl in LNR_V2. apply list_norepet_middleD in LNR_V2. destruct LNR_V2; clear LNR_V2.
             elim H. apply in_or_app. left. apply in_or_app. right; left; trivial.
           - simpl in U. rewrite if_true in U by trivial. inv U; trivial. }
         subst tj.
         rewrite InitGPred_middleD. (*cancel.*) rewrite ! sepcon_assoc. 
                 rewrite (sepcon_comm (InitGPred (filter isGvar VDp1) gv)).
                 rewrite ! sepcon_assoc. f_equal.
         assert (filter isGvar (filter isGvar VDp2) = filter isGvar (d2a ++ (i, u) :: d2b)).
         { rewrite App2; trivial. }
         rewrite filter_involutive, filter_app in H.
         rewrite App2 in VD2. destruct (map_app_inv _ _ _ VD2) as [V2a [V2b [HV2a [HV2b UU]]]]; subst V2.
         simpl in HV2b. destruct V2b as [ |v2 V2b]. inv HV2b. simpl in HV2b.
         destruct v2 as [j zz]; simpl in *. inv HV2b. rename H5 into HV2b.

         (*eapply derives_trans. eapply (IHVDp VDp1 (d2a++d2b)  VV V1 (V2a++V2b)) ; clear IHVDp; trivial.
         9: rewrite filter_app, InitGPred_app; trivial.*)
         rewrite (IHVDp VDp1 (d2a++d2b)  VV V1 (V2a++V2b)) ; clear IHVDp; trivial.
         * rewrite sepcon_comm, filter_app, InitGPred_app, <- ! sepcon_assoc. f_equal.
             rewrite 2 filter_redundant; trivial.
              intros. apply (filter_In _ _ VDp2). rewrite App2; apply in_or_app. right. right; trivial.
              intros. apply (filter_In _ _ VDp2). rewrite App2; apply in_or_app. left; trivial.
         * intros. specialize (HVardefs1 i d H0). rewrite if_false in HVardefs1; trivial.
             intros N; subst. rewrite <- VD1, <- VD2,  map_app  in DisjointVarspecs.
              apply find_id_In_map_fst in H0.
              apply (DisjointVarspecs j j); trivial. apply in_or_app. right; left; trivial.
         * intros. rewrite H in HVardefs2. specialize (HVardefs2 i d).
             assert (Hi: i <> j).
             { intros N; subst. clear - App2 VD2 H H0 LNR_V2 HeqQ1 HV2a HV2b .
               apply find_id_In_map_fst in H0. rewrite filter_app, map_app  in H0.
               rewrite <- VD2, map_app in LNR_V2. simpl in LNR_V2.
               apply list_norepet_middleD in LNR_V2; destruct LNR_V2 as [XX YY]; clear LNR_V2.
               clear - XX H0. elim XX; clear XX. apply in_or_app; apply in_app_or in H0; destruct H0.
               - left. apply in_map_iff in H; destruct H as [? [? ?]]; subst. apply filter_In in H0; destruct H0.
                 apply in_map_iff. exists x. split; trivial.
               - right. apply in_map_iff in H; destruct H as [? [? ?]]; subst. apply filter_In in H0; destruct H0.
                 apply in_map_iff. exists x. split; trivial. }
             rewrite if_false in HVardefs2 by trivial. apply HVardefs2. simpl. rewrite <- HeqQ1.
             rewrite find_id_app_char. simpl. rewrite filter_app, find_id_app_char in H0. rewrite if_false; trivial.
     
         * rewrite map_app in *. simpl in LNR_V2. apply semax_prog.list_norepet_cut_middle in LNR_V2; trivial.
         * intros. 
             assert (JI: i <> j).
             { rewrite map_app in LNR_V2. simpl in LNR_V2.
               apply list_norepet_middleD in LNR_V2. clear - LNR_V2 H0. intros N; subst.
               apply LNR_V2. apply find_id_In_map_fst in H0. rewrite map_app in H0; trivial. }
             specialize (HV2 i phi). rewrite if_false in HV2 by trivial.
             apply HV2. rewrite find_id_app_char in *. destruct (find_id i V2a); trivial.
             simpl. rewrite if_false; trivial.
         * intros. specialize (HV1 _ _ H0). rewrite if_false in HV1; trivial.
              intros N; subst. rewrite <- VD2, map_app  in DisjointVarspecs.
              apply find_id_In_map_fst in H0.
              apply (DisjointVarspecs j j); trivial. apply in_or_app. right; left; trivial.
         * rewrite map_app, <- HV2a, <- HV2b, filter_app, map_app. clear - App2.
              rewrite 2 filter_redundant; trivial.
              intros. apply (filter_In _ _ VDp2). rewrite App2; apply in_or_app. right. right; trivial.
              intros. apply (filter_In _ _ VDp2). rewrite App2; apply in_or_app. left; trivial.
         * rewrite map_app in DisjointVarspecs. simpl in DisjointVarspecs. rewrite map_app.
             apply list_disjoint_sym in DisjointVarspecs. apply list_disjoint_sym.
             apply list_disjoint_middleD in DisjointVarspecs. apply  DisjointVarspecs.
         * intros. assert (i<>j) by congruence. rewrite map_app. 
              simpl in domV; destruct (domV i) as [HH | HH]. right; trivial.
             left; trivial.
              rewrite map_app in HH; simpl in HH.
              apply in_app_or in HH. destruct HH. right; apply in_or_app; left; trivial.
              inv H5. congruence. right; apply in_or_app; right; trivial.
         (** { cancel. rewrite 2 filter_redundant; trivial.
              intros. apply (filter_In _ _ VDp2). rewrite App2; apply in_or_app. right. right; trivial.
              intros. apply (filter_In _ _ VDp2). rewrite App2; apply in_or_app. left; trivial. }*)
Qed.

Variable VD1: map fst (Vardefs p1) = map fst V1.
Variable VD2: map fst (Vardefs p2) = map fst V2.
Variable VD: map fst (Vardefs p) = map fst V.

Variable HVardefs1: forall i d, find_id i (Vardefs p1) = Some d -> find_id i (Vardefs p) = Some d.
Variable HVardefs2: forall i d, find_id i (Vardefs p2) = Some d -> find_id i (Vardefs p) = Some d.

Lemma ComponentJoin:
   @Component Espec (*(V1++V2)*)V cs E Imports p Exports ((fun gv => GP1 gv * GP2 gv)%logic) (G_merge (Comp_G c1) (Comp_G c2)).
Proof.
  specialize (Comp_G_disjoint_from_Imports c1); intros D_GImp1.
  specialize (Comp_G_disjoint_from_Imports c2); intros D_GImp2.
  specialize (Comp_Interns_disjoint_from_Imports c1); intros D_ImpInt1.
  specialize (Comp_Interns_disjoint_from_Imports c2); intros D_ImpInt2.
  specialize (Comp_G_LNR c1); intros LNR_G1.
  specialize (Comp_G_LNR c2); intros LNR_G2.
  assert (LNR_Ints2 := Comp_LNR_Interns c2).
  assert (LNR_Ints1 := Comp_LNR_Interns c1). 
  assert (LMR_Imp:= LNR_Imports).
  assert (LMR_Exp:= LNR_Exports).

  remember (G_merge (Comp_G c1) (Comp_G c2)) as G.

  assert (DOM_G: forall i, In i (map fst G) ->
          In i (map fst (Comp_G c1 ++ Comp_G c2))).
  { intros. subst G. rewrite G_merge_dom, map_app in H.
    rewrite map_app. apply in_app_or in H. apply in_or_app.
    destruct H.
    + left; trivial. 
    + apply list_in_map_inv in H. destruct H as [[j phi] [JJ J]]; simpl in JJ; subst j.
      apply filter_In in J; destruct J as [J1 J2]. apply (in_map fst) in J1; right; trivial. } 

  assert (G_in_Fundefs: forall i, 
          In i (map fst G) ->
          In i (map fst (prog_funct p1) ++ map fst (prog_funct p2))).
  { subst G; clear - c1 c2; intros. apply G_merge_InDom in H; [ apply in_or_app | apply (Comp_G_LNR c1)].
    destruct H as [H | [_ H]]; apply Comp_G_in_Fundefs in H; 
    destruct H; apply find_id_In_map_fst in H; auto. }

  assert (LNR_E_Imports: list_norepet (map fst (E ++ Imports))).
  { subst E Imports.
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
  { subst G; clear - LNR_G1 LNR_G2 Externs2_Hyp Externs1_Hyp.
    apply G_merge_LNR; [ apply (Comp_G_LNR c1) | apply (Comp_G_LNR c2)]. }

  assert (V1_D1: list_disjoint (map fst V1) (map fst (Imports ++ G))).
  { eapply list_disjoint_mono with (l2':= (map fst (prog_funct p1) ++ map fst (prog_funct p2)))
    (l1':= map fst V1); trivial.
    + do 5 intros ?; subst. apply in_app_or in H0; destruct H0.
      apply (HV1p1 y y ); trivial. apply (HV1p2 y y); trivial.
    + intros. rewrite map_app in H. apply in_app_or in H. destruct H.
      apply Imports_in_Fundefs; trivial. apply G_in_Fundefs; trivial. }

  assert (V2_D1: list_disjoint (map fst V2) (map fst (Imports ++ G))).
  { eapply list_disjoint_mono with (l2':= (map fst (prog_funct p1) ++ map fst (prog_funct p2)))
    (l1':= map fst V2); trivial.
    + do 5 intros ?; subst. apply in_app_or in H0; destruct H0.
      apply (HV2p1 y y ); trivial. apply (HV2p2 y y); trivial.
    + intros. rewrite map_app in H. apply in_app_or in H. destruct H.
      apply Imports_in_Fundefs; trivial. apply G_in_Fundefs; trivial. }

  assert (Imports_G_disjoint: list_disjoint (map fst Imports) (map fst G)).
  { clear - ImportsDef HeqG D_GImp1 D_GImp2 LNR_G2 LNR_G1; subst Imports G. do 5 intros ?; subst.
      apply list_in_map_inv in H. destruct H as [[i phi] [Q Hi]]; simpl in Q; subst y.
      apply (@G_merge_InDom (Comp_G c1) (Comp_G c2) i (Comp_G_LNR c1)) in H0. 
      apply in_app_or in Hi; destruct Hi as [Hi | Hi]; apply filter_In in Hi; simpl in Hi.
      + destruct Hi. apply in_map_fst in H.
        apply (list_disjoint_notin i D_GImp1) in H.
        destruct H0 as [HH1 | [_ HH2]]. contradiction.
        destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)); simpl in H1. inv H1. clear H1.
        apply n; clear n; apply in_or_app.
        apply Comp_G_elim in HH2; destruct HH2. left; apply H0. right; apply H0.
      + destruct Hi. destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)). inv H1. clear H1.
        apply n; clear n; apply in_or_app. destruct H0 as [HH1 | [_ HH2]].
        - apply Comp_G_elim in HH1. destruct HH1. left; apply H0. destruct H0 as [? [? [f Hf]]]. right.
          apply in_or_app. left; trivial.
        - apply in_map_fst in H; elim (D_GImp2 i i); trivial. }

  assert (LNR4_V1: list_norepet (map fst V1 ++ map fst (Imports ++ G))). 
  { (*subst G.*) rewrite list_norepet_app; split3; trivial.
    rewrite map_app, list_norepet_app; split3; trivial.  }

  assert (LNR4_V2: list_norepet (map fst V2 ++ map fst (Imports ++ G))).
  {  subst G. rewrite list_norepet_app; split3; trivial.
     rewrite map_app, list_norepet_app; split3; trivial. }

  assert (LNR2: list_norepet (map fst V ++ map fst (Imports ++ (G_merge (Comp_G c1) (Comp_G c2))))).
  { subst G. forget (G_merge (Comp_G c1) (Comp_G c2)) as G. clear - domV V1_D1 V2_D1 LNR4_V2 V_LNR.
    apply list_norepet_append; [ trivial | apply list_norepet_append_right in LNR4_V2; trivial | ].
    intros ? ? ?. apply domV in H; destruct H; clear domV.
    apply (V1_D1 _ _ H).
    apply (V2_D1 _ _ H). }

  specialize (Comp_G_justified c2); intros JUST2. specialize (Comp_G_justified c1); intros JUST1.

assert (Condition1: forall i, In i (map fst Imports) ->
        exists (f : external_function) (ts : typelist) (t : type) (cc : calling_convention),
        find_id i (prog_defs p) = Some (Gfun (External f ts t cc))). 
{ subst Imports; clear - c1 c2 FP LNRp. intros. rewrite map_app in H. apply in_app_or in H; destruct H.
  - clear - H c1 c2 FP LNRp. specialize (FP i).
    apply list_in_map_inv in H. destruct H as [[j phi] [H J]]. simpl in H; subst j.
    apply filter_In in J. simpl in J. destruct J as [J1 J2]. 

    destruct (Comp_Imports_external c1 i) as [ef [ts [t [cc FND]]]].
    { apply (in_map fst) in J1. apply J1. }
    
    apply Fundef_of_Gfun in FND. red in  FP. rewrite FND in FP.
    remember (find_id i (prog_funct p2)) as u; symmetry in Hequ; destruct u.
    * apply Gfun_of_Fundef in Hequ. 2: apply c2.
      destruct f.
      ++ destruct (in_dec ident_eq i (map fst E2 ++ IntIDs p2)). inv J2. 
         elim n. apply in_or_app. right. apply in_map_iff.
         exists (i, Gfun (Internal f)); simpl; split; trivial. 
         rewrite filter_In; simpl. split; trivial. apply find_id_e; trivial.
      ++ apply Gfun_of_Fundef in FP. do 4 eexists; eassumption. apply LNRp.
    * apply Gfun_of_Fundef in FP. do 4 eexists; eassumption. apply LNRp.

  - specialize (FP i).
    apply list_in_map_inv in H. destruct H as [[j phi] [H J]]. simpl in H; subst j.
    apply filter_In in J. simpl in J. destruct J as [J1 J2]. 

    destruct (Comp_Imports_external c2 i) as [ef [ts [t [cc FND]]]].
    { apply (in_map fst) in J1. apply J1. }
    
    apply Fundef_of_Gfun in FND. hnf in FP. rewrite FND in FP.
    remember (find_id i (prog_funct p1)) as u; symmetry in Hequ; destruct u.
    * apply Gfun_of_Fundef in Hequ. 2: apply c1.
      destruct f.
      ++ destruct (in_dec ident_eq i (map fst E1 ++ IntIDs p1 ++ map fst Imports1)). inv J2. 
         elim n. apply in_or_app. right. apply in_or_app. left. apply in_map_iff.
         exists (i, Gfun (Internal f)); simpl; split; trivial. 
         rewrite filter_In; simpl. split; trivial. apply find_id_e; trivial.
      ++ apply Gfun_of_Fundef in FP. do 4 eexists; eassumption. apply LNRp.
    * apply Gfun_of_Fundef in FP. do 4 eexists; eassumption. apply LNRp. }

assert (Condition2: forall i : ident, In i (map fst E) ->
        exists ef ts t cc, find_id i (prog_defs p) = Some (Gfun (External ef ts t cc))).
{ intros; subst E. specialize (FP i). hnf in FP. apply G_merge_InDom in H. destruct H as [Hi | [NE Hi]].
  - destruct (Comp_Externs c1 _ Hi) as [ef [tys [rt [cc P1i]]]]. exists ef, tys, rt, cc.
    clear - P1i Hi FP Externs1_Hyp LNRp c2.
    apply Fundef_of_Gfun in P1i. hnf in FP; rewrite P1i in FP.
    remember (find_id i (prog_funct p2)) as u; symmetry in Hequ; destruct u.
    * destruct f.
      ++ apply Gfun_of_Fundef in Hequ. 2: apply c2.
         apply IntIDs_i in Hequ.
         elim (Externs1_Hyp i i); trivial.
      ++ apply Gfun_of_Fundef in FP; trivial. 
    * apply Gfun_of_Fundef in FP; trivial. 
  - destruct (Comp_Externs c2 _ Hi) as [ef [tys [rt [cc P2i]]]]. exists ef, tys, rt, cc.
    clear - P2i Hi FP Externs2_Hyp LNRp Externs1_Hyp c2 c1 FundefsMatch.
    specialize (FundefsMatch i).
    apply Fundef_of_Gfun in P2i. rewrite P2i in *. 
    remember (find_id i (prog_funct p1)) as u; symmetry in Hequ; destruct u.
    * destruct f.
      ++ apply Gfun_of_Fundef in Hequ. 2: apply c1.
         clear - Hequ Externs2_Hyp Hi. apply IntIDs_i in Hequ.
         elim (Externs2_Hyp i i); trivial.
      ++ specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). inv FundefsMatch.
         apply Gfun_of_Fundef in FP; trivial. 
    * apply Gfun_of_Fundef in FP; trivial.
  - apply (Comp_Externs_LNR c1). }

assert ( SUBSUME1 : forall i : ident,
           subsumespec (find_id i (Imports1 ++ Comp_G c1)) (find_id i (Imports ++ G))).
{ subst Imports G; intros i. specialize (@Calling_conventions_match i).
  assert (HCi := HC i).
  clear - c1 c2 HCi Externs2_Hyp Externs1_Hyp (*HContexts*) (*Calling_conventions_match *) SC1 SC2 JUST1 JUST2. 
  intros CC. apply subsumespec_app_left; intros.
           { rewrite ! find_id_app_char. 
             remember (find_id i Imports1) as q1; symmetry in Heqq1; destruct q1 as [phi1 |]; simpl; trivial.
             (*assert (LNRphi1:= Comp_Imports_paramsLNR c1 i). rewrite Heqq1 in LNRphi1.
             split; trivial.*)
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
               (*assert (LNRphi1:= Comp_G_paramsLNR' c1 _ _ Heqd).
              split; trivial.*)
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
      rewrite ImportsDef; clear ImportsDef. rewrite <- app_assoc, ! find_id_app_char, ! find_id_filter_char; try apply (Comp_Imports_LNR c2) ; try apply (Comp_Imports_LNR c1).
      simpl. remember (find_id i Imports2) as q; symmetry in Heqq; destruct q as [phi2' |].
      + inv Hequ. clear - D_GImp2 i HV2p1 Heqq SC1 LNR_G1 HImports.
        (*assert (LNRphi2:= Comp_Imports_paramsLNR c2 i). rewrite Heqq in LNRphi2.
        split; trivial.*)
        specialize (list_disjoint_map_fst_find_id1 D_GImp2 _ _ Heqq); intros.
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
          (*assert (pLNRphi2:= Comp_G_paramsLNR' c2 _ _ Hequ).
          split; trivial.*)
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

assert (TypesOfFunspecs1: forall i, sub_option (make_tycontext_g V1 (Imports1 ++ Comp_G c1)) ! i
  (make_tycontext_g (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2))) ! i).
{ subst G; clear - SUBSUME1 LNR_V1 LNR4_V1 HV1p1 LNR2 HV1. intros i.
  rewrite 2 semax_prog.make_context_g_char, 2 make_tycontext_s_find_id; trivial.
  specialize (SUBSUME1 i). red in SUBSUME1. destruct (find_id i (Imports1 ++ Comp_G c1)); simpl.
  + destruct SUBSUME1 as [psi2 [PHI2 Sub]]. rewrite PHI2.
    exploit (Sub (compcert_rmaps.RML.empty_rmap 0)); [ trivial | intros FS].
    apply type_of_funspec_sub_si in FS; rewrite FS; trivial.
  + remember (find_id i V1) as w; symmetry in Heqw; destruct w as [phi |]; simpl; trivial.
    rewrite (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V1 i phi Heqw).
    apply HV1; trivial.
  + apply LNR3_V1.
}

assert (TypesOfFunspecs2: forall i, sub_option (make_tycontext_g V2 (Imports2 ++ Comp_G c2)) ! i
  (make_tycontext_g (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2))) ! i).
{ subst G; clear - DisjointVarspecs SUBSUME2 LNR_V2 LNR4_V2 HV2p2 LNR2 HV2. intros i.
  rewrite 2 semax_prog.make_context_g_char, 2 make_tycontext_s_find_id; trivial.
  specialize (SUBSUME2 i). red in SUBSUME2. destruct (find_id i (Imports2 ++ Comp_G c2)); simpl.
  + destruct SUBSUME2 as [psi2 [PHI2 Sub]]. rewrite PHI2.
    exploit (Sub (compcert_rmaps.RML.empty_rmap 0)); [ trivial | intros FS].
    apply type_of_funspec_sub_si in FS; rewrite FS; trivial.
  + remember (find_id i V2) as w; symmetry in Heqw; destruct w as [phi |]; simpl; trivial.
    rewrite (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V2 _ _ Heqw).
    apply HV2; trivial.
  + apply LNR3_V2.
}

apply Build_Component (*with (Comp_G := G)*) (*with 
     (Comp_InitPred := fun gv => (Comp_InitPred c1 gv * Comp_InitPred c2 gv)%logic)*); trivial.
+ intros. subst G E. split; intros. 
  - apply G_merge_InDom; [ apply c1 | apply in_app_or in H; destruct H].
    * destruct (in_dec ident_eq i (map fst (Comp_G c1))). left; trivial. right; split; trivial.
      apply c2. specialize (FP i). hnf in FP.
      remember (find_id i (prog_funct p1) ) as q1; destruct q1.
      ++ destruct f.
         -- clear - Heqq1 FP LNRp H n.
            symmetry in Heqq1. elim n. apply c1. apply in_or_app; left. 
            apply Gfun_of_Fundef in Heqq1. 2: apply c1. apply IntIDs_i in Heqq1; trivial.
         -- clear - Heqq1 FP LNRp H n c2. 
            (*the following 8 lines are repeated below*)
            remember (find_id i (prog_funct p2)) as q2; destruct q2.
            ** destruct f. symmetry in Heqq2. apply in_or_app; left.
               apply Gfun_of_Fundef in Heqq2. 2: apply c2. apply IntIDs_i in Heqq2; trivial.
               apply In_map_fst_find_id in H. destruct H. 
               rewrite find_id_filter_char in H; trivial; simpl in H.
               apply Gfun_of_Fundef in FP. rewrite FP in H. simpl in H; inv H.
               trivial. apply list_norepet_map_fst_filter; trivial.
            ** apply IntIDs_e in H; [destruct H | trivial]. apply Fundef_of_Gfun in H. congruence.
       ++ clear - Heqq1 FP LNRp H n c2.
          (*here's the repetition*)
            remember (find_id i (prog_funct p2)) as q2; destruct q2.
            ** destruct f. symmetry in Heqq2. apply in_or_app; left.
               apply Gfun_of_Fundef in Heqq2. 2: apply c2. apply IntIDs_i in Heqq2; trivial.
               apply In_map_fst_find_id in H. destruct H. 
               rewrite find_id_filter_char in H; trivial; simpl in H.
               apply Gfun_of_Fundef in FP. rewrite FP in H. simpl in H; inv H.
               trivial. apply list_norepet_map_fst_filter; trivial.
            ** apply IntIDs_e in H; [destruct H | trivial]. apply Fundef_of_Gfun in H. congruence.
    * apply G_merge_InDom in H; [ destruct H as [H | [HE H]] | apply (Comp_Externs_LNR c1)].
      ++ left. apply In_map_fst_find_id in H. destruct H. apply (Comp_E_in_G_find c1) in H. apply find_id_In_map_fst in H; trivial. apply (Comp_Externs_LNR c1).
      ++ right. split; [ intros N | apply Comp_E_in_G; trivial ].
         apply (list_disjoint_notin  _ Externs2_Hyp H). apply (Comp_G_dom c1) in N. apply in_app_or in N; destruct N; [ trivial | contradiction].
  - specialize (FP i). hnf in FP. 
    apply G_merge_InDom in H; [ destruct H as [H | [HE H]] | apply (Comp_G_LNR c1)].
    * apply (Comp_G_dom c1) in H.  apply in_app_or in H; apply in_or_app; destruct H.
      ++ left. apply In_map_fst_find_id in H; [ destruct H as [fd Hfd] | trivial].
         clear - c1 FP Hfd LNRp. 
         rewrite find_id_filter_char in Hfd; [ simpl in Hfd | apply c1].
         remember (find_id i (prog_defs p1)) as q; symmetry in Heqq; destruct q; [ | discriminate].
         destruct g; [ simpl in Hfd | discriminate].
         destruct f; inv Hfd. apply Fundef_of_Gfun in Heqq. rewrite Heqq in FP.
         apply Gfun_of_Fundef in FP; trivial.
         apply IntIDs_i in FP; trivial.
      ++ right. apply G_merge_InDom. apply (Comp_Externs_LNR c1). left; trivial.
    * apply in_or_app. apply Comp_G_elim in H. destruct H as [[HE2 EXT] | [HE2 [INT [f FI]]]].
      ++ right. apply G_merge_InDom.  apply (Comp_Externs_LNR c1). 
         right; split; trivial. intros N. apply HE. apply Comp_E_in_G. apply N.
      ++ rewrite (Fundef_of_Gfun FI) in FP.
         remember (find_id i (prog_funct p1)) as w1; symmetry in Heqw1; destruct w1.
         { left. clear - FP LNRp.
           destruct f0; apply Gfun_of_Fundef in FP; trivial;
                        apply IntIDs_i in FP; trivial. }
         left. clear - FP LNRp.
               apply Gfun_of_Fundef in FP; trivial;
               apply IntIDs_i in FP; trivial.

+ subst G E; intros. specialize (FP i); hnf in FP.
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
      apply (Comp_LNR_Interns c2).
  - specialize (Comp_E_in_G_find c2 _ _ Phi); intros. apply G_merge_find_id_NoneSome; trivial.
      remember (find_id i (Comp_G c1)) as u; symmetry in Hequ; destruct u as [psi1 |]; trivial.
      apply find_id_In_map_fst in Hequ. apply Comp_G_elim in Hequ. destruct Hequ as [[HH _] | [_ [? ]]].
      apply find_id_None_iff in Heqq1. contradiction. 
      apply In_map_fst_find_id in H1. destruct H1. rewrite(list_disjoint_map_fst_find_id1 Externs2_Hyp _ _ Phi) in H1. inv H1.
      apply (Comp_LNR_Interns c1).
  - apply (Comp_Externs_LNR c2).
+ (*SF*) subst G. intros. clear Condition1 Condition2 ImportsDef.
  assert (HCi := HC i).
  specialize (FP i). hnf in FP. specialize (FundefsMatch i).
  apply G_merge_find_id_Some in H0. 2: apply (Comp_G_LNR c2).
  remember (find_id i (Comp_G c1)) as q1; symmetry in Heqq1; destruct q1 as [phi1 |].
  - subst phi; 
     clear - c1 c2 HCi LNR4_V1 LNR4_V2 HV1 HV2 Heqq1 JUST1 JUST2 CS1 CS2 LNRp (*Ge1_FS Ge2_FS Ge1_FFP Ge2_FFPGe1 Ge2*) H 
            SUBSUME1 SUBSUME2 TypesOfFunspecs1 TypesOfFunspecs2 (*HContexts*)
            Externs1_Hyp Externs2_Hyp FP FundefsMatch.
    exploit (Comp_G_in_Fundefs' c1). apply Heqq1. intros [fd1 FD1].
    specialize (JUST1 _ _ _ FD1 Heqq1). 
    specialize (SF_subsumespec JUST1 _ V SUBSUME1 HV1 (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V1) (Comp_ctx_LNR c1)); clear JUST1 SUBSUME1; intros SF1.
    remember (find_id i (Comp_G c2)) as q2; symmetry in Heqq2; destruct q2 as [phi2 |].
    * exploit (Comp_G_in_Fundefs' c2). apply Heqq2. intros [fd2 FD2].
      specialize (JUST2 _ _ _ FD2 Heqq2).
      specialize (SF_subsumespec JUST2 _ V SUBSUME2 HV2 (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V2) (Comp_ctx_LNR c2)); clear JUST2 SUBSUME2; intros SF2.
      rewrite FD1, FD2, H in *. specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl.
      destruct fd1; destruct fd2.
      ++ (*Internal/Internal*)
         inv FundefsMatch. inv FP.
         assert (BI : binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2))).
         { apply merge_specs_succeed. apply HCi; auto.
           apply InternalInfo_cc in SF1. rewrite <- SF1.
           apply InternalInfo_cc in SF2. trivial. }
         simpl.
         eapply internalInfo_binary_intersection; [ | | apply BI].
         -- apply (InternalInfo_envs_sub CS1 (Genv.globalenv p1)); [ apply SF1 | clear - LNRp H(*FP*)].
            apply Gfun_of_Fundef in H. 2: apply LNRp.
            apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
         -- apply (InternalInfo_envs_sub CS2 (Genv.globalenv p2)); [ apply SF2 | clear - LNRp H(*FP*)].
            apply Gfun_of_Fundef in H. 2: apply LNRp.
            apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
      ++ (*InternalExternal*) 
         clear - FP FundefsMatch Externs2_Hyp FD1 FD2 Heqq1 Heqq2.
         apply find_id_In_map_fst in Heqq2. apply Comp_G_elim in Heqq2. destruct Heqq2 as [[? ?]|  [? ?]].
         -- elim (list_disjoint_notin i Externs2_Hyp H). clear - FD1 c1. 
            apply Gfun_of_Fundef in FD1. apply IntIDs_i in FD1; trivial. apply c1.
         -- destruct H0 as [? [? ?]]. apply Gfun_of_Fundef in FD2. congruence. apply c2.
      ++ (*ExternalInternal*)
         clear - FP FundefsMatch Externs1_Hyp FD1 FD2 Heqq1 Heqq2.
         apply find_id_In_map_fst in Heqq1. apply Comp_G_elim in Heqq1. destruct Heqq1 as [[? ?]|  [? ?]].
         -- elim (list_disjoint_notin i Externs1_Hyp H). clear - FD2 c2.
            apply Gfun_of_Fundef in FD2. apply IntIDs_i in FD2; trivial. apply c2.
         -- destruct H0 as [? [? ?]]. apply Gfun_of_Fundef in FD1. congruence. apply c1.
      ++ (*ExternalExternal*)
         rewrite FP in H. inv H. inv FundefsMatch. inv FP.
         assert (BI : binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2))).
         { apply merge_specs_succeed. apply HCi; auto.
           apply ExternalInfo_cc in SF1. rewrite <- SF1. 
           apply ExternalInfo_cc in SF2. trivial. }
         eapply (externalInfo_binary_intersection); [ | | apply BI].
         -- eapply ExternalInfo_envs_sub; [ apply SF1 | clear - LNRp H1 ].
            apply Gfun_of_Fundef in H1. 2: apply LNRp.
            apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
         -- eapply ExternalInfo_envs_sub; [ apply SF2 | clear - LNRp H1 ].
            apply Gfun_of_Fundef in H1. 2: apply LNRp.
            apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
    * (*i in G1 but not in G2*)
      apply find_id_In_map_fst in Heqq1. apply Comp_G_elim in Heqq1. 
      rewrite FD1 in *. destruct Heqq1 as [[HE EF1] | [HE [INT1 IF1]]].
      ++ destruct EF1 as [ef [tys [rt [cc EF1]]]].
         apply Gfun_of_Fundef in FD1; [ rewrite FD1 in *; inv EF1 | apply c1].
         remember (find_id i (prog_funct p2)) as w2; symmetry in Heqw2; destruct w2.
         -- destruct f.
            ** clear - c2 HE Externs1_Hyp Heqw2. elim (list_disjoint_notin i Externs1_Hyp HE).
               apply Gfun_of_Fundef in Heqw2. apply IntIDs_i in Heqw2; trivial. apply c2.
            ** specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch.
               rewrite FP in H. inv H. simpl.
               eapply ExternalInfo_envs_sub; [ apply SF1 | clear - LNRp FP].
               apply Gfun_of_Fundef in FP. 2: apply LNRp.
               apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption. (*
               eapply ExternalInfo_envs_sub; [ intros; apply Ge1; eassumption | apply JUST1].*)
         -- clear FundefsMatch. rewrite FP in H. inv H. simpl.
               eapply ExternalInfo_envs_sub; [ apply SF1 | clear - LNRp FP].
               apply Gfun_of_Fundef in FP. 2: apply LNRp.
               apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
            (*eapply ExternalInfo_envs_sub; [ intros; apply Ge1; eassumption | apply JUST1].*)
      ++ destruct IF1 as [f IF1]. apply Gfun_of_Fundef in FD1; [ rewrite FD1 in IF1; inv IF1 | apply c1].
         remember (find_id i (prog_funct p2)) as w2; symmetry in Heqw2; destruct w2.
         -- destruct f0.
            ** specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch. 
               rewrite FP in H. inv H. 
               apply (InternalInfo_envs_sub CS1 (Genv.globalenv p1)); [ apply SF1 | clear - LNRp FP].
               apply Gfun_of_Fundef in FP. 2: apply LNRp.
               apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
            ** specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. 
               destruct FundefsMatch as [SIGs [psi2 PSI2]].
               rewrite FP in H. inv H. simpl.
               apply (InternalInfo_envs_sub CS1 (Genv.globalenv p1)); [ apply SF1 | clear - LNRp FP].
               apply Gfun_of_Fundef in FP. 2: apply LNRp.
               apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
          -- clear FundefsMatch Heqw2.
             rewrite FP in H. inv H. simpl. 
             apply (InternalInfo_envs_sub CS1 (Genv.globalenv p1)); [ apply SF1 | clear - LNRp FP].
             apply Gfun_of_Fundef in FP. 2: apply LNRp.
             apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.

   - (*i in G2 but not in G1 -- symmetric*) 
      specialize (JUST2 i phi). specialize (JUST1 i). rewrite <- H0 in JUST2.
      apply find_id_In_map_fst in H0. apply Comp_G_elim in H0.
      destruct H0 as [[HE EF2] | [HE [INT2 IF2]]].
      ++ destruct EF2 as [ef [tys [rt [cc EF2]]]]. apply Fundef_of_Gfun in EF2. specialize (JUST2 _ EF2 (eq_refl _)).
         remember (find_id i (prog_funct p1)) as w1; symmetry in Heqw1; destruct w1.
         -- destruct f.
            ** clear - c1 HE Externs2_Hyp Heqw1. elim (list_disjoint_notin i Externs2_Hyp HE). 
               apply Gfun_of_Fundef in Heqw1. apply IntIDs_i in Heqw1; trivial. apply c1.
            ** rewrite EF2 in FundefsMatch, FP. 
               specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch.
               rewrite FP in H. inv H. simpl.
               (*eapply ExternalInfo_envs_sub; [ intros; apply Ge2; eassumption | apply JUST2].*)
               eapply ExternalInfo_envs_sub; [ apply JUST2 | clear - LNRp FP].
               apply Gfun_of_Fundef in FP. 2: apply LNRp.
               apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.

         -- clear FundefsMatch. rewrite EF2 in FP. rewrite FP in H. inv H. simpl.
            (*eapply ExternalInfo_envs_sub; [ intros; apply Ge2; eassumption | apply JUST2].*)
               eapply ExternalInfo_envs_sub; [ apply JUST2 | clear - LNRp FP].
               apply Gfun_of_Fundef in FP. 2: apply LNRp.
               apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
      ++ destruct IF2 as [f IF2]. apply Fundef_of_Gfun in IF2. rewrite IF2 in *.
         specialize (JUST2 _ (eq_refl _) (eq_refl _)).
         specialize (SF_subsumespec JUST2 _ V SUBSUME2 HV2 (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V2) (Comp_ctx_LNR c2)); clear JUST2 SUBSUME2; intros SF2.
  
         remember (find_id i (prog_funct p1)) as w1; symmetry in Heqw1; destruct w1.
         -- destruct f0.
            ** specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch.
               rewrite FP in H. inv H.
               clear JUST1.
               apply (InternalInfo_envs_sub CS2 (Genv.globalenv p2)); [ apply SF2 | clear - LNRp FP].
               apply Gfun_of_Fundef in FP. 2: apply LNRp.
               apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption. 
            ** specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. 
               destruct FundefsMatch as [SIGs [psi2 PSI2]].
               rewrite FP in H. inv H. simpl.
               apply (InternalInfo_envs_sub CS2 (Genv.globalenv p2)); [ apply SF2 | clear - LNRp FP].
                    apply Gfun_of_Fundef in FP. 2: apply LNRp.
                    apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.
          -- clear FundefsMatch Heqw1.
             rewrite FP in H. inv H. simpl.
             apply (InternalInfo_envs_sub CS2 (Genv.globalenv p2)); [ apply SF2 | clear - LNRp FP].
                    apply Gfun_of_Fundef in FP. 2: apply LNRp.
                    apply semax_prog.find_funct_ptr_exists. apply LNRp. eapply find_id_e; eassumption.

+ (*TODO: clean up this proof*)
  intros i phi Hi. subst Exports G.
  assert (HCi := HC i).
  specialize (G_merge_find_id_Some Hi (Comp_Exports_LNR c2)); clear Hi; intros Hi.
  specialize (FP i). hnf in FP.
  remember (find_id i (Comp_G c1)) as u1; symmetry in Hequ1; destruct u1 as [phi1 |].
  - remember (find_id i (Comp_G c2)) as u2; symmetry in Hequ2; destruct u2 as [phi2 |]. 
    * (*assert (SigsPhi: funsigs_match (funsig_of_funspec phi1) (funsig_of_funspec phi2) = true).*)
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

         (*assert (SigsPsi: funsigs_match (funsig_of_funspec psi1) (funsig_of_funspec psi2) = true).*)
         assert (SigsPsi: typesig_of_funspec psi1 =typesig_of_funspec psi2).
         { clear - SigsPhi TAU1 TAU2. destruct tau1; destruct tau2.
           destruct psi1; destruct TAU1 as [AA1 _].
           destruct psi2; destruct TAU2 as [AA2 _]. simpl in *.
           (*rewrite funsigs_match_symm in AA1. 
           eapply funsigs_match_trans; [ apply AA1 |].
           eapply funsigs_match_trans; eassumption.*) destruct AA1; destruct AA2; subst; trivial. }
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
         (*apply funspec_sub_funsigs_match in PSI. apply funsigs_match_LNR2 in PSI.*)
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
(*+ intros. remember (find_id i Imports) as q; destruct q; [symmetry in Heqq; simpl | simpl; trivial].
  clear - Heqq ImportsDef c1 c2. subst. apply find_id_app in Heqq.
  destruct Heqq as [H | H].
  - apply find_id_filter_Some in H; [ destruct H as [? _] | apply (Comp_Imports_LNR c1)].
    apply (Imports_paramsLNR' c1 _ _ H).
  - apply find_id_filter_Some in H; [ destruct H as [? _] | apply (Comp_Imports_LNR c2)].
    apply (Imports_paramsLNR' c2 _ _ H). *)
+ clear - c1 c2 HV1 HV2 V_LNR domV V HVardefs1 HVardefs2 VD1 VD2 VD LNR_V1 LNR_V2 DisjointVarspecs; intros.
(*
  (*rewrite <- (Comp_MkInitPred c1 gv), <- (Comp_MkInitPred c2 gv).
  apply InitGPred_join; trivial.*)
  eapply derives_trans with ((GP1 gv * TT) *(GP2 gv * TT))%logic; [ eapply derives_trans | cancel].
  2: apply sepcon_derives; [ apply (Comp_MkInitPred c1 gv) | apply (Comp_MkInitPred c2 gv)].
  clear cs1 cs2 c1 c2 E1 Imports1 Exports1 G1 E2 Imports2 Exports2 G2.
  unfold Vardefs in *.
  rewrite (InitGPred_join _ _ _ VD1 VD2 VD); trivial.*)
  eapply derives_trans. 
  2: apply sepcon_derives; [ apply (Comp_MkInitPred c1 gv) | apply (Comp_MkInitPred c2 gv)].
  clear cs1 cs2 c1 c2 E1 Imports1 Exports1 G1 E2 Imports2 Exports2 G2.
  unfold Vardefs in *.
  rewrite (InitGPred_join _ _ _ VD1 VD2 VD); trivial.
Qed.

End ComponentJoin.

Section VSUJoin.

Variable Espec: OracleKind.
Variable V1 V2 V: varspecs.
Variable cs1 cs2 cs: compspecs. 
Variable E1 Imports1 Exports1 E2 Imports2 Exports2 E Imports Exports: funspecs.
Variable p1 p2 p: Clight.program.
Variable GP1 GP2: globals -> mpred.
Variable vsu1: @VSU Espec V1 cs1 E1 Imports1 p1 Exports1 GP1.
Variable vsu2: @VSU Espec V2 cs2 E2 Imports2 p2 Exports2 GP2.

Variable DisjointVarspecs: list_disjoint (map fst V1) (map fst V2).
Variable HV1p1: list_disjoint (map fst V1) (map fst (prog_funct p1)).
Variable HV1p2: list_disjoint (map fst V1) (map fst (prog_funct p2)).
Variable HV2p1: list_disjoint (map fst V2) (map fst (prog_funct p1)).
Variable HV2p2: list_disjoint (map fst V2) (map fst (prog_funct p2)).
Variable LNR_V1: list_norepet (map fst V1).
Variable LNR_V2: list_norepet (map fst V2).
Variable CS1: cspecs_sub cs1 cs.
Variable CS2: cspecs_sub cs2 cs.

Variable HV1: forall i phi, find_id i V1 = Some phi -> find_id i V = Some phi.
Variable HV2: forall i phi, find_id i V2 = Some phi -> find_id i V = Some phi.

Variable FundefsMatch: Fundefs_match p1 p2 Imports1 Imports2.

Variable FP: forall i, Functions_preserved p1 p2 p i.

(********************Assumptions involving E1 and E2  ********)

Variable Externs1_Hyp: list_disjoint (map fst E1) (IntIDs p2).
Variable Externs2_Hyp: list_disjoint (map fst E2) (IntIDs p1).

Variable ExternsHyp: E = G_merge E1 E2. 

(************************************************************)

(*one could try to weaken this hypothesis by weakening the second condition to In i (IntIDs p1),
  so that it is possible to delay resolving the spec for an extern in case several modules prove (mergaable but different) specs for it. The present cluase forces one to use match with the first spec one finds*)
Variable SC1: forall i phiI, find_id i Imports2 = Some phiI -> In i (map fst E1 ++ IntIDs p1) ->
              exists phiE, find_id i Exports1 = Some phiE /\ funspec_sub phiE phiI.

(*same comment here*)
Variable SC2: forall i phiI, find_id i Imports1 = Some phiI -> In i (map fst E2 ++ IntIDs p2) ->
                          exists phiE, find_id i Exports2 = Some phiE /\ funspec_sub phiE phiI.

Variable HImports: forall i phi1 phi2, find_id i Imports1 = Some phi1 -> find_id i Imports2 = Some phi2 -> phi1=phi2.

Variable ImportsDef: Imports = 
                     filter (fun x => negb (in_dec ident_eq (fst x) (map fst E2 ++ IntIDs p2))) Imports1 ++
                     filter (fun x => negb (in_dec ident_eq (fst x) (map fst E1 ++ IntIDs p1 ++ map fst Imports1))) Imports2.

Variable ExportsDef: Exports = G_merge Exports1 Exports2.

Variable LNRp: list_norepet (map fst (prog_defs p)).
Variable V_LNR: list_norepet (map fst V).
Variable domV: forall i, In i (map fst V) -> In i (map fst V1) \/ In i (map fst V2).

Variable VD1: map fst (Vardefs p1) = map fst V1.
Variable VD2: map fst (Vardefs p2) = map fst V2.
Variable VD: map fst (Vardefs p) = map fst V.

Variable HVardefs1: forall i d, find_id i (Vardefs p1) = Some d -> find_id i (Vardefs p) = Some d.
Variable HVardefs2: forall i d, find_id i (Vardefs p2) = Some d -> find_id i (Vardefs p) = Some d.

Lemma VSUJoin: @VSU Espec (*(V1++V2)*)V cs E Imports p Exports (fun gv => GP1 gv * GP2 gv)%logic.
Proof.
  destruct vsu1 as [G1 c1]. destruct vsu2 as [G2 c2].
  exists (G_merge (Comp_G c1) (Comp_G c2)).
  eapply ComponentJoin; trivial.
Qed.

End VSUJoin.

Lemma SF_ctx_subsumption {Espec cs} V G ge i fd phi (HSF:  @SF Espec cs V ge G i fd phi)
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

Lemma SF_ctx_extensional {Espec cs} V G ge i fd phi (HSF:  @SF Espec cs V ge G i fd phi)
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

Record CanonicalComponent {Espec V cs} Externs Imports p Exports GP G:= {
  CC_component :> @Component Espec V(*(mk_varspecs' p)*) cs(*make _compspecs p)*) Externs Imports p Exports GP G;
  CC_canonical: map fst (Comp_G CC_component) = 
                map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ map fst Externs))
                        (prog_defs p))
}.

Lemma CanonicalComponent_entail {Espec V cs E Imp p Exp G} GP1 GP2 : 
      @CanonicalComponent Espec V cs E Imp p Exp GP1 G -> (forall gv, GP1 gv |-- GP2 gv) -> 
      @CanonicalComponent Espec V cs E Imp p Exp GP2 G.
Proof.
  intros. destruct H as [C X]. 
  apply (Build_CanonicalComponent _ _ _ _ _ _ _ _ _ (Comp_entail C _ H0) X).
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
(*
Lemma C_to_CC {Espec V cs Ext Imp p Exp} (c: @Component Espec V cs Ext Imp p Exp):
      @CanonicalComponent Espec V cs Ext Imp p Exp.
Proof.
  remember (order (Comp_G c) 
                  (map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ (map fst Ext))) (prog_defs p)))) as Gopt.
  destruct Gopt as [G |]; symmetry in HeqGopt.
+ specialize (LNR_Internals_Externs c); intros LNR_IEc.
  assert (X6: forall i : ident, In i (IntIDs p ++ map fst Ext) <-> In i (map fst G)).
  { intros. rewrite <- (order_dom HeqGopt).
    remember (prog_defs p) as l. remember (IntIDs p ++ map fst Ext) as l'.
    assert (forall j, In j l' -> In j (map fst l)).
    { subst. clear -c. intros. apply c in H. destruct (Comp_G_in_progdefs c j H).
      apply find_id_In_map_fst in H0; trivial. }
    clear - H.
    split; intros. 
    + specialize (H _ H0). apply in_map_iff in H. destruct H as [[j d] [J HJ]]; simpl in *; subst.
      apply in_map_iff. exists (i,d); simpl; split; trivial. apply filter_In; simpl. split; trivial.
      destruct (in_dec ident_eq i l'); trivial. contradiction.
    + apply in_map_iff in H0. destruct H0 as [[j d] [J HJ]]; simpl in *; subst.
      apply filter_In in HJ; simpl in HJ; destruct HJ. 
      destruct (in_dec ident_eq i l'); trivial. discriminate. }
  assert (X7: list_norepet (map fst G)).
  { rewrite <- (order_dom HeqGopt). apply list_norepet_map_fst_filter. apply c. }
  assert (Y: forall i, find_id i (Comp_G c) = find_id i G).
  { clear - HeqGopt X6. apply (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply c.
    intros. rewrite (order_dom HeqGopt). apply X6. apply c. trivial. }
  assert (X8: forall i, In i (map fst Ext) -> find_id i Ext = find_id i G).
  { intros. rewrite (Comp_G_E c _ H); trivial. }

  assert (X1: forall i, In i (map fst Imp) ->
      exists
        (f : external_function) (ts : typelist) (t : type) (cc : calling_convention),
        find_id i (prog_defs p) = Some (Gfun (External f ts t cc))) by apply c.

  assert (X2: list_norepet (map fst (prog_defs p))) by apply c.
  assert (X3: list_norepet (map fst (Ext ++ Imp))) by apply c.

  assert (X4: list_norepet (map fst Exp)) by apply c.
  assert (X5: forall i, In i (map fst Ext) -> exists f ts t cc,
    find_id i (prog_defs p) = Some (Gfun (External f ts t cc))) by apply c.

  assert (X11: forall i : ident, params_LNR (find_id i Imp)).
  { clear -c. intros j.
    remember (find_id j Imp) as q; destruct q; simpl; [symmetry in Heqq | trivial].
    specialize (Imports_paramsLNR' c j); rewrite Heqq.
    intros X; apply X; trivial. }
  assert (X9: forall i phi fd,
    find_id i (prog_funct p) = Some fd -> find_id i G = Some phi -> 
   @SF Espec cs V (Genv.globalenv p) (Imp ++ G) i fd phi).
  { intros.
    eapply SF_ctx_extensional. 
    + rewrite <- Y in H0; apply (Comp_G_justified c _ phi _ H H0).
    + apply Comp_ctx_LNR.
    + clear H H0. intros j. remember (find_id j (Imp ++ Comp_G c)) as q; destruct q; simpl; [symmetry in Heqq | trivial].
      rewrite find_id_app_char in Heqq. specialize (X11 j).
      destruct (find_id j Imp).
      - inv Heqq; apply X11.
      - apply (Comp_G_paramsLNR' c) in Heqq; trivial.
    + intros j. rewrite 2 find_id_app_char, Y; trivial. }

  assert (X10: forall i phi, find_id i Exp = Some phi -> 
          exists phi', find_id i G = Some phi' /\ funspec_sub phi' phi).
  { intros. destruct (Comp_G_Exports c _ _ H) as [phi' [Phi' Sub]].
    exists phi'; split; trivial. rewrite <- (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply c.
    intros. rewrite (order_dom HeqGopt). apply X6. apply c. trivial. }

  remember (@Build_Component Espec V cs Ext Imp p Exp X1 X2 X3 X4 X5 G X6 X7 X8 X9 X10 X11) as cc.

  apply Build_CanonicalComponent with cc.
  subst cc; simpl. symmetry; apply (order_dom HeqGopt).
+ apply order_i' in HeqGopt. contradiction. apply c.
  clear - c. intros.
  apply Comp_G_dom. apply in_map_iff in H. destruct H as [[j d] [J HJ]]. simpl in J; subst.
  apply filter_In in HJ; simpl in HJ; destruct HJ.
  destruct (in_dec ident_eq i (IntIDs p ++ map fst Ext)). trivial. inv H0.
Qed.*)

Record CanonicalComponent_M {Espec V cs} Externs Imports p Exports GP G:= {
  CCM_G: funspecs;
  CCM_component :> @CanonicalComponent Espec V cs Externs Imports p Exports GP CCM_G;
  CCM_main: find_id (prog_main p) CCM_G = find_id (prog_main p) G
}.
Lemma Comp_to_CanComp {Espec V cs Ext Imp p Exp GP G} (C: @Component Espec V cs Ext Imp p Exp GP G):
      @CanonicalComponent_M Espec V cs Ext Imp p Exp GP G.
Proof.
  assert (HG: G = Comp_G C). reflexivity.
  remember (order (Comp_G C) 
                  (map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ (map fst Ext))) (prog_defs p)))) as Gopt.
  destruct Gopt as [GG |]; symmetry in HeqGopt.
+ specialize (LNR_Internals_Externs C); intros LNR_IEc.
  assert (X6: forall i : ident, In i (IntIDs p ++ map fst Ext) <-> In i (map fst GG)).
  { intros. rewrite <- (order_dom HeqGopt).
    remember (prog_defs p) as l. remember (IntIDs p ++ map fst Ext) as l'.
    assert (forall j, In j l' -> In j (map fst l)).
    { subst. clear -C. intros. apply C in H. destruct (Comp_G_in_progdefs C j H).
      apply find_id_In_map_fst in H0; trivial. }
    clear - H.
    split; intros. 
    + specialize (H _ H0). apply in_map_iff in H. destruct H as [[j d] [J HJ]]; simpl in *; subst.
      apply in_map_iff. exists (i,d); simpl; split; trivial. apply filter_In; simpl. split; trivial.
      destruct (in_dec ident_eq i l'); trivial. contradiction.
    + apply in_map_iff in H0. destruct H0 as [[j d] [J HJ]]; simpl in *; subst.
      apply filter_In in HJ; simpl in HJ; destruct HJ. 
      destruct (in_dec ident_eq i l'); trivial. discriminate. }
  assert (X7: list_norepet (map fst GG)).
  { rewrite <- (order_dom HeqGopt). apply list_norepet_map_fst_filter. apply C. }
  assert (Y: forall i, find_id i (Comp_G C) = find_id i GG).
  { clear - HeqGopt X6. apply (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply C.
    intros. rewrite (order_dom HeqGopt). apply X6. apply C. trivial. }
  assert (X8: forall i, In i (map fst Ext) -> find_id i Ext = find_id i GG).
  { intros. rewrite (Comp_G_E C _ H); trivial. }

  assert (X1: forall i, In i (map fst Imp) ->
      exists
        (f : external_function) (ts : typelist) (t : type) (cc : calling_convention),
        find_id i (prog_defs p) = Some (Gfun (External f ts t cc))) by apply C.

  assert (X2: list_norepet (map fst (prog_defs p))) by apply C.
  assert (X3: list_norepet (map fst (Ext ++ Imp))) by apply C.

  assert (X4: list_norepet (map fst Exp)) by apply C.
  assert (X5: forall i, In i (map fst Ext) -> exists f ts t cc,
    find_id i (prog_defs p) = Some (Gfun (External f ts t cc))) by apply C.

  (*assert (X11: forall i : ident, params_LNR (find_id i Imp)).
  { clear -c. intros j.
    remember (find_id j Imp) as q; destruct q; simpl; [symmetry in Heqq | trivial].
    specialize (Imports_paramsLNR' c j); rewrite Heqq.
    intros X; apply X; trivial. }*)
  assert (X9: forall i phi fd,
    find_id i (prog_funct p) = Some fd -> find_id i GG = Some phi -> 
   @SF Espec cs V (Genv.globalenv p) (Imp ++ GG) i fd phi).
  { intros.
    eapply SF_ctx_extensional. 
    + rewrite <- Y in H0; apply (Comp_G_justified C _ phi _ H H0).
    + apply (Comp_ctx_LNR C).
(*    + clear H H0. intros j. unfold Comp_G in *. remember (find_id j (Imp ++ GG)) as q; destruct q; simpl; [symmetry in Heqq | trivial].
      rewrite find_id_app_char in Heqq. (* specialize (X11 j).*)
      destruct (find_id j Imp).
      - inv Heqq. apply X11.
      - apply (Comp_G_paramsLNR' c) in Heqq; trivial.*)
    + intros j. rewrite 2 find_id_app_char, Y; trivial. }

  assert (X10: forall i phi, find_id i Exp = Some phi -> 
          exists phi', find_id i GG = Some phi' /\ funspec_sub phi' phi).
  { intros. destruct (Comp_G_Exports C _ _ H) as [phi' [Phi' Sub]].
    exists phi'; split; trivial. rewrite <- (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply C.
    intros. rewrite (order_dom HeqGopt). apply X6. apply C. trivial. }

  remember (@Build_Component Espec V cs Ext Imp p Exp GP GG X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 (*X11*)
             (*(Comp_InitPred C)*) (Comp_MkInitPred C)) as cc.
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
(*alternative definition but leads to Universe inconsistency (cuplirat: /\  versus InitPred/MkInitPred
Lemma Comp_to_CanComp {Espec V cs Ext Imp p Exp G} (C: @Component Espec V cs Ext Imp p Exp G):
  sigT (fun GG => @CanonicalComponent Espec V cs Ext Imp p Exp GG /\
                  find_id (prog_main p) GG = find_id (prog_main p) G.
Proof.
  assert (HG: G = Comp_G C). reflexivity.
  remember (order (Comp_G C) 
                  (map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ (map fst Ext))) (prog_defs p)))) as Gopt.
  destruct Gopt as [GG |]; symmetry in HeqGopt.
+ specialize (LNR_Internals_Externs C); intros LNR_IEc.
  assert (X6: forall i : ident, In i (IntIDs p ++ map fst Ext) <-> In i (map fst GG)).
  { intros. rewrite <- (order_dom HeqGopt).
    remember (prog_defs p) as l. remember (IntIDs p ++ map fst Ext) as l'.
    assert (forall j, In j l' -> In j (map fst l)).
    { subst. clear -C. intros. apply C in H. destruct (@Comp_G_in_progdefs _ _ _ _ _ _ _ _ C j H).
      apply find_id_In_map_fst in H0; trivial. }
    clear - H.
    split; intros. 
    + specialize (H _ H0). apply in_map_iff in H. destruct H as [[j d] [J HJ]]; simpl in *; subst.
      apply in_map_iff. exists (i,d); simpl; split; trivial. apply filter_In; simpl. split; trivial.
      destruct (in_dec ident_eq i l'); trivial. contradiction.
    + apply in_map_iff in H0. destruct H0 as [[j d] [J HJ]]; simpl in *; subst.
      apply filter_In in HJ; simpl in HJ; destruct HJ. 
      destruct (in_dec ident_eq i l'); trivial. discriminate. }
  assert (X7: list_norepet (map fst GG)).
  { rewrite <- (order_dom HeqGopt). apply list_norepet_map_fst_filter. apply C. }
  assert (Y: forall i, find_id i (Comp_G C) = find_id i GG).
  { clear - HeqGopt X6. apply (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply C.
    intros. rewrite (order_dom HeqGopt). apply X6. apply C. trivial. }
  assert (X8: forall i, In i (map fst Ext) -> find_id i Ext = find_id i GG).
  { intros. rewrite (Comp_G_E C _ H); trivial. }

  assert (X1: forall i, In i (map fst Imp) ->
      exists
        (f : external_function) (ts : typelist) (t : type) (cc : calling_convention),
        find_id i (prog_defs p) = Some (Gfun (External f ts t cc))) by apply C.

  assert (X2: list_norepet (map fst (prog_defs p))) by apply C.
  assert (X3: list_norepet (map fst (Ext ++ Imp))) by apply C.

  assert (X4: list_norepet (map fst Exp)) by apply C.
  assert (X5: forall i, In i (map fst Ext) -> exists f ts t cc,
    find_id i (prog_defs p) = Some (Gfun (External f ts t cc))) by apply C.

  (*assert (X11: forall i : ident, params_LNR (find_id i Imp)).
  { clear -c. intros j.
    remember (find_id j Imp) as q; destruct q; simpl; [symmetry in Heqq | trivial].
    specialize (Imports_paramsLNR' c j); rewrite Heqq.
    intros X; apply X; trivial. }*)
  assert (X9: forall i phi fd,
    find_id i (prog_funct p) = Some fd -> find_id i GG = Some phi -> 
   @SF Espec cs V (Genv.globalenv p) (Imp ++ GG) i fd phi).
  { intros.
    eapply SF_ctx_extensional. 
    + rewrite <- Y in H0; apply (Comp_G_justified C _ phi _ H H0).
    + apply (Comp_ctx_LNR C).
(*    + clear H H0. intros j. unfold Comp_G in *. remember (find_id j (Imp ++ GG)) as q; destruct q; simpl; [symmetry in Heqq | trivial].
      rewrite find_id_app_char in Heqq. (* specialize (X11 j).*)
      destruct (find_id j Imp).
      - inv Heqq. apply X11.
      - apply (Comp_G_paramsLNR' c) in Heqq; trivial.*)
    + intros j. rewrite 2 find_id_app_char, Y; trivial. }

  assert (X10: forall i phi, find_id i Exp = Some phi -> 
          exists phi', find_id i GG = Some phi' /\ funspec_sub phi' phi).
  { intros. destruct (Comp_G_Exports C _ _ H) as [phi' [Phi' Sub]].
    exists phi'; split; trivial. rewrite <- (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply C.
    intros. rewrite (order_dom HeqGopt). apply X6. apply C. trivial. }

  remember (@Build_Component Espec V cs Ext Imp p Exp GG X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 (*X11*)) as cc.
  exists GG.
  split. apply Build_CanonicalComponent with cc.
         subst cc; simpl. symmetry; apply (order_dom HeqGopt).
  rewrite HG, Y; trivial.
+ apply order_i' in HeqGopt. contradiction. apply C. unfold Comp_G in *.
  clear - C. intros.
  apply (Comp_G_dom C). apply in_map_iff in H. destruct H as [[j d] [J HJ]]. simpl in J; subst.
  apply filter_In in HJ; simpl in HJ; destruct HJ.
  destruct (in_dec ident_eq i (IntIDs p ++ map fst Ext)). trivial. inv H0.
Qed.*)

Lemma CanonicalComponent_M_entail {Espec V cs E Imp p Exp G} GP1 GP2 : 
      @CanonicalComponent_M Espec V cs E Imp p Exp GP1 G -> (forall gv, GP1 gv |-- GP2 gv) -> 
      @CanonicalComponent_M Espec V cs E Imp p Exp GP2 G.
Proof.
  intros. eapply Build_CanonicalComponent_M. apply (CanonicalComponent_entail _ _ X H). apply X.
Qed.

Definition CanonicalVSU {Espec V cs} E Imports p Exports GP :=
  sigT (fun G => @CanonicalComponent_M Espec V cs E Imports p Exports GP G).

Lemma VSU_to_CanonicalVSU {Espec V cs Ext Imp p Exp GP} (vsu: @VSU Espec V cs Ext Imp p Exp GP):
      @CanonicalVSU Espec V cs Ext Imp p Exp GP.
Proof.
  destruct vsu as [GG c]. remember (Comp_to_CanComp c) as CC. destruct CC as [G C M]. clear HeqCC.
  (*exists G. econstructor. apply C. trivial.*)
  exists GG. econstructor. apply C. trivial. (*both constructions complete the proof*)
Qed.

Lemma CanonicalVSU_entail {Espec V cs E Imp p Exp} GP1 GP2 : 
      @CanonicalVSU Espec V cs E Imp p Exp GP1 -> (forall gv, GP1 gv |-- GP2 gv) -> 
      @CanonicalVSU Espec V cs E Imp p Exp GP2.
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
  (*destruct H5 as [b [Ha1 H5b]].*) subst.
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

Lemma filter_prog_funct_defs {f g p} 
      (GF: forall i x, f (i,x) = g (i, Gfun x))
      (*(HG: forall i v, g (i, Gvar v) = false):*)
      (HG: forall i v, In (i, Gvar v) (prog_defs p) -> g (i, Gvar v) = false):
      map fst (filter f (prog_funct p)) = map fst (filter g (prog_defs p)).
Proof.
  unfold prog_funct. forget (prog_defs p) as l.
  induction l; simpl. trivial.
  destruct a as [i d]. destruct d; simpl.
  + rewrite GF.
    destruct (g (i, Gfun f0)); simpl;
     rewrite IHl; trivial; intros; apply HG; right; trivial.
  + rewrite IHl, HG; trivial. left; trivial.
    intros; apply HG; right; trivial.
Qed.

Lemma Canonical_semaxfunc {Espec cs V E} p Exp GP G
      (c: @CanonicalComponent Espec V cs E nil p Exp GP G):
   semaxfunc V (Comp_G c) (Genv.globalenv p) 
             (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ map fst E)) 
                     (prog_funct p))
             G.
Proof.
  specialize (Comp_G_justified c); intros. destruct c as [c DOM]; simpl.
  simpl in *.
  assert (LNRp:=Comp_p_LNR c).
  assert (LNRfuncs: list_norepet (map fst (prog_funct p)))
    by (apply initialize.list_norepet_prog_funct'; trivial).
  apply SF_semaxfunc.
+ intros. apply find_id_filter_Some in H0; trivial.
  destruct H0. apply H; trivial.
+ apply list_norepet_map_fst_filter; trivial.
+ unfold Comp_G in *. rewrite DOM; clear DOM H LNRfuncs.
  apply filter_prog_funct_defs; intros; simpl. trivial.
  destruct (in_dec ident_eq i (IntIDs p ++ map fst E)); simpl; trivial. 
  apply find_id_i in H; trivial.
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

Lemma Canonical_semax_func {Espec cs V E p Exp GP G}
      (c: @CanonicalComponent Espec V cs  E nil p Exp GP G)
      (HE: map fst E =
           map fst (filter (fun x  => negb (isInternal (Gfun (snd x)))) (prog_funct p))):
      @semax_func Espec V (Comp_G c) cs (Genv.globalenv p) (prog_funct p) (Comp_G c).
Proof. 
  apply semaxfunc_sound.
  specialize (Canonical_semaxfunc _ _ _ _ c).
  rewrite filter_true; trivial.
  rewrite HE; clear; intros. 
  destruct (in_dec ident_eq (fst i)
    (IntIDs p ++ map fst
       (filter (fun x => negb (isInternal (Gfun (snd x)))) (prog_funct p))) ); simpl; trivial.
  elim n; clear n. destruct i as [i d]; simpl. unfold IntIDs, prog_funct in *.
  forget (prog_defs p) as l. clear p.
  induction l; simpl in *; trivial.
  destruct a as [j a]; simpl in *. destruct a; simpl in *; [|auto].
  destruct f; simpl in *.
  + destruct H; [ inv H; left; trivial | right; auto].
  + destruct H.
    - inv H; simpl. apply in_or_app. right; left; trivial.
    - apply in_or_app. specialize (IHl H); apply in_app_or in IHl.
      destruct IHl; [ left; trivial | right; right; trivial].
Qed.
(*
Lemma CanonicalPre_PROG {Espec cs V E} {ora: OK_ty} p Exp G
      (c: @CanonicalPreComponent Espec V cs E nil p Exp G)
       (HE : map fst E = map fst (filter (fun x => negb (isInternal (Gfun (snd x)))) (prog_funct p)))

      (LNR_Names: compute_list_norepet (prog_defs_names p) = true)
      (ALGN: all_initializers_aligned p)
      (HCS: cenv_cs = prog_comp_env p)
      (HV: match_globvars (prog_vars p) V = true) 
      (Main: exists post, find_id (prog_main p) G = Some (main_spec_ext' p ora post)):
      @semax_prog Espec cs p ora V G.
Proof.
  unfold semax_prog; red. simpl.
assert (augment_funspecs p G = G). ?
rewrite H. destruct Main as [post M]. rewrite M. intuition.
 2: exists post; trivial.
Qed.*)
(*
Lemma Canonical_PROG_ext {Espec cs V E} p Exp
      (c: @CanonicalComponent Espec V cs E nil p Exp)
       (HE : map fst E = map fst (filter (fun x => negb (isInternal (Gfun (snd x)))) (prog_funct p)))

      (LNR_Names: compute_list_norepet (prog_defs_names p) = true)
      (ALGN: all_initializers_aligned p)
      (HCS: cenv_cs = prog_comp_env p)
      (HV: match_globvars (prog_vars p) V = true) ora MainPost
      (Main: find_id (prog_main p) (Comp_G c) = Some (main_spec_ext' p ora MainPost)):
      @semax_prog Espec cs p ora V (Comp_G c).
Proof.
  red. red. rewrite Main. intuition.
  apply  Canonical_semax_func; trivial.
  eexists; reflexivity.
Qed.*)

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
(*
Ltac semax_body_proof_to_SF P :=
  clear; apply SF_internal_sound; eapply _SF_internal;
   [ reflexivity 
   | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
   | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
   | reflexivity 
   | (*LookupID
   | LookupB*)
   | apply P].
*)
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

Ltac mkComponent (*G_internal*) := 
  eapply Build_Component (*with G_internal*);
  [ intros i H; 
    first [ repeat (destruct H; [subst; do 4 eexists; findentry; reflexivity  |]); contradiction
          | (*fail 99 "SC1"*)idtac ]
  | apply compute_list_norepet_e; reflexivity
  | apply compute_list_norepet_e; reflexivity
  | apply compute_list_norepet_e; reflexivity
  | intros i H; first [ solve contradiction | simpl in H];
    repeat (destruct H; [ subst; do 4 eexists; reflexivity |]); try contradiction
  | intros; simpl; split; trivial; try solve [lookup_tac]
  | apply compute_list_norepet_e; reflexivity
  | intros i H; first [ solve contradiction | simpl in H];
    repeat (destruct H; [ subst; reflexivity |]); try contradiction
  | intros i phi fd H H0; simpl in H;
    repeat (if_tac in H; [ inv H; inv H0 | ]; try discriminate)
  | finishComponent
  (*| intros; simpl; 
    repeat (if_tac; simpl; [ apply compute_list_norepet_e; reflexivity | ]); trivial*)
  | intros; first [ solve [apply derives_refl] | solve [reflexivity] | solve [simpl; cancel] | idtac]
  ].

Ltac solve_SF_internal P :=
  clear; apply SF_internal_sound; eapply _SF_internal;
   [  reflexivity 
   | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
   | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
   | reflexivity
   | apply P
   | eexists; split; [ LookupID | LookupB ]
   ].

(*slihgtly slower*)
Ltac solve_SF_external_with_intuition B :=
   first [simpl; split; intuition; [ try solve [entailer!] | try apply B | eexists; split; cbv; reflexivity ] | idtac].

(*Slightly faster*)
Ltac solve_SF_external B :=
  first [ split3; [ reflexivity 
                     | reflexivity 
                     | split3; [ reflexivity
                               | reflexivity
                               | split3; [ left; trivial
                                         | intros ? ? ? ?; try solve [entailer!](*; normalize*)
                                         | split; [ try apply B
                                                  | eexists; split; cbv; reflexivity ]] ] ]
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
  FDM_entries (prog_funct p1) (prog_funct p2) = Some entries ->
  Forall (check_FDM_entry Imports1 Imports2) entries ->
  Fundefs_match p1 p2 Imports1 Imports2.
Proof. red. forget (prog_funct p1) as funs1. forget (prog_funct p2) as funs2.
  clear p1 p2. generalize dependent funs2. induction funs1; simpl; intros. discriminate.
  destruct a as [j fdj].
  remember (find_id j funs2) as J2; destruct J2; [ symmetry in HeqJ2 | ].
  - remember (FDM_entries funs1 funs2) as entriesTL; destruct entriesTL; [inv H | discriminate].
    symmetry in HeqentriesTL. inv H0. (*specialize (IHfuns1 _ _ HeqentriesTL H5).*)
    if_tac in H1; subst.
    + (*i=j*) 
      clear IHfuns1. inv H1. rewrite HeqJ2 in H2; inv H2. simpl in H4.
      destruct fd1; destruct fd2; trivial.
      * destruct (find_id j Imports2); [ split; [ | exists f0]; trivial | contradiction].
      * destruct (find_id j Imports1); [ split; [ | exists f0]; trivial | contradiction].
    + eapply IHfuns1; eassumption.
  - if_tac in H1; subst. congruence. eapply IHfuns1; eassumption. 
Qed.

Lemma FDM_complete {p1 p2 Imports1 Imports2}
  (FM: Fundefs_match p1 p2 Imports1 Imports2) 
  (LNRp1:list_norepet (map fst (prog_defs p1))):
  exists entries,
  FDM_entries (prog_funct p1) (prog_funct p2) = Some entries /\
  Forall (check_FDM_entry Imports1 Imports2) entries.
Proof. red in FM. remember (prog_funct p1) as funs1.
  assert (LNR1: list_norepet (map fst funs1)).
  { subst. apply initialize.list_norepet_prog_funct'; trivial. }
  forget (prog_funct p2) as funs2.
  clear Heqfuns1 LNRp1 p1 p2. generalize dependent funs2.
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

Lemma FP_entries_sound {p1 p2 p entries1 entries2}:
  let funs1 := (prog_funct p1) in
  let funs2 := (prog_funct p2) in
  let funs := (prog_funct p) in
  FP_entries1 funs1 funs2 funs = Some entries1 ->
  Forall (fun x => fst x = snd x) entries1 ->
  FP_entries2 (filter (fun x => (negb (in_dec peq (fst x) (map fst funs1)))) funs2)  funs = Some entries2 ->
  Forall (fun x => fst x = snd x) entries2 ->
  FP_entries_inv (map fst funs1) (map fst funs2) (map fst funs) = true ->
  forall i, Functions_preserved p1 p2 p i.
Proof. intros. subst funs1 funs2 funs.
  specialize (FP_entries1_soundA H H0 i). clear H H0.
  specialize (FP_entries2_soundA' H1 H2 i). clear H1 H2.
  specialize (FP_entries_inv_sound H3 i). clear H3. intros.
  red. unfold Functions_preserved_A in *.
  remember (find_id i (prog_funct p1)) as q1; destruct q1. 1: eapply H1; reflexivity. symmetry in Heqq1.
  remember (find_id i (prog_funct p2)) as q2; destruct q2. 1: eapply H0; reflexivity. symmetry in Heqq2.
  apply assoclists.find_id_None_iff in Heqq1. apply assoclists.find_id_None_iff in Heqq2.
  destruct (in_dec peq i (map fst (prog_funct p))).
  + destruct (H i0) as [K | K]; contradiction.
  + apply assoclists.find_id_None_iff; trivial.
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
(*
Record SortedComponent {Espec V cs} Externs Imports p Exports G:= {
  SC_component :> @Component Espec V cs Externs Imports p Exports G;
  SC_sorted: (*G = SortFunspec.sort G*) Sorted.LocallySorted
         (fun x x0 : ident * funspec =>
          Datatypes.is_true
            ((fun x1 y : ident * funspec => (fst x1 <=? fst y)%positive) x x0))  G
}.*)
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
(*
Definition SortComponent {Espec V cs Externs Imports p Exports G} 
           (C:@Component Espec V cs Externs Imports p Exports G):
           @SortedComponent Espec V cs Externs Imports p Exports (SortFunspec.sort G).
constructor; [ | apply SortFunspec.Sorted_sort || apply SortFunspec.LocallySorted_sort ].
specialize (Comp_ctx_LNR C); intros DISJ.
(*destruct C;*) unfold Comp_G in DISJ.
constructor; trivial; try apply C; clear - C DISJ.
+ intros. destruct (Comp_G_dom C i).
  split; intros.
  - apply H in H1. clear - C H1.
    destruct (In_map_fst_find_id H1 (Comp_G_LNR C)) as [x Hx].
    apply (@sort_In_map_fst G); trivial. 
  - apply H0. clear - C H1.
    apply sort_In_map_fst; trivial.
+ apply (@sort_LNR G); apply C.
+ intros. rewrite (Comp_G_E C _ H).
  apply sort_find_id; apply C.
+ intros. eapply SF_ctx_extensional.
  - apply (Comp_G_justified C i phi fd). trivial. clear - H0 C.
     rewrite (sort_find_id (Comp_G_LNR C)); trivial.
  - apply DISJ.
  - clear - DISJ C; intros. rewrite 2 find_id_app_char. 
    rewrite (sort_find_id (Comp_G_LNR C)). trivial.
+ intros. destruct (Comp_G_Exports C _ _ E) as [phi' [? ?]].
  exists phi'; split; trivial. clear - H C.
  rewrite <- (sort_find_id (Comp_G_LNR C)). trivial.
Qed.*)

Ltac prove_cspecs_sub := split3; intros ?i; apply sub_option_get;
     repeat (constructor; [ reflexivity |]); constructor.

Ltac solve_entry H H0:=
     inv H; inv H0; first [ solve [ trivial ] | split; [ reflexivity | eexists; reflexivity] ].

Ltac LNR_tac := apply compute_list_norepet_e; reflexivity.

Ltac list_disjoint_tac := (*red; simpl; intros; contradiction.*)
     apply list_norepet_append_inv; LNR_tac.

Ltac ExternsHyp_tac := first [ reflexivity | idtac ].
Ltac SC_tac := simpl; intros ? ? X H;
  repeat (destruct H; [ subst; simpl; simpl in X; try discriminate | ]);
  inv X; first [ eexists; split; [reflexivity | apply funspec_sub_refl] | idtac]; try contradiction.

Ltac HImports_tac := simpl; intros ? ? ? H1 H2;
  repeat (if_tac in H1; subst; simpl in *; try discriminate).

Ltac ImportsDef_tac := first [ reflexivity | idtac ].
Ltac ExportsDef_tac := first [ reflexivity | idtac ].
Ltac domV_tac := cbv; intros; auto.

Ltac FunctionsPreserved_tac :=
  eapply FP_entries_sound;
  [ cbv; reflexivity
  | solve [repeat (constructor; [ reflexivity | ]); constructor]
  | cbv; reflexivity
  | repeat (constructor; [ reflexivity | ]); constructor
  | cbv; reflexivity ].
Ltac FDM_tac := eapply FDM; [ cbv; reflexivity | repeat (constructor; [ cbv; reflexivity | ]); constructor].

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
| FDM_tac
| FunctionsPreserved_tac
| list_disjoint_tac
| list_disjoint_tac
| ExternsHyp_tac
| SC_tac
| SC_tac
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

Lemma VSU_ext {Espec V cs E Imp p Exp GP1 GP2}:
      @VSU Espec V cs E Imp p Exp GP1 -> GP1=GP2 ->
      @VSU Espec V cs E Imp p Exp GP2.
Proof. intros; subst; trivial. Qed.

Ltac VSUMerge VSU1 VSU2 :=
eapply VSU_ext;
[ eapply (VSUJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  VSU1 VSU2);
[ list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| LNR_tac
| LNR_tac
| prove_cspecs_sub
| prove_cspecs_sub
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
| FDM_tac
| FunctionsPreserved_tac
| list_disjoint_tac
| list_disjoint_tac
| ExternsHyp_tac
| SC_tac
| SC_tac
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
]
|
].

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
(*
Definition LinkedProgVSU {Espec V cs} E Imports p Exports :=
  sigT (fun G => @CanonicalComponent Espec V cs E Imports p Exports G /\
          exists post ora, find_id (prog_main p) G = 
           Some (@main_spec_ext' (@OK_ty Espec) p ora post)).*)
Record LinkedProgVSU {Espec V cs} E Imports p Exports GP := {
  LP_G: funspecs;
  LP_C: @CanonicalComponent Espec V cs E Imports p Exports GP LP_G;
  LP_main: exists phi, find_id (prog_main p) LP_G = Some phi /\
                      find_id (prog_main p) Exports = Some phi
}.
(*Alternative def that leads to univ inconsitency snce introduction of CompInitPred:
Definition LinkedProgVSU {Espec V cs} E Imports p Exports :=
  sigT (fun G => @CanonicalComponent Espec V cs E Imports p Exports G /\
          exists phi, find_id (prog_main p) G = Some phi /\
                      find_id (prog_main p) Exports = Some phi)
*)

Lemma LP_VSU_ext {Espec V cs E Imp p Exp GP1 GP2}:
      @LinkedProgVSU Espec V cs E Imp p Exp GP1 -> GP1=GP2 ->
      @LinkedProgVSU Espec V cs E Imp p Exp GP2.
Proof. intros; subst; trivial. Qed.

Lemma LP_VSU_entail {Espec V cs E Imp p Exp} GP1 GP2 : 
      @LinkedProgVSU Espec V cs E Imp p Exp GP1 -> (forall gv, GP1 gv |-- GP2 gv) -> 
      @LinkedProgVSU Espec V cs E Imp p Exp GP2.
Proof.
 intros. destruct X as [G C M].
 apply (Build_LinkedProgVSU _ _ _ _ _ _ _ _ _ (CanonicalComponent_entail _ _ C H) M).
Qed.

Definition G_of_CanonicalVSU {Espec V cs E Imports p Exports GP} (vsu: @CanonicalVSU Espec V cs E Imports p Exports GP): funspecs.
destruct vsu as [G CCM]. (*apply G.*) destruct CCM as [GG CC M]. apply GG. Defined. 

Lemma G_of_CanonicalVSU_char {Espec V cs E Imports p Exports GP} (vsu: @CanonicalVSU Espec V cs E Imports p Exports GP):
     map fst (G_of_CanonicalVSU vsu) = 
                map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ map fst E))
                        (prog_defs p)).
Proof. destruct vsu as [G CCM]. simpl. destruct CCM as [GG CC M].
 destruct CC. unfold Comp_G in *. trivial. Qed.

Lemma G_of_CanoncialVSU_justified {Espec V cs E Imports p Exports GP} (vsu: @CanonicalVSU Espec V cs E Imports p Exports GP):
       forall (i : ident) (phi : funspec) (fd : fundef function),
       initial_world.find_id i (prog_funct p) = Some fd ->
       initial_world.find_id i (G_of_CanonicalVSU vsu) = Some phi -> 
       @SF Espec cs V  (@Genv.globalenv (fundef function) type p) (Imports ++ (G_of_CanonicalVSU vsu)) i fd phi.
Proof. intros. destruct vsu. apply (Comp_G_justified c _ _ _ H H0). Qed.

Lemma LNR_G_of_CanoncialVSU {Espec V cs E Imports p Exports GP} (vsu: @CanonicalVSU Espec V cs E Imports p Exports GP):
      list_norepet (map fst (G_of_CanonicalVSU vsu)).
Proof. intros. destruct vsu. apply (Comp_G_LNR c). Qed.

Lemma LNR_progdefs_progfunct {F} {p: program F}: list_norepet (map fst (prog_defs p)) -> 
      list_norepet (map fst (prog_funct p)).
Proof. apply initialize.list_norepet_prog_funct'. Qed.

Definition ExtIDs (p: Ctypes.program function): list ident := 
  map fst ((filter (fun x => negb (isInternal (snd x)))) (prog_defs p)).
(*
Definition InitPred_of_CanonicalVSU {Espec V cs E Imports p Exports GP} (vsu: @CanonicalVSU Espec V cs E Imports p Exports GP)
           : globals -> mpred.
Proof. apply GP. (* destruct vsu as [G [GG CC M]]. eapply Comp_InitPred. apply CC.*) Defined.

Lemma MkInitPred_of_CanonicalVSU {Espec V cs E Imports p Exports GP} (vsu: @CanonicalVSU Espec V cs E Imports p Exports GP):
      forall gv, InitGPred (Vardefs p) gv = InitPred_of_CanonicalVSU vsu gv.
Proof. intros. destruct vsu as [G [GG CC M]]. simpl. apply (Comp_MkInitPred CC). Qed.*)
(*
Lemma MkInitPred_of_CanonicalVSU {Espec V cs E Imports p Exports GP} (vsu: @CanonicalVSU Espec V cs E Imports p Exports GP):
      forall gv, InitGPred (Vardefs p) gv |-- (GP gv * TT)%logic.
Proof. destruct vsu as [G [GG CC M]]. apply (Comp_MkInitPred CC). Qed.*)
Lemma MkInitPred_of_CanonicalVSU {Espec V cs E Imports p Exports GP} (vsu: @CanonicalVSU Espec V cs E Imports p Exports GP):
      forall gv, InitGPred (Vardefs p) gv |-- GP gv.
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