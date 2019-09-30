Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.initial_world.
Require Import VST.msl.normalize.
Require Import VST.veric.semax_call.
Require Import VST.veric.Clight_initial_world.
Require Import VST.veric.initialize.
Require Import VST.veric.coqlib4.
Require Import Coq.Logic.JMeq.

Require Import Coq.Logic.JMeq.
Require Import VST.veric.ghost_PCM.

Require Import VST.veric.assoclists.
Require Import VST.veric.semax_prog.

Lemma semax_body_binaryintersection {V G cs} f sp1 sp2 phi
  (SB1: @semax_body V G cs f sp1) (SB2: @semax_body V G cs f sp2)
  (BI: binary_intersection (snd sp1) (snd sp2) = Some phi):
  @semax_body V G cs f (fst sp1, phi).
Proof.
  destruct sp1 as [i phi1]. destruct phi1 as [[tys1 rt1] cc1 A1 P1 Q1 P1_ne Q1_ne]. 
  destruct sp2 as [i2 phi2]. destruct phi2 as [[tys2 rt2] cc2 A2 P2 Q2 P2_ne Q2_ne]. 
  destruct phi as [[tys rt] cc A P Q P_ne Q_ne]. simpl in BI.
  if_tac in BI; [ inv H | discriminate]. if_tac in BI; [inv BI | discriminate].
  apply Classical_Prop.EqdepTheory.inj_pair2 in H6.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H5. subst. simpl fst; clear - SB1 SB2.
  destruct SB1 as [X SB1]; destruct SB2 as [_ SB2]; split; [ apply X | simpl in X; intros].
  destruct x as [b Hb]; destruct b; [ apply SB1 | apply SB2].
Qed.

Lemma funsig_of_binary_intersection {phi1 phi2 phi} (BI: binary_intersection phi1 phi2 = Some phi):
      funsig_of_funspec phi = funsig_of_funspec phi1 /\ funsig_of_funspec phi = funsig_of_funspec phi2.
Proof. destruct phi1; destruct phi2; destruct phi; simpl in *. if_tac in BI; [if_tac in BI; inv BI; split; trivial | discriminate].
Qed.

Lemma callconv_of_binary_intersection {phi1 phi2 phi} (BI: binary_intersection phi1 phi2 = Some phi):
      callingconvention_of_funspec phi = callingconvention_of_funspec phi1 /\ 
      callingconvention_of_funspec phi = callingconvention_of_funspec phi2.
Proof. destruct phi1; destruct phi2; destruct phi; simpl in *. if_tac in BI; [if_tac in BI; inv BI; split; trivial | discriminate].
Qed.

Lemma funspectype_of_binary_intersection {phi1 phi2 phi} (BI: binary_intersection phi1 phi2 = Some phi):
      type_of_funspec phi1 = type_of_funspec phi /\ 
      type_of_funspec phi2 = type_of_funspec phi.
Proof. destruct phi1; destruct phi2; destruct phi; simpl in *. if_tac in BI; [if_tac in BI; inv BI; split; trivial | discriminate].
Qed.

Definition semaxfunc_InternalInfo C V G (ge : Genv.t Clight.fundef type) id f phi := 
exists b,
  (id_in_list id (map fst G) && semax_body_params_ok f)%bool = true /\
  Forall (fun it : ident * type => complete_type (@cenv_cs C)(snd it) = true) (fn_vars f) /\
  var_sizes_ok cenv_cs (fn_vars f) /\
  fn_callconv f = callingconvention_of_funspec phi /\
  Genv.find_symbol ge id = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f) /\
  semax_body V G f (id, phi).

Definition semaxfunc_ExternalInfo Espec (ge : Genv.t Clight.fundef type) (id : ident) 
    (ef : external_function) (argsig : typelist) (retsig : type) (cc : calling_convention) phi := 
  match phi with mk_funspec (argsig', retsig') cc' A P Q NEP NEQ => exists ids b,
  retsig = retsig' /\ cc=cc' /\
  ids = map fst argsig' /\
  argsig' = zip_with_tl ids argsig /\
  ef_sig ef = {| sig_args := typlist_of_typelist (type_of_params argsig');
                 sig_res := opttyp_of_type retsig; sig_cc := cc |} /\
  Datatypes.length ids = Datatypes.length (typelist2list argsig) /\
  (forall (gx : genviron) (ts : list Type) x (ret : option val),
   Q ts x (make_ext_rval gx ret) && !! has_opttyp ret (opttyp_of_type retsig) |-- !! tc_option_val retsig ret) /\
  Genv.find_symbol ge id = Some b /\
  Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) /\
  (forall n : nat, semax_external Espec ids ef A P Q n)
  end.

Lemma InternalInfo_subsumption {ge cs V V' F F' i f phi}
  (HVF : forall i, (sub_option (make_tycontext_g V F) ! i) ((make_tycontext_g V' F') ! i))
  (HF : forall i, subsumespec (find_id i F) (find_id i F'))
  (LNRF : list_norepet (map fst F))
  (H : semaxfunc_InternalInfo cs V F ge i f phi):
  semaxfunc_InternalInfo cs V' F' ge i f phi.
Proof.
  destruct H as [b [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 Hb7]]]]]]].
  exists b; repeat split; trivial.
  + apply andb_true_iff in Hb1; destruct Hb1 as [X Y]; rewrite Y, andb_true_r.
    clear - X HF LNRF. apply id_in_list_true_i. apply id_in_list_true in X.
    apply In_map_fst_find_id in X; trivial. destruct X as [phi PHI].
    specialize (HF i); rewrite PHI in HF. destruct HF as [phi' [PHI' SUB]].
    apply find_id_In_map_fst in PHI'; trivial.
  + eapply semax_body_subsumption. eassumption. clear - HF HVF.
    red; simpl; intuition.
    - destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! id); trivial.
    - rewrite 2 make_tycontext_s_find_id; trivial.
    - red; intros; rewrite PTree.gempty; trivial.
Qed.

Lemma InternalInfo_envs_sub {CS CS'} (CSUB: cspecs_sub CS CS') ge ge'
  (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
  V G  i f phi (H : semaxfunc_InternalInfo CS V G ge i f phi):
semaxfunc_InternalInfo CS' V G ge' i f phi.
Proof. 
  destruct H as [b [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 Hb7]]]]]]].
  exists b. repeat split; try assumption.
  - destruct CSUB as [CSE _]. clear - CSE Hb2. induction Hb2; constructor; trivial.
    apply (@complete_type_cenv_sub _ _ CSE _ H).
  - destruct CSUB as [CSE _]. clear - CSE Hb2 Hb3. unfold var_sizes_ok in *.
    induction Hb3; trivial. inv Hb2. constructor. 2: eauto.
    rewrite (@cenv_sub_sizeof _ _ CSE); trivial.
  - specialize (Gfs i); rewrite Hb5 in Gfs; apply Gfs.
  - specialize (Gffp b); rewrite Hb6 in Gffp; apply Gffp.
  - apply (semax_body_cenv_sub CSUB); trivial.
Qed.

Lemma ExternalInfo_envs_sub Espec ge ge'
  (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
    i ef argsig retsig cc phi
  (H : semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi):
semaxfunc_ExternalInfo Espec ge' i ef argsig retsig cc phi.
Proof.
  destruct phi; destruct f. destruct H as [ids [b [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 [Hb7 [Hb8 [Hb9 Hb10]]]]]]]]]]].
  exists ids, b; repeat split; trivial.
  - specialize (Gfs i); rewrite Hb8 in Gfs; apply Gfs.
  - specialize (Gffp b); rewrite Hb9 in Gffp; apply Gffp.
Qed.

Lemma InternalInfo_cc {cs V G ge i f phi} (SF: @semaxfunc_InternalInfo cs V G ge i f phi):
  fn_callconv f = callingconvention_of_funspec phi.
Proof. destruct SF as [b [? [? [? [? [? [? ?]]]]]]]; trivial. Qed.

Lemma ExternalInfo_cc {Espec ge i ef tys rt cc phi} (SF: @semaxfunc_ExternalInfo Espec ge i ef tys rt cc phi):
  cc = callingconvention_of_funspec phi.
Proof. destruct phi. destruct f. destruct SF as [ids [b [? [? _]]]]; subst; trivial. Qed.

Lemma semax_external_binaryintersection {Espec ef A1 P1 Q1 P1ne Q1ne A2 P2 Q2 P2ne Q2ne 
      A P Q P_ne Q_ne sig cc ids n}
  (EXT1: @semax_external Espec ids ef A1 P1 Q1 n)
  (EXT2: @semax_external Espec ids ef A2 P2 Q2 n)
  (BI: binary_intersection (mk_funspec sig cc A1 P1 Q1 P1ne Q1ne) 
                      (mk_funspec sig cc A2 P2 Q2 P2ne Q2ne) =
     Some (mk_funspec sig cc A P Q P_ne Q_ne))
  (IDS: ids = map fst (fst sig)):
  @semax_external Espec ids ef A P Q n.
Proof.
  intros ge ts x.
  simpl in BI. rewrite 2 if_true in BI by trivial. inv BI.
  apply inj_pair2 in H1; subst P. apply inj_pair2 in H2; subst Q.
  destruct x as [bb BB]; destruct bb.
  * apply (EXT1 ge ts BB). 
  * apply (EXT2 ge ts BB).
Qed.

Lemma internalInfo_binary_intersection {cs V G ge i f phi1 phi2 phi}
      (F1_internal : semaxfunc_InternalInfo cs V G ge i f phi1)
      (F2_internal : semaxfunc_InternalInfo cs V G ge i f phi2)
      (BI : binary_intersection phi1 phi2 = Some phi):
   semaxfunc_InternalInfo cs V G ge i f phi.
Proof.
  destruct F1_internal as [b' [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 Hb7]]]]]]].
  destruct F2_internal as [b  [Kb1 [Kb2 [Kb3 [Kb4 [Kb5 [KHb6 Kb7]]]]]]].
  rewrite Hb5 in Kb5; inv Kb5.
  exists b. intuition.
  + apply callconv_of_binary_intersection in BI; destruct BI as [X Y].
    rewrite Hb4, X; trivial.
  + assert (Hi: i = fst (i, phi1)) by reflexivity. rewrite Hi; clear Hi.
    eapply semax_body_binaryintersection; eauto.
Qed.

Lemma externalInfo_binary_intersection {Espec ge i ef argsig retsig cc phi1 phi2 phi}
      (F1_external : semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi1)
      (F2_external : semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi2)
      (BI : binary_intersection phi1 phi2 = Some phi):
  semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi.
Proof.
  destruct (funsig_of_binary_intersection BI) as [SIG1 SIG2].
  destruct (callconv_of_binary_intersection BI) as [CC1 CC2].
  destruct phi. destruct f. simpl in CC1, CC2, SIG1, SIG2. 
  destruct phi1 as [sig1 c1 A1 P1 Q1 P1ne Q1ne]. simpl in SIG1, CC1. subst sig1 c1.
  destruct F1_external as [ids' [b' [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 [Hb7 [Hb8 [Hb9 EXT1]]]]]]]]]]]. subst t c l.
  destruct phi2 as [sig2 c2 A2 P2 Q2 P2ne Q2ne]. simpl in SIG2, CC2. subst sig2 c2.
  destruct F2_external as [ids [b  [_ [_ [Kb3 [_ [_ [_ [Kb7 [Kb8 [_ EXT2]]]]]]]]]]].
  rewrite <- Kb3 in Hb3. subst ids'.
  rewrite Hb8 in Kb8; inv Kb8.

  exists ids, b. repeat split; trivial.
  + simpl in BI. rewrite 2 if_true in BI by trivial. inv BI.
    apply inj_pair2 in H1; subst P. apply inj_pair2 in H2; subst Q.
    intros. destruct x as [bb BB]; destruct bb.
    - apply (Hb7 gx ts BB). 
    - apply (Kb7 gx ts BB).
  + intros n. eapply semax_external_binaryintersection. apply EXT1. apply EXT2. eassumption. trivial.
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

Lemma funspec_sub_cc phi psi: funspec_sub phi psi ->
      callingconvention_of_funspec phi = callingconvention_of_funspec psi.
Proof. destruct phi; destruct psi; simpl. intros [_ [? _]]; trivial. Qed.

Lemma subsumespec_app l1 l2 k1 k2 i
          (L1K1: subsumespec (find_id i l1) (find_id i k1)) 
          (L2K2: subsumespec (find_id i l2) (find_id i k2))
          (D:list_disjoint (map fst l2) (map fst k1)):
      subsumespec (find_id i (l1++l2)) (find_id i (k1++k2)).
Proof.
  red. rewrite ! find_id_app_char. (* specialize (L1K1 i). specialize (L2K2 i).*)
  remember (find_id i l1) as p1. destruct p1; simpl in *; symmetry in Heqp1.
+ destruct L1K1 as [phi [? ?]]. rewrite H. exists phi; split; trivial.
+ remember (find_id i l2) as p2. destruct p2; simpl in *; symmetry in Heqp2; trivial.
  destruct L2K2 as [phi [? ?]]. rewrite (list_disjoint_map_fst_find_id1 D _ _ Heqp2), H.
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
(*
Definition isInternal (fd:globdef (Ctypes.fundef Clight.function) type) :=
   match fd with Gfun (Internal _) => true | _ => false end.*)

Definition IntIDs (funs:list(ident*Clight.fundef)): list ident := 
  map fst ((filter (fun x => match (snd x) with Internal _ => true | _ => false end)) funs).

Lemma IntIDs_elim {i l}: In i (IntIDs l) -> exists f, In (i, Internal f) l.
Proof. unfold IntIDs. 
  induction l; simpl; intros. contradiction.
  destruct a; simpl in *.
  destruct f.
  - simpl in H. destruct H; subst. eexists; left; reflexivity.
    apply IHl in H; destruct H. exists x; right; trivial.
  - apply IHl in H; destruct H. exists x; right; trivial.
Qed.

Lemma IntIDs_e {i l}: In i (IntIDs l) -> list_norepet (map fst l) ->
      exists f, find_id i l = Some (Internal f).
Proof. intros. apply IntIDs_elim in H. destruct H. exists x. apply find_id_i; trivial. Qed.

Lemma IntIDs_intro {i l f}: In (i, Internal f) l -> In i (IntIDs l).
Proof. unfold IntIDs. 
  induction l; simpl; intros. contradiction.
  destruct a; simpl in *.
  destruct H.
  - inv H; simpl. left; trivial.
  - apply IHl in H; clear IHl. 
    destruct f0; simpl; trivial. right; trivial.
Qed.

Lemma IntIDs_i {i l f}: find_id i l = Some (Internal f) -> In i (IntIDs l).
Proof. intros. apply find_id_e in H. eapply IntIDs_intro. eassumption. Qed.
(*
Lemma Fundef_of_Gfun {i p f}: find_id i (prog_defs p) = Some (Gfun f) ->
      find_id i (prog_funct p) = Some f.
Proof.
  unfold prog_funct. forget (prog_defs p) as l.
  induction l; simpl; intros. inv H.
  destruct a. destruct g; simpl. if_tac; subst. inv H; trivial. auto. if_tac in H. inv H. auto.
Qed.*)

Lemma in_map_fst_prog_funct' {F V i l}: In i (map fst (@prog_funct' F V l)) -> 
      In i (map fst l).
Proof.
  induction l; simpl; trivial.
  destruct a. destruct g; simpl; intros. destruct H; subst; [ left; trivial | right; eauto].
  right; eauto.
Qed.
Lemma in_map_fst_fundefs {i p}: In i (map fst (prog_funct p)) -> In i (map fst (prog_defs p)).
Proof. apply in_map_fst_prog_funct'. Qed.
(*
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
*)
Definition SF {Espec cs V ge} G (i:ident) (fd:Clight.fundef) (phi:funspec) :=
  match fd with
    Internal f => semaxfunc_InternalInfo cs V G ge i f phi
  | External ef argsig retsig cc => semaxfunc_ExternalInfo Espec ge i ef argsig retsig cc phi
  end.

(*V should be the varspecs of p, and cs the compspecs* 
VSTexterns, "E": Syscalls, functions implemented in assembly... These functions are represented
  as GFun(external ...) in Clight, but nevertheless should be in G (and hence 
  should be justified by a semaxfunc - in fact by a semax_func_extern. Since they are in G
  they may be in Exports, too. -*)
Check prog_funct. Check IntIDs.
Record Component {Espec:OracleKind} {V:varspecs} {cs:compspecs} {ge}
      (E Imports: funspecs) (*(p: Clight.program)*)(funs:list(ident*Clight.fundef)) (Exports: funspecs) := {
  Comp_Imports_external: forall i, In i (map fst Imports) -> 
                         exists f ts t cc, find_id i funs = Some (External f ts t cc);

  Comp_funs_LNR: list_norepet (map fst funs);
  Comp_ExternsImports_LNR: list_norepet (map fst (E++Imports));

  Comp_Exports_LNR: list_norepet (map fst Exports);

  (*VSTexternals are External functions in CompCert*)
  Comp_Externs: forall i, In i (map fst E) -> 
                exists f ts t cc, find_id i funs = Some (External f ts t cc);

  Comp_G: funspecs;

  Comp_G_dom: forall i, In i (IntIDs funs ++ (map fst E)) <-> In i (map fst Comp_G);
  Comp_G_LNR: list_norepet (map fst Comp_G);
  Comp_G_E: forall i, In i (map fst E) -> find_id i E = find_id i Comp_G;

  Comp_G_justified: forall i phi fd,
                    find_id i funs = Some fd ->
                    find_id i Comp_G = Some phi ->
                    @SF Espec cs V ge (Imports ++ Comp_G) i fd phi;

  Comp_G_Exports: forall i phi (E: find_id i Exports = Some phi), 
                  exists phi', find_id i Comp_G = Some phi' /\ funspec_sub phi' phi
}.

Arguments Comp_Imports_external {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_funs_LNR {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_ExternsImports_LNR {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_Exports_LNR {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_Externs {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_G {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_G_dom {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_G_LNR {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_G_justified {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_G_Exports {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_G_E {Espec V cs ge E Imports funs Exports} c.

Section Component.
Variable Espec: OracleKind.
Variable V: varspecs.
Variable cs: compspecs.
Variable ge: Genv.t Clight.fundef type.
Variable E Imports: funspecs.
Variable funs: list(ident*Clight.fundef).
Variable Exports: funspecs.

Variable c: @Component Espec V cs ge E Imports funs Exports.

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
Proof. intros. rewrite <- Comp_G_E; trivial. apply find_id_In_map_fst in H; trivial. Qed.

Lemma Comp_E_in_G: forall {i}, In i (map fst E) -> In i (map fst (Comp_G c)).
Proof. intros. apply In_map_fst_find_id in H. destruct H.
  apply Comp_E_in_G_find in H. apply find_id_In_map_fst in H; trivial. apply Comp_Externs_LNR.
Qed. 

Lemma Comp_LNR_Interns: list_norepet (IntIDs funs).
Proof.
  eapply sublist_norepet. 2: apply (Comp_funs_LNR c). unfold IntIDs. clear.
  induction funs; simpl; intros. constructor.
  destruct a; simpl. destruct f; subst; constructor; auto.
Qed.

Lemma LNR_Internals_Externs: list_norepet (IntIDs funs ++ map fst E).
Proof.
  specialize (Comp_funs_LNR c); specialize Comp_Externs_LNR; specialize Comp_LNR_Interns; intros.
  apply list_norepet_app; split3; trivial.
  do 5 intros ?; subst.
  apply (Comp_Externs c) in H3. destruct H3 as [ef [tys [rt [cc Hy]]]].
  apply IntIDs_e in H2; [destruct H2 | trivial]. congruence.
Qed.

Lemma Comp_G_intern {i} (Hi: In i (map fst (Comp_G c))):
      ( ~ In i (map fst E)) <->
      ( exists f, find_id i funs = Some (Internal f)).
Proof. 
  apply list_in_map_inv in Hi. destruct Hi as [[ii phi] [H Hi]]; simpl in H; subst ii.
  apply in_map_fst in Hi. rewrite <- Comp_G_dom in Hi.
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
      exists ef tys rt cc, find_id i funs = Some (External ef tys rt cc).
Proof. 
  apply list_in_map_inv in Hi. destruct Hi as [[ii phi] [H Hi]]; simpl in H; subst ii.
  apply in_map_fst in Hi. rewrite <- Comp_G_dom in Hi.
  apply in_app_or in Hi; destruct Hi.
+ split; intros.
  - specialize LNR_Internals_Externs.
    rewrite list_norepet_app; intros [? [? X]]. elim (X i i); trivial.
  - apply IntIDs_e in H; [destruct H | apply c]. destruct H0 as [ef [tys [rt [cc He]]]]; congruence.
+ split; intros; trivial.
  apply c in H; trivial.
Qed.

Lemma Comp_G_elim {i} (Hi: In i (map fst (Comp_G c))):
      (In i (map fst E) /\ exists ef tys rt cc, find_id i funs = Some (External ef tys rt cc))
    \/ ((~In i (map fst E)) /\ In i (IntIDs funs) /\ exists f, find_id i funs = Some (Internal f)).
Proof.
  destruct (in_dec ident_eq i (map fst E)).
+ left. split; trivial. apply (Comp_G_extern Hi); trivial.
+ right; split; trivial. apply (Comp_G_intern Hi) in n. split; trivial.
  destruct n. apply IntIDs_i in H; trivial.
Qed.

Lemma Comp_G_in_Fundefs {i} (Hi: In i (map fst (Comp_G c))):
      exists fd, find_id i funs = Some fd.
Proof. 
  destruct (in_dec ident_eq  i (map fst E)).
+ apply (Comp_G_extern Hi) in i0. destruct i0 as [ef [tys [rt [cc Hef]]]].
  eexists; eassumption.
+ apply (Comp_G_intern Hi) in n. destruct n as [f Hf].
  eexists; eassumption.
Qed.

Lemma Comp_G_in_progdefs' {i phi} (Hi: find_id i (Comp_G c) = Some phi):
      exists fd, find_id i funs  = Some fd.
Proof. apply find_id_In_map_fst in Hi. 
  apply Comp_G_in_Fundefs in Hi. trivial.
Qed.

Lemma Comp_G_in_Fundefs' {i phi} (Hi: find_id i (Comp_G c) = Some phi):
      exists fd, find_id i funs = Some fd.
Proof. apply find_id_In_map_fst in Hi. apply Comp_G_in_Fundefs; trivial. Qed.

Lemma Comp_G_in_progdefs {i} (Hi: In i (map fst (Comp_G c))):
      exists fd, find_id i funs = Some fd.
Proof.
  apply Comp_G_elim in Hi.
  destruct Hi as [[HE [ef [tys [rt [cc H]]]]] | [HE [INT [f H]]]]; rewrite H; eexists; reflexivity.
Qed.

Lemma Comp_Imports_in_Fundefs {i phi}: find_id i Imports = Some phi ->
      exists f , find_id i funs = Some f.
Proof.
  specialize (Comp_Imports_external c); intros. apply find_id_e in H0. apply in_map_fst in H0.
  destruct (H _ H0) as [f [ts [t [cc Hf]]]]; clear H. eexists; eassumption.
Qed.

Lemma Comp_Exports_in_Fundefs {i phi}: find_id i Exports = Some phi ->
      exists f , find_id i funs = Some f.
Proof.
  intros. apply (Comp_G_Exports c) in H. destruct H as [psi [H _]].
  apply Comp_G_in_Fundefs' in H; trivial.
Qed.

Lemma Comp_Imports_in_progdefs {i}: In i (map fst(Imports)) -> In i (map fst funs).
Proof.
  specialize (Comp_Imports_external c); intros.
  destruct (H _ H0) as [f [ts [t [cc Hf]]]]; clear H.
  apply find_id_In_map_fst in Hf; trivial.
Qed.

Lemma Comp_Exports_in_progdefs {i}: In i (map fst(Exports)) -> In i (map fst funs).
Proof.
  intros. apply In_map_fst_find_id in H; [ destruct H | apply c].
  apply Comp_Exports_in_Fundefs in H. destruct H.
  apply find_id_In_map_fst in H. trivial.
Qed.

Lemma Comp_Imports_ExternalFundefs {i phi}: find_id i Imports = Some phi ->
      exists ef tys rt cc, find_id i funs = Some (External ef tys rt cc).
Proof.
  specialize (Comp_Imports_external c); intros. apply find_id_In_map_fst in H0.
  apply (H _ H0).
Qed.

Lemma Comp_Interns_disjoint_from_Imports: list_disjoint (IntIDs funs) (map fst Imports).
Proof.
  intros x y X Y.
  apply (Comp_Imports_external c) in Y. destruct Y as [f [ef [ts [t FE]]]].
  apply list_in_map_inv in X. destruct X as [[j fd] [J FD]]; simpl in J; subst j.
  apply filter_In in FD. simpl in FD; destruct FD. destruct fd; inv H0.
  apply find_id_i in H. intros ?; subst. unfold fundef in FE.  congruence. apply c.
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
  apply Comp_G_LNR.
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

Lemma Comp_Imports_sub Imports' (HI1: map fst Imports' = map fst Imports)
      (HV: list_norepet (map fst V ++ map fst (Imports ++ (Comp_G c))))
      (HI2: Forall2 funspec_sub (map snd Imports') (map snd Imports)): @Component Espec V cs ge E Imports' funs Exports.
Proof.
  assert (AUX1: forall i, subsumespec ((find_id i (Imports ++ Comp_G c)))
                                      ((find_id i (Imports' ++ Comp_G c)))).
  { intros. (* rewrite 2 make_tycontext_s_find_id.*)
    remember (find_id i (Imports ++ Comp_G c)) as s; symmetry in Heqs; destruct s; simpl; trivial.
    rename f into phi. apply find_id_app in Heqs; destruct Heqs.
    + assert (exists phi', find_id i Imports' = Some phi' /\ funspec_sub phi' phi).
      { clear - H HI1 HI2. symmetry in HI1. eapply find_funspec_sub; eassumption. }
      destruct H0 as [phi' [H' Sub]]. rewrite find_id_app1 with (x:=phi'); trivial.
      apply funspec_sub_sub_si in Sub.
      exists phi'; split; trivial.
    + rewrite find_id_app2 with (x:=phi); trivial.
      exists phi; split; [ trivial | apply funspec_sub_si_refl ].
      specialize Comp_ctx_LNR. subst. rewrite ! map_app, HI1; trivial. }
  assert (AUX2: forall i, sub_option ((make_tycontext_g V (Imports ++ Comp_G c)) ! i)
                                     ((make_tycontext_g V (Imports' ++ Comp_G c)) ! i)).
  { intros. rewrite 2 make_context_g_char; trivial. 2: rewrite map_app in *; rewrite HI1; trivial.
    rewrite 2 make_tycontext_s_find_id.
    remember (find_id i (Imports ++ Comp_G c)) as s; symmetry in Heqs; destruct s; simpl.
    + rename f into phi. apply find_id_app in Heqs; destruct Heqs.
      - assert (exists phi', find_id i Imports' = Some phi' /\ funspec_sub phi' phi).
        { clear - H HI1 HI2. symmetry in HI1. eapply find_funspec_sub; eassumption. }
        destruct H0 as [phi' [H' Sub]]. apply type_of_funspec_sub in Sub; rewrite <- Sub.
        rewrite find_id_app1 with (x:=phi'); trivial.
      - rewrite find_id_app2 with (x:=phi); trivial.
        specialize Comp_ctx_LNR; subst; rewrite ! map_app, HI1; trivial.
    + apply find_id_None_iff in Heqs. rewrite map_app, <- HI1, <- map_app in Heqs.
      apply find_id_None_iff in Heqs. rewrite Heqs. apply sub_option_refl. }
  eapply Build_Component with (Comp_G c); subst; try solve [apply c].
+ rewrite HI1; apply c. 
+ rewrite map_app, HI1, <- map_app; apply c.
+ intros. specialize (Comp_G_justified c i _ _ H H0); intros; destruct fd.
  - eapply InternalInfo_subsumption. apply AUX2. apply AUX1. apply Comp_ctx_LNR. apply H1.
  - apply H1.
Qed.

Lemma Comp_Exports_sub Exports' (HE1: map fst Exports' = map fst Exports)
      (HE2: Forall2 funspec_sub (map snd Exports) (map snd Exports')): @Component Espec V cs ge E Imports funs Exports'.
Proof.
  eapply Build_Component with (Comp_G c); try apply c.
+ rewrite HE1; apply c. 
+ intros i phi Hi. rename phi into phi'.
  assert (X: exists phi, find_id i Exports = Some phi /\ funspec_sub phi phi').
  { clear - HE1 HE2 Hi. eapply find_funspec_sub; eassumption. }
  destruct X as [phi [Phi PHI]].
  destruct (Comp_G_Exports c _ _ Phi) as [psi [Psi PSI]].
  exists psi; split; [ trivial | eapply funspec_sub_trans; eassumption ].
Qed.

End Component.

Arguments Comp_G_LNR {Espec V cs ge E Imports funs Exports}.
Arguments Comp_LNR_Interns {Espec V cs ge E Imports funs Exports}.
Arguments Comp_ctx_LNR {Espec V cs ge E Imports funs Exports}.
Arguments Comp_Imports_sub {Espec V cs ge E Imports funs Exports}.
Arguments Comp_Exports_sub {Espec V cs ge E Imports funs Exports}.
Arguments Comp_G_disjoint_from_Imports {Espec V cs ge E Imports funs Exports}.
Arguments Comp_G_disjoint_from_Imports_find_id {Espec V cs ge E Imports funs Exports}.
Arguments Comp_Interns_disjoint_from_Imports {Espec V cs ge E Imports funs Exports}.
Arguments Comp_Exports_in_progdefs {Espec V cs ge E Imports funs Exports}.

Arguments Comp_Externs_LNR {Espec V cs ge E Imports funs Exports}. }
Arguments Comp_Imports_in_Fundefs {Espec V cs ge E Imports funs Exports}.
Arguments Comp_Exports_in_Fundefs {Espec V cs ge E Imports funs Exports}.
Arguments Comp_Imports_in_progdefs {Espec V cs ge E Imports funs Exports}.
Arguments Comp_Exports_in_progdefs {Espec V cs ge E Imports funs Exports}.

Arguments Comp_G_intern {Espec V cs ge E Imports funs Exports}.
Arguments Comp_G_extern {Espec V cs ge E Imports funs Exports}.

Arguments Comp_Imports_LNR {Espec V cs ge E Imports funs Exports} c.
Arguments LNR_Internals_Externs {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_G_in_Fundefs {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_E_in_G {Espec V cs ge E Imports funs Exports} c.
Arguments Comp_E_in_G_find {Espec V cs ge E Imports funs Exports} c.

Definition merge_specs (phi1:funspec) (sp2: option funspec): funspec :=
  match sp2 with 
    Some phi2 => match binary_intersection phi1 phi2 with
                                  Some phi => phi
                                | None => (*None*) phi1
                            end
  | None => phi1
  end.

Lemma merge_specs_succeed {phi1 phi2}:
      funsig_of_funspec phi1 = funsig_of_funspec phi2 ->
      callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2 ->
  binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2)).
Proof. clear. intros.
  simpl. destruct phi1; destruct phi2; simpl in *. subst f0 c0.
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
  destruct (eq_dec i0 i); subst; simpl in *. rewrite if_true in Hi; [ discriminate | trivial].
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
             (Sigs: funsig_of_funspec phi1 = funsig_of_funspec phi2)
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
      | Some phi1, Some phi2 => ~ (funsig_of_funspec phi1 = funsig_of_funspec phi2 /\
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
      (SIG: funsig_of_funspec phi1 = funsig_of_funspec phi2)
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
    rewrite ! if_true, Heqt in * by trivial.
    destruct (eq_dec i j); [ congruence | simpl]; clear n0.
    destruct (ident_eq i i); [ simpl in *; clear e | congruence].
    f_equal.
    * f_equal. extensionality x. destruct x as [ii phi]; simpl.
      if_tac; subst. rewrite Heqt, if_false; [ simpl | congruence]. destruct (ident_eq i i); [ reflexivity | congruence].
      destruct (eq_dec ii j); simpl; trivial. destruct (ident_eq i ii); [ congruence | simpl ]. rewrite andb_true_r; trivial.
    * f_equal. extensionality x. destruct x as [ii phi]; simpl.
      if_tac; subst. rewrite Heqt, if_false; [ simpl | congruence]. destruct (ident_eq i i); [ reflexivity | congruence].
      destruct (eq_dec ii j); simpl; trivial. destruct (ident_eq i ii); [ congruence | simpl ]. rewrite andb_true_r; trivial.
Qed.

Lemma subsumespec_G_merge_l l1 l2 i
  (SigsCC: forall phi1 phi2, find_id i l1 = Some phi1 -> find_id i l2 = Some phi2 ->
    funsig_of_funspec phi1 = funsig_of_funspec phi2 /\
    callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2):
 subsumespec (find_id i l1) (find_id i (G_merge l1 l2)).
Proof.
  red. remember (find_id i l1) as q1; symmetry in Heqq1. remember (find_id i l2) as q2; symmetry in Heqq2.
  destruct q1 as [phi1 |]; destruct q2 as [phi2 |]; trivial.
+ destruct (G_merge_find_id_SomeSome Heqq1 Heqq2) as [phi [BI Phi]]. apply SigsCC; trivial. apply SigsCC; trivial.
  rewrite Phi. eexists; split. trivial. apply funspec_sub_sub_si. apply binaryintersection_sub in BI. apply BI.
+ rewrite (G_merge_find_id_SomeNone Heqq1 Heqq2). eexists; split. reflexivity. apply funspec_sub_si_refl.
Qed.
 
Lemma subsumespec_G_merge_r l1 l2 i
  (SigsCC: forall phi1 phi2, find_id i l1 = Some phi1 -> find_id i l2 = Some phi2 ->
    funsig_of_funspec phi1 = funsig_of_funspec phi2 /\
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
                     sig_res := opttyp_of_type (fn_return f);
                     sig_cc := fn_callconv f |}
  | External ef tys rt cc => signature_of_type tys rt cc
 end.

Definition Fundefs_match funs1 funs2 (Imports1 Imports2:funspecs) := 
           forall i fd1 fd2,
                         find_id i funs1 = Some fd1 ->
                         find_id i funs2 = Some fd2 ->
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

Section ComponentJoin.
Variable Espec: OracleKind.
Variable V1 V2: varspecs.
Variable cs1 cs2 cs: compspecs. 
Variable E1 Imports1 Exports1 E2 Imports2 Exports2 E Imports Exports: funspecs.
(*Variable p1 p2 p: Clight.program.*)
Variable ge1 ge2 ge: Genv.t Clight.fundef type.
Variable funs1 funs2 funs: list(ident*Clight.fundef).
Variable c1: @Component Espec V1 cs1 ge1 E1 Imports1 funs1 Exports1.
Variable c2: @Component Espec V2 cs2 ge2 E2 Imports2 funs2 Exports2.

Variable DisjointVarspecs: list_disjoint (map fst V1) (map fst V2).
Variable HV1p1: list_disjoint (map fst V1) (map fst funs1).
Variable HV1p2: list_disjoint (map fst V1) (map fst funs2).
Variable HV2p1: list_disjoint (map fst V2) (map fst funs1).
Variable HV2p2: list_disjoint (map fst V2) (map fst funs2).
Variable LNR_V1: list_norepet (map fst V1).
Variable LNR_V2: list_norepet (map fst V2).
Variable CS1: cspecs_sub cs1 cs.
Variable CS2: cspecs_sub cs2 cs.

Variable V: varspecs.
Variable HV1: forall i phi, find_id i V1 = Some phi -> find_id i V = Some phi.
Variable HV2: forall i phi, find_id i V2 = Some phi -> find_id i V = Some phi.

Variable FundefsMatch: Fundefs_match funs1 funs2 Imports1 Imports2.

Variable Functions_preserved: forall i,
         match find_id i funs1, find_id i funs2 with
           Some (Internal f1), _ => find_id i funs = Some (Internal f1)
         | _, Some (Internal f2) => find_id i funs = Some (Internal f2)
         | Some (External ef1 tys1 rt1 cc1), _ =>
               find_id i funs = Some (External ef1 tys1 rt1 cc1)
         | _, Some (External ef2 tys2 rt2 cc2) =>
               find_id i funs = Some (External ef2 tys2 rt2 cc2)
         | None, None => find_id i funs = None
         end.

(********************Assumptions involving E1 and E2  ********)

Variable Externs1_Hyp: list_disjoint (map fst E1) (IntIDs funs2).
Variable Externs2_Hyp: list_disjoint (map fst E2) (IntIDs funs1).

Variable ExternsHyp: E = G_merge E1 E2. 

(************************************************************)

(*one could try to weaken this hypothesis by weakening the second condition to In i (IntIDs p1),
  so that it is possible to delay resolving the spec for an extern in case several modules prove (mergaable but different) specs for it. The present cluase forces one to use match with the first spec one finds*)
Variable SC1: forall i phiI, find_id i Imports2 = Some phiI -> In i (map fst E1 ++ IntIDs funs1) ->
              exists phiE, find_id i Exports1 = Some phiE /\ funspec_sub phiE phiI.

(*same comment here*)
Variable SC2: forall i phiI, find_id i Imports1 = Some phiI -> In i (map fst E2 ++ IntIDs funs2) ->
                          exists phiE, find_id i Exports2 = Some phiE /\ funspec_sub phiE phiI.

Variable HImports: forall i phi1 phi2, find_id i Imports1 = Some phi1 -> find_id i Imports2 = Some phi2 -> phi1=phi2.

(*It may be possible to eliminate this condition by modifying the definition
  of binary intersection such that instead of requiring parameter names
  to be identical the names are suitably renamed. Note that equality of the
  argument (and return) types already holds, by the semaxfunc properties inside c1 and c2*)
Variable HContexts: forall i phi1 phi2, find_id i (Comp_G c1) = Some phi1 ->
                    find_id i (Comp_G c2) = Some phi2 -> funsig_of_funspec phi1 = funsig_of_funspec phi2.

Variable ImportsDef: Imports = 
                     filter (fun x => negb (in_dec ident_eq (fst x) (map fst E2 ++ IntIDs funs2))) Imports1 ++
                     filter (fun x => negb (in_dec ident_eq (fst x) (map fst E1 ++ IntIDs funs1 ++ map fst Imports1))) Imports2.

Variable ExportsDef: Exports = G_merge Exports1 Exports2.

Variable Ge1_FS: forall i, sub_option (Genv.find_symbol ge1 i) 
                                      (Genv.find_symbol ge i).

Variable Ge2_FS: forall i, sub_option (Genv.find_symbol ge2 i) 
                                      (Genv.find_symbol ge i).

Variable Ge1_FFP: forall b, sub_option (Genv.find_funct_ptr ge1 b)
                                       (Genv.find_funct_ptr ge b).

Variable Ge2_FFP: forall b, sub_option (Genv.find_funct_ptr ge2 b)
                                       (Genv.find_funct_ptr ge b).

Variable LNRp: list_norepet (map fst funs).

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
      destruct (in_dec ident_eq x2 (map fst E2 ++IntIDs funs2)); [ inv Y1 | clear Y1].
      destruct (in_dec ident_eq x2 (map fst E1 ++ IntIDs funs1 ++ map fst Imports1)); [inv Y2 | clear Y2]. 
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
    apply find_id_i in PHI; [ | apply Comp_G_LNR ].
    destruct (@Comp_G_in_Fundefs' _ _ _ _ _ _ _ _ c1 _ _  PHI) as [f F]. apply find_id_In_map_fst in F; trivial.
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
    apply find_id_i in PHI; [ | apply Comp_G_LNR ].
    destruct (@Comp_G_in_Fundefs' _ _ _ _ _ _ _ _ c2 _ _ PHI) as [f F]. apply find_id_In_map_fst in F; trivial.
Qed.

Lemma Imports_in_Fundefs: forall x, In x (map fst Imports) ->
      In x (map fst funs1 ++ map fst funs2).
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
            remember (find_id i funs1) as k; symmetry in Heqk; destruct k.
            ++ left. apply find_id_e in Heqk. apply in_map_fst in Heqk. trivial.
            ++ right. apply find_id_In_map_fst in Hf. trivial. 
Qed.

Variable LNR2: list_norepet (map fst V ++ map fst (Imports ++ (G_merge (Comp_G c1) (Comp_G c2)))).
(*satisfied eg if V=V1++V2, see inside the proof below*)

Lemma ComponentJoin: 
   @Component Espec (*(V1++V2)*)V cs ge E Imports funs Exports.
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
          In i (map fst funs1 ++ map fst funs2)).
  { subst G; clear - c1 c2; intros. apply G_merge_InDom in H; [ apply in_or_app | apply Comp_G_LNR].
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
        destruct (in_dec ident_eq y (map fst E2 ++IntIDs funs2)); simpl in *. discriminate. 
        elim n. apply (in_map fst) in PHI1. apply in_or_app. left. apply PHI1. 
      * clear. rewrite G_merge_aux_dom.
        do 5 intros ?; subst. apply in_map_iff in H0. destruct H0 as [[j phi] [J PHI]]. simpl in J; subst.
         apply filter_In in PHI. simpl in PHI. destruct PHI. apply negb_true_iff in H1. 
         destruct (in_dec ident_eq y (map fst E1 ++ IntIDs funs1 ++ map fst Imports1)); simpl in H1. discriminate.
         apply n. apply in_or_app. left; trivial.
      * clear - c2. specialize (Comp_ExternsImports_LNR c2). rewrite map_app, list_norepet_app. intros [? [? ?]]. 
        eapply list_disjoint_mono. apply H1.
        + clear. intros. apply in_map_iff. apply in_map_iff in H. destruct H as [[j phi] [J PHI]]. simpl in J; subst.
          apply filter_In in PHI. destruct PHI. exists (x,phi); split; trivial.
        + clear. intros. apply in_map_iff. apply in_map_iff in H. destruct H as [[j phi] [J PHI]]. simpl in J; subst.
          apply filter_In in PHI. destruct PHI. exists (x,phi); split; trivial. }

  assert (LNR_G: list_norepet (map fst G)).
  { subst G; clear - LNR_G1 LNR_G2 Externs2_Hyp Externs1_Hyp.
    apply G_merge_LNR; apply Comp_G_LNR. }

  assert (V1_D1: list_disjoint (map fst V1) (map fst (Imports ++ G))).
  { eapply list_disjoint_mono with (l2':= (map fst funs1 ++ map fst funs2))
    (l1':= map fst V1); trivial.
    + do 5 intros ?; subst. apply in_app_or in H0; destruct H0.
      apply (HV1p1 y y ); trivial. apply (HV1p2 y y); trivial.
    + intros. rewrite map_app in H. apply in_app_or in H. destruct H.
      apply Imports_in_Fundefs; trivial. apply G_in_Fundefs; trivial. }

  assert (V2_D1: list_disjoint (map fst V2) (map fst (Imports ++ G))).
  { eapply list_disjoint_mono with (l2':= (map fst funs1 ++ map fst funs2))
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
        destruct (in_dec ident_eq i (map fst E2 ++ IntIDs funs2)); simpl in H1. inv H1. clear H1.
        apply n; clear n; apply in_or_app.
        apply Comp_G_elim in HH2; destruct HH2. left; apply H0. right; apply H0.
      + destruct Hi. destruct (in_dec ident_eq i (map fst E1 ++ IntIDs funs1 ++ map fst Imports1)). inv H1. clear H1.
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

  (*assert (LNR2: list_norepet (map fst V1 ++ map fst V2 ++ map fst (Imports ++ G))).
  { clear ExportsDef CS1 CS2 HExports HImports Functions_preserved. subst G.  
    rewrite list_norepet_app; split3; trivial.
    apply list_disjoint_app_R; trivial. } 
*)
  specialize (Comp_G_justified c2); intros JUST2. specialize (Comp_G_justified c1); intros JUST1.
(*
assert (LNR2': list_norepet
  (map fst (V1 ++ V2) ++ map fst (Imports ++ G))). 
{ subst G. rewrite map_app, <- app_assoc. trivial. }

clear LNR2; rename LNR2' into LNR2.
*)

assert (Condition1: forall i, In i (map fst Imports) ->
        exists f ts t cc, find_id i funs = Some (External f ts t cc)).
{ subst Imports; clear - c1 c2 Functions_preserved LNRp. intros. rewrite map_app in H. apply in_app_or in H; destruct H.
  - clear - H c1 c2 Functions_preserved LNRp. specialize (Functions_preserved i).
    apply list_in_map_inv in H. destruct H as [[j phi] [H J]]. simpl in H; subst j.
    apply filter_In in J. simpl in J. destruct J as [J1 J2]. 

    destruct (Comp_Imports_external c1 i) as [ef [ts [t [cc FND]]]].
    { apply (in_map fst) in J1. apply J1. }

    rewrite FND in Functions_preserved.
    remember (find_id i funs2) as u; symmetry in Hequ; destruct u.
    * destruct f.
      ++ destruct (in_dec ident_eq i (map fst E2 ++ IntIDs funs2)). inv J2. 
         elim n. apply in_or_app. right. apply in_map_iff.
         exists (i, Internal f); simpl; split; trivial. 
         rewrite filter_In; simpl. split; trivial. apply find_id_e; trivial.
      ++ do 4 eexists; eassumption.
    * do 4 eexists; eassumption.

  - specialize (Functions_preserved i).
    apply list_in_map_inv in H. destruct H as [[j phi] [H J]]. simpl in H; subst j.
    apply filter_In in J. simpl in J. destruct J as [J1 J2]. 

    destruct (Comp_Imports_external c2 i) as [ef [ts [t [cc FND]]]].
    { apply (in_map fst) in J1. apply J1. }

    rewrite FND in Functions_preserved.
    remember (find_id i funs1) as u; symmetry in Hequ; destruct u.
    * destruct f.
      ++ destruct (in_dec ident_eq i (map fst E1 ++ IntIDs funs1 ++ map fst Imports1)). inv J2. 
         elim n. apply in_or_app. right. apply in_or_app. left. apply in_map_iff.
         exists (i, Internal f); simpl; split; trivial. 
         rewrite filter_In; simpl. split; trivial. apply find_id_e; trivial.
      ++ do 4 eexists; eassumption.
    * do 4 eexists; eassumption. }

assert (Condition2: forall i : ident, In i (map fst E) ->
        exists ef ts t cc, find_id i funs = Some (External ef ts t cc)).
{ intros; subst E. specialize (Functions_preserved i). apply G_merge_InDom in H. destruct H as [Hi | [NE Hi]].
  - destruct (Comp_Externs c1 _ Hi) as [ef [tys [rt [cc P1i]]]]. exists ef, tys, rt, cc.
    clear - P1i Hi Functions_preserved Externs1_Hyp LNRp c2.
    rewrite P1i in Functions_preserved.
    remember (find_id i funs2) as u; symmetry in Hequ; destruct u.
    * destruct f.
      ++ apply IntIDs_i in Hequ.
         elim (Externs1_Hyp i i); trivial.
      ++ trivial. 
    * trivial. 
  - destruct (Comp_Externs c2 _ Hi) as [ef [tys [rt [cc P2i]]]]. exists ef, tys, rt, cc.
    clear - P2i Hi Functions_preserved Externs2_Hyp LNRp Externs1_Hyp c2 c1 FundefsMatch.
    specialize (FundefsMatch i).
    rewrite P2i in *.
    remember (find_id i funs1) as u; symmetry in Hequ; destruct u.
    * destruct f.
      ++ clear - Hequ Externs2_Hyp Hi. apply IntIDs_i in Hequ.
         elim (Externs2_Hyp i i); trivial.
      ++ specialize (FundefsMatch _ _ Hequ P2i). inv FundefsMatch. trivial.
    * trivial.
  - apply (Comp_Externs_LNR c1). }

assert (Calling_conventions_match: forall i phi1 phi2, 
         find_id i (Comp_G c1) = Some phi1 ->  find_id i (Comp_G c2) = Some phi2 -> 
         callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2).
{ clear - FundefsMatch JUST1 JUST2. intros ? ? ? I1 I2; specialize (FundefsMatch i). 
                     specialize (JUST1 i); rewrite I1 (* <- Fundefs_progfunct*) in JUST1.
                     specialize (JUST2 i); rewrite I2 (* <- Fundefs_progfunct*) in JUST2.
                     apply find_id_In_map_fst in I1. apply Comp_G_elim in I1. 
                     apply find_id_In_map_fst in I2. apply Comp_G_elim in I2.
                     destruct I1 as [ [_ [? [? [? [? HH1]]]]] | [_ [ ? [? HH1]]]]; rewrite HH1 in *;
                     destruct I2 as [ [_ [? [? [? [? HH2]]]]] | [_ [ ? [? HH2]]]]; rewrite HH2 in *;
                     specialize (JUST1 _ _ (eq_refl _) (eq_refl _)); simpl in JUST1;
                     specialize (JUST2 _ _ (eq_refl _) (eq_refl _)); simpl in JUST2;
                     specialize (FundefsMatch _ _ HH1 HH2); simpl in FundefsMatch; subst; inv FundefsMatch;
                     first [ apply ExternalInfo_cc in JUST1 | apply InternalInfo_cc in JUST1];
                     first [ apply ExternalInfo_cc in JUST2 | apply InternalInfo_cc in JUST2];
                     rewrite <- JUST1; trivial.
                     inv H0. trivial.  
                     inv H0. trivial. }

assert ( SUBSUME1 : forall i : ident,
           subsumespec (find_id i (Imports1 ++ Comp_G c1)) (find_id i (Imports ++ G))).
{ subst Imports G; clear - c1 c2 Externs2_Hyp Externs1_Hyp HContexts (*FundefsMatch*)Calling_conventions_match  SC1 SC2 JUST1 JUST2. 
  intros. apply subsumespec_app_left; intros.
           { rewrite ! find_id_app_char. 
             remember (find_id i Imports1) as q1; symmetry in Heqq1; destruct q1 as [phi1 |]; simpl; trivial.
             specialize (list_disjoint_map_fst_find_id1 (Comp_G_disjoint_from_Imports c1) _ _ Heqq1); intros.
             rewrite G_merge_None_l; trivial. 2: apply c2.
             rewrite find_id_filter_char, Heqq1 by apply (Comp_Imports_LNR c1); simpl.
             destruct (in_dec ident_eq i (map fst E2 ++ IntIDs funs2)); simpl.
             2: exists phi1; split; [ reflexivity | apply funspec_sub_si_refl].
             rewrite find_id_filter_char by apply (Comp_Imports_LNR c2); simpl.
             destruct (in_dec ident_eq i (map fst E1 ++ IntIDs funs1 ++ map fst Imports1)); simpl.
             + apply find_id_None_iff in H.
               remember (find_id i (Comp_G c2)) as w2; symmetry in Heqw2; destruct w2 as [psi2 |].
               - exists psi2; split. destruct (find_id i Imports2); trivial.
                 destruct (SC2 _ _ Heqq1 i0) as [tau2 [Tau2 SubTau]].
                 apply funspec_sub_sub_si. apply funspec_sub_trans with tau2; trivial.
                 destruct (Comp_G_Exports c2 _ _ Tau2) as [omega [Omega SubOM]].
                 rewrite Heqw2 in Omega; inv Omega; trivial.
               - destruct (SC2 _ _ Heqq1 i0) as [tau2 [TAU Tau]]. 
                 destruct (Comp_G_Exports c2 _ _ TAU) as [omega [Omega OM]]. congruence.
             + destruct (SC2 _ _ Heqq1 i0) as [tau2 [TAU Tau]]. 
               destruct (Comp_G_Exports c2 _ _ TAU) as [omega [Omega OM]]; rewrite Omega.
               specialize (Comp_G_disjoint_from_Imports c2); intros.
               rewrite (list_disjoint_map_fst_find_id2 (Comp_G_disjoint_from_Imports c2) _ _ Omega).
               exists omega; split; trivial. apply funspec_sub_sub_si. apply funspec_sub_trans with tau2; trivial. }
           { specialize (HContexts i). remember (find_id i (Comp_G c1)) as d; symmetry in Heqd; destruct d as [phi1 |]; simpl; trivial.
               rewrite!  find_id_app_char, find_id_filter_None_I; [ | trivial | apply (Comp_Imports_LNR c1) ].
               rewrite find_id_filter_char by apply (Comp_Imports_LNR c2); simpl.
               remember (find_id i Imports2) as w2; symmetry in Heqw2; destruct w2 as [psi2 |]; simpl.
               - destruct (in_dec ident_eq i (map fst E1 ++ IntIDs funs1 ++ map fst Imports1)); simpl.
                 * rewrite (G_merge_find_id_SomeNone Heqd (list_disjoint_map_fst_find_id1 (Comp_G_disjoint_from_Imports c2) _ _ Heqw2)).
                   eexists; split. reflexivity. apply funspec_sub_si_refl.
                 * apply find_id_In_map_fst in Heqd. apply Comp_G_dom in Heqd.
                   elim n; clear - Heqd. rewrite app_assoc. apply in_or_app. left; apply in_app_or in Heqd; apply in_or_app. destruct Heqd; auto.
               - remember (find_id i (Comp_G c2)) as q2; destruct q2 as [phi2 |]; symmetry in Heqq2; simpl; trivial.
                 * destruct (G_merge_find_id_SomeSome Heqd Heqq2) as [phi [BI PHI]].
                   { apply HContexts; trivial. }
                   { apply (Calling_conventions_match i); trivial. }
                   rewrite PHI. exists phi; split; trivial. apply binaryintersection_sub in BI. apply funspec_sub_sub_si. apply BI.
                 * rewrite G_merge_None_r, Heqd; trivial. exists phi1. split; trivial. apply funspec_sub_si_refl.
                   apply (Comp_G_LNR c2). }
}

assert ( SUBSUME2 : forall i : ident,
           subsumespec (find_id i (Imports2 ++ Comp_G c2))
             (find_id i (Imports ++ G))). 
    { intros. remember (find_id i (Imports2 ++ Comp_G c2)) as u; symmetry in Hequ; destruct u as [phi2 |]; simpl; [| trivial].
      rewrite find_id_app_char in Hequ.
      rewrite ImportsDef; clear ImportsDef. rewrite <- app_assoc, ! find_id_app_char, ! find_id_filter_char; try apply (Comp_Imports_LNR c2) ; try apply (Comp_Imports_LNR c1).
      simpl. remember (find_id i Imports2) as q; symmetry in Heqq; destruct q as [phi2' |].
      + inv Hequ. clear - D_GImp2 i HV2p1 Heqq SC1 LNR_G1 HImports.
        specialize (list_disjoint_map_fst_find_id1 D_GImp2 _ _ Heqq); intros.
        rewrite G_merge_None_r; trivial. 2: apply Comp_G_LNR.
        destruct (in_dec ident_eq i (map fst E2 ++ IntIDs funs2)); simpl.
        - apply find_id_None_iff in H; elim H.
          apply (Comp_G_dom c2 i). apply in_or_app. apply in_app_or in i0. destruct i0; auto.
        - remember (find_id i Imports1) as w1; symmetry in Heqw1; destruct w1 as [ph1 |].
          * specialize (HImports _ _ _ Heqw1 Heqq); subst. eexists; split. reflexivity. apply funspec_sub_si_refl.
          * destruct (in_dec ident_eq i (map fst E1 ++ IntIDs funs1 ++ map fst Imports1)); simpl.
            ++ rewrite app_assoc in i0; apply in_app_or in i0; destruct i0.
               -- destruct (SC1 _ _ Heqq H0) as [phi1 [EXP1 Sub]].
                  destruct (Comp_G_Exports c1 _ _ EXP1) as [psi1 [G1i Psi1]].
                  eexists; split. eassumption. apply funspec_sub_sub_si. apply funspec_sub_trans with phi1; trivial.
               -- apply find_id_None_iff in Heqw1. contradiction.
            ++ eexists; split. reflexivity. apply funspec_sub_si_refl.
      + destruct (in_dec ident_eq i (map fst E2 ++ IntIDs funs2)); simpl.
        - subst G.
          remember (find_id i (Comp_G c1)) as q1; symmetry in Heqq1; destruct q1 as [phi1 |].
          * destruct (G_merge_find_id_SomeSome Heqq1 Hequ) as [phi [BI Sub]].
            { apply (HContexts i); trivial. }
            {  apply (Calling_conventions_match i); trivial. }
             exists phi; split.
             -- destruct (find_id i Imports1); trivial.
             -- apply funspec_sub_sub_si. eapply (binaryintersection_sub _ _ _ BI).
          * rewrite (G_merge_find_id_NoneSome Heqq1 Hequ).
            exists phi2; split. destruct (find_id i Imports1); trivial. apply funspec_sub_si_refl.
            apply Comp_G_LNR.
        - elim n. apply find_id_In_map_fst in Hequ. rewrite <- (Comp_G_dom c2) in Hequ. elim n; apply in_or_app.
          apply in_app_or in Hequ; destruct Hequ; auto. }

assert (TypesOfFunspecs1: forall i, sub_option (make_tycontext_g V1 (Imports1 ++ Comp_G c1)) ! i
  (make_tycontext_g (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2))) ! i).
{ subst G; clear - SUBSUME1 LNR_V1 LNR4_V1 HV1p1 LNR2 HV1. intros i.
  rewrite 2 make_context_g_char, 2 make_tycontext_s_find_id; trivial.
  specialize (SUBSUME1 i). red in SUBSUME1. destruct (find_id i (Imports1 ++ Comp_G c1)); simpl.
  + destruct SUBSUME1 as [psi2 [PHI2 SUB]]. rewrite PHI2.
    exploit (SUB (empty_rmap 0)); [ trivial | intros FS].
    apply type_of_funspec_sub_si in FS; rewrite FS; trivial.
  + remember (find_id i V1) as w; symmetry in Heqw; destruct w as [phi |]; simpl; trivial.
    rewrite (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V1 i phi Heqw).
    apply HV1; trivial.
  + apply LNR3_V1. 
}

assert (TypesOfFunspecs2: forall i, sub_option (make_tycontext_g V2 (Imports2 ++ Comp_G c2)) ! i
  (make_tycontext_g (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2))) ! i).
{ subst G; clear - DisjointVarspecs SUBSUME2 LNR_V2 LNR4_V2 HV2p2 LNR2 HV2. intros i.
  rewrite 2 make_context_g_char, 2 make_tycontext_s_find_id; trivial.
  specialize (SUBSUME2 i). red in SUBSUME2. destruct (find_id i (Imports2 ++ Comp_G c2)); simpl.
  + destruct SUBSUME2 as [psi2 [PHI2 SUB]]. rewrite PHI2.
    exploit (SUB (empty_rmap 0)); [ trivial | intros FS].
    apply type_of_funspec_sub_si in FS; rewrite FS; trivial.
  + remember (find_id i V2) as w; symmetry in Heqw; destruct w as [phi |]; simpl; trivial.
    rewrite (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR4_V2 _ _ Heqw).
    apply HV2; trivial.
  + apply LNR3_V2.
}

apply Build_Component with (Comp_G := G); trivial.
+ intros. subst G E. split; intros. 
  - apply G_merge_InDom; [ apply c1 | apply in_app_or in H; destruct H].
    * destruct (in_dec ident_eq i (map fst (Comp_G c1))). left; trivial. right; split; trivial.
      apply c2. specialize (Functions_preserved i).
      remember (find_id i funs1) as q1; destruct q1.
      ++ destruct f.
         -- clear - Heqq1 Functions_preserved LNRp H n.
            symmetry in Heqq1. elim n. apply c1. apply in_or_app; left. 
            apply IntIDs_i in Heqq1; trivial.
         -- clear - Heqq1 Functions_preserved LNRp H n c2. 
            (*the following 8 lines are repeated below*)
            remember (find_id i funs2) as q2; destruct q2.
            ** destruct f. symmetry in Heqq2. apply in_or_app; left.
               apply IntIDs_i in Heqq2; trivial.
               apply In_map_fst_find_id in H. destruct H. 
               rewrite find_id_filter_char in H; trivial; simpl in H.
               unfold fundef in Functions_preserved. rewrite Functions_preserved in H. simpl in H; inv H.
               trivial. apply list_norepet_map_fst_filter; trivial.
            ** apply IntIDs_e in H; [destruct H | trivial]. congruence.
       ++ clear - Heqq1 Functions_preserved LNRp H n c2.
          (*here's the repetition*)
            remember (find_id i funs2) as q2; destruct q2.
            ** destruct f. symmetry in Heqq2. apply in_or_app; left.
               apply IntIDs_i in Heqq2; trivial.
               apply In_map_fst_find_id in H. destruct H. 
               rewrite find_id_filter_char in H; trivial; simpl in H.
               unfold fundef in Functions_preserved. rewrite Functions_preserved in H. simpl in H; inv H.
               trivial. apply list_norepet_map_fst_filter; trivial.
            ** apply IntIDs_e in H; [destruct H | trivial]. congruence.
    * apply G_merge_InDom in H; [ destruct H as [H | [HE H]] | apply (Comp_Externs_LNR c1)].
      ++ left. apply In_map_fst_find_id in H. destruct H. apply (Comp_E_in_G_find c1) in H. apply find_id_In_map_fst in H; trivial. apply (Comp_Externs_LNR c1).
      ++ right. split; [ intros N | apply Comp_E_in_G; trivial ].
         apply (list_disjoint_notin  _ Externs2_Hyp H). apply Comp_G_dom in N. apply in_app_or in N; destruct N; [ trivial | contradiction].
  - apply G_merge_InDom in H; [ destruct H as [H | [HE H]] | apply (Comp_G_LNR c1)].
    * apply Comp_G_dom in H.  apply in_app_or in H; apply in_or_app; destruct H.
      ++ left. apply In_map_fst_find_id in H; [ destruct H as [fd Hfd] | trivial].
         specialize (Functions_preserved i). clear - c1 Functions_preserved Hfd LNRp. 
         rewrite find_id_filter_char in Hfd; [ simpl in Hfd | apply c1].
         unfold fundef in Functions_preserved. remember (@find_id (Ctypes.fundef function) i funs1) as q; symmetry in Heqq; destruct q; [ | discriminate].
         destruct f; inv Hfd.
         apply IntIDs_i in Functions_preserved; trivial.
      ++ right. apply G_merge_InDom. apply (Comp_Externs_LNR c1). left; trivial.
    * apply in_or_app. apply Comp_G_elim in H. destruct H as [[HE2 EXT] | [HE2 [INT [f FI]]]].
      ++ right. apply G_merge_InDom.  apply (Comp_Externs_LNR c1). 
         right; split; trivial. intros N. apply HE. apply Comp_E_in_G. apply N.
      ++ specialize (Functions_preserved i).
         rewrite FI in Functions_preserved.
         remember (find_id i funs1) as w1; symmetry in Heqw1; destruct w1.
         { left. clear - Functions_preserved LNRp.
           destruct f0; apply IntIDs_i in Functions_preserved; trivial. }
         left. clear - Functions_preserved LNRp.
               apply IntIDs_i in Functions_preserved; trivial.

+ subst G E; intros. destruct (In_map_fst_find_id H) as [phi Phi]. apply G_merge_LNR. apply (Comp_Externs_LNR c1).  apply (Comp_Externs_LNR c2). 
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
+ (*SF*) subst G. intros. clear Condition1 Condition2 ImportsDef. apply G_merge_find_id_Some in H0. 2: apply (Comp_G_LNR c2).
  specialize (Functions_preserved i). specialize (FundefsMatch i).
  remember (find_id i (Comp_G c1)) as q1; symmetry in Heqq1; destruct q1 as [phi1 |].
  - subst phi; 
     clear - c1 c2 Heqq1 JUST1 JUST2 CS1 CS2 Ge1_FS Ge2_FS Ge1_FFP Ge2_FFP H 
            SUBSUME1 SUBSUME2 TypesOfFunspecs1 TypesOfFunspecs2 HContexts
            Externs1_Hyp Externs2_Hyp Functions_preserved FundefsMatch.
    exploit (@Comp_G_in_Fundefs' _ _ _ _ _ _ _ _ c1). apply Heqq1. intros [fd1 FD1].
    specialize (JUST1 _ _ _ FD1 Heqq1).
    unfold fundef in *. rewrite FD1 in Functions_preserved, FundefsMatch. red in JUST1.
   
    remember (find_id i (Comp_G c2)) as q2; symmetry in Heqq2; destruct q2 as [phi2 |].
    * exploit (@Comp_G_in_Fundefs' _ _ _ _ _ _ _ _ c2). apply Heqq2. intros [fd2 FD2].
      specialize (JUST2 _ _ _ FD2 Heqq2).
      unfold fundef in *. rewrite FD2 in Functions_preserved, FundefsMatch. red in JUST2.
      specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)).
      destruct fd1; destruct fd2.
      ++ (*Internal/Internal*)
         rewrite Functions_preserved in H. inv H. inv FundefsMatch.
         assert (SF1: semaxfunc_InternalInfo cs (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2)) ge i f0 phi1).
         { eapply InternalInfo_subsumption.
           4:  apply (InternalInfo_envs_sub CS1 ge1); [trivial | trivial | apply JUST1]. 
           trivial. trivial. apply Comp_ctx_LNR. }
         assert (SF2: semaxfunc_InternalInfo cs (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2)) ge i f0 phi2).
         { eapply InternalInfo_subsumption.
           4: apply (InternalInfo_envs_sub CS2 ge2); trivial; apply JUST2.
           trivial. trivial. apply Comp_ctx_LNR. } 
         assert (BI : binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2))).
         { apply merge_specs_succeed. apply (HContexts i); auto.
           apply InternalInfo_cc in SF1. rewrite <- SF1. 
           apply InternalInfo_cc in SF2. trivial. } 
         apply (internalInfo_binary_intersection SF1 SF2 BI).
      ++ (*InternalExternal*) 
         clear - Functions_preserved FundefsMatch Externs2_Hyp FD1 FD2 Heqq1 Heqq2.
         apply find_id_In_map_fst in Heqq2. apply Comp_G_elim in Heqq2. destruct Heqq2 as [[? ?]|  [? ?]].
         -- elim (list_disjoint_notin i Externs2_Hyp H). clear - FD1 c1. 
            apply IntIDs_i in FD1; trivial.
         -- destruct H0 as [? [? ?]]. unfold fundef in *. congruence.
      ++ (*ExternalInternal*)
         clear - Functions_preserved FundefsMatch Externs1_Hyp FD1 FD2 Heqq1 Heqq2.
         apply find_id_In_map_fst in Heqq1. apply Comp_G_elim in Heqq1. destruct Heqq1 as [[? ?]|  [? ?]].
         -- elim (list_disjoint_notin i Externs1_Hyp H). clear - FD2 c2.
            apply IntIDs_i in FD2; trivial.
         -- destruct H0 as [? [? ?]]. unfold fundef in *. congruence.
      ++ (*ExternalExternal*)
         rewrite Functions_preserved in H. inv H. inv FundefsMatch.
         assert (SF1: semaxfunc_ExternalInfo Espec ge i e0 t1 t2 c0 phi1).
         { eapply ExternalInfo_envs_sub. 3: apply JUST1. trivial. trivial. }
         assert (SF2: semaxfunc_ExternalInfo Espec ge i e0 t1 t2 c0 phi2).
         { eapply ExternalInfo_envs_sub. 3: apply JUST2. trivial. trivial. }
         assert (BI : binary_intersection phi1 phi2 = Some (merge_specs phi1 (Some phi2))).
         { apply merge_specs_succeed. apply (HContexts i); auto.
           apply ExternalInfo_cc in SF1. rewrite <- SF1. 
           apply ExternalInfo_cc in SF2. trivial. }
         eapply (externalInfo_binary_intersection). apply SF1. apply SF2. apply BI.
    * (*i in G1 but not in G2*)
      apply find_id_In_map_fst in Heqq1. apply Comp_G_elim in Heqq1. destruct Heqq1 as [[HE EF1] | [HE [INT1 IF1]]].
      ++ destruct EF1 as [ef [tys [rt [cc EF1]]]]. unfold fundef in *. rewrite FD1 in EF1; inv EF1.
         remember (find_id i funs2) as w2; symmetry in Heqw2; destruct w2.
         -- destruct f.
            ** clear - c2 HE Externs1_Hyp Heqw2. elim (list_disjoint_notin i Externs1_Hyp HE).
               apply IntIDs_i in Heqw2; trivial.
            ** specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch.
               rewrite Functions_preserved in H. inv H. simpl.
               eapply ExternalInfo_envs_sub. 3: apply JUST1. trivial. trivial.
         -- clear FundefsMatch. rewrite Functions_preserved in H. inv H. simpl.
            eapply ExternalInfo_envs_sub. 3: apply JUST1. trivial. trivial.
      ++ destruct IF1 as [f IF1]. unfold fundef in *. rewrite FD1 in IF1; inv IF1.
         remember (find_id i funs2) as w2; symmetry in Heqw2; destruct w2.
         -- destruct f0.
            ** specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch. 
               rewrite Functions_preserved in H. inv H. 
               assert (SF1: semaxfunc_InternalInfo cs (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2)) ge i f0 (merge_specs phi1 None)).
               { eapply InternalInfo_subsumption.
                 4: apply (InternalInfo_envs_sub CS1 ge1); trivial; apply JUST1.
                 trivial. trivial. apply Comp_ctx_LNR. }
               apply SF1. 
            ** specialize (FundefsMatch _ _ (eq_refl _) (eq_refl _)). simpl in FundefsMatch. 
               destruct FundefsMatch as [SIGs [psi2 PSI2]].
               rewrite Functions_preserved in H. inv H. simpl.
               assert (SF1: semaxfunc_InternalInfo cs (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2)) ge i f phi1).
               { eapply InternalInfo_subsumption.
                 4: apply (InternalInfo_envs_sub CS1 ge1); trivial; apply JUST1.
                 trivial. trivial. apply Comp_ctx_LNR. }
               apply SF1. (*idential to previous case...*)
          -- clear FundefsMatch Heqw2.
             rewrite Functions_preserved in H. inv H. simpl. 
              assert (SF1: semaxfunc_InternalInfo cs (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2)) ge i f phi1).
              { eapply InternalInfo_subsumption.
                4: apply (InternalInfo_envs_sub CS1 ge1); trivial; apply JUST1.
                trivial. trivial. apply Comp_ctx_LNR. }
              apply SF1.
   - (*i in G2 but not in G1 -- symmetric*) 
      specialize (JUST2 i). specialize (JUST1 i). rewrite H0 in JUST2.
      apply find_id_In_map_fst in H0. apply Comp_G_elim in H0. destruct H0 as [[HE EF2] | [HE [INT2 IF2]]].
      ++ destruct EF2 as [ef [tys [rt [cc EF2]]]]. specialize (JUST2 _ _ EF2 (eq_refl _)).
         remember (find_id i funs1) as w1; symmetry in Heqw1; destruct w1.
         -- destruct f.
            ** clear - c1 HE Externs2_Hyp Heqw1. elim (list_disjoint_notin i Externs2_Hyp HE). 
               apply IntIDs_i in Heqw1; trivial.
            ** unfold fundef in *.  rewrite EF2 in FundefsMatch, Functions_preserved. 
               specialize (FundefsMatch _ _ Heqw1 (eq_refl _)). simpl in FundefsMatch. inv FundefsMatch.
               rewrite Functions_preserved in H. inv H. simpl.
               eapply ExternalInfo_envs_sub. 3: apply JUST2. trivial. trivial.
         -- clear FundefsMatch. rewrite EF2 in Functions_preserved. rewrite Functions_preserved in H. inv H. simpl.
            eapply ExternalInfo_envs_sub. 3: apply JUST2. trivial. trivial.
      ++ destruct IF2 as [f IF2]. rewrite IF2 in *. specialize (JUST2 _ _ (eq_refl _) (eq_refl _)).
         remember (find_id i funs1) as w1; symmetry in Heqw1; destruct w1.
         -- destruct f0.
            ** specialize (FundefsMatch _ _ Heqw1 IF2). simpl in FundefsMatch. inv FundefsMatch. 
               rewrite Functions_preserved in H. inv H. 
               assert (SF2: semaxfunc_InternalInfo cs (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2)) ge i f phi).
               { eapply InternalInfo_subsumption.
                 4: apply (InternalInfo_envs_sub CS2 ge2); trivial; apply JUST2.
                 trivial. trivial. apply Comp_ctx_LNR. }
               apply SF2. 
            ** specialize (FundefsMatch _ _ Heqw1 IF2). simpl in FundefsMatch. 
               destruct FundefsMatch as [SIGs [psi2 PSI2]].
               rewrite Functions_preserved in H. inv H. simpl.
               assert (SF2: semaxfunc_InternalInfo cs (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2)) ge i f phi).
               { eapply InternalInfo_subsumption.
                 4: apply (InternalInfo_envs_sub CS2 ge2); trivial; apply JUST2.
                 trivial. trivial. apply Comp_ctx_LNR. }
               apply SF2. (*idential to previous case...*)
          -- clear FundefsMatch Heqw1.
             rewrite Functions_preserved in H. inv H. simpl. 
              assert (SF2: semaxfunc_InternalInfo cs (*(V1 ++ V2)*)V (Imports ++ G_merge (Comp_G c1) (Comp_G c2)) ge i f phi).
               { eapply InternalInfo_subsumption.
                 4: apply (InternalInfo_envs_sub CS2 ge2); trivial; apply JUST2.
                 trivial. trivial. apply Comp_ctx_LNR. }
               apply SF2.

+ (*TODO: clean up this proof*)
  intros i phi Hi. subst Exports G.
  specialize (G_merge_find_id_Some Hi (Comp_Exports_LNR c2)); clear Hi; intros Hi.
  specialize (Functions_preserved i).
  remember (find_id i (Comp_G c1)) as u1; symmetry in Hequ1; destruct u1 as [phi1 |].
  - remember (find_id i (Comp_G c2)) as u2; symmetry in Hequ2; destruct u2 as [phi2 |]. 
    * assert (SigsPhi: funsig_of_funspec phi1 = funsig_of_funspec phi2).
      { clear - Hequ1 Hequ2 HContexts. apply (HContexts i phi1 phi2); trivial. }
      exploit (Calling_conventions_match i phi1 phi2); trivial. intros CCPhi.

      destruct (G_merge_find_id_SomeSome Hequ1 Hequ2 SigsPhi CCPhi) as [phi' [BI' PHI']].
      rewrite PHI'. exists phi'; split. trivial. clear PHI'.
      apply binaryintersection_sub in BI'; destruct BI' as [Phi1' Phi2'].
      remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
      ++ subst phi. destruct (Comp_G_Exports c1 _ _ Heqq1) as [tau1 [Tau1 TAU1]].
         rewrite Hequ1 in Tau1; inv Tau1.
         remember (find_id i Exports2) as q2; symmetry in Heqq2; destruct q2 as [psi2 |].

         2: solve [simpl; apply funspec_sub_trans with tau1; trivial ].

         destruct (Comp_G_Exports c2 _ _ Heqq2) as [tau2 [Tau2 TAU2]].
         rewrite Hequ2 in Tau2; inv Tau2.

         assert (SigsPsi: funsig_of_funspec psi1 = funsig_of_funspec psi2).
         { clear - SigsPhi TAU1 TAU2. destruct tau1; destruct tau2.
           destruct psi1; destruct TAU1 as [AA1 _].
           destruct psi2; destruct TAU2 as [AA2 _]. subst. simpl in *; trivial. }
         assert (CCPsi: callingconvention_of_funspec psi1 = callingconvention_of_funspec psi2).
         { clear - CCPhi TAU1 TAU2. apply funspec_sub_cc in TAU1. apply funspec_sub_cc in TAU2. 
           rewrite <- TAU1, <- TAU2; trivial. }
         destruct (G_merge_find_id_SomeSome Heqq1 Heqq2 SigsPsi CCPsi) as [tau' [BI TAU']].
         simpl. rewrite BI. clear - BI Phi1' Phi2' TAU1 TAU2.
         apply (BINARY_intersection_sub3 _ _ _ BI); clear BI.
         apply funspec_sub_trans with tau1; trivial.
         apply funspec_sub_trans with tau2; trivial.
      ++ destruct (Comp_G_Exports c2 _ _ Hi) as [tau2 [Tau2 TAU2]].
         rewrite Hequ2 in Tau2; inv Tau2.
         apply funspec_sub_trans with tau2; trivial.

    * rewrite (G_merge_find_id_SomeNone Hequ1 Hequ2).
      remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
      ++ subst.  eexists; split. reflexivity.
         destruct (Comp_G_Exports c1 _ _ Heqq1) as [psi [Psi PSI]]. rewrite Hequ1 in Psi. inv Psi.
         eapply funspec_sub_trans. apply PSI.
         clear - Heqq1 Hequ2 c2. remember (find_id i Exports2) as w; symmetry in Heqw; destruct w as [psi2 |].
         -- destruct (Comp_G_Exports c2 _ _ Heqw) as [phi2 [? ?]]. congruence.
         -- simpl. apply funspec_sub_refl.
      ++ eexists; split. reflexivity.
         apply (Comp_G_Exports c2) in Hi. destruct Hi as [? [? _]]. congruence. 
  - remember (find_id i Exports1) as q1; symmetry in Heqq1; destruct q1 as [psi1 |].
    * destruct (Comp_G_Exports c1 _ _ Heqq1) as [psi [Psi PSI]]. congruence.
    * destruct (Comp_G_Exports c2 _ _ Hi) as [psi2 [Psi2 PSI2]].
      rewrite (G_merge_find_id_NoneSome Hequ1 Psi2).
      eexists; split. reflexivity. trivial. apply (Comp_G_LNR c2).
Qed.

End ComponentJoin.

Lemma make_tycontext_g_G_None V i: forall G, find_id i G = None ->
   (make_tycontext_g V G) ! i = find_id i V.
Proof. induction G; intros.
+ apply make_tycontext_g_nilG_find_id. 
+ simpl in H. destruct a as [j a]; simpl. rewrite PTree.gsspec.
  if_tac in H; subst. inv H. rewrite if_false; auto.
Qed.
 
Lemma SF_ctx_extensional {Espec cs} V G ge i fd phi (HSF:  @SF Espec cs V ge G i fd phi)
  (LNR_G: list_norepet (map fst G)) G' (GG': forall j, find_id j G = find_id j G'):
  @SF Espec cs V ge G' i fd phi.
Proof.
  destruct fd; simpl; [ | apply HSF].
  eapply InternalInfo_subsumption; [ | | eassumption | eassumption].
  + intros j; red. remember ((make_tycontext_g V G) ! j) as q; destruct q; simpl; trivial.
    symmetry in Heqq. 
    specialize (make_tycontext_s_g V G j). 
    specialize (make_tycontext_s_g V G' j).
    rewrite 2 make_tycontext_s_find_id, GG'. intros.
    remember (find_id j G') as w; destruct w.
    * rewrite (H _ (eq_refl _)). rewrite (H0 _ (eq_refl _)) in Heqq; trivial.
    * clear H H0; symmetry in Heqw. specialize (GG' j); rewrite Heqw in GG'.
      rewrite make_tycontext_g_G_None by trivial. 
      rewrite make_tycontext_g_G_None in Heqq; trivial.
  + intros j; rewrite GG'. apply subsumespec_refl.
Qed.

Record CanonicalComponent {Espec V cs ge} Externs Imports funs Exports := {
  CC_component :> @Component Espec V(*(mk_varspecs' p)*) cs(*make _compspecs p)*) ge Externs Imports funs Exports;
  CC_canonical: map fst (Comp_G CC_component) = 
                map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs funs ++ map fst Externs))
                        funs)
}.

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

Lemma C_to_CC {Espec V cs ge Ext Imp funs Exp} (c: @Component Espec V cs ge Ext Imp funs Exp):
      @CanonicalComponent Espec V cs ge Ext Imp funs Exp.
Proof.
  remember (order (Comp_G c) 
                  (map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs funs ++ (map fst Ext))) funs))) as Gopt.
  destruct Gopt as [G |]; symmetry in HeqGopt.
+ specialize (LNR_Internals_Externs c); intros LNR_IEc.
  assert (X6: forall i : ident, In i (IntIDs funs ++ map fst Ext) <-> In i (map fst G)).
  { intros. rewrite <- (order_dom HeqGopt).
(*    remember (prog_defs p) as l.*) remember (IntIDs funs ++ map fst Ext) as l'.
    assert (forall j, In j l' -> In j (map fst funs)).
    { subst. clear -c. intros. apply c in H. destruct (@Comp_G_in_progdefs _ _ _ _ _ _ _ _ c j H).
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
      exists f ts t cc,
        find_id i funs = Some (External f ts t cc)) by apply c.

  assert (X2: list_norepet (map fst funs)) by apply c.
  assert (X3: list_norepet (map fst (Ext ++ Imp))) by apply c.

  assert (X4: list_norepet (map fst Exp)) by apply c.
  assert (X5: forall i, In i (map fst Ext) -> exists f ts t cc,
    find_id i funs = Some (External f ts t cc)) by apply c.

  assert (X9: forall i phi fd,
    find_id i funs = Some fd -> find_id i G = Some phi -> 
   @SF Espec cs V ge (Imp ++ G) i fd phi).
  { intros.
    eapply SF_ctx_extensional. 
    rewrite <- Y in H0; apply (Comp_G_justified c _ phi _ H H0).
    apply Comp_ctx_LNR.
    intros j. rewrite 2 find_id_app_char, Y; trivial. }

  assert (X10: forall i phi, find_id i Exp = Some phi -> 
          exists phi', find_id i G = Some phi' /\ funspec_sub phi' phi).
  { intros. destruct (Comp_G_Exports c _ _ H) as [phi' [Phi' SUB]].
    exists phi'; split; trivial. rewrite <- (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply c.
    intros. rewrite (order_dom HeqGopt). apply X6. apply c. trivial. }

  remember (@Build_Component Espec V cs ge Ext Imp funs Exp X1 X2 X3 X4 X5 G X6 X7 X8 X9 X10) as cc.

  apply Build_CanonicalComponent with cc.
  subst cc; simpl. symmetry; apply (order_dom HeqGopt).
+ apply order_i' in HeqGopt. contradiction. apply c.
  clear - c. intros.
  apply Comp_G_dom. apply in_map_iff in H. destruct H as [[j d] [J HJ]]. simpl in J; subst.
  apply filter_In in HJ; simpl in HJ; destruct HJ.
  destruct (in_dec ident_eq i (IntIDs funs ++ map fst Ext)). trivial. inv H0.
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

Lemma semaxfunc_sound {Espec cs V G ge funs G'} (SF: @semaxfunc Espec cs V G ge funs G'):
  @semax_func Espec V G cs ge funs G'.
Proof.
  induction SF.
+ apply semax_func_nil.
+ destruct H as [b Hb]; destruct phi. eapply semax_func_cons; try eapply Hb; trivial.
  rewrite H0; simpl; eapply Hb.
+ destruct phi; destruct f. destruct H as [ids [rt [ID [RT H]]]]; subst.
  eapply semax_func_cons_ext; try eapply H; trivial. 
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
  apply id_in_list_false_i in H2.
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

Lemma Canonical_semaxfunc {Espec V cs ge E} funs Exp
      (c: @CanonicalComponent Espec V cs ge E nil funs Exp):
   semaxfunc V (Comp_G c) ge
             (filter (fun x => in_dec ident_eq (fst x) (IntIDs funs ++ map fst E)) 
                     funs )
             (Comp_G c).
Proof.
  specialize (Comp_G_justified c); intros. destruct c as [c DOM].
  simpl in *.
  assert (LNRp:=Comp_funs_LNR c).
  apply SF_semaxfunc.
+ intros. apply find_id_filter_Some in H0; trivial.
  destruct H0. apply H; trivial.
+ apply list_norepet_map_fst_filter; trivial.
+ rewrite DOM; trivial.
Qed.

Lemma filter_true {A f}: forall (l:list A) (Hf: forall i, In i l -> f i=true),
      filter f l = l.
Proof.
  induction l; simpl; intros; auto. rewrite (Hf a).
  rewrite IHl; trivial. intros. apply Hf. right; trivial. left; trivial.
Qed.

Lemma Canonical_semax_func {Espec V cs ge E funs Exp}
      (c: @CanonicalComponent Espec V cs ge E nil funs Exp)
      (HE: map fst E =
           map fst (filter (fun x  => negb (in_dec ident_eq (fst x) (IntIDs funs))) funs)):
      @semax_func Espec V (Comp_G c) cs ge funs (Comp_G c).
Proof. 
  apply semaxfunc_sound.
  specialize (Canonical_semaxfunc _ _ c).
  rewrite filter_true; trivial.
  rewrite HE; clear -c; intros. 
  destruct (in_dec ident_eq (fst i)
    (IntIDs funs ++ map fst (filter (fun x : positive * fundef => negb (in_dec ident_eq (fst x) (IntIDs funs))) funs))); simpl; trivial.
  elim n; clear n. destruct i as [i d]; simpl.
  apply in_or_app. destruct d.
  + left. unfold IntIDs. apply in_map_iff. exists (i, Internal f); simpl; split; trivial.
    apply filter_In. simpl; split; trivial.
  + right. apply in_map_iff. exists (i, External e t t0 c0); simpl; split; trivial.
    apply filter_In. simpl; split; trivial.
    destruct (in_dec ident_eq i (IntIDs funs)); simpl; trivial.
    apply IntIDs_elim in i0. destruct i0.
    specialize (Comp_funs_LNR c); intros. 
    specialize (@list_norepet_In_In _ _ _ _ _ _ H1 H H0). congruence. 
Qed.

Lemma Canonical_PROG {Espec cs V E} (p:Clight.program) Exp
      (c: @CanonicalComponent Espec V cs (Genv.globalenv p) E nil (prog_funct p) Exp)
       (HE : map fst E = map fst (filter (fun x => negb (in_dec ident_eq (fst x) (IntIDs (prog_funct p)))) (prog_funct p)))

      (LNR_Names: compute_list_norepet (prog_defs_names p) = true)
      (ALGN: all_initializers_aligned p)
      (HCS: cenv_cs = prog_comp_env p)
      (HV: match_globvars (prog_vars p) V = true) MainPost
      (Main: find_id (prog_main p) (Comp_G c) = Some (main_spec' p MainPost)):
      @semax_prog Espec cs p V (Comp_G c).
Proof.
  red. rewrite Main. intuition.
  apply  Canonical_semax_func; trivial.
  eexists; reflexivity.
Qed.

Lemma Canonical_PROG_ext {Espec cs V E} (p:Clight.program) Exp
      (c: @CanonicalComponent Espec V cs (Genv.globalenv p) E nil (prog_funct p) Exp)
       (HE : map fst E = map fst (filter (fun x => negb (in_dec ident_eq (fst x) (IntIDs (prog_funct p)))) (prog_funct p)))

      (LNR_Names: compute_list_norepet (prog_defs_names p) = true)
      (ALGN: all_initializers_aligned p)
      (HCS: cenv_cs = prog_comp_env p)
      (HV: match_globvars (prog_vars p) V = true) ora MainPost
      (Main: find_id (prog_main p) (Comp_G c) = Some (main_spec_ext' p ora MainPost)):
      @semax_prog_ext Espec cs p ora V (Comp_G c).
Proof.
  red. rewrite Main. intuition.
  apply  Canonical_semax_func; trivial.
  eexists; reflexivity.
Qed.

Definition semax_OPTprog {Espec V cs} (prog: Clight.program) (G: funspecs) : Prop :=
exists funs,
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
cenv_cs = prog_comp_env prog /\
@semax_func Espec V G cs (Genv.globalenv prog) funs G /\
match_globvars (prog_vars prog) V = true /\
match find_id prog.(prog_main) G with
| Some s => exists post, s = main_spec' prog post
| None => False
end /\
forall i fd, find_id i funs = Some fd -> find_id i (prog_funct prog) = Some fd.

Lemma Canonical_OPTPROG {Espec cs V E} (p:Clight.program) Exp funs
      (c: @CanonicalComponent Espec V cs (Genv.globalenv p) E nil funs Exp)
       (HE : map fst E = map fst (filter (fun x => negb (in_dec ident_eq (fst x) (IntIDs (prog_funct p)))) funs))

      (LNR_Names: compute_list_norepet (prog_defs_names p) = true)
      (ALGN: all_initializers_aligned p)
      (HCS: cenv_cs = prog_comp_env p)
      (HV: match_globvars (prog_vars p) V = true) MainPost
      (Main: find_id (prog_main p) (Comp_G c) = Some (main_spec' p MainPost))
      (Funs: forall i fd, find_id i funs = Some fd -> find_id i (prog_funct p) = Some fd):
      @semax_OPTprog Espec V cs p (Comp_G c).
Proof.
  red. exists funs. rewrite Main. intuition.
  apply  Canonical_semax_func; trivial.
  { rewrite HE. f_equal. apply filter_fg; intros.
    destruct x as [i d]; simpl. apply find_id_i in H; [ specialize (Funs _ _ H) | apply c].
    f_equal. destruct (in_dec ident_eq i (IntIDs (prog_funct p))); destruct (in_dec ident_eq i (IntIDs funs)); trivial; simpl.
    + elim n; clear - i0 H Funs LNR_Names. unfold prog_defs_names in LNR_Names. 
      apply compute_list_norepet_e in LNR_Names.
      destruct (IntIDs_e i0) as [f Hf].
      - eapply sublist_norepet. 2: apply LNR_Names.
        unfold prog_funct. destruct p; simpl. clear. induction prog_defs; simpl. constructor.
        destruct a. destruct g; simpl; constructor; trivial.
      - unfold fundef in *. rewrite Funs in Hf. inv Hf.
        eapply IntIDs_i. eassumption.
    + elim n; clear - i0 H Funs c.
      destruct (IntIDs_e i0) as [f Hf].
      - apply (Comp_funs_LNR c).
      - unfold fundef in *. rewrite H in Hf. inv Hf.
        eapply IntIDs_i. eassumption. }
  eexists; reflexivity.
Qed.
(*
Definition semax_OPTprog_ext {Espec V cs} (ora:OK_ty) (prog: Clight.program) (G: funspecs) : Prop :=
exists funs,
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
cenv_cs = prog_comp_env prog /\
@semax_func Espec V G cs (Genv.globalenv prog) funs G /\
match_globvars (prog_vars prog) V = true /\
match find_id prog.(prog_main) G with
| Some s => exists post, s = main_spec_ext' prog ora post
| None => False
end /\
forall i fd, find_id i funs = Some fd -> find_id i (prog_funct prog) = Some fd.

(*yields Anomaly "grounding a non evar-free term" Please report at http://coq.inria.fr/bugs/.*)*)
