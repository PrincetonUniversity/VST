Require Import VST.floyd.proofauto.
Require Import VST.floyd.assoclists.
Require Import VST.floyd.VSU.
(*Require Import verif_core.
Require Import main.*)
Require Import VST.veric.initial_world.

Definition ExtIDs (p: Ctypes.program function): list ident := 
  map fst ((filter (fun x => negb (isInternal (snd x)))) (prog_defs p)).

Lemma find_id_delete_id {A} {lp p: list (ident *A)} {i j a} (IJ: i <> j):
       delete_id j lp = Some (a, p) -> find_id i lp = find_id i p.
Proof. intros. apply  delete_id_elim in H. destruct H. rewrite <- (firstn_skipn x p); subst.
rewrite 2 find_id_app_char; simpl. rewrite if_false; trivial.
Qed.
 
Lemma find_id_delete_id2 {A i} {lp: list (ident *A)}: forall {p j a},
      delete_id j lp = Some (a, p) -> list_norepet (map fst lp) ->
      find_id i lp =  if ident_eq i j then Some a else find_id i p.
Proof. induction lp; simpl; intros. inv H. inv H0.
destruct a as [k a]. if_tac; subst; simpl in *.
+ if_tac; subst.
  - rewrite if_true in H;[ inv H |]; trivial.
  - rewrite if_false in H by intuition.
    remember (delete_id j lp) as u; symmetry in Hequ; destruct u; try discriminate. 
    destruct p0. inv H; simpl. rewrite if_true; trivial.
+ if_tac; subst.
  - rewrite if_false in H by trivial.
    remember (delete_id j lp) as u; symmetry in Hequ; destruct u; try discriminate. 
    destruct p0. inv H. specialize (IHlp _ _ _ Hequ H4). rewrite if_true in IHlp; trivial.
  - if_tac in H. inv H; trivial.
    remember (delete_id j lp) as u; symmetry in Hequ; destruct u; try discriminate. 
    destruct p0. inv H. simpl. rewrite if_false by trivial. 
    specialize (IHlp _ _ _ Hequ H4). rewrite if_false in IHlp; trivial.
Qed.

(*Definition main_spec main p:=
 DECLARE main
 WITH gv: globals
 PRE [ ] main_pre p tt gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).*)
(*
Definition main_spec main p:=
  DECLARE main (main_spec_ext p tt).*)

Section ADD_MAIN.
Variable Espec: OracleKind.
Variable coreV: varspecs.
Variable coreCS: compspecs.
Variable coreE: funspecs.
Notation coreImports:= (@nil (ident * funspec)). (*nil - we're only linking main if this yields a full prog*)
Variable p: Clight.program.
Variable coreExports: funspecs.
Variable CoreVSU: @CanonicalVSU Espec coreV coreCS coreE coreImports p coreExports.

Variable lp: Clight.program.
Variable CS: compspecs.
Variable CSSUB: cspecs_sub coreCS CS.
Variable main:ident.
Variable mainspec: funspec.

Variable mainFun : function.

Variable MainFresh : find_id main (prog_defs p) = None.
Variable P_LP: delete_id main (prog_funct lp) = Some (Internal mainFun, prog_funct p).

Variable LNR_LP : list_norepet (map fst (prog_defs lp)).

Definition LNR_Funs:= LNR_progdefs_progfunct LNR_LP.
Lemma Main i: 
      find_id i (prog_funct lp) = 
      if ident_eq i main then Some (Internal mainFun)
                         else find_id i (prog_funct p).
Proof. apply find_id_delete_id2; [trivial | apply LNR_Funs]. Qed. 

Definition CoreG := G_of_CanonicalVSU CoreVSU.

Definition linked_internal_specs :=
  SortFunspec.sort
         (filter (fun a => in_dec ident_eq (fst a) (IntIDs lp)) ((*main_spec main lp*)(main,mainspec) :: CoreG)).

Variable Vprog: varspecs.
Variable LNR_Vprog: list_norepet (map fst Vprog).
Variable disjoint_Vprog_lpfuns: list_disjoint (map fst Vprog) (map fst (prog_funct lp)).
Variable coreV_in_Vprog: forall {i phi}, find_id i coreV = Some phi -> find_id i Vprog = Some phi. 

Variable LNR_coreV: list_norepet (map fst coreV).

Variable MainE : list (ident * funspec).
Variable LNR_MainE : list_norepet (map fst MainE).

Variable HypME1: forall i, In i (map fst MainE) -> exists ef ts t cc,
           find_id i (prog_defs lp) = Some (Gfun (External ef ts t cc))(* /\
           We expect the following conjunct will always hold, but we only need it
           for find_id i CoreG = None so put it in hypothesis MainE_vacuous below:
           ef_sig ef = {| sig_args := typlist_of_typelist ts;
                          sig_res := opttyp_of_type t;
                          sig_cc := cc_of_fundef (External ef ts t cc) |}*).
  
Lemma Disj_internalspecs_MainE: list_disjoint (map fst linked_internal_specs) (map fst MainE).
Proof.
     intros x y X Y. destruct (HypME1 _ Y) as [f [tys [ts [cc EXT]]]]; clear HypME1.
     unfold linked_internal_specs in X. apply sort_In_map_fst_e in X.
     apply In_map_fst_filter2 in X; destruct X as [INT _].
     apply IntIDs_e in INT; [ destruct INT; congruence | trivial].
Qed.

Definition Gprog := linked_internal_specs ++ MainE.


Lemma IntIDsMainE_Gprog i: In i (IntIDs lp ++ map fst MainE) -> In i (map fst Gprog).
Proof. 
  intros. unfold Gprog. (*apply sort_In_map_fst_i.*)
  rewrite map_app. apply in_or_app. apply in_app_or in H. destruct H; [ left | right; trivial].
  unfold linked_internal_specs. apply sort_In_map_fst_i. apply In_map_fst_filter; trivial. simpl.
  destruct (IntIDs_elim H) as [f Hf]. apply find_id_i in Hf; [| trivial].
  apply Fundef_of_Gfun in Hf. specialize (Main i). rewrite Hf; intros MainI.
  if_tac in MainI. 
  + subst; left; trivial.
  + right.
    unfold CoreG; simpl. destruct CoreVSU. simpl. 
    apply (Comp_G_dom c). apply in_or_app; left.
    eapply IntIDs_i. apply Gfun_of_Fundef. rewrite <- MainI. reflexivity.
    apply c.
Qed.

Lemma Gprog_IntIDsMainE i: In i (map fst Gprog) -> In i (IntIDs lp ++ map fst MainE).
Proof. intros. unfold Gprog in H. rewrite map_app in H.
    apply in_or_app. apply in_app_or in H. destruct H; [ | right; trivial].
    unfold linked_internal_specs in H. apply sort_In_map_fst_e in H.
    apply In_map_fst_filter2 in H. left; apply H.
Qed.

Lemma LNR_main_CoreG: list_norepet (main :: map fst CoreG).
Proof.
  constructor.
  unfold CoreG.
+ destruct CoreVSU; simpl. intros N. rewrite <- (Comp_G_dom c) in N.
  apply in_app_or in N; destruct N as [N | N]. 
  apply IntIDs_e in N; [ destruct N | ]. (* apply Fundef_of_Gfun in H. *)congruence. apply c.
  destruct (Comp_Externs c _ N) as [ef [tys [ts [cc H]]]]. (*apply Fundef_of_Gfun in H.*) congruence.
+ apply LNR_G_of_CanoncialVSU.
Qed.

Lemma LNR_internalspecs: list_norepet (map fst linked_internal_specs).
Proof. clear LNR_MainE HypME1 MainE. unfold linked_internal_specs.
     apply LNR_sort_i. apply list_norepet_map_fst_filter. apply LNR_main_CoreG.
Qed.

Lemma LNR_Gprog: list_norepet (map fst Gprog).
Proof. unfold Gprog. rewrite map_app. apply list_norepet_append; trivial.
   - apply LNR_internalspecs.
   - apply Disj_internalspecs_MainE.
Qed.

Variable coreE_in_MainE: forall {i phi}, find_id i coreE = Some phi -> find_id i MainE = Some phi.

Lemma LNR_coreV_coreG: list_norepet (map fst coreV ++ map fst CoreG).
Proof.
apply list_norepet_append; trivial. 
apply LNR_G_of_CanoncialVSU.
eapply list_disjoint_mono.
- apply disjoint_Vprog_lpfuns.
- remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'. 
  intros. apply (Comp_G_in_Fundefs COMP) in H. destruct H as [f Hf]. 
  eapply find_id_In_map_fst. rewrite Main, if_false. apply Hf. clear - Hf MainFresh COMP.
  apply Gfun_of_Fundef in Hf. intros N; subst. congruence. apply COMP.
- intros. apply In_map_fst_find_id in H. destruct H as [t Ht].
  apply coreV_in_Vprog in Ht. apply find_id_In_map_fst in Ht. trivial.
  apply LNR_coreV.
Qed.

Lemma disjoint_Vprog_Gprog: list_disjoint (map fst Vprog) (map fst Gprog).
Proof. unfold Gprog. rewrite map_app. apply list_disjoint_app_R.
+ unfold linked_internal_specs. intros x y X Y ?; subst.
  apply sort_In_map_fst_e in Y. apply In_map_fst_filter2 in Y; destruct Y.
  apply IntIDs_e in H; [ destruct H as [f Hf] | trivial].
  apply Fundef_of_Gfun in Hf. apply find_id_In_map_fst in Hf.  apply (disjoint_Vprog_lpfuns y y); trivial.
+ intros x y X Y ?; subst. destruct (HypME1 _ Y) as [ef [ts [t [cc Hf]]]].
  apply Fundef_of_Gfun in Hf. apply find_id_In_map_fst in Hf.  apply (disjoint_Vprog_lpfuns y y); trivial.
Qed.

Lemma LNR_Vprog_Gprog: list_norepet (map fst Vprog ++ map fst Gprog).
Proof. apply list_norepet_app; split3.
  apply LNR_Vprog.
  apply LNR_Gprog.
  apply disjoint_Vprog_Gprog.
Qed.

Lemma Gprog_main: find_id main Gprog = Some (snd (*(main_spec main lp)*)(main,mainspec)).
Proof.
  specialize (Main main).
  unfold Gprog, linked_internal_specs.
  rewrite find_id_app_char, <- sort_find_id, filter_cons,
          find_id_app_char, find_id_filter_char.
  try destruct mainspec as [main phi]; simpl in *.
+ clear - LNR_LP mainFun P_LP. rewrite 2 if_true by trivial.
  intros MainI.
  destruct (in_dec ident_eq main (IntIDs lp)); simpl; trivial.
  elim n. eapply IntIDs_i.
  apply Gfun_of_Fundef. apply MainI. trivial.
+ simpl. constructor. auto. constructor.
+ apply LNR_sort_e. apply LNR_internalspecs.
Qed.

Lemma IntIDs_preserved i: In i (IntIDs p) -> In i (IntIDs lp).
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'. 
  destruct (Comp_G_dom COMP i) as [_ HH]. clear - mainFun  P_LP HH MainFresh LNR_LP COMP. specialize (Main i); intros MainI.
  intros. if_tac in MainI; subst; apply IntIDs_e in H; try apply COMP; destruct H; [ congruence |].
  apply Fundef_of_Gfun in H. rewrite <- MainI in H.
  apply Gfun_of_Fundef in H; trivial. apply IntIDs_i in H; trivial.
Qed.

Lemma IntIDs_lp i: In i (IntIDs lp) -> i=main \/ In i (IntIDs p).
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  clear - mainFun  P_LP COMP LNR_LP. intros. destruct (IntIDs_e H LNR_LP) as [f Hf]. apply Fundef_of_Gfun in Hf.
  specialize (Main i). rewrite Hf; intros MainI. if_tac in MainI; [ left; trivial | right].
  symmetry in MainI. apply Gfun_of_Fundef in MainI; [ apply IntIDs_i in MainI; trivial | apply COMP].
Qed.

Lemma coreG_in_Gprog {i phi}: find_id i CoreG = Some phi -> find_id i Gprog = Some phi.
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  unfold Gprog, linked_internal_specs; intros. 
  destruct (Comp_G_dom COMP i) as [_ HH].
  rewrite find_id_app_char, <- sort_find_id, find_id_filter_char.
+ specialize IntIDs_preserved; intros Pres.
  simpl. rewrite if_false, H.
  - exploit HH; clear HH. eapply find_id_In_map_fst; apply H.
    intros K. apply in_app_or in K; destruct K.
    * apply Pres in H0. destruct  (in_dec ident_eq i (IntIDs lp)); simpl; trivial. contradiction.
    * destruct (in_dec ident_eq i (IntIDs lp)); simpl; trivial. 
      rewrite <- (Comp_G_E COMP i H0) in H. apply coreE_in_MainE; trivial.
  - intros M; subst main. destruct (@Comp_G_in_progdefs' _ _ _ _ _ _ _ _ COMP i phi H). congruence.
+ apply LNR_main_CoreG.
+ apply LNR_sort_e; apply LNR_internalspecs.
Qed.

Lemma LNR_coreExports: list_norepet (map fst coreExports).
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  apply (Comp_Exports_LNR COMP).
Qed.

Lemma LNR_coreExports': list_norepet (main::map fst coreExports).
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  constructor.
+ intros N.
  apply (Comp_Exports_in_progdefs COMP) in N. apply find_id_None_iff in MainFresh. contradiction.
+ apply (Comp_Exports_LNR COMP).
Qed.

Lemma subsumespec_coreExports_Gprog i: subsumespec (find_id i coreExports) (find_id i Gprog).
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  red. remember (find_id i coreExports) as w; symmetry in Heqw; destruct w; trivial.
  destruct (Comp_G_Exports COMP _ _ Heqw) as [phi [Phi PHI]].
  exists phi; split. apply (coreG_in_Gprog Phi).
  apply seplog.funspec_sub_sub_si. apply PHI. 
Qed.
 
Lemma subsumespec_coreExports_Gprog' i: subsumespec (find_id i ((*main_spec main lp*)(main,mainspec)::coreExports)) (find_id i Gprog).
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  red. simpl. if_tac.
  + subst i. rewrite Gprog_main. eexists; split. reflexivity. apply funspec_sub_si_refl.
  + remember (find_id i coreExports) as w; symmetry in Heqw; destruct w; trivial.
    destruct (Comp_G_Exports COMP _ _ Heqw) as [phi [Phi PHI]].
    exists phi; split. apply (coreG_in_Gprog Phi).
    apply seplog.funspec_sub_sub_si. apply PHI. 
Qed.

Lemma coreExports_in_Gprog i: sub_option (make_tycontext_g Vprog coreExports) ! i (make_tycontext_g Vprog Gprog) ! i.
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  red. rewrite 2 semax_prog.make_context_g_char; try apply LNR_Vprog_Gprog.
  + rewrite 2 make_tycontext_s_find_id.
    remember (find_id i coreExports) as w; symmetry in Heqw; destruct w.
    - destruct (Comp_G_Exports COMP _ _ Heqw) as [phi [ Phi PHI]].
      rewrite (coreG_in_Gprog Phi), (type_of_funspec_sub _ _ PHI); trivial.
    - remember (find_id i Vprog) as u; symmetry in Hequ; destruct u; trivial.
      rewrite (list_norepet_find_id_app_exclusive1 LNR_Vprog_Gprog Hequ); trivial.
  + specialize LNR_coreExports; intros LNR_EXP.
    apply list_norepet_append; trivial.
    eapply list_disjoint_mono; [ apply disjoint_Vprog_Gprog | | ]; trivial.
    intros. apply In_map_fst_find_id in H; trivial.
    destruct H as [f Hf]. destruct ( Comp_G_Exports COMP _ _ Hf) as [phi [Phi _]].
    apply coreG_in_Gprog in Phi. apply find_id_In_map_fst in Phi; trivial.
Qed.

Lemma coreExports_in_Gprog' i: sub_option (make_tycontext_g Vprog ((*main_spec main lp*)(main,mainspec)::coreExports)) ! i (make_tycontext_g Vprog Gprog) ! i.
Proof.
  remember  CoreVSU as VSU'. destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  red. rewrite 2 semax_prog.make_context_g_char; try apply LNR_Vprog_Gprog.
  + rewrite 2 make_tycontext_s_find_id. simpl. if_tac.
    { (*main*) subst i. rewrite Gprog_main. reflexivity. }
    remember (find_id i coreExports) as w; symmetry in Heqw; destruct w.
    - destruct (Comp_G_Exports COMP _ _ Heqw) as [phi [ Phi PHI]].
      rewrite (coreG_in_Gprog Phi), (type_of_funspec_sub _ _ PHI); trivial.
    - remember (find_id i Vprog) as u; symmetry in Hequ; destruct u; trivial.
      rewrite (list_norepet_find_id_app_exclusive1 LNR_Vprog_Gprog Hequ); trivial.
  + specialize LNR_coreExports'; intros LNR_EXP.
    apply list_norepet_append; trivial.
    eapply list_disjoint_mono; [ apply disjoint_Vprog_Gprog | | ]; trivial.
    intros. apply In_map_fst_find_id in H; trivial.
    destruct H as [f Hf]. simpl in Hf.
    if_tac in Hf.
    { subst x. apply (find_id_In_map_fst _ _ _ Gprog_main). }
    destruct ( Comp_G_Exports COMP _ _ Hf) as [phi [Phi _]].
    apply coreG_in_Gprog in Phi. apply find_id_In_map_fst in Phi; trivial.
Qed.
(*
Variable InternalInfo_main:
      semaxfunc_InternalInfo CS Vprog coreExports (Genv.globalenv lp) main mainFun (snd (main_spec main lp)).

Lemma InternalInfo_mainGprog:
      semaxfunc_InternalInfo CS Vprog Gprog (Genv.globalenv lp) main mainFun (snd (main_spec main lp)).
Proof.
eapply InternalInfo_subsumption. 4: apply InternalInfo_main.
apply coreExports_in_Gprog.
apply subsumespec_coreExports_Gprog.
apply LNR_coreExports. 
Qed. *)

Variable InternalInfo_main:
      semaxfunc_InternalInfo CS Vprog ((*main_spec main lp*)(main,mainspec)::coreExports) 
                             (Genv.globalenv lp) main mainFun (*(snd (main_spec main lp))*)mainspec.

Lemma InternalInfo_mainGprog:
      semaxfunc_InternalInfo CS Vprog Gprog (Genv.globalenv lp) main mainFun (*(snd (main_spec main lp))*)mainspec.
Proof.
eapply InternalInfo_subsumption. 4: apply InternalInfo_main.
apply coreExports_in_Gprog'.
apply subsumespec_coreExports_Gprog'.
apply LNR_coreExports'. 
Qed.
 (*
Variable MainE_vacuous: forall i phi, find_id i MainE = Some phi -> find_id i CoreG = None ->
         exists ef argsig retsig cc, 
           phi = vacuous_funspec (External ef argsig retsig cc) /\ 
           find_id i (prog_funct p) = Some (External ef argsig retsig cc) /\
           ef_sig ef = {| sig_args := typlist_of_typelist argsig;
                          sig_res := opttyp_of_type retsig;
                          sig_cc := cc_of_fundef (External ef argsig retsig cc) |}.*)

Variable MainE_vacuous: forall i phi, find_id i MainE = Some phi -> find_id i coreE = None ->
         exists ef argsig retsig cc, 
           phi = vacuous_funspec (External ef argsig retsig cc) /\ 
           find_id i (prog_funct p) = Some (External ef argsig retsig cc) /\
           ef_sig ef = {| sig_args := typlist_of_typelist argsig;
                          sig_res := opttyp_of_type retsig;
                          sig_cc := cc_of_fundef (External ef argsig retsig cc) |}.

Lemma add_main:
      @Component Espec Vprog CS
      MainE nil lp ((*main_spec main lp*)(main, mainspec)::nil(*Exports*)) Gprog.
Proof.
constructor; trivial.
+ contradiction.
+ rewrite app_nil_r; trivial.
+ constructor; [ auto | constructor].
(*+ clear - HypME1; intros.
  destruct (HypME1 _ H) as [ef [ts [t [cc [EF _]]]]]; clear HypME1.
  do 4 eexists; apply EF.*)
+ intros; split.
  - apply IntIDsMainE_Gprog.
  - apply Gprog_IntIDsMainE.
+ apply LNR_Gprog.
+ (*forall i, In i (map fst MainE) -> find_id i MainE = find_id i Gprog*)
  intros. destruct (HypME1 _ H) as [f [ts [t [cc EXT]]]].
  unfold Gprog. rewrite find_id_app_char.
  apply In_map_fst_find_id in H. destruct H as [phi Hi]; rewrite Hi.
  rewrite (list_disjoint_map_fst_find_id2  Disj_internalspecs_MainE i _ Hi); trivial.
  trivial.
+ specialize InternalInfo_mainGprog; intros IIG. 
  simpl. intros. 
  specialize (G_of_CanoncialVSU_justified CoreVSU); intros JUST.
  specialize (progfunct_GFF LNR_LP H); intros GFF.
  unfold Gprog, linked_internal_specs in H0.
  rewrite find_id_app_char, <- sort_find_id, find_id_filter_char in H0. simpl in H0.
  rewrite Main in H. remember  CoreVSU as VSU'.
  destruct VSU' as [G COMP]. assert (G = CoreG). unfold CoreG. rewrite <- HeqVSU'. reflexivity. subst G. clear HeqVSU'.
  assert (MainI := Main i). if_tac in H.
  - (*i=main*) subst; rewrite if_true in H0 by trivial.
    clear JUST MainE_vacuous. inv H.
    destruct (in_dec ident_eq main (IntIDs lp)); [ simpl in H0; inv H0 | elim n; clear - MainI LNR_LP].
    2: apply Gfun_of_Fundef in MainI; [ eapply IntIDs_i; apply MainI | trivial].
    apply IIG. (*InternalInfo_mainGprog.*)
  - rewrite H in MainI by trivial.
    rewrite if_false in H0 by trivial. specialize (JUST i). simpl in JUST.
    remember (find_id i CoreG) as u; symmetry in Hequ; destruct u.
    * destruct (in_dec ident_eq i (IntIDs lp)) as [INT|X]; simpl in H0.
      ++ inv H0. clear MainE_vacuous.
         specialize (JUST _ _ H (eq_refl )). 
         eapply (@SF_ctx_subsumption _ coreCS coreV).
           apply JUST.
           apply (Comp_ctx_LNR COMP).
           trivial.
           apply GFF.
           { (*sub_option (make_tycontext_g coreV CoreG) ! j (make_tycontext_g Vprog Gprog) ! j *)
             intros.
             rewrite 2 semax_prog.make_context_g_char; [ | apply LNR_Vprog_Gprog | apply LNR_coreV_coreG ].
             rewrite 2 make_tycontext_s_find_id.
             remember (find_id j CoreG) as w; symmetry in Heqw; destruct w.
             + rewrite (coreG_in_Gprog Heqw); reflexivity. 
             + remember (find_id j coreV) as q; symmetry in Heqq; destruct q; simpl; trivial.
               apply coreV_in_Vprog in Heqq.
               rewrite (list_disjoint_map_fst_find_id1 disjoint_Vprog_Gprog _ _ Heqq); trivial. }
           { (*forall j : ident, subsumespec (find_id j CoreG) (find_id j Gprog)*)
             intros. apply semax_prog.sub_option_subsumespec. red; intros.
             specialize (@coreG_in_Gprog j). intros W. destruct (find_id j CoreG); [ apply W |]; trivial. }
      ++ clear MainE_vacuous. 
         specialize (JUST _ _ H (eq_refl )).
         specialize (find_id_In_map_fst _ _ _ Hequ); intros.
         destruct (Comp_G_dom COMP i) as [_ HH]. specialize (HH H2). apply in_app_or in HH; destruct HH as [ HH | HH].
         1: solve [ apply IntIDs_preserved in HH; contradiction].
         rewrite <- (Comp_G_E COMP _ HH) in Hequ. apply coreE_in_MainE in Hequ. rewrite H0 in Hequ; inv Hequ.
         eapply (@SF_ctx_subsumption _ coreCS coreV).
           apply JUST.
           apply (Comp_ctx_LNR COMP).
           trivial.
           apply GFF.
           { (*sub_option (make_tycontext_g coreV CoreG) ! j (make_tycontext_g Vprog Gprog) ! j *)
             intros.
             rewrite 2 semax_prog.make_context_g_char; [ | apply LNR_Vprog_Gprog | apply LNR_coreV_coreG].
             rewrite 2 make_tycontext_s_find_id.
             remember (find_id j CoreG) as w; symmetry in Heqw; destruct w.
             + rewrite (coreG_in_Gprog Heqw); reflexivity. 
             + remember (find_id j coreV) as q; symmetry in Heqq; destruct q; simpl; trivial.
               apply coreV_in_Vprog in Heqq.
               rewrite (list_disjoint_map_fst_find_id1 disjoint_Vprog_Gprog _ _ Heqq); trivial. }
           { (*forall j : ident, subsumespec (find_id j CoreG) (find_id j Gprog)*)
             intros. apply semax_prog.sub_option_subsumespec. red; intros.
             specialize (@coreG_in_Gprog j). intros W. destruct (find_id j CoreG); [ apply W |]; trivial. }
    * assert (coreE_i: find_id i coreE = None).
      { clear - Hequ COMP. specialize (Comp_E_in_G_find COMP i); unfold Comp_G; intros.
        destruct (find_id i coreE ); trivial. rewrite (H _ (eq_refl _)) in Hequ; congruence. }
      (*destruct (MainE_vacuous _ _ H0 Hequ) as [ef [tys [rt [cc [PHI [FDp EFsig]]]]]]; clear MainE_vacuous JUST.*)
      destruct (MainE_vacuous _ _ H0 coreE_i) as [ef [tys [rt [cc [PHI [FDp EFsig]]]]]]; clear MainE_vacuous JUST.  rewrite FDp in H; inv H.
      apply find_id_In_map_fst in H0. (*destruct (HypME1 _ H0) as [ef [ts [t [cc HH]]]];*) clear HypME1.
      (*apply Fundef_of_Gfun in HH.*)
      (*rewrite Main in HH. inv HH.*)
      split3; trivial.
      split3; [ apply typelist2list_arglist
              | apply EFsig |].
      split3; [ right; red; simpl; intros h H; inv H
              | simpl; intros gx l H; inv H |].
      split; [ apply semax_external_FF | apply GFF].
  - apply LNR_main_CoreG.
  - apply LNR_sort_e. apply LNR_internalspecs.
+ simpl; intros. if_tac in E; inv E. subst phi.
  rewrite Gprog_main. eexists; split. reflexivity. apply funspec_sub_refl.
Qed.

Definition add_CanComp := Comp_to_CanComp add_main.

Variable Hmain: main = prog_main lp.
Variable HEspec: Espec = NullExtension.Espec.

Program Definition AddMainProgVSU:@LinkedProgVSU Espec Vprog CS
      MainE nil lp [(*main_spec main lp*)(main, mainspec)].
Proof. destruct add_CanComp as [G [CC M]].
exists G. split. apply CC. rewrite M, <- Hmain, Gprog_main by (apply LNR_Gprog). 
clear - HEspec. subst. simpl. rewrite if_true by trivial. eexists; split; reflexivity.
Qed.

End ADD_MAIN.

Ltac find_sub_sub_tac :=
     intros i phi Hphi; assert (FIND:= find_id_In_map_fst _ _ _ Hphi); cbv in FIND;
     repeat (destruct FIND as [FIND |FIND]; [ subst; inv Hphi; reflexivity |]); contradiction.

Ltac AddMainProgProgVSU_tac vsu :=
eapply (@AddMainProgVSU _ _ _ _ _ _ vsu);
   [ try apply cspecs_sub_refl (*Perhaps a more general tactic is only needed if main.c contains data structure definitions?*)
   | try reflexivity
   | try reflexivity
   | try LNR_tac
   | try LNR_tac
   |(* (*list_disjoint (map fst Vprog) (map fst (prog_funct linked_prog))*)
     intros x y X Y ?; subst x. cbv in X. apply assoclists.find_id_None_iff in Y. trivial. clear H Y.
     repeat (destruct X as [X | X]; [ subst y; cbv; reflexivity |]); contradiction.*)
   | try find_sub_sub_tac
   | try LNR_tac
   | try LNR_tac
   | (* apply HypME1. *)
   | try find_sub_sub_tac
   | split3; [ | | split3; [ | |split]];
     [ try (cbv; reflexivity)
     | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
     | unfold var_sizes_ok; repeat constructor; try (simpl; rep_omega)
     | reflexivity
     | (* apply body_main.*)
     | eexists; split; [ LookupID | LookupB ] ]
   | (*apply MainE_vacuous.*)
   | try reflexivity].

(*based on tactic floyd.forward.semax_prog_aux*)
Ltac prove_linked_semax_prog :=
 split3; [ | | split3; [ | | split]];
 [ reflexivity || fail "duplicate identifier in prog_defs"
 | reflexivity || fail "unaligned initializer"
 | solve [solve_cenvcs_goal || fail "comp_specs not equal"]
   (*compute; repeat f_equal; apply proof_irr] || fail "comp_specs not equal"*)
 |
 | reflexivity || fail "match_globvars failed"
 | (*match goal with
     |- match find_id (prog_main ?prog) ?Gprog with _ => _ end =>
     unfold prog at 1; (rewrite extract_prog_main || rewrite extract_prog_main');
     ((eexists; try (unfold NDmk_funspec'; rewrite_old_main_pre); reflexivity) || 
        fail "Funspec of _main is not in the proper form")
    end*)
 ].

Section MainVSUJoinVSU.

Variable Espec: OracleKind.
Variable V1 V2 V: varspecs.
Variable cs1 cs2 cs: compspecs. 
Variable E1 Imports1 Exports1 E2 Imports2 Exports2 E Imports Exports: funspecs.
Variable p1 p2 p: Clight.program.

Variable vsu1: @LinkedProgVSU Espec V1 cs1 E1 Imports1 p1 Exports1.
Variable vsu2: @VSU Espec V2 cs2 E2 Imports2 p2 Exports2.

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

Variable Main_Unique: prog_main p1 = prog_main p2 /\ prog_main p1 = prog_main p.
Variable ProgP2None: find_id (prog_main p1) (prog_funct p2) = None.

Lemma MainVSUJoinVSU: @LinkedProgVSU Espec (*(V1++V2)*)V cs E Imports p Exports.
Proof.
  destruct vsu1 as [G1 [[c1 X] MAIN1]]. destruct vsu2 as [G2 c2].
  specialize (ComponentJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ E Imports Exports p1 p2 p c1 c2 HV1p1 HV1p2 HV2p1 HV2p2
       LNR_V1 LNR_V2 CS1 CS2 _ HV1 HV2 FundefsMatch FP Externs1_Hyp Externs2_Hyp ExternsHyp SC1 SC2
       HImports ImportsDef ExportsDef LNRp V_LNR domV). intros C.
  destruct (Comp_to_CanComp C) as [GG [CC MM]].
  eexists; split. apply CC. rewrite MM.
  destruct MAIN1 as [phi [PhiG PhiE]]. 
  unfold Comp_G in *.
  destruct Main_Unique as [MU1 MU2]. rewrite <- MU2 in *. subst Exports.
  remember (find_id (prog_main p1) G2) as w; symmetry in Heqw; destruct w.
  { specialize (@Comp_G_in_Fundefs' _ _ _ _ _ _ _ _ c2 _ _ Heqw).
    rewrite ProgP2None; clear; intros [? ?]; congruence. }
  rewrite (G_merge_find_id_SomeNone PhiG Heqw).
  rewrite (G_merge_find_id_SomeNone PhiE).
  exists phi; split; trivial.
  specialize (Comp_G_Exports c2 (prog_main p1)).
  destruct (find_id (prog_main p1) Exports2); intros; trivial.
  destruct (H _ (eq_refl _)) as [psi [? _]]. congruence.
Qed. 

End MainVSUJoinVSU.
Ltac MainVSUJoinVSU LP_VSU1 VSU2 :=
  apply (@MainVSUJoinVSU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LP_VSU1 VSU2);
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
| try (split; reflexivity)
| try reflexivity
].