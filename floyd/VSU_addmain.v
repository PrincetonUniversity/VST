Require Import VST.floyd.proofauto.
Require Import VST.floyd.assoclists.
Require Import VST.floyd.VSU.

Require Import VST.veric.initial_world.

Record CanonicalComponent {Espec} V Externs Imports p Exports GP G:= {
  CC_component :> @Component Espec V Externs Imports p Exports GP G;
  CC_canonical: map fst (Comp_G CC_component) = 
                map fst (filter (fun x => in_dec ident_eq (fst x) (IntIDs p ++ map fst Externs))
                        (PTree.elements (QP.prog_defs p)))
}.

Lemma CanonicalComponent_entail {Espec V E Imp p Exp G} GP1 GP2 : 
      @CanonicalComponent Espec V E Imp p Exp GP1 G ->
       (forall gv, GP1 gv |-- GP2 gv) -> 
      @CanonicalComponent Espec V E Imp p Exp GP2 G.
Proof.
  intros. destruct H as [C X]. 
  apply (Build_CanonicalComponent _ _ _ _ _ _ _ _ (Comp_entail C _ H0) X).
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


Record CanonicalComponent_M {Espec} V Externs Imports p Exports GP G:= {
  CCM_G: funspecs;
  CCM_component :> @CanonicalComponent Espec V Externs Imports p Exports GP CCM_G;
  CCM_main: find_id (QP.prog_main p) CCM_G = find_id (QP.prog_main p) G
}.

Lemma Comp_to_CanComp {Espec V Ext Imp p Exp GP G} 
      (C: @Component Espec V Ext Imp p Exp GP G):
      @CanonicalComponent_M Espec V Ext Imp p Exp GP G.
Proof.
  assert (HG: G = Comp_G C) by reflexivity.
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

  assert (X3: list_norepet (map fst V ++ map fst (GG ++ Imp))). {
   pose proof (Comp_LNR C).
   rewrite map_app in H |-*.
   rewrite !list_norepet_app in H|-*.
   destruct H as [? [[? [? ?]] ?]]; split3; [ | split3 | ]; auto.
   intros i j ? ? ?; subst j.
   assert (In i (map fst G)).
      apply In_map_fst_find_id in H4; auto. destruct H4. rewrite <- Y in H4.
      apply find_id_In_map_fst in H4; auto.
   contradiction (list_disjoint_notin _ H2 H6).
   intros i j ? ? ?; subst j.
   apply (list_disjoint_notin _ H3 H4).
   rewrite in_app in H5|-*.
   destruct H5; auto. left.
      apply In_map_fst_find_id in H5; auto. destruct H5. rewrite <- Y in H5.
      apply find_id_In_map_fst in H5; auto.
 }

  assert (X4: list_norepet (map fst Ext)) by apply C.
  assert (X4': list_norepet (map fst Exp)) by apply C.
  assert (X5: forall i, In i (map fst Ext) -> exists f ts t cc,
    PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc))) by apply C.

  assert (X9: forall i phi fd,
    PTree.get i (QP.prog_defs p) = Some (Gfun fd) -> find_id i GG = Some phi -> 
   @SF Espec (Comp_cs C) V (QPglobalenv p) (Imp ++ GG) i fd phi).
  { intros.
    eapply SF_ctx_extensional. 
    + rewrite <- Y in H0. apply (Comp_G_justified C _ phi _ H H0).
    + apply (Comp_ctx_LNR C).
    + intros j. rewrite 2 find_id_app_char, Y; trivial. }

  assert (X10: forall i phi, find_id i Exp = Some phi -> 
          exists phi', find_id i GG = Some phi' /\ funspec_sub phi' phi).
  { intros. destruct (Comp_G_Exports C _ _ H) as [phi' [Phi' Sub]].
    exists phi'; split; trivial. rewrite <- (order_SOC HeqGopt); trivial.
    apply list_norepet_map_fst_filter. apply PTree.elements_keys_norepet.
    intros. rewrite (order_dom HeqGopt). apply X6. apply C. trivial. }

  remember (@Build_Component Espec V Ext Imp p Exp GP GG
  (Comp_prog_OK C) X1 X3 X4 X4' X5 X6 X8 X9 X10
          (Comp_MkInitPred C)) as cc.
  exists GG.
  - apply Build_CanonicalComponent with cc.
         subst cc; simpl. symmetry; apply (order_dom HeqGopt).
  - rewrite HG, Y; trivial.
+ apply order_i' in HeqGopt. contradiction. apply (Comp_G_LNR C). unfold Comp_G in *.
  clear - C. intros.
  apply (Comp_G_dom C). apply in_map_iff in H. destruct H as [[j d] [J HJ]]. simpl in J; subst.
  apply filter_In in HJ; simpl in HJ; destruct HJ.
  destruct (in_dec ident_eq i (IntIDs p ++ map fst Ext)). trivial. inv H0.
Qed.

Lemma CanonicalComponent_M_entail {Espec V E Imp p Exp G} GP1 GP2 : 
      @CanonicalComponent_M Espec V E Imp p Exp GP1 G -> (forall gv, GP1 gv |-- GP2 gv) -> 
      @CanonicalComponent_M Espec V E Imp p Exp GP2 G.
Proof.
  intros. eapply Build_CanonicalComponent_M. apply (CanonicalComponent_entail _ _ X H). apply X.
Defined.

Definition CanonicalVSU {Espec} E Imports p Exports GP :=
  sigT (fun G => @CanonicalComponent_M Espec (QPvarspecs p) E Imports p Exports GP G).

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
       Genv.find_symbol ge id = Some b ->
       Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
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

Lemma Canonical_semaxfunc {Espec V E p Exp GP G}
      (c: @CanonicalComponent Espec V E nil p Exp GP G):
   @semaxfunc Espec (Comp_cs c) V (Comp_G c) (QPglobalenv p) 
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

Lemma Canonical_semax_func {Espec V E p Exp GP G}
      (c: @CanonicalComponent Espec V E nil p Exp GP G)
      (HE: map fst E =
           map fst (filter (fun x  => negb (isInternal (Gfun (snd x)))) (QPprog_funct p))):
      @semax_func Espec V (Comp_G c) (Comp_cs c) (QPglobalenv p) (QPprog_funct p) (Comp_G c).
Proof.
  apply semaxfunc_sound.
  specialize (Canonical_semaxfunc c).
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


Lemma progfunct_eq:SeparationLogic.prog_funct = prog_funct.
Proof. reflexivity. Qed.

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
  LP_C: @CanonicalComponent Espec (QPvarspecs p) E Imports p Exports GP LP_G;
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

Lemma LNR_progdefs_progfunct {p: Clight.program}: list_norepet (map fst (prog_defs p)) -> 
      list_norepet (map fst (prog_funct p)).
Proof. apply initialize.list_norepet_prog_funct'. Qed.

Definition ExtIDs (p: Ctypes.program function): list ident := 
  map fst ((filter (fun x => negb (isInternal (snd x)))) (prog_defs p)).

Lemma MkInitPred_of_CanonicalVSU {Espec E Imports p Exports GP} 
       (vsu: @CanonicalVSU Espec E Imports p Exports GP):
      forall gv, globals_ok gv -> InitGPred (Vardefs p) gv |-- GP gv.
Proof. destruct vsu as [G [GG CC M]]. apply (Comp_MkInitPred CC). Qed.


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

Definition PTree_eq {A} (m1 m2: PTree.t A) :=
 forall i, PTree.get i m1 = PTree.get i m2.

Section ADD_MAIN.
Variable Espec: OracleKind.
(*Variable coreV: varspecs.
Variable coreCS: compspecs.*)
Variable coreE: funspecs.
Notation coreImports:= (@nil (ident * funspec)). (*nil - we're only linking main if this yields a full prog*)
Variable p: QP.program function.
Variable coreExports: funspecs.
Variable coreGP: globals -> mpred.
Variable CoreVSU: @CanonicalVSU Espec coreE coreImports p coreExports coreGP.

Variable lp: QP.program function.

(*Variable CS: compspecs.
Variable CSSUB: cspecs_sub (Comp_cs (projT2 CoreVSU)) CS.
*)
Variable main:ident.
Variable mainspec: funspec.

Variable mainFun : function.

Variable MainFresh : (QP.prog_defs p) ! main = None.
Variable P_LP: PTree_eq (PTree.set main (Gfun (Internal mainFun)) (QP.prog_defs p)) (QP.prog_defs lp).

(*Variable LNR_LP : list_norepet (map fst (prog_defs lp)).*)
(*Definition LNR_Funs:= LNR_progdefs_progfunct LNR_LP. *)
Lemma Main i: 
      (QP.prog_defs lp) ! i = 
      if ident_eq i main then Some (Gfun (Internal mainFun))
                         else (QP.prog_defs p) ! i.
Proof.
 rewrite <- P_LP.
 if_tac. subst. apply PTree.gss.
 apply PTree.gso; auto.
Qed.

Definition CoreG := G_of_CanonicalVSU CoreVSU.

Definition linked_internal_specs :=
  SortFunspec.sort
         (filter (fun a => in_dec ident_eq (fst a) (IntIDs lp)) ((main,mainspec) :: CoreG)).

(*
Variable Vprog: varspecs.
Variable LNR_Vprog: list_norepet (map fst Vprog).
Variable disjoint_Vprog_lpfuns: list_disjoint (map fst Vprog) (map fst (prog_funct lp)).
Variable coreV_in_Vprog: forall {i phi}, find_id i coreV = Some phi -> find_id i Vprog = Some phi. 

Variable LNR_coreV: list_norepet (map fst coreV).
*)
Variable MainE : list (ident * funspec).
Variable LNR_MainE : list_norepet (map fst MainE).

Variable HypME1: forall i, In i (map fst MainE) -> exists ef ts t cc,
           (QP.prog_defs lp) ! i = Some (Gfun (External ef ts t cc)).

Definition notin {A} (L:list (ident * A)) (x:ident * A):bool :=
  match find_id (fst x) L with None => true | _ => false end.

Definition MainVardefs := filter (notin (Vardefs p)) (Vardefs lp).

Variable Vardefs_contained: forall i d, find_id i (Vardefs p) = Some d -> find_id i (Vardefs lp) = Some d.

Variable Main_InitPred: globals -> mpred.
Variable Main_MkInitPred: forall gv, InitGPred MainVardefs gv |-- Main_InitPred gv.
(*Variable LNR_PV: list_norepet (map fst (Vardefs p)).
Variable LNR_LV: list_norepet (map fst (Vardefs lp)).
*)
Lemma Vardefs_norepet: forall p, list_norepet (map fst (Vardefs p)).
Proof.
intros.
unfold Vardefs.
apply list_norepet_map_fst_filter.
apply PTree.elements_keys_norepet.
Qed.

Lemma MkInitPred gv: globals_ok gv -> InitGPred (Vardefs lp) gv |-- (Main_InitPred gv * coreGP gv)%logic.
Proof.
  intro Hgv.
  simpl. eapply derives_trans.
  2: apply sepcon_derives; [ apply Main_MkInitPred | apply (MkInitPred_of_CanonicalVSU CoreVSU)]; auto.
  clear Hgv.

  clear - Vardefs_contained. unfold MainVardefs.
  assert (LNR_LV := Vardefs_norepet lp).
  assert (LNR_PV := Vardefs_norepet p).
  forget (Vardefs lp) as LV. forget (Vardefs p) as PV. clear p lp. 
  revert Vardefs_contained LNR_PV LNR_LV. generalize dependent PV.
  induction LV; simpl; intros.
+ destruct PV; simpl. rewrite ! InitGPred_nilD. rewrite emp_sepcon; trivial.
  exfalso.
  destruct p as [i d]. specialize (Vardefs_contained i d); simpl in Vardefs_contained.
  rewrite if_true in Vardefs_contained by trivial. specialize (Vardefs_contained (eq_refl _)); congruence.
+ rewrite ! InitGPred_consD. destruct a as [j d]. unfold notin at 1. simpl fst in *.
  inv LNR_LV.
  assert (VCj := Vardefs_contained j). 
  remember (find_id j PV) as b; symmetry in Heqb; destruct b; simpl in VCj.
  2:{ rewrite InitGPred_consD. cancel.
      apply IHLV; clear IHLV; trivial.
      intros. 
      specialize (Vardefs_contained _ _ H). 
      rewrite if_false in Vardefs_contained; trivial. congruence.  }
  rewrite if_true in VCj by trivial. specialize (VCj _ (eq_refl _)). inv VCj.
  destruct (find_id_in_split Heqb) as [PV1 [PV2 [HPV [HPV1 HPV2]]]]; trivial.
  subst PV. clear Heqb. rewrite InitGPred_app, InitGPred_consD.
  cancel.
  rewrite map_app in LNR_PV; simpl in LNR_PV. apply list_norepet_middleD in LNR_PV.
  destruct LNR_PV as [PV12j LNR_PV12].
  eapply derives_trans.
  - apply (IHLV (PV1++PV2)); clear IHLV; trivial. 2: rewrite map_app; trivial.
    intros.
    specialize (Vardefs_contained i d). rewrite find_id_app_char in Vardefs_contained, H.
    simpl in *.
    remember (find_id i PV1) as r; destruct r; simpl in *.
    * inv H. rewrite if_false in Vardefs_contained; auto. congruence.
    * clear Heqr. remember (find_id i PV2) as r; destruct r; simpl in *; trivial; inv H.
      rewrite 2 if_false in Vardefs_contained; auto; congruence.
  - clear IHLV Vardefs_contained. rewrite InitGPred_app. cancel.
    apply derives_refl'. f_equal.
    apply filter_fg. intros [i d] ID. unfold notin; simpl. rewrite 2 find_id_app_char. simpl.
    rewrite if_false; trivial. specialize (in_map fst _ _ ID); simpl. congruence.
Qed.

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
  intros. unfold Gprog.
  rewrite map_app. apply in_or_app. apply in_app_or in H. destruct H; [ left | right; trivial].
  unfold linked_internal_specs. apply sort_In_map_fst_i. apply In_map_fst_filter; trivial. simpl.
  destruct (IntIDs_elim H) as [f Hf]. apply find_id_i in Hf; [| trivial].
  assert (MainI := Main i).
   if_tac in MainI; auto. 
   right.
    unfold CoreG. destruct CoreVSU. simpl. 
    apply (Comp_G_dom c). apply in_or_app; left.
    eapply IntIDs_i. rewrite <- MainI. rewrite <- find_id_elements. apply Hf.
    apply PTree.elements_keys_norepet.
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
  apply IntIDs_e in N; [ destruct N | ]. congruence. apply c.
  destruct (Comp_Externs c _ N) as [ef [tys [ts [cc H]]]].  congruence.
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

Lemma LNR_coreV_coreG: list_norepet (map fst (Vardefs p) ++ map fst CoreG).
Proof.
apply list_norepet_append.
apply Vardefs_norepet.
apply LNR_G_of_CanoncialVSU.
apply (list_disjoint_mono _ (map fst (Vardefs lp)) _ (map fst (QPprog_funct lp))).
-
     intros i j ? ? ?; subst j.
     clear - H H0.
     unfold Vardefs, QPprog_funct in *.
     pose proof (PTree.elements_keys_norepet (QP.prog_defs lp)).
     induction (PTree.elements (QP.prog_defs lp)).
     inv H.
     destruct a, g; simpl in *. inv H1.
     destruct H0; subst; auto.
     apply H4. clear - H.
     apply list_in_map_inv in H. destruct H as [? [??]]; subst.
     apply in_map. apply filter_In in H0. destruct H0; auto.
     inv H1. destruct H; auto. subst.
     apply H4. clear - H0.
     induction l; simpl in *; auto. destruct a, g; simpl in *; auto.
     destruct H0; auto.
-
  unfold CoreG. unfold G_of_CanonicalVSU. remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].
  intros. apply (Comp_G_in_Fundefs COMP) in H. destruct H as [f Hf].
  assert (Hf': (QP.prog_defs lp) ! x = Some (Gfun f)).
  rewrite Main. rewrite if_false; auto. intro; subst x; rewrite MainFresh in Hf; inv Hf.
  clear - Hf'.
  apply PTree.elements_correct in Hf'.
  unfold QPprog_funct, QPprog_funct'.
  induction (PTree.elements (QP.prog_defs lp)) as [|[??]]. inv Hf'.
  destruct Hf'. inv H. left; auto.
  destruct g; simpl; auto.
- intros.
 apply In_map_fst_find_id in H. destruct H as [t Ht].
 eapply find_id_In_map_fst.   apply Vardefs_contained; eauto.
 apply Vardefs_norepet.
Qed.

Lemma disjoint_Vprog_Gprog: list_disjoint (map fst (QPvarspecs p)) (map fst Gprog).
Proof. unfold Gprog. rewrite map_app. apply list_disjoint_app_R.
+ unfold linked_internal_specs. intros x y X Y ?; subst.
  apply sort_In_map_fst_e in Y. apply In_map_fst_filter2 in Y; destruct Y.
  apply IntIDs_e in H; [ destruct H as [f Hf] | trivial].
  rewrite <- P_LP in Hf.
  clear - MainFresh X Hf.
  apply In_map_fst_find_id in X; try apply QPvarspecs_norepet.
  destruct X as [a ?].
  rewrite find_id_QPvarspecs in H.
  destruct H as [g [? ?]]. 
  destruct (ident_eq y main). congruence.
  rewrite PTree.gso in Hf by auto. congruence.
+ intros x y X Y ?; subst. destruct (HypME1 _ Y) as [ef [ts [t [cc Hf]]]].
  rewrite <- P_LP in Hf.
  clear - MainFresh X Hf.
  apply In_map_fst_find_id in X; try apply QPvarspecs_norepet.
  destruct X as [a ?].
  rewrite find_id_QPvarspecs in H.
  destruct H as [g [? ?]]. 
  destruct (ident_eq y main). congruence.
  rewrite PTree.gso in Hf by auto. congruence.
Qed.

Lemma LNR_Vprog_Gprog: list_norepet (map fst (QPvarspecs p) ++ map fst Gprog).
Proof. apply list_norepet_app; split3.
  apply QPvarspecs_norepet.
  unfold Gprog.
  rewrite map_app; apply list_norepet_app; split3.
  apply LNR_internalspecs.
  auto. apply Disj_internalspecs_MainE.
  apply disjoint_Vprog_Gprog.
Qed.

Lemma Gprog_main: find_id main Gprog = Some (snd (main,mainspec)).
Proof.
  specialize (Main main).
  unfold Gprog, linked_internal_specs.
  rewrite find_id_app_char, <- sort_find_id, filter_cons,
          find_id_app_char, find_id_filter_char.
  try destruct mainspec as [main phi]; simpl in *.
+ clear - mainFun P_LP. rewrite 2 if_true by trivial.
  intros MainI.
  destruct (in_dec ident_eq main (IntIDs lp)); simpl; trivial.
  elim n. eapply IntIDs_i.
  rewrite <- P_LP. apply PTree.gss.
+ simpl. constructor. auto. constructor.
+ apply LNR_sort_e. apply LNR_internalspecs.
Qed.

Lemma IntIDs_lp i: In i (IntIDs lp) -> i=main \/ In i (IntIDs p).
Proof.
  unfold CoreG. unfold G_of_CanonicalVSU. remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  clear - mainFun  P_LP COMP. intros.
  apply IntIDs_e in H; auto. destruct H as [f Hf].
  specialize (Main i). rewrite Hf; intros MainI. if_tac in MainI; [ left; trivial | right].
  symmetry in MainI. apply IntIDs_i in MainI; trivial.
Qed.

Lemma IntIDs_preserved i: In i (IntIDs p) -> In i (IntIDs lp).
Proof.
  unfold CoreG. unfold G_of_CanonicalVSU. remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  destruct (Comp_G_dom COMP i) as [_ HH]. clear - mainFun  P_LP HH MainFresh COMP. specialize (Main i); intros MainI.
  intros. if_tac in MainI; subst; apply IntIDs_e in H; try apply COMP; destruct H; [ congruence |].
  rewrite <- MainI in H.
  apply IntIDs_i in H; trivial.
Qed.

Lemma coreG_in_Gprog {i phi}: find_id i CoreG = Some phi -> find_id i Gprog = Some phi.
Proof.
  assert (X: CoreG = G_of_CanonicalVSU CoreVSU) by reflexivity.
  remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  unfold Gprog, linked_internal_specs. intros.
  destruct (Comp_G_dom COMP i) as [_ HH].
  rewrite find_id_app_char, <- sort_find_id, find_id_filter_char.
+
  simpl. rewrite if_false, H; rewrite X in H.
  - exploit HH; clear HH. eapply find_id_In_map_fst. apply H.
    intros K. apply in_app_or in K; destruct K.
    * apply IntIDs_preserved in H0. destruct  (in_dec ident_eq i (IntIDs lp)); simpl; trivial. contradiction.
    * destruct (in_dec ident_eq i (IntIDs lp)); simpl; trivial.
      apply coreE_in_MainE. rewrite (Comp_G_E COMP i H0). apply H.
  - intros M; subst main. destruct (Comp_G_in_progdefs' COMP i phi H). congruence.
+ apply LNR_main_CoreG.
+ apply LNR_sort_e; apply LNR_internalspecs.
Qed.

Lemma LNR_coreExports: list_norepet (map fst coreExports).
Proof.
  assert (X: CoreG = G_of_CanonicalVSU CoreVSU) by reflexivity.
  remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  apply (Comp_Exports_LNR COMP).
Qed.

Lemma LNR_coreExports': list_norepet (main::map fst coreExports).
Proof.
  assert (X: CoreG = G_of_CanonicalVSU CoreVSU) by reflexivity.
  remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  constructor.
+ intros N.
  apply (Comp_Exports_in_progdefs COMP) in N.
Search In map.
  apply list_in_map_inv in N. destruct N as [[x ?] [? ?]]. simpl in H; subst x.
  apply PTree.elements_complete in H0. congruence.
+ apply (Comp_Exports_LNR COMP).
Qed.

Lemma subsumespec_coreExports_Gprog i: subsumespec (find_id i coreExports) (find_id i Gprog).
Proof.
  assert (X: CoreG = G_of_CanonicalVSU CoreVSU) by reflexivity.
  remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  red. remember (find_id i coreExports) as w; symmetry in Heqw; destruct w; trivial.
  destruct (Comp_G_Exports COMP _ _ Heqw) as [phi [Phi PHI]].
  exists phi; split. apply coreG_in_Gprog. try rewrite X; apply Phi.
  apply seplog.funspec_sub_sub_si. apply PHI. 
Qed.
 
Lemma subsumespec_coreExports_Gprog' i: subsumespec (find_id i ((*main_spec main lp*)(main,mainspec)::coreExports)) (find_id i Gprog).
Proof.
  assert (X: CoreG = G_of_CanonicalVSU CoreVSU) by reflexivity.
  remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  red. simpl. if_tac.
  + subst i. rewrite Gprog_main. eexists; split. reflexivity. apply funspec_sub_si_refl.
  + remember (find_id i coreExports) as w; symmetry in Heqw; destruct w; trivial.
    destruct (Comp_G_Exports COMP _ _ Heqw) as [phi [Phi PHI]].
    exists phi; split. apply coreG_in_Gprog; try rewrite X; apply Phi.
    apply seplog.funspec_sub_sub_si. apply PHI. 
Qed.

Lemma coreExports_in_Gprog i: sub_option (make_tycontext_g (QPvarspecs p) coreExports) ! i (make_tycontext_g (QPvarspecs p) Gprog) ! i.
Proof.
  assert (X: CoreG = G_of_CanonicalVSU CoreVSU) by reflexivity.
  remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  red. rewrite 2 semax_prog.make_context_g_char; try apply LNR_Vprog_Gprog.
  + rewrite 2 make_tycontext_s_find_id.
    remember (find_id i coreExports) as w; symmetry in Heqw; destruct w.
    - destruct (Comp_G_Exports COMP _ _ Heqw) as [phi [ Phi PHI]].
      erewrite coreG_in_Gprog, (type_of_funspec_sub _ _ PHI); trivial.
      try rewrite X; apply Phi.
    - remember (find_id i (QPvarspecs p)) as u; symmetry in Hequ; destruct u; trivial.

      rewrite (list_norepet_find_id_app_exclusive1 LNR_Vprog_Gprog Hequ); trivial.
  + specialize LNR_coreExports; intros LNR_EXP.
    apply list_norepet_append; trivial.
   apply QPvarspecs_norepet.
    eapply list_disjoint_mono; [ apply disjoint_Vprog_Gprog | | ]; trivial.
    intros. apply In_map_fst_find_id in H; trivial.
    destruct H as [f Hf]. destruct ( Comp_G_Exports COMP _ _ Hf) as [phi [Phi _]].
    eapply find_id_In_map_fst. apply coreG_in_Gprog. rewrite X. apply Phi.
Qed.

Lemma coreExports_in_Gprog' i: sub_option (make_tycontext_g (QPvarspecs p) ((main,mainspec)::coreExports)) ! i (make_tycontext_g (QPvarspecs p) Gprog) ! i.
Proof.
  assert (X: CoreG = G_of_CanonicalVSU CoreVSU) by reflexivity.
  remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]].

  red. rewrite 2 semax_prog.make_context_g_char; try apply LNR_Vprog_Gprog.
  + rewrite 2 make_tycontext_s_find_id. simpl. if_tac.
    { (*main*) subst i. rewrite Gprog_main. reflexivity. }
    remember (find_id i coreExports) as w; symmetry in Heqw; destruct w.
    - destruct (Comp_G_Exports COMP _ _ Heqw) as [phi [ Phi PHI]].
      erewrite coreG_in_Gprog, (type_of_funspec_sub _ _ PHI); trivial.
      try rewrite X; apply Phi.
    - remember (find_id i (QPvarspecs p)) as u; symmetry in Hequ; destruct u; trivial.
      rewrite (list_norepet_find_id_app_exclusive1 LNR_Vprog_Gprog Hequ); trivial.
  + specialize LNR_coreExports'; intros LNR_EXP.
    apply list_norepet_append; trivial.
    apply QPvarspecs_norepet.
    eapply list_disjoint_mono; [ apply disjoint_Vprog_Gprog | | ]; trivial.
    intros. apply In_map_fst_find_id in H; trivial.
    destruct H as [f Hf]. simpl in Hf.
    if_tac in Hf.
    { subst x. apply (find_id_In_map_fst _ _ _ Gprog_main). }
    destruct ( Comp_G_Exports COMP _ _ Hf) as [phi [Phi _]].
    eapply find_id_In_map_fst. apply coreG_in_Gprog. rewrite X. apply Phi.
Qed.

Definition CS: compspecs := Comp_cs (projT2 CoreVSU).

Variable InternalInfo_main:
      semaxfunc_InternalInfo CS (QPvarspecs p) ((main,mainspec)::coreExports) 
                             (QPglobalenv lp) main mainFun mainspec.

Lemma InternalInfo_mainGprog:
      semaxfunc_InternalInfo CS (QPvarspecs p) Gprog (QPglobalenv lp) main mainFun mainspec.
Proof.
eapply InternalInfo_subsumption. 4: apply InternalInfo_main.
apply coreExports_in_Gprog'.
apply subsumespec_coreExports_Gprog'.
apply LNR_coreExports'. 
Qed.

Variable MainE_vacuous: forall i phi, find_id i MainE = Some phi -> find_id i coreE = None ->
         exists ef argsig retsig cc, 
           phi = vacuous_funspec (External ef argsig retsig cc) /\ 
           find_id i (QPprog_funct p) = Some (External ef argsig retsig cc) /\
           ef_sig ef = {| sig_args := typlist_of_typelist argsig;
                          sig_res := rettype_of_type retsig;
                          sig_cc := cc_of_fundef (External ef argsig retsig cc) |}.

Lemma add_main:
      @Component Espec
       MainE nil lp ((main, mainspec)::nil) (fun gv => Main_InitPred gv * coreGP gv)%logic Gprog.
Proof.
eapply Build_Component with (Comp_cs := CS); trivial.
+ contradiction.
+ set (H := CC_component _ _ _ _ _ _ (CCM_component _ _ _ _ _ _ (projT2 CoreVSU))).
    pose proof (Comp_cs_OK H).
    
 simpl in H.
Check CCM_component.

 set (x := CCM_component _ _ _ _ _ _ H).
 CanonicalComponent_M.

pose (x := CCM_component coreExports H).
destruct H.
simpl in H.
 apply (Comp_cs_OK (projT2 .
+ rewrite app_nil_r; trivial.
+ constructor; [ auto | constructor].
+ intros; split.
  - apply IntIDsMainE_Gprog.
  - apply Gprog_IntIDsMainE.
+ apply LNR_Gprog.
+ 
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
  rewrite Main in H. 
  assert (CG: CoreG = G_of_CanonicalVSU CoreVSU) by reflexivity.
  remember  CoreVSU as VSU'. destruct VSU' as [G [GG COMP MM]]. clear HeqVSU'.

  assert (MainI := Main i). if_tac in H.
  - (*i=main*) subst; rewrite if_true in H0 by trivial.
    clear JUST MainE_vacuous. inv H.
    destruct (in_dec ident_eq main (IntIDs lp)); [ simpl in H0; inv H0 | elim n; clear - MainI LNR_LP].
    2: apply Gfun_of_Fundef in MainI; [ eapply IntIDs_i; apply MainI | trivial].
    apply IIG. 
  - rewrite H in MainI by trivial.
    rewrite if_false in H0 by trivial. simpl in CG. subst GG. specialize (JUST i). simpl in JUST.
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
      destruct (MainE_vacuous _ _ H0 coreE_i) as [ef [tys [rt [cc [PHI [FDp EFsig]]]]]]; clear MainE_vacuous JUST.  rewrite FDp in H; inv H.
      apply find_id_In_map_fst in H0. clear HypME1.
      split3; trivial.
      split3; [ apply typelist2list_arglist
              | apply EFsig |].
      split3; [ right; red; simpl; intros h H; inv H
              | simpl; intros gx l H; inv H |].
      split; [ apply semax_external_FF | apply GFF].
  - apply LNR_main_CoreG.
  - apply LNR_sort_e. apply LNR_internalspecs.
+ simpl; intros. if_tac in E; inv E. try subst phi.
  rewrite Gprog_main. eexists; split. reflexivity. apply funspec_sub_refl.
+ apply MkInitPred.
Qed.

Definition add_CanComp := Comp_to_CanComp add_main.

Variable Hmain: main = prog_main lp.
Variable HEspec: Espec = NullExtension.Espec.

Program Definition VSUAddMain:@LinkedProgVSU Espec Vprog CS
      MainE nil lp [(main, mainspec)]
      (fun gv => Main_InitPred gv * coreGP gv)%logic.
Proof. 
specialize Gprog_main. intros. 
destruct add_CanComp as [G [CC M]].
exists G. econstructor. apply M. rewrite CCM_main. rewrite Hmain in *. simpl.
rewrite if_true by trivial. exists mainspec; split; trivial.
Qed.

End ADD_MAIN.

Ltac find_sub_sub_tac :=
     intros i phi Hphi; assert (FIND:= find_id_In_map_fst _ _ _ Hphi); cbv in FIND;
     repeat (destruct FIND as [FIND |FIND]; [ subst; inv Hphi; reflexivity |]); contradiction.

Ltac VSUAddMain_tac' vsu :=
eapply LP_VSU_entail;
[ eapply (@VSUAddMain _ _ _ _ _ _ _ vsu);
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

    (*Four side conditions on Varspecs*)
   | try find_sub_sub_tac
   | intros; first [ solve [reflexivity] | solve [apply derives_refl] | idtac] (*instantiates InitPred to MainVarDefs*)
   | try LNR_tac
   | try LNR_tac

   | try find_sub_sub_tac
   | split3; [ | | split3; [ | |split]];
     [ try (cbv; reflexivity)
     | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
     | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
     | reflexivity
     | (* apply body_main.*)
     | eexists; split; [ LookupID | LookupB ] ]
   | (*apply MainE_vacuous.*)
   | try reflexivity]
| intros; simpl; first [ solve [unfold InitGPred; simpl; cancel] | idtac]
].

Ltac VSUAddMain_tac vsu :=
match type of vsu with 
|  VSU _ _ _ _ _ => let cvsu := constr:(VSU_to_CanonicalVSU vsu) in
                                   VSUAddMain_tac' cvsu
| CanonicalVSU _ _ _ _ _ => VSUAddMain_tac' vsu
end.

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

Lemma comp_env_proofirr: forall (ce1 ce2: list (ident * composite)),
   Forall2 (fun pc1 pc2 => fst pc1 = fst pc2 /\ getCompositeData (snd pc1) = getCompositeData (snd pc2))
           ce1 ce2 ->
    ce1=ce2.
Proof. intros.
induction H; auto.
f_equal; auto.
destruct x,y,H; f_equal; auto.
simpl in H,H1.
destruct c, c0.
simpl in H1.
inv H1.
f_equal; auto; try apply proof_irr.
Qed.

(*based on tactic floyd.forward.semax_prog_aux*)
Ltac solve_cenvcs_goal_eq :=
     apply comp_env_proofirr;
     repeat (constructor; [simpl; split; trivial |]); constructor.

Ltac prove_linked_semax_prog :=
 split3; [ | | split3; [ | | split]];
 [ reflexivity || fail "duplicate identifier in prog_defs"
 | reflexivity || fail "unaligned initializer"
 | solve [solve_cenvcs_goal_eq || solve_cenvcs_goal || fail "comp_specs not equal"]
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
Variable GP1 GP2: globals -> mpred.
Variable vsu1: @LinkedProgVSU Espec V1 cs1 E1 Imports1 p1 Exports1 GP1.
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

Variable Main_Unique: prog_main p1 = prog_main p2 /\ prog_main p1 = prog_main p.
Variable ProgP2None: find_id (prog_main p1) (prog_funct p2) = None.

Variable VD1: map fst (Vardefs p1) = map fst V1.
Variable VD2: map fst (Vardefs p2) = map fst V2.
Variable VD: map fst (Vardefs p) = map fst V.

Variable HVardefs1: forall i d, find_id i (Vardefs p1) = Some d -> find_id i (Vardefs p) = Some d.
Variable HVardefs2: forall i d, find_id i (Vardefs p2) = Some d -> find_id i (Vardefs p) = Some d.

Lemma MainVSUJoinVSU: @LinkedProgVSU Espec (*(V1++V2)*)V cs E Imports p Exports (fun gv => GP1 gv * GP2 gv)%logic.
Proof.
  destruct vsu1 as [G1 [c1 X1] Main1]. destruct vsu2 as [G2 c2].
  specialize (ComponentJoin _ _ _ _ _ _ _ _ _ G1 _ _ _ G2 E Imports Exports p1 p2 p GP1 GP2 c1 c2
       DisjointVarspecs HV1p1 HV1p2 HV2p1 HV2p2
       LNR_V1 LNR_V2 CS1 CS2 _ HV1 HV2 FundefsMatch FP Externs1_Hyp Externs2_Hyp ExternsHyp SC1 SC2
       HImports ImportsDef ExportsDef LNRp V_LNR domV VD1 VD2 VD HVardefs1 HVardefs2). intros C.
  econstructor. apply (Comp_to_CanComp C).
  destruct (Comp_to_CanComp C) as [GG [CC HGG] MM]. simpl.
  rewrite MM.
  destruct Main1 as [phi [PhiG PhiE]]. 
  unfold Comp_G in *.
  destruct Main_Unique as [MU1 MU2]. rewrite <- MU2 in *. subst Exports.
  remember (find_id (prog_main p1) G2) as w; symmetry in Heqw; destruct w.
  { specialize (Comp_G_in_Fundefs' c2 _ _ Heqw).
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
| try reflexivity
| try reflexivity
| try reflexivity
|
|
].

Definition in_dom {A} (T:PTree.t unit) (ia: ident*A) : bool :=
 match PTree.get (fst ia) T with Some _ => true | None => false end.

Definition mkLinkedSYS_aux (T:PTree.t unit) (p:Clight.program) Specs :funspecs :=
   filter (in_dom T) (augment_funspecs p Specs).

Definition mkLinkedSYS' (p:Clight.program) Specs :funspecs := 
  mkLinkedSYS_aux
  (fold_right (fun i t => PTree.set i tt t) (PTree.empty _) (ExtIDs p)) p Specs.
(*Do this on per-program basis
Definition mkLinkedSYS (p:Clight.program) Specs :funspecs := ltac: 
    (let x := constr:(mkLinkedSYS_aux
           (fold_right (fun i t => PTree.set i tt t) (PTree.empty _) (ExtIDs p)) p Specs)
           in let x := eval compute in x
           in exact x).
*)