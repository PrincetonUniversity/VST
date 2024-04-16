Require Import VST.floyd.proofauto.
Require Import VST.veric.Clight_initial_world.
Require Import VST.floyd.assoclists.
Require Export VST.floyd.PTops.
Require Export VST.floyd.QPcomposite.
Require Export VST.floyd.quickprogram.
Require Export VST.floyd.Component.
Import compcert.lib.Maps.

Require Import VST.floyd.SeparationLogicAsLogic. (*Soundness.*)
Require Import VST.floyd.SeparationLogicAsLogicSoundness.

Require Import VST.floyd.VSU.
(*Require Import VST.veric.tcb.*)
Require Import VST.veric.juicy_mem. (*for mem_sub*)
Require Import VST.sepcomp.event_semantics. (*for mem_event*)
Require Import VST.veric.Clight_core. (*for inline_external_call_mem_events*)
Require Import VST.sepcomp.extspec.
Require Import VST.veric.SequentialClight2.

Lemma prog_of_component_irr {Espec Externs p Exports GP G}
      c X Y: @prog_of_component Espec Externs p Exports GP G c X = @prog_of_component Espec Externs p Exports GP G c Y.
Proof. unfold prog_of_component. destruct c. simpl. f_equal. f_equal. apply proof_irr. Qed.

Lemma prog_funct'_app {F V}: forall l1 l2,
      @prog_funct' F V (l1 ++ l2) = @prog_funct' F V l1 ++ @prog_funct' F V l2.
Proof. induction l1; simpl; intros. trivial.
  destruct a. destruct g. rewrite IHl1. trivial. trivial.
Qed.

Lemma augment_funspecs'_cons i fd fds' G:
  augment_funspecs' ((i, fd) :: fds') G = 
      match delete_id i G with
      | Some (f, G') =>
          match augment_funspecs' fds' G' with
          | Some G2 => Some ((i, f) :: G2)
          | None => None
          end
      | None =>
          match augment_funspecs' fds' G with
          | Some G2 => Some ((i, vacuous_funspec fd) :: G2)
          | None => None
          end
      end.
Proof. reflexivity. Qed.

Lemma delete_id_Some_In_inv: forall (G:funspecs)
      (HG : list_norepet (map fst G))
      i j (IJ: i <> j) phi GG,
      delete_id i G = Some (phi, GG) -> In j (map fst GG) -> In j (map fst G).
Proof. induction G; simpl in *; intros. inv H.
  destruct a. simpl in *. inv HG. if_tac in H.
  + subst i0. inv H; right; trivial.
  + remember (delete_id i G) as d; symmetry in Heqd; destruct d; [destruct p | ]; inv H.
    simpl in H0; destruct H0.
    - left; trivial.
    - right. eauto.
Qed.

Lemma delete_id_Some_find_id_other_inv: forall (G:funspecs)
      (HG: list_norepet (map fst G)) i phi GG 
      (Hi : delete_id i G = Some (phi, GG)) j
      (Hij : i <> j) psi
      (J : find_id j GG = Some psi),
      find_id j G = Some psi.
Proof. induction G; simpl; intros. inv Hi.
  destruct a. inv HG. specialize (IHG H2). 
  destruct (Memory.EqDec_ident j i0).
+ subst i0. rewrite if_false in Hi by trivial.
  remember (delete_id i G) as d; symmetry in Heqd; destruct d; [ destruct p |]; inv Hi.
  simpl in J; rewrite if_true in J by trivial. inv J; trivial.
+ destruct (ident_eq i i0).
  - subst i0; inv Hi. trivial.
  - remember (delete_id i G) as d; symmetry in Heqd; destruct d; [ destruct p |]; inv Hi.
    simpl in J; rewrite if_false in J by trivial.
    eauto.
Qed.

Lemma LNR_delete_id G: forall (LNR_G : list_norepet (map fst G))
        i (phi : funspec) GG
        (Hi: delete_id i G = Some (phi, GG)),
      list_norepet (map fst GG).
Proof. induction G; simpl in *; intros. inv Hi.
  destruct a. inv LNR_G. if_tac in Hi.
+ inv Hi; trivial.
+ remember (delete_id i G) as q; symmetry in Heqq; destruct q; [ destruct p |]; inv Hi.
  simpl. constructor.
  { intros N. apply H1; clear H1. eapply delete_id_Some_In_inv; eassumption. }
  eapply IHG; eauto.
Qed.

Lemma augment_funspecs'_map_fst l: forall G G1,
      augment_funspecs' l G = Some G1 -> map fst G = map fst G1 -> G1=G.
Proof. induction l; simpl; intros.
+ destruct G; inv H; trivial.
+ destruct a. remember (delete_id i G) as d; destruct d; symmetry in Heqd.
  - destruct p. remember (augment_funspecs' l l0) as w; destruct w; symmetry in Heqw; inv H.
    simpl in *. destruct G; simpl in *. congruence.
    destruct p. simpl in H0; inv H0. rewrite if_true in Heqd by trivial.
    inv Heqd. apply IHl in Heqw; subst; auto.
  - apply delete_id_None in Heqd. 
    remember (augment_funspecs' l G) as z; destruct z; symmetry in Heqz; inv H.
    elim Heqd. rewrite H0. left; trivial. 
Qed. 

Axiom semaxfunc_AX:
      forall Espec V G cs ge fdecls GG,
           @MainTheorem.CSHL_MinimumLogic.CSHL_Def.semax_func Espec V G cs ge fdecls GG ->
           @SeparationLogicSoundness.VericMinimumSeparationLogic.CSHL_Def.semax_func Espec V G cs ge fdecls GG.

Lemma WholeComponent_DrySafe:
 forall {Espec Externs p Exports GP mainspec} G 
  (NOMAIN: find_id (QP.prog_main p) G = None)
   (c: @Component Espec (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G))
  (z: OK_ty)
  (MAIN: exists post, mainspec = QPmain_spec_ext' p z post)
  (MAIN': isSome (PTree.get (QP.prog_main p) (QP.prog_defs p)))
  (EXT_OK: all_unspecified_OK p)
  (ALIGNED: QPall_initializers_aligned p = true) (* should be part of QPprogram_OK *)
  (DEFS_NOT_BUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs p)) = true)  (* should be part of QPprogram_OK *)
  (CBC: forall H,
    cenv_built_correctly
        (map compdef_of_compenv_element
           (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) 
           = Errors.OK tt)

  (dryspec : extspec.ext_spec OK_ty)
  (dessicate : forall ef : external_function,
            juicy_mem ->
            @ext_spec_type juicy_mem external_function
              (@OK_ty Espec) (@OK_spec Espec) ef ->
            @ext_spec_type mem external_function
              (@OK_ty Espec) dryspec ef)
  (Jsub: forall (ef : external_function) (se : Senv.t) (lv : list val) (m : mem) (t : Events.trace) 
                (v : val) (m' : mem) (EFI : ef_inline ef = true) 
                (m1 : Mem.mem') (EFC : Events.external_call ef se lv m t v m'),
         mem_sub m m1 ->
         exists (m1' : mem) (EFC1 : Events.external_call ef se lv m1 t v m1'),
            mem_sub m' m1' /\
           @proj1_sig (list mem_event) (fun trace : list mem_event => ev_elim m1 trace m1')
                      (inline_external_call_mem_events ef se lv m1 t v m1' EFI EFC1) =
           @proj1_sig (list mem_event) (fun trace : list mem_event => ev_elim m trace m')
                      (inline_external_call_mem_events ef se lv m t v m' EFI EFC))
  (Jframe : @extspec_frame (@OK_ty Espec) (@OK_spec Espec))
  (JDE : juicy_dry_ext_spec (@OK_ty Espec) (@OK_spec Espec) dryspec dessicate)
  (DME : ext_spec_mem_evolve (@OK_ty Espec) dryspec)
  (PAE : semax_prog.postcondition_allows_exit Espec tint)
  (Esub : forall (v : option val) (z : @OK_ty Espec)
         (m : mem) (m' : Mem.mem'),
       @ext_spec_exit mem external_function
         (@OK_ty Espec) dryspec v z m ->
       mem_sub m m' ->
       @ext_spec_exit mem external_function
         (@OK_ty Espec) dryspec v z m')
  prog
  (Hprog: prog = (prog_of_component c (CBC _)))
  m (Hm: Genv.init_mem prog = Some m)
  (HA: exists GG, augment_funspecs' (prog_funct prog) (G_merge [(QP.prog_main p, mainspec)] G) = Some GG
       /\ map fst (G_merge [(QP.prog_main p, mainspec)] G) = map fst GG),
exists (b : block) (q : CC_core) (m' : mem),
   @Genv.find_symbol (Ctypes.fundef function) type
     (@Genv.globalenv (Ctypes.fundef function) type prog)
     (@prog_main (Ctypes.fundef function) type prog) = @Some block b /\
   @semantics.initial_core CC_core mem (cl_core_sem (globalenv prog)) 0 m q m'
     (Vptr b Ptrofs.zero) [] /\
   (forall n : nat, @step_lemmas.dry_safeN (Genv.t Clight.fundef type) CC_core mem 
      (@OK_ty Espec) (@semax.genv_symb_injective Clight.fundef type)
      (cl_core_sem (globalenv prog)) dryspec
      {| genv_genv := @Genv.globalenv (Ctypes.fundef function) type prog;
        genv_cenv := @prog_comp_env function prog |} n z q m').
Proof.
  intros.
  eapply (whole_program_sequential_safety z dryspec); trivial. eassumption.
   instantiate (1:=(G_merge [(QP.prog_main p, mainspec)] G)). instantiate (1:= (QPvarspecs p)).
    subst prog.
    assert (SP:=WholeComponent_semax_progConstructive _ _ _ _ _ _ _ c NOMAIN _ MAIN MAIN' EXT_OK ALIGNED DEFS_NOT_BUILTIN CBC).
    clear - NOMAIN MAIN' SP. 
    destruct SP as [Hnames [Halign [Hcenv [Hsemaxfunc [Hglobvars Hmainspec]]]]].
    red. rewrite Hcenv in *. intuition.

   + (*semax_func*) clear Hmainspec. clear - Hsemaxfunc HA.
     remember (wholeprog_of_QPprog p (Comp_prog_OK c)
                      (cenv_built_correctly_e
                         (map compdef_of_compenv_element
                            (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
                         (composite_env_of_QPcomposite_env (QP.prog_comp_env p)
                            (projT1 (proj2 (Comp_prog_OK c)))) (CBC (projT1 (proj2 (Comp_prog_OK c)))))) as wp.
     remember (CBC (projT1 (proj2 (Comp_prog_OK c)))) as OK.
     remember (prog_of_component c OK) as prog.
     assert (wp = prog).
     {  subst. reflexivity. }
     clear Heqwp; subst wp. clear - Hsemaxfunc HA. destruct HA as [GGG [HA1 HA2]]. 

     specialize (augment_funspecs'_map_fst (prog_funct prog) (G_merge [(QP.prog_main p, mainspec)] G) _ HA1 HA2); intros.
     subst GGG.
     unfold augment_funspecs in Hsemaxfunc. rewrite HA1 in Hsemaxfunc.
     apply semaxfunc_AX in Hsemaxfunc. apply Hsemaxfunc.

   + clear Hglobvars Hsemaxfunc Hcenv Halign.
     remember (wholeprog_of_QPprog p (Comp_prog_OK c)
                      (cenv_built_correctly_e
                         (map compdef_of_compenv_element
                            (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
                         (composite_env_of_QPcomposite_env (QP.prog_comp_env p)
                            (projT1 (proj2 (Comp_prog_OK c)))) (CBC (projT1 (proj2 (Comp_prog_OK c)))))) as wp.
     remember (CBC (projT1 (proj2 (Comp_prog_OK c)))) as OK.
     remember (Ctypes.prog_main (prog_of_component c OK)) as main.
     assert (main = QP.prog_main p).
     { subst main. unfold prog_of_component. reflexivity. }

     remember (prog_of_component c OK) as prog.
     assert (wp = prog).
     {  subst. reflexivity. }
     clear Heqwp; subst wp.
     rewrite <- Heqmain in *.
     remember (find_id main (augment_funspecs prog (G_merge [(QP.prog_main p, mainspec)] G))). 

     destruct o; [ symmetry in Heqo | contradiction].
     assert (find_id main (G_merge [(QP.prog_main p, mainspec)] G) = Some f).
     2: rewrite H0; trivial.
     clear Hmainspec.
     assert (LNR_GM: list_norepet (map fst (G_merge [(QP.prog_main p, mainspec)] G))).
     { clear -c; apply Comp_G_LNR in c; trivial. }
     unfold augment_funspecs in Heqo.
     remember (augment_funspecs' (prog_funct prog) (G_merge [(QP.prog_main p, mainspec)] G)) as r. 
     destruct r; [symmetry in Heqr | inv Heqo].
     rewrite <- H in *. rename H into Hmain. rename f0 into AUG.
     apply G_merge_find_id_SomeNone;[ | trivial].
     simpl; rewrite if_true; trivial.
     assert (find_id main AUG = Some mainspec); [ clear Heqo | rewrite H in Heqo; trivial].
     assert (In main (map fst (prog_funct prog))).
     { destruct (Comp_G_in_Fundefs' c (QP.prog_main p) mainspec) as [fd X].
       { destruct c; simpl. rewrite if_true by trivial. rewrite <- Hmain in *; clear - NOMAIN. rewrite NOMAIN. trivial. }
       subst prog. destruct c; simpl in *. unfold prog_funct. simpl. rewrite <- Hmain in *. clear - X.
       rewrite prog_funct'_app, map_app. apply in_or_app. right.
       apply PTree.elements_correct in X. forget (PTree.elements (QP.prog_defs p)) as l. clear - X.
       induction l; simpl in *. trivial. destruct a. destruct X.
       + inv H. left. trivial.
       + destruct g. right. auto. auto. }
     assert (LNR_l: list_norepet (map fst (prog_funct prog))).
     { subst prog. clear - c Hnames. destruct c; simpl in *. unfold prog_funct; simpl. unfold prog_of_component in Hnames. simpl in Hnames. clear - Hnames.
       apply compute_list_norepet_e in Hnames. unfold prog_defs_names in Hnames. simpl in Hnames.
       forget (map of_builtin (QP.prog_builtins p) ++ PTree.elements (QP.prog_defs p)) as l.
       clear - Hnames.  induction l; simpl in *. trivial.
       destruct a; simpl in *. inv Hnames. specialize (IHl H2).
       destruct g; auto. simpl.
       constructor; trivial. intros N; apply H1; clear H1. clear - N.
       induction l; simpl in *. trivial.
       destruct a; simpl. destruct g; simpl in *.
       + destruct N. left; trivial. right; auto.
       + right; auto. } 
     forget (prog_funct prog) as l. clear - Heqr H NOMAIN LNR_GM LNR_l.
     remember (G_merge [(main, mainspec)] G) as GM. 
     assert (forall f, find_id main GM = Some f -> f=mainspec).
     { subst GM; simpl. rewrite if_true by trivial. intros. inv H0. rewrite NOMAIN. reflexivity. }
     clear NOMAIN.
     assert (GMmain: find_id main GM <> None). { subst GM; simpl. rewrite if_true by trivial. congruence. } 
     clear HeqGM. generalize dependent AUG. generalize dependent GM.
     induction l; intros.
     { simpl in Heqr. destruct GM; inv Heqr. simpl in H; contradiction. }
     destruct a. simpl in H. rewrite augment_funspecs'_cons in Heqr. (* Opaque G_merge.*)
     destruct (ident_eq i main).
     - subst i. clear H. remember (delete_id main GM) as w; symmetry in Heqw; destruct w.
       * destruct p. remember (augment_funspecs' l l0) as d; symmetry in Heqd; destruct d; inv Heqr.
         simpl. rewrite if_true by trivial. f_equal. apply H0; clear H0.
         apply delete_id_Some in Heqw; destruct Heqw; trivial.
         subst. apply find_id_i; trivial.
       * remember (augment_funspecs' l GM) as d; symmetry in Heqd; destruct d; inv Heqr.
         exfalso. clear - GMmain Heqw LNR_GM LNR_l. 
         induction GM; simpl in *. congruence.
         destruct a; simpl in *. if_tac in Heqw.
         ++ subst. inv Heqw.
         ++ rewrite if_false in GMmain by trivial. inv LNR_GM.
            destruct (delete_id main GM). destruct p. congruence. auto.
     - destruct H. contradiction.
       simpl in LNR_l. inv LNR_l. specialize (IHl H H4).
       remember (delete_id i GM) as d; symmetry in Heqd; destruct d.
       * destruct p. remember (augment_funspecs' l l0) as z; symmetry in Heqz; destruct z; inv Heqr.
         simpl. rewrite if_false by congruence. rename f1 into AUG1.
         apply (IHl l0); trivial; clear IHl.
         ++ eapply LNR_delete_id; eauto.
         ++ intros. apply H0; clear - n H1 Heqd LNR_GM. eapply delete_id_Some_find_id_other_inv; eauto.
         ++ rename l0 into GG.

            clear - GMmain Heqd n LNR_GM. rename f0 into phi. generalize dependent GG. generalize dependent phi.
            induction GM; simpl; intros. inv Heqd.
            destruct a. simpl in *. inv LNR_GM. rename i0 into j. 
            if_tac in GMmain.
            { subst j. rewrite if_false in Heqd by trivial.
              remember (delete_id i GM) as w; symmetry in Heqw; destruct w; [ destruct p |]; inv Heqd.
              simpl; rewrite if_true by trivial. congruence. }
            if_tac in Heqd.
            { inv Heqd; trivial. }
            remember (delete_id i GM) as w; symmetry in Heqw; destruct w; [ destruct p |]; inv Heqd.
            simpl. rewrite if_false by trivial.
            apply (IHGM H2 GMmain _ _ (eq_refl _)).
   * remember (augment_funspecs' l GM) as z; symmetry in Heqz; destruct z; inv Heqr.
     simpl. rewrite if_false by congruence. rename f0 into GG.
     apply (IHl GM LNR_GM H0 GMmain _ Heqz).
Qed.

Lemma WholeComponent_DrySafe':
 forall {Espec Externs p Exports GP mainspec} G 
  (NOMAIN: find_id (QP.prog_main p) G = None)
   (c: @Component Espec (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G))
  (z: OK_ty)
  (MAIN: exists post, mainspec = QPmain_spec_ext' p z post)
  (MAIN': isSome (PTree.get (QP.prog_main p) (QP.prog_defs p)))
  (EXT_OK: all_unspecified_OK p)
  (ALIGNED: QPall_initializers_aligned p = true) (* should be part of QPprogram_OK *)
  (DEFS_NOT_BUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs p)) = true)  (* should be part of QPprogram_OK *)
  (CBC: forall H,
    cenv_built_correctly
        (map compdef_of_compenv_element
           (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) 
           = Errors.OK tt)

  (dryspec : extspec.ext_spec OK_ty)
  (dessicate : forall ef : external_function,
            juicy_mem ->
            @ext_spec_type juicy_mem external_function
              (@OK_ty Espec) (@OK_spec Espec) ef ->
            @ext_spec_type mem external_function
              (@OK_ty Espec) dryspec ef)
  (Jsub: forall (ef : external_function) (se : Senv.t) (lv : list val) (m : mem) (t : Events.trace) 
                (v : val) (m' : mem) (EFI : ef_inline ef = true) 
                (m1 : Mem.mem') (EFC : Events.external_call ef se lv m t v m'),
         mem_sub m m1 ->
         exists (m1' : mem) (EFC1 : Events.external_call ef se lv m1 t v m1'),
            mem_sub m' m1' /\
           @proj1_sig (list mem_event) (fun trace : list mem_event => ev_elim m1 trace m1')
                      (inline_external_call_mem_events ef se lv m1 t v m1' EFI EFC1) =
           @proj1_sig (list mem_event) (fun trace : list mem_event => ev_elim m trace m')
                      (inline_external_call_mem_events ef se lv m t v m' EFI EFC))
  (Jframe : @extspec_frame (@OK_ty Espec) (@OK_spec Espec))
  (JDE : juicy_dry_ext_spec (@OK_ty Espec) (@OK_spec Espec) dryspec dessicate)
  (DME : ext_spec_mem_evolve (@OK_ty Espec) dryspec)
  (PAE : semax_prog.postcondition_allows_exit Espec tint)
  (Esub : forall (v : option val) (z : @OK_ty Espec)
         (m : mem) (m' : Mem.mem'),
       @ext_spec_exit mem external_function
         (@OK_ty Espec) dryspec v z m ->
       mem_sub m m' ->
       @ext_spec_exit mem external_function
         (@OK_ty Espec) dryspec v z m')
  prog
  (Hprog: prog = (prog_of_component c (CBC _)))
  m (Hm: Genv.init_mem prog = Some m)
  (HA: exists GG, augment_funspecs prog (G_merge [(QP.prog_main p, mainspec)] G) = GG
       /\ map fst (G_merge [(QP.prog_main p, mainspec)] G) = map fst GG),
exists (b : block) (q : CC_core) (m' : mem),
   @Genv.find_symbol (Ctypes.fundef function) type
     (@Genv.globalenv (Ctypes.fundef function) type prog)
     (@prog_main (Ctypes.fundef function) type prog) = @Some block b /\
   @semantics.initial_core CC_core mem (cl_core_sem (globalenv prog)) 0 m q m'
     (Vptr b Ptrofs.zero) [] /\
   (forall n : nat, @step_lemmas.dry_safeN (Genv.t Clight.fundef type) CC_core mem 
      (@OK_ty Espec) (@semax.genv_symb_injective Clight.fundef type)
      (cl_core_sem (globalenv prog)) dryspec
      {| genv_genv := @Genv.globalenv (Ctypes.fundef function) type prog;
        genv_cenv := @prog_comp_env function prog |} n z q m').
Proof.
  intros. eapply (@WholeComponent_DrySafe Espec Externs p Exports GP mainspec G); try eassumption.
  clear - HA. destruct HA as [GG [HG1 HG2]]. unfold augment_funspecs in HG1.
  remember (augment_funspecs' (prog_funct prog) (G_merge [(QP.prog_main p, mainspec)] G)).
  destruct o. + subst f. exists GG. split; auto. +
  subst. inv HG2.
Qed.
(* (*
Lemma WholeComponent_DrySafe:
 forall {Espec Externs p Exports GP mainspec} (*
  (c: exists G, 
    find_id (QP.prog_main p) G = None /\
     @Component Espec (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G))*)
G (NOMAIN: find_id (QP.prog_main p) G = None)
   (c: @Component Espec (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G))
  (z: OK_ty)
  (MAIN: exists post, mainspec = QPmain_spec_ext' p z post)
  (MAIN': isSome (PTree.get (QP.prog_main p) (QP.prog_defs p)))
  (EXT_OK: all_unspecified_OK p)
  (ALIGNED: QPall_initializers_aligned p = true) (* should be part of QPprogram_OK *)
  (DEFS_NOT_BUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs p)) = true)  (* should be part of QPprogram_OK *)
  (CBC: forall H,
    cenv_built_correctly
        (map compdef_of_compenv_element
           (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) 
           = Errors.OK tt)

  (dryspec : extspec.ext_spec OK_ty)
  (dessicate : forall ef : external_function,
            juicy_mem ->
            @ext_spec_type juicy_mem external_function
              (@OK_ty Espec) (@OK_spec Espec) ef ->
            @ext_spec_type mem external_function
              (@OK_ty Espec) dryspec ef)
  (Jsub: forall (ef : external_function) (se : Senv.t) (lv : list val) (m : mem) (t : Events.trace) 
                (v : val) (m' : mem) (EFI : ef_inline ef = true) 
                (m1 : Mem.mem') (EFC : Events.external_call ef se lv m t v m'),
         mem_sub m m1 ->
         exists (m1' : mem) (EFC1 : Events.external_call ef se lv m1 t v m1'),
            mem_sub m' m1' /\
           @proj1_sig (list mem_event) (fun trace : list mem_event => ev_elim m1 trace m1')
                      (inline_external_call_mem_events ef se lv m1 t v m1' EFI EFC1) =
           @proj1_sig (list mem_event) (fun trace : list mem_event => ev_elim m trace m')
                      (inline_external_call_mem_events ef se lv m t v m' EFI EFC))
  (Jframe : @extspec_frame (@OK_ty Espec) (@OK_spec Espec))
  (JDE : juicy_dry_ext_spec (@OK_ty Espec) (@OK_spec Espec) dryspec dessicate)
  (DME : ext_spec_mem_evolve (@OK_ty Espec) dryspec)
  (PAE : semax_prog.postcondition_allows_exit Espec tint)
  (Esub : forall (v : option val) (z : @OK_ty Espec)
         (m : mem) (m' : Mem.mem'),
       @ext_spec_exit mem external_function
         (@OK_ty Espec) dryspec v z m ->
       mem_sub m m' ->
       @ext_spec_exit mem external_function
         (@OK_ty Espec) dryspec v z m')
  prog (* (Hprog: program_of_QPprogram p = Errors.OK prog)*)
  (Hprog: prog = (prog_of_component c (CBC _)))
  m (Hm: Genv.init_mem prog = Some m),
  P.
Proof.
  intros.
 (*
  assert (c: exists G, 
    find_id (QP.prog_main p) G = None /\
     @Component Espec (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G)).
  { exists G. split; trivial. }*)
  destruct (WholeComponent_semax_prog'' G NOMAIN c z MAIN MAIN' EXT_OK ALIGNED DEFS_NOT_BUILTIN CBC) as
  [cs [OK (*[GG*) SP(*]*)]].
assert (exists (b : block) (q : CC_core) (m' : mem),
   @Genv.find_symbol (Ctypes.fundef function) type
     (@Genv.globalenv (Ctypes.fundef function) type prog)
     (@prog_main (Ctypes.fundef function) type prog) = @Some block b /\
   @semantics.initial_core CC_core mem (cl_core_sem (globalenv prog)) 0 m q m'
     (Vptr b Ptrofs.zero) [] /\
   (forall n : nat,
    @step_lemmas.dry_safeN (Genv.t Clight.fundef type) CC_core mem 
      (@OK_ty Espec) (@semax.genv_symb_injective Clight.fundef type)
      (cl_core_sem (globalenv prog)) dryspec
      {|
        genv_genv := @Genv.globalenv (Ctypes.fundef function) type prog;
        genv_cenv := @prog_comp_env function prog
      |} n z q m')).
  { eapply (whole_program_sequential_safety z dryspec); trivial. eassumption.
   instantiate (1:=(G_merge [(QP.prog_main p, mainspec)] G)). instantiate (1:= (QPvarspecs p)).
    subst prog. clear - NOMAIN MAIN' SP.
    destruct SP as [Hnames [Halign [Hcenv [Hsemaxfunc [Hglobvars Hmainspec]]]]].
    red. intuition.
   + (*semax_func*) clear Hmainspec.
Search MainTheorem.CSHL_MinimumLogic.CSHL_Def.semax_func. Search MainTheorem.CSHL_Def.semax_func.
       unfold MainTheorem.CSHL_MinimumLogic.CSHL_Def.semax_func in Hsemaxfunc.
(*Search MainTheorem.CSHL_Def.semax_func.*)
       unfold SeparationLogicSoundness.VericMinimumSeparationLogic.CSHL_Def.semax_func.
Search semax_prog.semax_func.
       admit.
   + clear Hglobvars Hsemaxfunc Hcenv Halign.
     rewrite (prog_of_component_irr c _ OK). clear CBC.
     remember (Ctypes.prog_main (prog_of_component c OK)) as main.
     assert (main = QP.prog_main p).
     { subst main. unfold prog_of_component. reflexivity. }
     remember (prog_of_component c OK) as prog.
     remember (find_id main (augment_funspecs prog (G_merge [(QP.prog_main p, mainspec)] G))). 
     destruct o; [ symmetry in Heqo | contradiction].
     assert (find_id main (G_merge [(QP.prog_main p, mainspec)] G) = Some f).
     2: rewrite H0; trivial.
     clear Hmainspec.
     assert (LNR_GM: list_norepet (map fst (G_merge [(QP.prog_main p, mainspec)] G))).
     { clear -c; apply Comp_G_LNR in c; trivial. }
     unfold augment_funspecs in Heqo.
     remember (augment_funspecs' (prog_funct prog) (G_merge [(QP.prog_main p, mainspec)] G)) as r. 
     destruct r; [symmetry in Heqr | inv Heqo].
     rewrite <- H in *. rename H into Hmain. rename f0 into AUG.
     apply G_merge_find_id_SomeNone;[ | trivial].
     simpl; rewrite if_true; trivial.
     assert (find_id main AUG = Some mainspec); [ clear Heqo | rewrite H in Heqo; trivial].
     assert (In main (map fst (prog_funct prog))).
     { destruct (Comp_G_in_Fundefs' c (QP.prog_main p) mainspec) as [fd X].
       { destruct c; simpl. rewrite if_true by trivial. rewrite <- Hmain in *; clear - NOMAIN. rewrite NOMAIN. trivial. }
       subst prog. destruct c; simpl in *. unfold prog_funct. simpl. rewrite <- Hmain in *. clear - X.
       rewrite prog_funct'_app, map_app. apply in_or_app. right.
       apply PTree.elements_correct in X. forget (PTree.elements (QP.prog_defs p)) as l. clear - X.
       induction l; simpl in *. trivial. destruct a. destruct X.
       + inv H. left. trivial.
       + destruct g. right. auto. auto. }
     assert (LNR_l: list_norepet (map fst (prog_funct prog))).
     { subst prog. clear - c Hnames. destruct c; simpl in *. unfold prog_funct; simpl. unfold prog_of_component in Hnames. simpl in Hnames. clear - Hnames.
       apply compute_list_norepet_e in Hnames. unfold prog_defs_names in Hnames. simpl in Hnames.
       forget (map of_builtin (QP.prog_builtins p) ++ PTree.elements (QP.prog_defs p)) as l.
       clear - Hnames.  induction l; simpl in *. trivial.
       destruct a; simpl in *. inv Hnames. specialize (IHl H2).
       destruct g; auto. simpl.
       constructor; trivial. intros N; apply H1; clear H1. clear - N.
       induction l; simpl in *. trivial.
       destruct a; simpl. destruct g; simpl in *.
       + destruct N. left; trivial. right; auto.
       + right; auto. } 
     forget (prog_funct prog) as l. clear - Heqr H NOMAIN LNR_GM LNR_l.
     remember (G_merge [(main, mainspec)] G) as GM. 
     assert (forall f, find_id main GM = Some f -> f=mainspec).
     { subst GM; simpl. rewrite if_true by trivial. intros. inv H0. rewrite NOMAIN. reflexivity. }
     clear NOMAIN.
     assert (GMmain: find_id main GM <> None). { subst GM; simpl. rewrite if_true by trivial. congruence. } 
     clear HeqGM. generalize dependent AUG. generalize dependent GM.
     induction l; intros.
     { simpl in Heqr. destruct GM; inv Heqr. simpl in H; contradiction. }
     destruct a. simpl in H. rewrite augment_funspecs'_cons in Heqr. (* Opaque G_merge.*)
     destruct (ident_eq i main).
     - subst i. clear H. remember (delete_id main GM) as w; symmetry in Heqw; destruct w.
       * destruct p. remember (augment_funspecs' l l0) as d; symmetry in Heqd; destruct d; inv Heqr.
         simpl. rewrite if_true by trivial. f_equal. apply H0; clear H0.
         apply delete_id_Some in Heqw; destruct Heqw; trivial.
         subst. apply find_id_i; trivial.
       * remember (augment_funspecs' l GM) as d; symmetry in Heqd; destruct d; inv Heqr.
         exfalso. clear - GMmain Heqw LNR_GM LNR_l. 
         induction GM; simpl in *. congruence.
         destruct a; simpl in *. if_tac in Heqw.
         ++ subst. inv Heqw.
         ++ rewrite if_false in GMmain by trivial. inv LNR_GM.
            destruct (delete_id main GM). destruct p. congruence. auto.
     - destruct H. contradiction.
       simpl in LNR_l. inv LNR_l. specialize (IHl H H4).
       remember (delete_id i GM) as d; symmetry in Heqd; destruct d.
       * destruct p. remember (augment_funspecs' l l0) as z; symmetry in Heqz; destruct z; inv Heqr.
         simpl. rewrite if_false by congruence. rename f1 into AUG1.
         apply (IHl l0); trivial; clear IHl.
         ++ eapply LNR_delete_id; eauto.
         ++ intros. apply H0; clear - n H1 Heqd LNR_GM. eapply delete_id_Some_find_id_other_inv; eauto.
         ++ rename l0 into GG.

            clear - GMmain Heqd n LNR_GM. rename f0 into phi. generalize dependent GG. generalize dependent phi.
            induction GM; simpl; intros. inv Heqd.
            destruct a. simpl in *. inv LNR_GM. rename i0 into j. 
            if_tac in GMmain.
            { subst j. rewrite if_false in Heqd by trivial.
              remember (delete_id i GM) as w; symmetry in Heqw; destruct w; [ destruct p |]; inv Heqd.
              simpl; rewrite if_true by trivial. congruence. }
            if_tac in Heqd.
            { inv Heqd; trivial. }
            remember (delete_id i GM) as w; symmetry in Heqw; destruct w; [ destruct p |]; inv Heqd.
            simpl. rewrite if_false by trivial.
            apply (IHGM H2 GMmain _ _ (eq_refl _)).
   * remember (augment_funspecs' l GM) as z; symmetry in Heqz; destruct z; inv Heqr.
     simpl. rewrite if_false by congruence. rename f0 into GG.
     apply (IHl GM LNR_GM H0 GMmain _ Heqz).
Qed.

Definition WholeProgSafeType  {Espec E p Exports GP mainspec}
       (c: exists G, 
             find_id (QP.prog_main p) G = None /\
             @Component Espec (QPvarspecs p) E nil p Exports GP 
         (G_merge
                 [(QP.prog_main p, mainspec)] G))
             (z: @OK_ty Espec) :=
 exists cs, exists OK, exists CBC, exists G,
@semax_prog Espec cs
   (wholeprog_of_QPprog p OK
    (cenv_built_correctly_e
         (map compdef_of_compenv_element
            (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 OK)))
         CBC))
    z (QPvarspecs p) 
      (G_merge [(QP.prog_main p, mainspec)] G)

Lemma WholeComponent_drySafe:
 forall {Espec Externs p Exports GP mainspec}
  (c: exists G, 
    find_id (QP.prog_main p) G = None /\
     @Component Espec (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G))
  (z: OK_ty)
  (MAIN: exists post, mainspec = QPmain_spec_ext' p z post)
  (MAIN': isSome (PTree.get (QP.prog_main p) (QP.prog_defs p)))
  (EXT_OK: all_unspecified_OK p)
  (ALIGNED: QPall_initializers_aligned p = true) (* should be part of QPprogram_OK *)
  (DEFS_NOT_BUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs p)) = true)  (* should be part of QPprogram_OK *)
  (CBC: forall H,
    cenv_built_correctly
        (map compdef_of_compenv_element
           (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) 
           = Errors.OK tt)*),
  (*WholeProgSafeType c z*)
*)
