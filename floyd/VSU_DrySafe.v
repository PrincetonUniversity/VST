Require Import VST.floyd.proofauto.
Require Import VST.veric.Clight_initial_world.
Require Import VST.floyd.assoclists.
Require Export VST.floyd.PTops.
Require Export VST.floyd.QPcomposite.
Require Export VST.floyd.quickprogram.
Require Export VST.floyd.Component.

Require Import VST.floyd.SeparationLogicAsLogic. (*Soundness.*)
Require Import VST.floyd.SeparationLogicAsLogicSoundness.

Require Import VST.floyd.VSU.
Require Import VST.veric.juicy_mem. (*for mem_sub*)
Require Import VST.sepcomp.event_semantics. (*for mem_event*)
Require Import VST.veric.Clight_core. (*for inline_external_call_mem_events*)
Require Import VST.sepcomp.extspec. (*for ext_spec_type.*) 
Require Import VST.veric.SequentialClight. (*for extspec_frame *)

Local Unset SsrRewrite.

Section VST.

Context `{!VSTGS OK_ty Σ}.

Lemma prog_of_component_irr {Espec Externs p Exports GP G}
      c X Y: @prog_of_component _ _ _ Espec Externs p Exports GP G c X = @prog_of_component _ _ _ Espec Externs p Exports GP G c Y.
Proof. unfold prog_of_component. destruct c. simpl. f_equal. f_equal. apply proof_irr. Qed.

Lemma wholeprog_of_QPprog_irr p ok X Y: wholeprog_of_QPprog p ok X = wholeprog_of_QPprog p ok Y.
Proof. unfold wholeprog_of_QPprog. f_equal. apply proof_irr. Qed.

Lemma wholeprog_of_QPprog_irr_strong p ok ok' X Y: wholeprog_of_QPprog p ok X = wholeprog_of_QPprog p ok' Y.
Proof.
assert (ok = ok').
{ destruct ok; destruct ok'. f_equal; apply proof_irr. }
subst ok'. apply wholeprog_of_QPprog_irr.
Qed.

Lemma prog_funct'_app {F V}: forall l1 l2,
      @prog_funct' F V (l1 ++ l2) = @prog_funct' F V l1 ++ @prog_funct' F V l2.
Proof. induction l1; simpl; intros. trivial.
  destruct a. destruct g. rewrite IHl1. trivial. trivial.
Qed.

Lemma delete_id_elim {A}: forall {G i x GG}, 
      @delete_id A i G = Some (x, GG) ->
      exists n, G = Floyd_firstn n GG ++ (i, x) :: Floyd_skipn n GG.
Proof. induction G; simpl; intros. inv H. destruct a as [j b].
destruct (ident_eq i j); subst.
+ inv H. exists O; simpl; trivial.
+ specialize (IHG i). destruct (delete_id i G); [ | inv H].
   destruct p; inv H. destruct (IHG _ _ (eq_refl _)) as [k K]; clear IHG.
   subst. exists (S k); simpl; trivial.
Qed.

Lemma delete_id_Some_In_inv: forall (G:@funspecs Σ)
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

Lemma delete_id_Some_find_id_other_inv: forall (G:@funspecs Σ)
      (HG: list_norepet (map fst G)) i phi GG 
      (Hi : delete_id i G = Some (phi, GG)) j
      (Hij : i <> j) psi
      (J : find_id j GG = Some psi),
      find_id j G = Some psi.
Proof. induction G; simpl; intros. inv Hi.
  destruct a. inv HG. specialize (IHG H2). 
  if_tac.
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

Lemma augment_funspecs_find_id_None i: forall p G,
      find_id i G = None-> 
      find_id i (prog_funct p) = None ->
      find_id i (augment_funspecs p G) = None.
Proof.
  intros p. unfold augment_funspecs. forget (prog_funct p) as l. clear p.
  induction l; simpl; intros G.
+ intros. destruct G; simpl; intros; trivial.
+ destruct a as [j phi]; if_tac; subst; intros; try discriminate.
  remember (delete_id j G) as d; symmetry in Heqd; destruct d.
  - destruct p as [f GG]. specialize (IHl GG).
    destruct (augment_funspecs' l GG); trivial.
    simpl. rewrite if_false by trivial. apply IHl; trivial.
    specialize (delete_id_elim Heqd) as [n N]. subst. clear - H0 H.
    rewrite assoclists.find_id_app_char in H0.
    rewrite <- (Floyd_firstn_skipn n GG).
    rewrite assoclists.find_id_app_char.
    destruct (find_id i (Floyd_firstn n GG)); trivial.
    simpl in H0. rewrite if_false in H0; trivial.
  - specialize (IHl G). destruct (augment_funspecs' l G); simpl; trivial.
    rewrite if_false; trivial. auto.
Qed.

Lemma augment_funspecs_eq: forall p G, map fst G = map fst (prog_funct p) ->
  (augment_funspecs p G) = G.
Proof. intros.
unfold augment_funspecs.
forget (prog_funct p) as fds.
clear p.
revert G H; induction fds; destruct G; simpl; intros; inv H. trivial.
destruct a.
destruct p.
simpl in H1; subst i0.
rewrite if_true by auto.
specialize (IHfds G H2).
destruct (augment_funspecs' fds G) as [G' | ] eqn:?H.
2:{ destruct G; inv IHfds. destruct fds; inv H2. }
subst; trivial.
Qed.

(*Now trivial*)
Lemma augment_funspecs_sub: forall p G, map fst G = map fst (prog_funct p) ->
Forall2 (fun fs1 fs2 : ident * funspec => fst fs1 = fst fs2 /\ funspec_sub (snd fs1) (snd fs2)) G
  (augment_funspecs p G).
Proof. intros.
unfold augment_funspecs.
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
2:{ destruct G; inv IHfds. destruct fds; inv H2. }
constructor.
split; auto.
simpl.
apply funspec_sub_refl.
auto.
Qed.

Axiom semaxfunc_AX:
      forall Espec V G cs ge fdecls GG,
           MainTheorem.CSHL_MinimumLogic.CSHL_Def.semax_func (OK_spec := Espec) V G (C := cs) ge fdecls GG ->
           SeparationLogicSoundness.VericMinimumSeparationLogic.CSHL_Def.semax_func _ _ _ Espec V G cs ge fdecls GG.

End VST.

Lemma WholeComponent_DrySafe:
 forall Σ `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty} {Externs p Exports}
  {GP : forall `{VSTGS OK_ty Σ}, globals -> mpred} (mainspec : forall `{VSTGS OK_ty Σ}, funspec) (G : forall `{VSTGS OK_ty Σ}, funspecs)
  (NOMAIN: forall `{VSTGS OK_ty Σ}, find_id (QP.prog_main p) G = None)
   (c: forall {HH : VSTGS OK_ty Σ}, Component (Espec := Espec) (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G))
  (z: OK_ty)
  (MAIN: forall {HH : VSTGS OK_ty Σ}, exists post, mainspec = QPmain_spec_ext' p z post)
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
  (EXIT: forall {HH : VSTGS OK_ty Σ}, semax_prog.postcondition_allows_exit Espec tint)
  (Hdry : forall {HH : VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)

  wholeprog (X : forall {HH : VSTGS OK_ty Σ}, _)
  (Hprog: forall {HH : VSTGS OK_ty Σ}, wholeprog = wholeprog_of_QPprog p (Comp_prog_OK c) X)
  m (Hm: Genv.init_mem wholeprog = Some m),
exists (b : block) (q : CC_core),
   @Genv.find_symbol (Ctypes.fundef function) type
     (@Genv.globalenv (Ctypes.fundef function) type wholeprog)
     (prog_main wholeprog) = @Some block b /\
   @semantics.initial_core CC_core mem (cl_core_sem (globalenv wholeprog)) 0 m q m
     (Vptr b Ptrofs.zero) [] /\
   (forall n : nat, @step_lemmas.dry_safeN (Genv.t Clight.fundef type) CC_core mem
      (OK_ty) (@semax.genv_symb_injective Clight.fundef type)
      (cl_core_sem (globalenv wholeprog)) dryspec
      {| genv_genv := @Genv.globalenv (Ctypes.fundef function) type wholeprog;
        genv_cenv := @prog_comp_env function wholeprog |} n z q m).
Proof.
  intros.
  eapply whole_program_sequential_safety_ext; trivial.
  instantiate (1:= fun (HH : VSTGS OK_ty Σ) => augment_funspecs wholeprog (G_merge [(QP.prog_main p, mainspec HH)] (G HH))).
  instantiate (1:= (QPvarspecs p)).
  intros.
  assert (SP:=WholeComponent_semax_progConstructive _ _ _ _ _ _ _ (c HH) (NOMAIN HH) _ (MAIN HH) MAIN' EXT_OK ALIGNED DEFS_NOT_BUILTIN CBC).
  clear - NOMAIN MAIN' SP Hprog.
  specialize (Hprog HH).
  destruct SP as [Hnames [Halign [Hcenv [Hsemaxfunc [Hglobvars Hmainspec]]]]].
  remember (wholeprog_of_QPprog p (Comp_prog_OK (c HH))
                     (cenv_built_correctly_e
                        (map compdef_of_compenv_element
                           (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
                        (composite_env_of_QPcomposite_env (QP.prog_comp_env p)
                           (projT1 (proj2 (Comp_prog_OK (c HH)))))
                        (CBC (projT1 (proj2 (Comp_prog_OK (c HH))))))) as w.
  assert (WP: w = wholeprog) by (subst; apply wholeprog_of_QPprog_irr).
  clear Heqw; subst w.
  eexists. red. intuition.
  1: apply Hcenv.
  1: eapply semaxfunc_AX; apply Hsemaxfunc.
Qed.
