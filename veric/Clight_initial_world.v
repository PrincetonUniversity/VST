Require Import VST.veric.juicy_base.
Require Import VST.veric.external_state.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.

Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.

Require Export VST.veric.initial_world.

Import Clight.

Obligation Tactic := idtac.

Notation initial_core := (initial_core(F := function)).
Notation prog_funct := (@prog_funct function).
Notation prog_vars := (@prog_vars function).

Section mpred.

Context `{!heapGS Σ}.

Inductive match_fdecs: list  (ident * Clight.fundef) -> funspecs -> Prop :=
| match_fdecs_nil: match_fdecs nil nil
| match_fdecs_cons: forall i fd fspec fs G,
                  type_of_fundef fd = @type_of_funspec Σ fspec ->
                  match_fdecs fs G ->
                  match_fdecs ((i,fd)::fs) ((i,fspec)::G)
(* EXPERIMENT
| match_fdecs_skip: forall ifd fs G,
                 match_fdecs fs G ->
                 match_fdecs (ifd::fs) G*)
.

Lemma match_fdecs_exists_Gfun:
  forall prog G i f,
    find_id i G = Some f ->
    match_fdecs (prog_funct prog) G ->
    exists fd,   In (i, Gfun fd) (prog_defs prog) /\
                     type_of_fundef fd = type_of_funspec f.
Proof. unfold prog_funct. unfold prog_defs_names.
intros ? ? ? ?.
forget (prog_defs prog) as dl.
revert G; induction dl; simpl; intros.
inv H0. inv H.
destruct a as [i' [?|?]].
inv H0.
simpl in H; if_tac in H. subst i'; inv H.
eauto.
destruct (IHdl G0) as [fd [? ?]]; auto.
exists fd; split; auto.
destruct (IHdl G) as [fd [? ?]]; auto.
exists fd; split; auto.
(* EXPERIMENT
destruct (IHdl G) as [fd [? ?]]; auto.
exists fd; split; auto.
*)
Qed.

(*Lemma initial_jm_without_locks prog m:
  Genv.init_mem prog = Some m ->
  (* mem_auth m ∗ *) inflate_initial_mem m ⊢ no_locks.
Proof.
  rewrite /initial_mem /no_locks.
  iIntros "(%m & %Hinit & Hm)" (?????).
  iApply (bi.impl_intro_r with "Hm"); iIntros "H".
Abort.*)

(* How to relate Gamma to funspecs in memory, once we are outside the
   semax proofs?  We define 'matchfunspecs' which will be satisfied by
   the initial memory, and preserved under steps. *)

Definition matchfunspecs (ge : genv) (G : funspecs) E : mpred :=
  ∀ b:block, ∀ fs: funspec,
  func_at fs (b,0%Z) →
  ∃ id:ident, ∃ fs0: funspec, 
   ⌜Genv.find_symbol ge id = Some b /\ find_id id G = Some fs0⌝ ∧
     funspec_sub_si E fs0 fs.
(* This seems backwards -- why do we need to know that there are no other function pointers? *)

(*Lemma initial_jm_matchfunspecs prog G E:
  initial_core (globalenv prog) G ⊢ matchfunspecs (globalenv prog) G E.
Proof.
  rewrite /initial_core /matchfunspecs.
  iIntros "#H" (??) "#f".
  
  iDestruct ("H" $! b fs) as "[_ Hf]".
  iDestruct ("Hf" with "f") as %(id & ?%Genv.invert_find_symbol & ?).
  iExists id, fs; iSplit; first done.
  iApply funspec_sub_si_refl.
Qed.*)

End mpred.

Lemma prog_funct'_incl : forall {F V} (l : list (ident * globdef F V)), incl (map fst (prog_funct' l)) (map fst l).
Proof.
  induction l; simpl.
  - apply incl_nil_l.
  - destruct a, g; simpl.
    + by apply incl_same_head.
    + by apply incl_tl.
Qed.

Lemma prog_funct_norepet : forall (prog : program), list_norepet (prog_defs_names prog) -> list_norepet (map fst (prog_funct prog)).
Proof.
  destruct prog; rewrite /prog_funct /prog_defs_names /=.
  clear; induction prog_defs; auto; simpl.
  inversion 1; subst.
  destruct a, g; auto; simpl.
  constructor; auto.
  intros ?%prog_funct'_incl; done.
Qed.

Lemma match_ids : forall {Σ} fs G i, @match_fdecs Σ fs G -> In i (map fst fs) ↔ In i (map fst G).
Proof.
  induction 1; simpl; first done.
  rewrite IHmatch_fdecs //.
Qed.

Lemma match_fdecs_norepet : forall {Σ} fs G, @match_fdecs Σ fs G -> list_norepet (map fst fs) ↔ list_norepet (map fst G).
Proof.
  induction 1; simpl; first done.
  split; inversion 1; subst; constructor; try tauto; by [rewrite -match_ids | rewrite match_ids].
Qed.

(* compute the size of blocks allocated by Genv.alloc_globals *)
Fixpoint globals_bounds {F V} b (gl : list (ident * globdef F V)) :=
  match gl with
  | [] => fun _ => (0, O)
  | g :: gl' => let bounds' := globals_bounds (b + 1)%positive gl' in
      fun c => if eq_dec c b then
        match g.2 with
        | Gfun _ => (0, 1%nat)
        | Gvar v => let init := gvar_init v in
                    let sz := init_data_list_size init in
                    (0, Z.to_nat sz)
        end else bounds' c
  end.

Definition block_bounds {F V} (p : AST.program F V) := globals_bounds 1%positive (AST.prog_defs p).

Lemma globals_bounds_min : forall {F V} b0 (gl : list (ident * globdef F V)) b, (b < b0)%positive ->
  globals_bounds b0 gl b = (0, 0%nat).
Proof.
  intros until gl; revert b0; induction gl; simpl; intros; first done.
  rewrite if_false; last lia.
  apply IHgl; lia.
Qed.

Lemma globals_bounds_app1 : forall {F V} b0 (gl1 gl2 : list (ident * globdef F V)) b,
  (Pos.to_nat b < Pos.to_nat b0 + length gl1)%nat -> globals_bounds b0 (gl1 ++ gl2) b = globals_bounds b0 gl1 b.
Proof.
  intros; revert dependent b0; induction gl1; simpl; intros.
  { apply globals_bounds_min; lia. }
  if_tac; first done.
  apply IHgl1; lia.
Qed.

Lemma globals_bounds_nth : forall {F V} b0 (gl : list (ident * globdef F V)) b i g (Hb0 : (b0 <= b)%positive),
  nth_error gl (Pos.to_nat b - Pos.to_nat b0) = Some (i, g) ->
  globals_bounds b0 gl b = match g with
                           | Gfun _ => (0, 1%nat)
                           | Gvar v => let init := gvar_init v in let sz := init_data_list_size init in (0, Z.to_nat sz)
                           end.
Proof.
  intros; revert dependent b0; induction gl; simpl; intros.
  - rewrite nth_error_nil // in H.
  - destruct (Pos.to_nat b - Pos.to_nat b0)%nat eqn: Hn; simpl in H.
    + inv H.
      rewrite if_true //; lia.
    + rewrite if_false; last lia.
      apply IHgl; try lia.
      replace (_ - _)%nat with n by lia; done.
Qed.

Lemma block_bounds_nth : forall {F V} (prog : AST.program F V) b i g,
  nth_error (AST.prog_defs prog) (Z.to_nat (Z.pos b - 1)) = Some (i, g) ->
  block_bounds prog b = match g with
                           | Gfun _ => (0, 1%nat)
                           | Gvar v => let init := gvar_init v in let sz := init_data_list_size init in (0, Z.to_nat sz)
                           end.
Proof.
  intros; eapply globals_bounds_nth; first lia.
  by rewrite Z2Nat.inj_sub // Z2Nat.inj_pos in H.
Qed.

Require Import VST.veric.wsat.

(* Should we compute the block bounds from Genv.init_mem, or leave them arbitrary?
   We at least need to know that they include 0 for all function pointers. *)
Lemma alloc_initial_state  `{!inG Σ (excl_authR (leibnizO Z))} `{!wsatGpreS Σ} `{!gen_heapGpreS (@resource' Σ) Σ} :
  forall (prog: program) G z m
      (Hnorepet : list_norepet (prog_defs_names prog))
      (Hmatch : match_fdecs (prog_funct prog) G)
      (Hm : Genv.init_mem prog = Some m),
  ⊢ |==> ∃ _ : externalGS Z Σ, ∃ _ : heapGS Σ,
    ext_auth z ∗ has_ext z ∗ wsat ∗ ownE ⊤ ∗ mem_auth m ∗ inflate_initial_mem m (block_bounds prog) (globalenv prog) G ∗ initial_core (globalenv prog) G
    ∗ ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta) (gen_meta_name _) Tsh ∅.
Proof.
  intros; iIntros.
  iMod (ext_alloc z) as (?) "(? & ?)".
  iMod (alloc_initial_mem m (block_bounds prog) (globalenv prog) G) as (?) "(? & ? & ? & Hm & ?)".
  assert (list_norepet (map fst G)).
  { rewrite -match_fdecs_norepet //; by apply prog_funct_norepet. }
  rewrite initial_mem_initial_core //.
  iDestruct "Hm" as "(? & ?)".
  iExists _, _; by iFrame.
  - intros ?? Hid Hb.
    apply elem_of_list_fmap_2 in Hid as ((?, ?) & -> & Hi).
    apply elem_of_list_In, find_id_i in Hi; last done.
    eapply match_fdecs_exists_Gfun in Hi as (? & Hdef & ?); last done.
    apply (prog_defmap_norepet (program_of_program prog)) in Hdef; last done.
    apply Genv.find_def_symbol in Hdef as (b' & Hb' & Hdef); assert (b' = b) as -> by (rewrite Hb' in Hb; inv Hb; done).
    rewrite -Genv.find_funct_ptr_iff in Hdef.
    eapply Genv.init_mem_characterization_2 in Hdef as (Hperm & Hmax); last done.
    apply perm_mem_access in Hperm as (? & Hperm & Haccess).
    destruct (Hmax _ _ _ (access_perm _ _ _ _ _ Haccess)); subst; done.
  - intros ?? Hid Hb.
    apply elem_of_list_fmap_2 in Hid as ((?, ?) & -> & Hi).
    apply elem_of_list_In, find_id_i in Hi; last done.
    eapply match_fdecs_exists_Gfun in Hi as (? & Hdef & ?); last done.
    apply find_symbol_globalenv in Hb as (? & ? & Hnth); last done.
    pose proof (nth_error_In _ _ Hnth).
    eapply list_norepet_In_In in Hdef; eauto; subst.
    by erewrite block_bounds_nth by done.
  - rewrite Forall_forall; intros (?, ?) Hi.
    apply elem_of_list_In, find_id_i in Hi; last done.
    eapply match_fdecs_exists_Gfun in Hi as (? & Hdef & ?); last done.
    apply (prog_defmap_norepet (program_of_program prog)) in Hdef; last done.
    apply Genv.find_def_symbol in Hdef as (b & Hb & Hdef).
    rewrite Hb; by eapply Genv.find_symbol_not_fresh.
Qed.
