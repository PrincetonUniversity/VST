Require Import VST.zlist.sublist.
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

Notation initial_core m := (initial_core m (F := function)).
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

Lemma match_ids : forall fs G i, match_fdecs fs G -> In i (map fst fs) ↔ In i (map fst G).
Proof.
  induction 1; simpl; first done.
  rewrite IHmatch_fdecs //.
Qed.

Lemma match_fdecs_norepet : forall fs G, match_fdecs fs G -> list_norepet (map fst fs) ↔ list_norepet (map fst G).
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

Lemma alloc_globals_block : forall {F} prog_pub (ge : Genv.t (Ctypes.fundef F) type) b gl l m m'
  (Hl : list_norepet (map fst (gl ++ l)))
  (Hge : ge = Genv.add_globals (Genv.empty_genv (Ctypes.fundef F) type prog_pub) (gl ++ l))
  (Hlen : Pos.to_nat (nextblock m') - 1 = length gl), Genv.alloc_globals ge m gl = Some m' ->
  (nextblock m <= b < nextblock m')%positive ->
  exists id g, In (id, g) gl /\ Genv.find_symbol ge id = Some b.
Proof.
  induction gl as [| a] using rev_ind; simpl; intros.
  { inv H; lia. }
  apply alloc_globals_app in H as (m1 & ? & H).
  simpl in H.
  destruct (Genv.alloc_global _ _ _) eqn: Halloc; inv H.
  pose proof (Genv.alloc_global_nextblock _ _ _ Halloc).
  destruct (plt b (nextblock m1)).
  - rewrite <- app_assoc in *.
    edestruct IHgl as (? & ? & ? & ?); eauto.
    { rewrite app_length /= in Hlen; lia. }
    { unfold Plt in *; lia. }
    eexists _, _; rewrite in_app_iff; eauto.
  - assert (b = nextblock m1) as -> by (unfold Plt in *; lia).
    destruct a; eexists _, _; rewrite in_app_iff; split; first by simpl; eauto.
    set (gl' := ((_ ++ _) ++ _)).
    assert (Pos.to_nat (nextblock m1) <= length gl').
    { subst gl'; rewrite app_length; lia. }
    rewrite (add_globals_hack (rev _)); [| | rewrite rev_involutive // |].
    + rewrite nth_error_map nth_error_rev rev_length; last lia.
      replace (_ - (_ - Pos.to_nat (nextblock m1)))%nat with (Pos.to_nat (nextblock m1)) by lia.
      subst gl'; rewrite nth_error_app1; last lia.
      rewrite app_length /= in Hlen; rewrite nth_error_app2; last lia.
      replace (_ - _)%nat with O by lia; done.
    + subst gl'.
      rewrite map_rev list_norepet_rev //.
    + rewrite Zlength_rev Zlength_correct; lia.
Qed.

Lemma init_mem_all : forall (prog: program) m b
  (Hnorepet : list_norepet (prog_defs_names prog)), Genv.init_mem prog = Some m -> (b < nextblock m)%positive ->
  exists id g, In (id, g) (AST.prog_defs prog) /\ Genv.find_symbol (globalenv prog) id = Some b.
Proof.
  intros; eapply alloc_globals_block; eauto.
  - instantiate (1 := []); rewrite app_nil_r //.
  - rewrite app_nil_r //.
  - apply Genv.init_mem_genv_next in H as <-.
    rewrite Genv.genv_next_add_globals /= advance_next_length; lia.
  - simpl; lia.
Qed.

Lemma In_prog_funct : forall prog i f, In (i, Gfun f) (prog_defs prog) -> In (i, f) (prog_funct prog).
Proof.
  intros; rewrite /prog_funct; induction (prog_defs prog); simpl in *; first done.
  destruct H as [-> | ?]; first by simpl; auto.
  destruct a as (?, [|]); simpl; auto.
Qed.

Lemma initialize_mem' :
  forall (prog: program) G m
      (Hnorepet : list_norepet (prog_defs_names prog))
      (Hmatch : match_fdecs (prog_funct prog) G)
      (Hm : Genv.init_mem prog = Some m),
  mem_auth Mem.empty ⊢ |==> mem_auth m ∗ inflate_initial_mem m (block_bounds prog) (globalenv prog) G ∗ initial_core m (globalenv prog) G.
Proof.
  intros.
  assert (list_norepet (map fst G)).
  { rewrite -match_fdecs_norepet //; by apply prog_funct_norepet. }
  rewrite -initial_mem_initial_core; first by apply initialize_mem.
  - intros ? Hb.
    eapply init_mem_all in Hb as (id & g & Hin & Hb); eauto.
    pose proof (prog_defmap_norepet _ _ _ Hnorepet Hin) as Hdef.
    apply Genv.find_def_symbol in Hdef as (b' & Hb' & Hdef); assert (b' = b) as -> by (rewrite Hb' in Hb; inv Hb; done).
    apply Genv.init_mem_characterization_gen in Hm.
    specialize (Hm b _ Hdef).
    rewrite /funspec_of_loc /=.
    erewrite Genv.find_invert_symbol by done.
    destruct g.
    + apply In_prog_funct in Hin.
      assert (In id (map fst (prog_funct prog))) as Hin' by (rewrite in_map_iff; eexists (_, _); eauto).
      rewrite match_ids // in_map_iff in Hin'; destruct Hin' as ((?, ?) & ? & ?); simpl in *; subst.
      erewrite find_id_i by done.
      destruct Hm as (Hperm & Hmax).
      apply perm_mem_access in Hperm as (? & Hperm & Haccess).
      destruct (Hmax _ _ _ (access_perm _ _ _ _ _ Haccess)); subst; done.
    + destruct (find_id id G) eqn: Hfind; last done.
      eapply match_fdecs_exists_Gfun in Hfind as (? & Hin' & ?); last done.
      eapply list_norepet_In_In in Hin; eauto; done.
  - intros ? Hb.
    eapply init_mem_all in Hb as (id & g & Hin & Hb); eauto.
    apply find_symbol_globalenv in Hb as (? & g' & ?); last done.
    erewrite block_bounds_nth by done.
    destruct g'; try done; simpl; lia.
Qed.

Lemma initial_core_funassert :
  forall (prog: program) V G m ve te
      (Hnorepet : list_norepet (prog_defs_names prog))
      (Hmatch : match_fdecs (prog_funct prog) G)
      (Hm : Genv.init_mem prog = Some m),
  initial_core m (globalenv prog) G ⊢ funassert (nofunc_tycontext V G) (mkEnviron (filter_genv (globalenv prog)) ve te).
Proof.
  intros; iIntros "#H !>".
  rewrite /initial_world.initial_core /Map.get /filter_genv /=; iSplit.
  - iIntros (?? Hid); simpl in *.
    rewrite make_tycontext_s_find_id in Hid.
    edestruct match_fdecs_exists_Gfun as (? & Hid' & ?); [done.. |].
    apply (Genv.find_symbol_exists (program_of_program _)) in Hid' as (b & Hfind); rewrite Hfind.
    iExists _; iSplit; first done.
    unshelve erewrite (big_sepL_lookup _ _ (Pos.to_nat b - 1)); last (apply lookup_seq; split; first done).
    replace (Pos.of_nat _) with b by lia.
    rewrite /funspec_of_loc /=.
    erewrite Genv.find_invert_symbol by done.
    rewrite Hid //.
    { left; intros; destruct (funspec_of_loc _ _ _); apply _. }
    { eapply Genv.find_symbol_not_fresh in Hfind; last done.
      unfold valid_block, Plt in Hfind; lia. }
  - iIntros (b (? & Hfind & Hid)).
    rewrite make_tycontext_s_find_id in Hid.
    unshelve erewrite (big_sepL_lookup _ _ (Pos.to_nat b - 1)); last (apply lookup_seq; split; first done).
    replace (Pos.of_nat _) with b by lia.
    rewrite /funspec_of_loc /=.
    erewrite Genv.find_invert_symbol by done.
    rewrite Hid //.
    { left; intros; destruct (funspec_of_loc _ _ _); apply _. }
    { eapply Genv.find_symbol_not_fresh in Hfind; last done.
      unfold valid_block, Plt in Hfind; lia. }
Qed.

End mpred.

Require Import VST.veric.wsat.

(* This is provable, but we probably don't want to use it: we should set up the proof infrastructure
   (heapGS, etc.) first, and then allocate the initial memory in a later step. *)
Lemma alloc_initial_state  `{!inG Σ (excl_authR (leibnizO Z))} `{!wsatGpreS Σ} `{!gen_heapGpreS (@resource' Σ) Σ} :
  forall (prog: program) G z m
      (Hnorepet : list_norepet (prog_defs_names prog))
      (Hmatch : match_fdecs (prog_funct prog) G)
      (Hm : Genv.init_mem prog = Some m),
  ⊢ |==> ∃ _ : externalGS Z Σ, ∃ _ : heapGS Σ,
    ext_auth z ∗ has_ext z ∗ wsat ∗ ownE ⊤ ∗ mem_auth m ∗ inflate_initial_mem m (block_bounds prog) (globalenv prog) G ∗ initial_core m (globalenv prog) G
    ∗ ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta) (gen_meta_name _) 1 ∅.
Proof.
  intros; iIntros.
  iMod (ext_alloc z) as (?) "(? & ?)".
  iMod (alloc_initial_mem Mem.empty (fun _ => (0%Z, O)) (globalenv prog) G) as (?) "(? & ? & Hm & _ & ?)".
  iMod (initialize_mem' with "Hm") as "(? & ? & ?)".
  iExists _, _; by iFrame.
Qed.
