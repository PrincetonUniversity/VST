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
                  type_of_fundef fd = type_of_funspec fspec ->
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

Lemma initial_jm_without_locks m:
  (* mem_auth m ∗ *) inflate_initial_mem m ⊢ no_locks.
Proof.
  rewrite /no_locks.
  iIntros "Hm" (?????).
  iApply (bi.impl_intro_r with "Hm"); iIntros "H".
Abort.

(* How to relate Gamma to funspecs in memory, once we are outside the
   semax proofs?  We define 'matchfunspecs' which will be satisfied by
   the initial memory, and preserved under steps. *)

Definition matchfunspecs (ge : genv) (G : funspecs) E : mpred :=
  ∀ b:block, ∀ fs: funspec,
  func_at fs (b,0%Z) →
  ∃ id:ident, ∃ fs0: funspec, 
   ⌜Genv.find_symbol ge id = Some b /\ find_id id G = Some fs0⌝ ∧
     funspec_sub_si E fs0 fs.

(* How do we prove this? Via initial_core? *)

(*Lemma initial_jm_matchfunspecs prog m G n H H1 H2:
  matchfunspecs (globalenv prog) G (m_phi (initial_jm prog m G n H H1 H2)).
Proof.
  intros b  [fsig cc A P Q ? ?].
  simpl m_phi.
  intros phi' ? H0 Hext FAT.
  simpl in FAT.
  apply rmap_order in Hext as (Hl & Hr & _).
  rewrite <- Hr in FAT; clear Hr.
  assert (H3 := proj2 (necR_PURE' _ _ (b,0) (FUN fsig cc) H0)).
  spec H3. eauto.
  destruct H3 as [pp H3].
  unfold inflate_initial_mem at 1 in H3. rewrite resource_at_make_rmap in H3.
  unfold inflate_initial_mem' in H3. 
  destruct (access_at m (b,0) Cur) eqn:Haccess; [ | inv H3].
  destruct p; try discriminate H3.
  destruct (initial_core (Genv.globalenv prog) G n @ (b, 0)) eqn:?H; try discriminate H3.
  inv H3.
  assert (H3: inflate_initial_mem m (initial_core (Genv.globalenv prog) G n) @ (b,0) = PURE (FUN fsig cc) pp).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4. rewrite Haccess. auto.
  unfold initial_core in H4. rewrite resource_at_make_rmap in H4.
  unfold initial_world.initial_core' in H4. simpl in H4.
  destruct (Genv.invert_symbol (Genv.globalenv prog) b) eqn:?H; try discriminate.
  destruct (find_id i G) eqn:?H; try discriminate.
  destruct f; inv H4.
  assert (H8 := necR_PURE _ _ _ _ _ H0 H3). clear H0 H3.
  rewrite FAT in H8.
  injection H8; intro. subst A0.
  apply PURE_inj in H8. destruct H8 as [_ H8].
  simpl in H8.
  do 2 eexists. split. split. 
  apply Genv.invert_find_symbol; eauto. eauto.
  split. split; auto.
  clear H6 H5 i.
  rewrite later_unfash.
  do 3 red.
  clear FAT. forget (level phi') as n'. rewrite <- Hl in *. clear phi'. clear dependent a''.
  intros n1' Hn1'. apply laterR_nat in Hn1'.
  intros ts ftor garg.
  intros phi Hphi phi' phi'' Hphi' Hext'.
  apply necR_level in Hphi'. apply ext_level in Hext'.
  assert (n' > level phi'')%nat by lia.
  clear n1' Hphi phi Hphi' Hn1' phi' Hext'.
  rename phi'' into phi.
  intros [_ ?].
  assert (approx n' (P ts ftor garg) phi).
  split; auto.
  clear H3.
  apply fupd.fupd_intro.
  exists ts.
  assert (H5 := equal_f_dep (equal_f_dep H8 ts) ftor). clear H8.
  simpl in H5.
  assert (HP := equal_f (equal_f_dep H5 true) garg).
  assert (HQ := equal_f_dep H5 false).
  clear H5.
   simpl in HP, HQ.
   rewrite P_ne in H4. rewrite HP in H4. clear HP.
   change (approx _ (approx _ ?A) _) with ((approx n' oo approx n) A phi) in H4.
   rewrite fmap_app in H4.
   rewrite fmap_app in HQ.
   change (approx _ (approx _ ?A)) with ((approx n' oo approx n) A) in HQ.
   exists (fmap (dependent_type_functor_rec ts A) (approx n oo approx n')
             (approx n' oo approx n) ftor).
  rewrite (approx_min n' n) in *.
  exists emp. rewrite !emp_sepcon.
  destruct H4.
  split. auto.
  intro rho.
  pose proof (equal_f HQ rho). simpl in H5.
  intros phi' Hphi'.
  rewrite emp_sepcon.
  intros ? phi'' Hphi'' Hext''.
  intros [_ ?].
  rewrite (approx_min n n') in *.
  rewrite (Nat.min_comm n n') in *.
  assert (approx (min n' n) (Q0 ts
       (fmap (dependent_type_functor_rec ts A) (approx (Init.Nat.min n' n))
          (approx (Init.Nat.min n' n)) ftor) rho) phi'').
  split; auto.
  apply necR_level in Hphi''; apply ext_level in Hext''; lia.
  rewrite <- H5 in H7; clear H5.
  rewrite <- Q_ne in H7.
  destruct H7.
  auto.
Qed. *)

End mpred.

Lemma alloc_initial_state  `{!inG Σ (excl_authR (leibnizO Z))} `{!wsatGpreS Σ} `{!gen_heapGpreS resource' Σ} :
  forall (prog: program) G n m,
      list_norepet (prog_defs_names prog) ->
      match_fdecs (prog_funct prog) G ->
      Genv.init_mem prog = Some m ->
  ⊢ |==> ∃ _ : externalGS Z Σ, ∃ _ : heapGS Σ, ext_auth z ∗ has_ext z ∗ wsat ∗ ownE ⊤ ∗ mem_auth m ∗ inflate_initial_mem m ∗ initial_core m.
Proof.
  ext_alloc
  alloc_initial_mem
