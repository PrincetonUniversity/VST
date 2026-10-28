(**
  Adequacy of the program logic of [at_logic.v] for the atomic machine.

  [at_adequacy] is Iris's adequacy for [at_lang], starting from a memory
  [m] with no reservations ([at_init_mu m]).  The rest of the file carries
  it over to [at_step]: the machine's thread pool is always [map_seq 0] of
  the Iris thread list, because [Spawn] uses the least free index, which is
  where Iris appends forked threads ([am_steps_erased]).  Hence a [WP] proof
  makes the machine safe ([at_adequacy_am_safe]), and the postcondition holds
  of the main thread's result ([at_adequacy_am_result]).
*)

From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Export adequacy.
From iris.proofmode Require Import proofmode.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.at_logic.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

Local Notation lr_tstate := (tstate (L := lr_language)).

Class lrAtGpreS Σ := LrAtGpreS {
  lrAtGpreS_inv :: invGpreS Σ;
  lrAtGpreS_heap :: inG Σ (authR heapUR);
  lrAtGpreS_heap_freeable :: inG Σ (authR heap_freeableUR);
  lrAtGpreS_reads :: ghost_mapG Σ nat (loc * Qp * val);
  lrAtGpreS_writes :: ghost_mapG Σ loc val;
  lrAtGpreS_frees :: inG Σ (authR (gset_disjUR loc))
}.

Definition lrAtΣ : gFunctors :=
  #[invΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR));
    ghost_mapΣ nat (loc * Qp * val);
    ghost_mapΣ loc val;
    GFunctor (authR (gset_disjUR loc))].
Global Instance subG_lrAtGpreS {Σ} : subG lrAtΣ Σ -> lrAtGpreS Σ.
Proof. solve_inG. Qed.

(** The initial reader/writer map: every location is unreserved. *)
Definition at_init_mu (m : lr_mem) : rw_map := (fun _ => Rst 0) <$> m.

Lemma at_resv_rel_init (m : lr_mem) : at_resv_rel m (at_init_mu m) ∅ ∅ ∅.
Proof.
  split; [ | set_solver ].
  intros l. rewrite /at_init_mu lookup_fmap resv_count_empty lookup_empty.
  destruct (m !! l) as [v | ] eqn:Hl; rewrite /= ?Hl /=; by split_and!.
Qed.

Theorem at_adequacy Σ `{!lrAtGpreS Σ} (e : expr) (m : lr_mem) (φ : at_val -> Prop) :
  (forall `{!lrAtGS Σ}, ⊢ WP Running e [] {{ v, ⌜φ v⌝ }}) ->
  adequate NotStuck (Running e [] : lr_tstate) ((m, at_init_mu m) : at_state) (fun v _ => φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??).
  iMod (own_alloc (● to_heap (sq_heap m))) as (vγ) "Hvγ".
  { apply (auth_auth_valid (to_heap _)), to_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    first by apply auth_auth_valid.
  iMod (ghost_map_alloc_empty (K := nat) (V := loc * Qp * val)) as (rγ) "Hrγ".
  iMod (ghost_map_alloc_empty (K := loc) (V := val)) as (wγ) "Hwγ".
  iMod (own_alloc (● (GSet ∅ : gset_disjUR loc))) as (pγ) "Hpγ";
    first by apply auth_auth_valid.
  set (Hheap := HeapGS _ _ _ vγ fγ).
  set (Hat := LrAtGS _ (LrSqGS _ _ Hheap) _ _ _ rγ wγ pγ).
  iModIntro. iExists (fun σ _ => at_si (lrAtGS0 := Hat) σ.1 σ.2), (fun _ => True%I).
  iSplitL.
  { iSplitL "Hvγ Hfγ".
    { iExists ∅. iFrame. iPureIntro. intros ?? Hb. by rewrite lookup_empty in Hb. }
    iExists ∅, ∅, ∅. iFrame. rewrite !big_sepM_empty. iPureIntro. split_and!; try done.
    apply at_resv_rel_init. }
  by iApply (Hwp Hat).
Qed.

(** * From [at_lang] to [at_step] *)

(** Every machine step is a primitive step of one thread. *)
Lemma at_step_prim_step (tp : tpool) m mu tp' m' mu' :
  at_step (AMCfg tp m mu) (AMCfg tp' m' mu') ->
  exists (i : nat) t t' efs, tp !! i = Some t /\ at_prim_step t (m, mu) [] t' (m', mu') efs /\
    ((efs = [] /\ tp' = <[i := t']> tp) \/
     (exists t_new (j : nat), efs = [t_new] /\ tp !! j = None /\
        (forall k : nat, (k < j)%nat -> is_Some (tp !! k)) /\
        tp' = <[j := t_new]> (<[i := t']> tp))).
Proof.
  inversion 1; subst.
  - eexists i, _, _, []. split; [ done | ]. split; [ by eapply AtTry | by left ].
  - eexists i, _, _, []. split; [ done | ]. split; [ by eapply AtCommit | by left ].
  - eexists i, _, _, []. split; [ done | ]. split; [ by eapply AtRead | by left ].
  - eexists i, _, _, []. split; [ done | ]. split; [ by eapply AtWrite | by left ].
  - eexists i, _, _, []. split; [ done | ]. split; [ by eapply AtCasSuc | by left ].
  - eexists i, _, _, []. split; [ done | ]. split; [ by eapply AtCasFail | by left ].
  - eexists i, _, _, []. split; [ done | ]. split; [ by eapply AtCasStuck | by left ].
  - eexists i, _, _, [_]. split; [ done | ]. split; [ by eapply AtSpawn | ].
    right. eexists _, j. eauto.
Qed.

(** The pool [map_seq 0 tl] steps with the thread list [tl]. *)
Lemma at_step_erased (tl : list lr_tstate) m mu tp' m' mu' :
  at_step (AMCfg (map_seq 0 tl) m mu) (AMCfg tp' m' mu') ->
  exists tl', tp' = map_seq 0 tl' /\ erased_step (tl, (m, mu) : at_state) (tl', (m', mu')).
Proof.
  intros (i & t & t' & efs & Hi & Hstep & Hcase)%at_step_prim_step.
  rewrite lookup_map_seq_0 in Hi. pose proof (lookup_lt_Some _ _ _ Hi) as Hlen.
  exists (<[i := t']> tl ++ efs). split.
  - destruct Hcase as [[-> ->] | (t_new & j & -> & Hj & Hleast & ->)].
    + by rewrite app_nil_r insert_map_seq_0.
    + rewrite lookup_map_seq_0 lookup_ge_None in Hj.
      assert (j = length tl) as ->.
      { destruct (decide (length tl < j)%nat) as [Hlt | ]; [ | lia ].
        destruct (Hleast _ Hlt) as [x Hx]. rewrite lookup_map_seq_0 in Hx.
        apply lookup_lt_Some in Hx. lia. }
      by rewrite map_seq_snoc length_insert -insert_map_seq_0.
  - exists []. eapply step_atomic with (t1 := take i tl) (t2 := drop (S i) tl).
    + by rewrite take_drop_middle.
    + by rewrite insert_take_drop // -app_assoc.
    + exact Hstep.
Qed.

Lemma am_steps_erased (tl : list lr_tstate) m mu tp' m' mu' :
  am_steps (AMCfg (map_seq 0 tl) m mu) (AMCfg tp' m' mu') ->
  exists tl', tp' = map_seq 0 tl' /\
    rtc erased_step (tl, (m, mu) : at_state) (tl', (m', mu')).
Proof.
  unfold am_steps. intros Hsteps.
  remember (AMCfg (map_seq 0 tl) m mu) as q eqn:Hq. remember (AMCfg tp' m' mu') as q' eqn:Hq'.
  revert tl m mu Hq. induction Hsteps as [q | q [tp1 m1 mu1] q' Hstep Hsteps IH];
    intros tl m mu ->.
  - simplify_eq. exists tl. split; [ done | apply rtc_refl ].
  - destruct (at_step_erased _ _ _ _ _ _ Hstep) as (tl1 & -> & Hstep').
    destruct (IH Hq' tl1 m1 mu1 eq_refl) as (tl' & -> & Hsteps').
    exists tl'. split; [ done | ]. by eapply rtc_l.
Qed.

(** A thread that can take a primitive step can step in a singleton pool. *)
Lemma at_prim_step_am_reducible t m mu κ t' σ' efs :
  at_prim_step t (m, mu) κ t' σ' efs -> am_reducible t m mu.
Proof.
  inversion 1; subst; eexists.
  - by eapply Core_Try; [ apply (lookup_singleton_eq (M := gmap nat)) | .. ].
  - by eapply Core_Commit; [ apply (lookup_singleton_eq (M := gmap nat)) | .. ].
  - by eapply SC_Read; [ apply (lookup_singleton_eq (M := gmap nat)) | .. ].
  - by eapply SC_Write; [ apply (lookup_singleton_eq (M := gmap nat)) | .. ].
  - by eapply SC_Cas_Suc; [ apply (lookup_singleton_eq (M := gmap nat)) | .. ].
  - by eapply SC_Cas_Fail; [ apply (lookup_singleton_eq (M := gmap nat)) | .. ].
  - by eapply SC_Cas_Stuck; [ apply (lookup_singleton_eq (M := gmap nat)) | .. ].
  - eapply (Spawn _ _ _ 0 _ _ _ 1); [ apply (lookup_singleton_eq (M := gmap nat)) | done | by rewrite (lookup_singleton_ne (M := gmap nat)) | ].
    intros k Hk. assert (k = 0%nat) as -> by lia. by rewrite (lookup_singleton_eq (M := gmap nat)).
Qed.

Lemma at_not_stuck_am t m mu : not_stuck t ((m, mu) : at_state) -> am_not_stuck t m mu.
Proof.
  intros [[v Hv] | (κ & t' & σ' & efs & Hstep)].
  - left. destruct t as [e [ | ] | ]; simpl in Hv; try discriminate.
    exists e. split; [ done | ]. by exists v.
  - right. by eapply at_prim_step_am_reducible.
Qed.

(** * Adequacy for the machine *)

Theorem at_adequacy_am_safe Σ `{!lrAtGpreS Σ} (e : expr) (m : lr_mem) :
  (forall `{!lrAtGS Σ}, ⊢ WP Running e [] {{ _, True }}) ->
  am_safe (AMCfg {[0%nat := Running e []]} m (at_init_mu m)).
Proof.
  intros Hwp.
  assert (Had : adequate NotStuck (Running e [] : lr_tstate) ((m, at_init_mu m) : at_state)
                  (fun _ _ => True)).
  { apply (at_adequacy Σ e m (fun _ => True)). intros HAt.
    iApply (wp_wand with "[]"); [ iApply (Hwp HAt) | by iIntros (v) "_" ]. }
  intros tp m' mu' Hsteps i t Hi. rewrite -map_seq_singleton in Hsteps.
  destruct (am_steps_erased _ _ _ _ _ _ Hsteps) as (tl & -> & Hsteps').
  rewrite lookup_map_seq_0 in Hi.
  apply at_not_stuck_am. eapply (adequate_not_stuck _ _ _ _ Had); [ done | exact Hsteps' | ].
  by eapply list_elem_of_lookup_2.
Qed.

Theorem at_adequacy_am_result Σ `{!lrAtGpreS Σ} (e : expr) (m : lr_mem) (φ : at_val -> Prop) :
  (forall `{!lrAtGS Σ}, ⊢ WP Running e [] {{ v, ⌜φ v⌝ }}) ->
  forall tp m' mu' v,
    am_steps (AMCfg {[0%nat := Running e []]} m (at_init_mu m)) (AMCfg tp m' mu') ->
    tp !! 0%nat = Some (Running (of_val v) []) -> φ v.
Proof.
  intros Hwp tp m' mu' v Hsteps H0. assert (Had := at_adequacy Σ e m φ Hwp).
  rewrite -map_seq_singleton in Hsteps.
  destruct (am_steps_erased _ _ _ _ _ _ Hsteps) as (tl & -> & Hsteps').
  rewrite lookup_map_seq_0 in H0. destruct tl as [ | t tl ]; [ done | ]. injection H0 as ->.
  exact (adequate_result _ _ _ _ Had tl _ v Hsteps').
Qed.
