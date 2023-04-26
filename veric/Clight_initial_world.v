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

Lemma initial_jm_matchfunspecs prog G E:
  initial_core (globalenv prog) G ⊢ matchfunspecs (globalenv prog) G E.
Proof.
  rewrite /initial_core /matchfunspecs.
  iIntros "#H" (??) "#f".
  iDestruct ("H" $! b fs) as "[_ Hf]".
  iDestruct ("Hf" with "f") as %(id & ?%Genv.invert_find_symbol & ?).
  iExists id, fs; iSplit; first done.
  iApply funspec_sub_si_refl.
Qed.

End mpred.

Require Import VST.veric.wsat.

Print funspecs.
Search gvar_volatile.
(* Should we compute the block bounds from Genv.init_mem, or leave them arbitrary? *)
(* Would it make more sense to build our initial predicate along the lines of Genv.init_mem, instead of
   allocating funspecs and data separately? *)
(* We can use the G to determine where to put funspecs. *)
Lemma alloc_initial_state  `{!inG Σ (excl_authR (leibnizO Z))} `{!wsatGpreS Σ} `{!gen_heapGpreS (@resource' Σ) Σ} :
  forall (prog: program) G z m block_bounds,
      list_norepet (prog_defs_names prog) ->
      match_fdecs (prog_funct prog) G ->
      Genv.init_mem prog = Some m ->
  ⊢ |==> ∃ _ : externalGS Z Σ, ∃ H : heapGS Σ,
    ext_auth z ∗ has_ext z ∗ wsat ∗ ownE ⊤ ∗ mem_auth m ∗ inflate_initial_mem m block_bounds ∗ initial_world.initial_core(heapGS0 := H) (globalenv prog) G.
Proof.
  intros; iIntros.
  iMod (ext_alloc z) as (?) "(? & ?)".
  iMod (alloc_initial_mem m block_bounds) as (?) "(? & ? & ? & ? & ?)".
  iExists _, _.
  iFrame.
  iIntros (?).
