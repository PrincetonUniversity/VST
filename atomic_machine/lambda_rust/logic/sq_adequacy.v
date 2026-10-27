(**
  Adequacy of the sequential program logic of [sq_logic.v], after
  lambda-Rust's [lrust.lang.adequacy]: a [WP] proof shows that the single
  thread never gets stuck ([sq_adequacy]).  [sq_reducible] states what not
  being stuck means in terms of [sq_sem.v]: the thread can take an
  [lr_step].
*)

From iris.algebra Require Import auth.
From iris.program_logic Require Export adequacy.
From iris.proofmode Require Import proofmode.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_logic.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

Class lrSqGpreS Σ := LrSqGpreS {
  lrSqGpreS_inv :: invGpreS Σ;
  lrSqGpreS_heap :: inG Σ (authR heapUR);
  lrSqGpreS_heap_freeable :: inG Σ (authR heap_freeableUR)
}.

Definition lrSqΣ : gFunctors :=
  #[invΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR))].
Global Instance subG_lrSqGpreS {Σ} : subG lrSqΣ Σ -> lrSqGpreS Σ.
Proof. solve_inG. Qed.

Theorem sq_adequacy Σ `{!lrSqGpreS Σ} (e : sq_expr) (m : lr_mem) (φ : sq_val -> Prop) :
  (forall `{!lrSqGS Σ}, ⊢ WP e {{ v, ⌜φ v⌝ }}) ->
  adequate NotStuck e m (fun v _ => φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??).
  iMod (own_alloc (● to_heap (sq_heap m))) as (vγ) "Hvγ".
  { apply (auth_auth_valid (to_heap _)), to_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    first by apply auth_auth_valid.
  set (Hheap := HeapGS _ _ _ vγ fγ).
  iModIntro. iExists (fun m _ => heap_ctx (sq_heap m)), (fun _ => True%I). iSplitL.
  { iExists ∅. by iFrame. }
  by iApply (Hwp (LrSqGS _ _ Hheap)).
Qed.

(** Not being stuck, in terms of [sq_sem.v]. *)

Lemma sq_reducible (e : sq_expr) (m : lr_mem) :
  reducible e m <-> exists T e' m', lr_step e m T e' m'.
Proof.
  split.
  - intros (κ & e' & m' & efs & [K e1 e2 -> -> Hstep]).
    inversion Hstep as [????? Hhead]; subst. do 3 eexists. by apply LREctxStep.
  - intros (T & e' & m' & [K e1 m1 T1 e2 m2 Hhead]).
    do 4 eexists. apply (Ectx_step' (Λ := sq_ectx_lang) K). by apply SqHeadStep.
Qed.
