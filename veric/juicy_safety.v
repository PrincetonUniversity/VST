Require Import AST.
Require Import Globalenvs.

Require Import msl.ageable.

Require Import sepcomp.core_semantics.
Require Import sepcomp.extspec.
Require Import sepcomp.step_lemmas.

Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.

Definition pures_sub (jm jm' : juicy_mem) := 
  forall adr,
  match resource_at (m_phi jm) adr with
    | PURE k pp => resource_at (m_phi jm') adr 
                 = PURE k (preds_fmap (approx (level jm')) pp)
    | _ => True
  end.

Section juicy_safety.
  Context {F V C Z:Type}.
  Context (Hcore:CoreSemantics (Genv.t F V) C juicy_mem).
  Variable (Hspec:external_specification juicy_mem external_function Z).
  Definition Hrel m m' :=
    (level m' <= level m)%nat /\ 
    pures_sub m m'.
  Definition safeN := @safeN_ F V C juicy_mem Z Hrel Hcore Hspec.
End juicy_safety.
