(** * Tactics for concurrency *)

From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.threadPool.
Require Import VST.msl.Axioms. (*for proof_irr *)

Import HybridMachineSig.

Module Tactics.

Ltac pf_cleanup :=
    repeat match goal with
           | [H1: invariant ?X, H2: invariant ?X |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
             subst H2
           | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
             subst H2
           | [H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: ThreadPool.containsThread ?TP ?M, H2: ThreadPool.containsThread ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: ThreadPool.containsThread ?TP ?M,
                  H2: ThreadPool.containsThread (@ThreadPool.updThreadC _ ?TP _ _) ?M |- _] =>
             apply ThreadPool.cntUpdateC' in H2;
             assert (H1 = H2) by (by eapply ThreadPool.cnt_irr); subst H2
           | [H1: ThreadPool.containsThread ?TP ?M,
                  H2: ThreadPool.containsThread (@ThreadPool.updThread _ ?TP _ _ _) ?M |- _] =>
             apply ThreadPool.cntUpdate' in H2;
             assert (H1 = H2) by (by eapply ThreadPool.cnt_irr); subst H2
           | [H1: OrdinalPool.containsThread ?TP ?M, H2: OrdinalPool.containsThread ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: OrdinalPool.containsThread ?TP ?M,
                  H2: OrdinalPool.containsThread (@OrdinalPool.updThreadC _ ?TP _ _) ?M |- _] =>
             apply OrdinalPool.cntUpdateC' in H2;
             assert (H1 = H2) by (by eapply OrdinalPool.cnt_irr); subst H2
           | [H1: OrdinalPool.containsThread ?TP ?M,
                  H2: OrdinalPool.containsThread (@OrdinalPool.updThread _ ?TP _ _ _) ?M |- _] =>
             apply OrdinalPool.cntUpdate' in H2;
             assert (H1 = H2) by (by eapply OrdinalPool.cnt_irr); subst H2
           | [H1: ThreadPool.containsThread ?TP ?M, H2: OrdinalPool.containsThread ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           end.
End Tactics.
