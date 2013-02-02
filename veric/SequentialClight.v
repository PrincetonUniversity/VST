Load loadpath.
Require Import compositional_compcert.core_semantics.

Require Import veric.base.
Require Import veric.Clight_new.
Require Import veric.Clight_lemmas.
Require Import compositional_compcert.step_lemmas.
Require Import veric.SeparationLogic.
Require Import veric.juicy_extspec.
Require Import veric.juicy_mem.
Require Import veric.NullExtension.
Require Import veric.Clight_sim.
Require Import veric.SeparationLogicSoundness.
Require Import compositional_compcert.extspec.
Require Import msl.msl_standard.

Module SeqC := MakeSeparationLogic NullExtension.
Import SeqC.
Import CSL ExtSpec.

Definition dryspec : ext_spec unit :=
 Build_external_specification mem external_function unit
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef tys vl m z => False) 
     (*ext_spec_post*)
     (fun ef Hef ty vl m z => False).

 Lemma hoare_safe:
   forall prog V G m,
     semax_prog prog V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       make_initial_core cl_core_sem
                    (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
       forall n, 
        safeN cl_core_sem dryspec (Genv.globalenv prog) n tt q m.
Proof.
  assert (H0:=True).
  intros.
  destruct (semax_prog_rule tt _ _ _ _ H H1) as [b [q [? [? ?]]]].
  exists b, q.
 split3; auto.
 intro n.
 specialize (H4 n).
 destruct H4 as [jm [? [? ?]]].
 unfold semax.jsafeN in H6.
 subst m.
 clear - H6 H5.
 revert jm q H5 H6; induction n; simpl; intros; auto.
 revert H6; case_eq (cl_at_external q); intros; auto.
 destruct p. destruct p. destruct H6. contradiction.
 destruct H6 as [c' [m' [? ?]]].
 exists c'; exists (m_dry m'); split; auto.
 destruct H0; auto.
 destruct H0.
 destruct H2.
 apply IHn; auto.
 change (level (m_phi jm)) with (level jm) in H5. rewrite H5 in H3; inv H3; auto.
Qed.
