Require Import sepcomp.core_semantics.

Require Import veric.base.
Require Import veric.Clight_new.
Require Import veric.Clight_lemmas.
Require Import sepcomp.step_lemmas.
Require Import veric.SeparationLogic.
Require Import veric.juicy_extspec.
Require Import veric.juicy_mem.
Require veric.NullExtension.
Require Import veric.Clight_sim.
Require Import veric.SeparationLogicSoundness.
Require Import sepcomp.extspec.
Require Import msl.msl_standard.

Import SoundSeparationLogic.
Import CSL.

Definition dryspec : ext_spec unit :=
 Build_external_specification mem external_function unit
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef ge tys vl m z => False) 
     (*ext_spec_post*)
     (fun ef Hef ge ty vl m z => False)
     (*ext_spec_exit*)
     (fun rv m z => False).

 Lemma whole_program_sequential_safety:
   forall prog V G m,
     @semax_prog NullExtension.Espec prog V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core cl_core_sem
                    (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
       forall n, 
        dry_safeN cl_core_sem dryspec (Genv.globalenv prog) n tt q m.
Proof.
 intros.
 destruct (@semax_prog_rule NullExtension.Espec tt _ _ _ _ H H0) as [b [q [? [? ?]]]].
 exists b, q.
 split3; auto.
 intro n.
 specialize (H3 n).
 destruct H3 as [jm [? [? ?]]].
 unfold semax.jsafeN in H5.
 subst m.
 clear - H4 H5.
 revert jm q H4 H5; induction n; simpl; intros. constructor.
 inv H5.
 destruct H0 as (?&?&?).
 econstructor; eauto. 
 apply IHn; auto. 
 change (level (m_phi jm)) with (level jm) in H4. 
   rewrite H4 in H2; inv H2; auto.
 exfalso; auto.
 eapply safeN_halted; eauto.
Qed.
