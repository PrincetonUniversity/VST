Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.veric.aging_lemmas.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.permjoin.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.sync_preds_defs.

Set Bullet Behavior "Strict Subproofs".

Open Scope string_scope.

Section Jspec'_properties.
  Variables
    (CS : compspecs)
    (ext_link : string -> ident)
    (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2).

  Definition Jspec' := (@OK_spec (Concurrent_Espec unit CS ext_link)).

  Lemma is_EF_external ef : ext_spec_type Jspec' ef -> exists name sg, ef = EF_external name sg.
  Proof.
    destruct ef as [name sg | | | | | | | | | | | ]; first (now eauto); simpl; repeat (if_tac; [ now breakhyps | ]); now intros [].
  Qed.

  Open Scope string_scope.

  Lemma Jspec'_juicy_mem_equiv : ext_spec_stable juicy_mem_equiv (JE_spec _ Jspec').
  Proof.
    split; [ | easy ].
    intros e x b tl vl z m1 m2 E.

    destruct (is_EF_external e x) as (name & sg & ->).

    (* dependent destruction *)
    revert x.

    (** * the case of acquire *)
    funspec_destruct "acquire".
    rewrite (proj2 E).
    exact (fun x y => y).

    (** * the case of release *)
    funspec_destruct "release".
    rewrite (proj2 E).
    exact (fun x y => y).

    (** * the case of makelock *)
    funspec_destruct "makelock".
    rewrite (proj2 E).
    exact (fun x y => y).

    (** * the case of freelock *)
    funspec_destruct "freelock".
    rewrite (proj2 E).
    exact (fun x y => y).

    (** * the case of spawn *)
    funspec_destruct "spawn".
    rewrite (proj2 E).
    exact (fun x y => y).

    (** * no more cases *)
    simpl; tauto.
  Qed.

  Lemma Jspec'_hered : ext_spec_stable age (JE_spec _ Jspec').
  Proof.
    split; [ | easy ].
    apply JE_pre_hered.
  Qed.

  Lemma Jspec'_jsafe_phi ge ora c jm ext :
    cl_at_external c = Some ext ->
    jsafeN Jspec' ge ora c jm ->
    jsafe_phi Jspec' ge ora c (m_phi jm).
  Proof.
    intros atex safe.
    inversion safe as [ | ? ? ? c' jm' step safe'
                        | ? ? ? ef args x atex' Pre Post | ]; subst.
    - intros jm_ Ejm_. constructor. rewrite level_juice_level_phi, Ejm_, <- level_juice_level_phi; auto.
    - (* corestep: not at external *)
      destruct step as [step rd].
      erewrite cl_corestep_not_at_external in atex. discriminate. apply step.
    - (* at_ex: interesting case *)
      intros jm_ Ejm_.
      apply jsafeN_external with (e := ef) (args := args) (x := x).
      + auto.

      + (* precondition only cares about phi *)
        clear Post.
        unfold Jspec' in *.
        destruct (is_EF_external ef x) as (name & sg & ->).
        revert x Pre.
        funspec_destruct "acquire"; [|funspec_destruct "release"; [|funspec_destruct "makelock"; [|
          funspec_destruct "freelock"; [|funspec_destruct "spawn"; [|solve[intros[]]]]]]].

        all: intros x Pre.
        all: exact_eq Pre.
        all: rewrite Ejm_; try reflexivity.

      + (* postcondition only cares about phi *)
        unfold Jspec' in *.
        destruct (is_EF_external ef x) as (name & sg & ->).
        clear Pre.
        revert x Post.
        funspec_destruct "acquire"; [|funspec_destruct "release"; [|funspec_destruct "makelock"; [|
          funspec_destruct "freelock"; [|funspec_destruct "spawn"; [|solve[intros[]]]]]]].

        all: intros x Post.
        all: exact_eq Post.
        all: unfold Hrel in *.
        all: rewrite !level_juice_level_phi.
        all: rewrite Ejm_; reflexivity.

    - (* halted *)
      repeat intro; apply jsafeN_halted with (i := i); auto.
  Qed.

End Jspec'_properties.
