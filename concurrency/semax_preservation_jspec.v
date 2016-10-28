Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import msl.seplog.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.juicy_safety.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.res_predicates.
Require Import veric.mem_lessdef.
Require Import floyd.coqlib3.
Require Import sepcomp.extspec.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import sepcomp.semantics_lemmas.
Require Import concurrency.coqlib5.
Require Import concurrency.permjoin.
Require Import concurrency.semax_conc.
Require Import concurrency.semax_invariant.
Require Import concurrency.sync_preds_defs.
Require Import concurrency.aging_lemmas.

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
    destruct ef as [name sg | | | | | | | | | | | ].
    - now eauto.
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
    - simpl; do 5 (if_tac; [ now breakhyps | ]); now intros [].
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
    intros e x b tl vl z m1 m2 A.
    
    unfold Jspec' in *.
    destruct (is_EF_external e x) as (name & sg & ->).
    
    apply age_jm_phi in A.
    
    (* dependent destruction *)
    revert x.
    1:funspec_destruct "acquire".
    2:funspec_destruct "release".
    3:funspec_destruct "makelock".
    4:funspec_destruct "freelock".
    5:funspec_destruct "spawn".
    
    6: solve[intros[]].
    all:intros x (Hargsty & H); split; [apply Hargsty | ].
    all:breakhyps.
    all:agejoinhyp.
    all:breakhyps.
    all:agehyps.
    all:agehyps.
    all:eauto.
  Qed.
  
End Jspec'_properties.  
