(** ** Erasure to X86SC Machine*)

Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.SC_erasure.
Require Import concurrency.x86_context.
Require Import ccc26x86.Asm ccc26x86.Asm_coop.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module X86CoreErasure <: CoreErasure X86SEM.
  Import X86SEM ValErasure MemErasure event_semantics.
  
  Definition erased_reg (r:PregEq.t) (rs rs' : regset) : Prop :=
    erased_val (Pregmap.get r rs) (Pregmap.get r rs').
  
  Definition erased_regs rs rs' : Prop :=
    forall r, erased_reg r rs rs'.

  Definition erased_loader (l l' : load_frame) : Prop :=
    l = l'.

  Definition erasedCores c c' :=
    match c, c' with
    | State rs loader, State rs' loader' =>
      erased_regs rs rs' /\ erased_loader loader loader'
    | Asm_CallstateIn vf args tys retty, Asm_CallstateIn vf' args' tys' retty' =>
      vf = vf' /\ erased_val_list args args' /\
      tys = tys' /\ retty = retty'
    | Asm_CallstateOut ef vals rs loader, Asm_CallstateOut ef' vals' rs' loader' =>
      ef = ef' /\ erased_val_list vals vals'
      /\ erased_regs rs rs' /\ erased_loader loader loader'
    | _, _ => False
    end.
 
  Lemma erased_regs_refl:
    forall rs, erased_regs rs rs.
  Proof with eauto with erased.
    intros rs r;
    unfold erased_reg...
  Qed.

  Lemma erased_loader_refl:
    forall loader, erased_loader loader loader.
  Proof.
    unfold erased_loader; auto.
  Qed.
  
  Hint Immediate erased_regs_refl erased_loader_refl
       erased_val_list_refl : erased.

  Lemma erasedCores_refl:
    forall c, erasedCores c c.
  Proof with eauto with erased.
    destruct c; simpl;
    repeat split...
  Qed.

  Hint Immediate erasedCores_refl: erased.
  
  Lemma erased_regs_set:
    forall rs rs' v v' r
      (Hrs_ren: erased_regs rs rs')
      (Hval: erased_val v v'),
      erased_regs (rs # r <- v) (rs' # r <- v').
  Proof.
    intros.
    intros r'.
    unfold erased_reg.
    do 2 rewrite Pregmap.gsspec.
    destruct (Pregmap.elt_eq r' r); auto.
    eapply Hrs_ren.
  Qed.

  (*NOTE THIS IS DUPLICATED WITH X86_INJ*)
  Lemma set_regs_empty_1:
    forall regs rs,
      set_regs regs [::] rs = rs.
  Proof.
    intros;
    induction regs; by reflexivity.
  Qed.
  
  Hint Resolve erased_regs_set : erased.

  (** ** Result about at_external, after_external and initial_core *)
  Lemma at_external_erase:
    forall c c' (Herase: erasedCores c c'),
      match at_external Sem c, at_external Sem c' with
      | Some (ef, sig, vs), Some (ef', sig', vs') =>
        ef = ef' /\ sig = sig' /\ erased_val_list vs vs'
      | None, None => True
      | _, _ => False
      end.
  Proof.
    intros.
    unfold erasedCores in *.
    destruct c, c'; try (by exfalso);
    repeat match goal with
    | [H: _ /\ _ |- _] => destruct H
           end; subst;
    unfold at_external; simpl; auto.
    destruct (BuiltinEffects.observableEF_dec f0); auto.
    split; auto.
    split; auto.
    eapply erased_val_list_decode; eauto.
  Qed.

  Lemma after_external_erase :
    forall v v' c c' c2
      (HeraseCores: erasedCores c c')
      (HeraseVal: erased_val v v')
      (Hafter_external: after_external X86SEM.Sem (Some v) c = Some c2),
    exists (c2' : state),
      after_external X86SEM.Sem (Some v') c' = Some c2' /\
      erasedCores c2 c2'.
  Proof.
    intros.
    unfold after_external in *.
    simpl in *.
    unfold Asm_after_external in *.
    destruct c; try discriminate.
    inv Hafter_external.
    unfold erasedCores in HeraseCores.
    destruct c'; try by exfalso.
    destruct HeraseCores as (? & ? & ? &?); subst.
    unfold erased_loader in H2; subst.
    eexists; split; eauto.
    simpl.
    split; [|unfold erased_loader; auto].      
    destruct (loc_external_result (ef_sig f0)) as [|r' regs];
      simpl.
    eapply erased_regs_set; eauto.
    eapply H1.
    destruct (sig_res (ef_sig f0)) as [ty|];
      try destruct ty;
      simpl;
      try do 2 rewrite set_regs_empty_1;
      repeat apply erased_regs_set; eauto;
      try apply H1.
    destruct regs as [|r'' regs'']; simpl;
    eauto with erased.
    do 2 rewrite set_regs_empty_1;
      eauto with erased.
  Qed.

  Lemma erasure_initial_core:
    forall ge v arg v' arg' c
      (Hv: erased_val v v')
      (Harg: erased_val arg arg')
      (Hinit: initial_core Sem ge v [:: arg] = Some c),
      initial_core Sem ge v' [:: arg'] = Some c.
  Proof.
    intros.
    unfold initial_core in *; simpl in *.
    unfold  Asm_initial_core in *.
    destruct v; try discriminate.
    inversion Hv; subst.
    destruct (Int.eq_dec i Int.zero); try discriminate.
    destruct (Genv.find_funct_ptr ge b); try discriminate.
    destruct f; try discriminate.
    match goal with
    | [H: match ?Expr with _ => _ end = _ |- _] =>
      destruct Expr eqn:?
    end; try discriminate.
    apply andb_true_iff in Heqb0.
    destruct Heqb0.
    apply andb_true_iff in H.
    destruct H.
    unfold val_casted.vals_defined in *.
    destruct arg; (try discriminate);
    inv Harg; rewrite H0 H; simpl;
    auto.
  Qed.

  Lemma halted_erase:
    forall c c'
      (HeraseCores: erasedCores c c')
      (Hhalted: halted Sem c),
      halted Sem c'.
  Proof.
    intros.
    unfold halted in *; simpl in *.
    unfold Asm_halted in *.
    destruct c; try by exfalso.
    destruct c'; try by exfalso.
    destruct HeraseCores.
    unfold erased_loader in H0. subst.
    destruct loader0; try by exfalso.
    destruct (Val.eq (rs PC) Vundef).
    rewrite e in Hhalted.
    simpl in Hhalted; by exfalso.
    pose proof (H PC). unfold erased_reg, Pregmap.get in H0.
    erewrite <- erased_val_cmp_bool; eauto.
    destruct (Val.cmp_bool Ceq (rs PC) Vzero); try by exfalso.
    destruct retty; try by exfalso.
    destruct t; auto.
    auto.
  Qed.

  Lemma exec_instr_erased:
    forall (g : genv) (fn : function) (i : instruction) (rs rs' rs2: regset)
      (m m' m2 : mem)
      (HeraseCores: erased_regs rs rs')
      (HerasedMem: erasedMem m m')
      (Hexec: exec_instr g fn i rs m = Next rs2 m2),
    exists rs2' m2',
      exec_instr g fn i rs' m' = Next rs2' m2' /\
      erased_regs rs2 rs2' /\ erasedMem m2 (erasePerm m2').
 Admitted.

  (* TODO: move this to the right place*)
  Lemma get_erased_reg:
    forall rs rs' r
      (Herased_regs: erased_regs rs rs')
      (Hundef: rs r <> Vundef),
      rs r = rs' r.
  Proof.
    intros.
    unfold erased_regs, erased_reg, Pregmap.get, erased_val in *.
    specialize (Herased_regs r).
    destruct (rs r); tauto.
  Qed.

  Lemma evstep_erase:
    forall ge c1 c1' c2 ev m1 m1' m2
      (HeraseCores: erasedCores c1 c1')
      (HerasedMem: erasedMem m1 m1')
      (Hstep: ev_step Sem ge c1 m1 ev c2 m2),
    exists c2' m2',
      ev_step Sem ge c1' m1' ev c2' m2' /\
      erasedCores c2 c2' /\ erasedMem m2 (erasePerm m2').
  Proof with eauto with erased.
    intros.
    destruct c1 as [rs1 loader1 | |]; simpl in *;
    destruct c1' as [rs1' loader1' | |]; try by exfalso.
    - destruct HeraseCores as [Hrs Hloader].
      unfold erased_loader in Hloader; subst.
      inversion Hstep; subst; try (by exfalso).
      + assert (Hpc' : rs1' PC = Vptr b ofs)
          by (erewrite get_erased_reg in H1; eauto;
              rewrite H1; discriminate).
      destruct (exec_instr_erased _ _ _ Hrs HerasedMem H4)
        as (rs2' & m2' & Hexec' & Hrs2 & Hm2).
      exists (State rs2' loader1'), m2'.
      repeat match goal with
             | [ |- _ /\ _] =>
               split; simpl; eauto with erased
             end.
      econstructor...
      admit.
    + assert (Hpc' := get_reg_ren PC Hrs_ren H1).
      destruct Hpc' as [v' [Hpc' Hpc_obs]].
      inversion Hpc_obs; subst. rewrite <- H0 in Hpc_obs.
      assert (Hargs' := extcall_arguments_ren _ H6 Hobs_eq Hrs_ren).
      assert (Hfun := find_funct_ptr_ren Hfg Hge_wd Hincr Hpc_obs H2); subst b2.
      destruct Hargs' as [args' [Hargs' Hval_obs']].
      exists (Asm_CallstateOut ef args' rsF loaderF), mf, f.
      unfold ren_incr, ren_separated.
      repeat match goal with
             | [|- _ /\ _] => split; auto
             | [|- forall _, _] => intros
             end; try (by congruence);
      econstructor; eauto.
  - inversion Hcorestep; subst.
    split; auto. split.
    exists f; split; eauto using ren_domain_incr_refl.
    intros f' Hdomain'.
    simpl.
    destruct Hwd.
    split; first by (eapply extcall_arguments_valid; eauto with wd).
    split...
  - inversion Hcorestep; subst.
    destruct Hwd.
    assert (Hstk := Mem.valid_new_block _ _ _ _ _ H7).
    eapply mem_valid_alloc in H7; eauto.
    destruct H7. destruct H2 as [f' [Hincr' Hdomain']].
    split.
    eapply valid_val_list_incr in H0; eauto.
    eapply load_frame_store_args_rec_valid with (f := f'); eauto.
    split.
    exists f'; split; eauto.
    eapply load_frame_store_args_rec_domain...
    intros f'' Hdomain''.
    simpl.
    erewrite (Hdomain' stk) in Hstk.
    assert (domain_memren f' m')
      by (eapply load_frame_store_args_rec_domain; eauto with wd).
    assert (exists x, f'' stk = Some x).
    { erewrite <- (H2 stk) in Hstk.
      erewrite (Hdomain'' stk) in Hstk.
      destruct (f'' stk); try by exfalso.
      eexists; eauto. }
    split.
    intro r.
    unfold Pregmap.get.
    apply regset_wd_set; auto.
    apply regset_wd_set; simpl; auto.
    apply regset_wd_set; simpl.
    apply Hincr' in H.
    erewrite <- (H2 f0) in H.
    erewrite (Hdomain'' f0) in H.
    destruct (f'' f0); try by exfalso.
    eexists; eauto.
    intro r0. unfold Pregmap.get. rewrite Pregmap.gi.
    simpl; auto.
    destruct H3. rewrite H3. auto.
  - inversion Hcorestep; by exfalso.
  Qed.

End X86CoreErasure.
  



