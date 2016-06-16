Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import concurrency.addressFiniteMap.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Notation EXIT := 
  (EF_external 1%positive (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation CREATE := (EF_external 2%positive CREATE_SIG).

Notation READ := 
  (EF_external 3%positive 
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation WRITE := 
  (EF_external 4%positive 
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).

Notation MKLOCK := 
  (EF_external 5%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation FREE_LOCK := 
  (EF_external 6%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation LOCK := (EF_external 7%positive LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation UNLOCK := (EF_external 8%positive UNLOCK_SIG).

Require Import concurrency.threads_lemmas.
Require Import concurrency.mem_obs_eq.
Require Import ccc26x86.Asm ccc26x86.Asm_coop.
Require Import concurrency.dry_context.

Import CoreInjections ValObsEq Renamings.

(** ** Well defined X86 cores *)
Module X86WD.
  Import MemoryWD Genv SEM.
  Section X86WD.
    Variable f: memren.

    Definition regset_wd rs : Prop :=
      forall r, valid_val f (Pregmap.get r rs).
    
    Definition loader_wd (loader : load_frame) : Prop :=
      match loader with
      | mk_load_frame b _ =>
        f b
      end.
   
  Definition core_wd (c : state) : Prop :=
    match c with
    | State rs loader =>
      regset_wd rs /\
      loader_wd loader
    | Asm_CallstateIn vf args _ _ =>
      f vf /\ valid_val_list f args
    | Asm_CallstateOut ef vals rs loader =>
      valid_val_list f vals /\ regset_wd rs /\ loader_wd loader
    end.

  Definition ge_wd (the_ge: genv) : Prop :=
    (forall b, Maps.PTree.get b (genv_funs the_ge) ->
          f b) /\
    (forall b, Maps.PTree.get b (genv_vars the_ge) ->
          f b).
  
  End X86WD.

  Lemma regset_wd_incr :
    forall f1 f2 rs
      (Hincr: ren_domain_incr f1 f2)
      (Hwd: regset_wd f1 rs),
      regset_wd f2 rs.
  Proof.
    intros. unfold regset_wd in *.
    intros r. specialize (Hwd r).
    eapply valid_val_incr;
        by eauto.
  Qed.

  Lemma loader_wd_incr:
    forall f1 f2 loader
      (Hwd: loader_wd f1 loader)
      (Hincr: ren_domain_incr f1 f2),
      loader_wd f2 loader.
  Proof.
    intros.
    unfold loader_wd in *.
    destruct loader.
      by eauto.
  Qed.

  Lemma regset_wd_domain :
    forall f1 f2 m rs
      (Hdomain1: domain_memren f1 m)
      (Hdomain2: domain_memren f2 m)
      (Hwd: regset_wd f1 rs),
      regset_wd f2 rs.
  Proof.
    intros. unfold regset_wd in *.
    intros r. specialize (Hwd r).
    eapply valid_val_domain;
      by eauto.
  Qed.

  Lemma loader_wd_domain :
    forall f1 f2 m loader
      (Hdomain1: domain_memren f1 m)
      (Hdomain2: domain_memren f2 m)
      (Hwd: loader_wd f1 loader),
      loader_wd f2 loader.
  Proof.
    intros; unfold loader_wd in *.
    destruct loader;
      unfold domain_memren in *;
      destruct (Hdomain1 sp), (Hdomain2 sp);
        by eauto.
  Qed.

  Lemma decode_longs_valid_val:
    forall f vals tys,
      valid_val_list f vals ->
      valid_val_list f (decode_longs tys vals).
  Proof.
    intros.
    generalize dependent vals.
    induction tys; intros.
    simpl. by constructor.
    simpl.
    destruct vals;
      [destruct a; constructor |
       destruct a; inversion H; subst];
      try econstructor; eauto.
    destruct vals; first by constructor.
    unfold Val.longofwords.
    inversion H3; subst.
    destruct v;
      constructor; try constructor; eauto.
    destruct v0;
      by constructor.
  Qed.
  
  Instance x86_wd : CoreWD :=
    {| CoreInjections.core_wd := core_wd;
       CoreInjections.ge_wd := ge_wd
    |}.
  Proof.
    - (* ge_wd_incr *)
      intros.
      unfold ge_wd in *.
      destruct H;
        split;
        intros b Hget;
          by eauto.
    - (* ge_wd_domain *)
      intros.
      unfold ge_wd in *.
      destruct H as [Hf Hv];
        split;
        intros b Hget;
      try specialize (Hf _ ltac:(eauto));
      try specialize (Hv _ ltac:(eauto));
      unfold domain_memren in *;
      destruct (H0 b), (H1 b);
        by eauto.
    - (* core_wd_incr *)
      intros.
      unfold core_wd in *.
      destruct c;
        repeat match goal with
               | [H: _ /\ _ |- _ ] => destruct H
               | [|- _ /\ _] => split
               | [|- regset_wd _ _] => eapply regset_wd_incr; eauto
               | [|- loader_wd _ _] => eapply loader_wd_incr; eauto
               | [|- valid_val_list _ _] =>
                 eapply valid_val_list_incr; eauto
               end;
          by eauto.
    - (* core_wd_domain*)
      intros.
      unfold core_wd.
      destruct c; simpl in H;
      repeat match goal with
             | [H: _ /\ _ |- _ ] => destruct H
             | [|- _ /\ _] => split
             | [|- regset_wd _ _] => eapply regset_wd_domain with (f1 := f); eauto
             | [|- loader_wd _ _] => eapply loader_wd_domain with (f1 := f); eauto
             | [|- valid_val_list _ _] =>
               eapply valid_val_list_domain with (f := f); eauto
             end.
      destruct (H0 f0), (H1 f0);
        by eauto.
    - (* at_external_wd *)
      intros.
      unfold core_wd in H.
      simpl in H0.
      unfold Asm_at_external in H0.
      destruct c; try discriminate.
      destruct (BuiltinEffects.observableEF_dec f0); try discriminate.
      inversion H0.
      subst.
      destruct H;
        by eapply decode_longs_valid_val.
    - (* after_external_wd *)
      intros.
      simpl in *.
      unfold core_wd, Asm_at_external, Asm_after_external in *.
      destruct c; try discriminate.
      destruct (BuiltinEffects.observableEF_dec f0); try discriminate.
      destruct H0 as (? & ? & ?).
      inversion H; subst.
      destruct ov; inversion H2; subst.
      + split; auto.
        intros r.
        specialize (H3 r).
        destruct (PregEq.eq r PC).
        * subst. admit.
        (*NOTE: admitting this for now to avoid getting into the
        complicated details *)
        * admit.
      + split; auto.
        admit.
    - (* wd_init *)
      intros.
      simpl in *.
      unfold core_wd, Asm_initial_core in *.
      repeat match goal with
             | [H: match ?Expr with _ => _ end = _ |- _] =>
               destruct Expr eqn:?;
                        try discriminate
             end; subst.
      apply Bool.andb_true_iff in Heqb0.
      destruct Heqb0.
      apply Bool.andb_true_iff in H2.
      destruct H2.
      inversion H; subst.
      split.
      unfold find_funct_ptr in Heqo;
        by specialize ((proj1 H1) b ltac:(rewrite Heqo; auto)).
      constructor;
        by [auto | constructor].
  Admitted.

End X86WD.
  
(** ** Injections on X86 cores *)

Module X86Inj.
(** Injections on registers *)
Definition reg_ren f (r:PregEq.t) (rs rs' : regset) : Prop :=
  val_obs f (Pregmap.get r rs) (Pregmap.get r rs').

Definition regset_ren f rs rs' : Prop :=
  forall r, reg_ren f r rs rs'.

Definition loader_ren f (l l' : load_frame) : Prop :=
  match l, l' with
  | mk_load_frame b ty, mk_load_frame b' ty' =>
    f b = Some b' /\ ty = ty'
  end.
  
Definition core_ren f c c' :=
  match c, c' with
  | State rs loader, State rs' loader' =>
    regset_ren f rs rs' /\ loader_ren f loader loader'
  | Asm_CallstateIn vf args tys retty, Asm_CallstateIn vf' args' tys' retty' =>
    f vf = Some vf' /\ val_obs_list f args args' /\
    tys = tys' /\ retty = retty'
  | Asm_CallstateOut ef vals rs loader, Asm_CallstateOut ef' vals' rs' loader' =>
    ef = ef' /\ val_obs_list f vals vals'
    /\ regset_ren f rs rs' /\ loader_ren f loader loader'
  | _, _ => False
  end.

Import X86WD MemoryWD.

Lemma decode_longs_val_obs_list:
  forall f (vals vals' : seq val) tys
    (Hobs_eq: val_obs_list f vals vals'),
    val_obs_list f (decode_longs tys vals) (decode_longs tys vals').
Proof.
  intros.
  generalize dependent vals.
  generalize dependent vals'.
  induction tys; intros;
  first by (simpl; constructor).
  simpl.
  destruct vals, vals';
    destruct a; try constructor;
    try (inversion Hobs_eq; subst);
    auto.
  destruct vals, vals'; auto;
  try (inversion H4); subst.
  unfold Val.longofwords.
  destruct v; inversion H2; subst;
  constructor; try constructor;
  try auto.
  destruct v1;
    inversion H3; subst;
    constructor; try constructor; auto.
Qed.

Instance x86_inj : CoreInj x86_wd :=
  {| core_inj := core_ren |}.
Proof.
  - (* core_inj_ext *)
    intros.
    simpl.
    unfold core_ren in Hinj.
    destruct (Asm_at_external c) as [[[ef sig] vs]|] eqn:Hat_external;
      destruct (Asm_at_external c') as [[[ef' sig'] vs']|] eqn:Hat_external';
      destruct c, c'; try discriminate; auto;
    destruct Hinj as (? & ? & ? & ?);
    simpl in *; subst;
    match goal with
    | [H: match ?Expr with _ => _ end = _ |- _] =>
      destruct Expr
    end;
    inversion Hat_external;
    inversion Hat_external'; subst.
    subst.
    split; auto.
    split; auto.
    eapply decode_longs_val_obs_list; eauto.

     
      
    
    

    