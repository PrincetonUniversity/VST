Require Import sepcomp.semantics.
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
Require Import concurrency.threads_lemmas.
Require Import concurrency.mem_obs_eq.
Require Import ccc26x86.Asm ccc26x86.Asm_coop.
Require Import concurrency.dry_context.

Import ValObsEq Renamings.

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

    (** Well-definedness for global env not only implies that every
  valid block in it is mapped, but also that it's mapped with the id
  renaming *)
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
  
End X86WD.

(** ** Injections on X86 cores *)

Module X86Inj <: CoreInjections.
    
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
  
  Definition core_inj f c c' :=
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

  Import Genv.
  Definition ge_inj f (g g' : genv) :=
    (genv_public g) = (genv_public g') /\
    (genv_symb g) = (genv_symb g') /\
    (forall b b', f b = Some b' ->
             Maps.PTree.get b (genv_funs g) =
             Maps.PTree.get b' (genv_funs g')) /\
    (forall b b', f b = Some b' ->
             Maps.PTree.get b (genv_vars g) =
             Maps.PTree.get b' (genv_vars g')).
  
  Import MemoryWD.
  Include X86WD.

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

  Lemma set_regs_empty_1:
    forall regs rs,
      set_regs regs [::] rs = rs.
  Proof.
    intros;
    induction regs; by reflexivity.
  Qed.

  Lemma set_regs_empty_2:
    forall vs rs,
      set_regs [::] vs rs = rs.
  Proof.
    intros; simpl; reflexivity.
  Qed.

  Lemma set_regs_gsspec_1:
    forall r regs v rs,
      Pregmap.get r (set_regs (r :: regs) [:: v] rs) = v.
  Proof.
    intros.
    simpl. rewrite set_regs_empty_1.
    rewrite Pregmap.gsspec.
    rewrite Coqlib2.if_true;
      by auto.
  Qed.

  Lemma set_regs_gsspec_2:
    forall r r' regs v rs,
      r <> r' ->
      Pregmap.get r (set_regs (r' :: regs) [:: v] rs) = Pregmap.get r rs.
  Proof.
    intros.
    simpl.
    rewrite set_regs_empty_1.
    rewrite Pregmap.gsspec.
    rewrite Coqlib2.if_false; auto.
  Qed.

  Lemma get_reg_renC:
    forall f r rs rs',
      regset_ren f rs rs' ->
      rs' r = val_obsC f (rs r).
  Proof.
    intros.
    unfold regset_ren, reg_ren, Pregmap.get in *.
    specialize (H r).
    destruct (rs r) eqn:Heqv;
      inversion H; simpl; try reflexivity.
    subst.
      by rewrite H1.
  Qed.

  Lemma get_reg_ren:
    forall f r rs rs' v,
      regset_ren f rs rs' ->
      rs r = v ->
      exists v', rs' r = v' /\ val_obs f v v'.
  Proof.
    intros.
    unfold regset_ren, reg_ren in *.
    specialize (H r).
    unfold Pregmap.get in *.
    rewrite H0 in H.
    eexists;
      by eauto.
  Qed.

  Lemma val_obs_reg:
    forall f r rs rs',
      regset_ren f rs rs' ->
      val_obs f (rs r) (rs' r).
  Proof.
    intros.
    specialize (H r).
      by auto.
  Qed.
    
  Lemma regset_ren_trans:
    forall f f' f'' rs rs' rs'',
      regset_ren f rs rs'' ->
      regset_ren f' rs rs' ->
      (forall b b' b'' : block,
          f b = Some b'' -> f' b = Some b' -> f'' b' = Some b'') ->
      regset_ren f'' rs' rs''.
  Proof.
    intros.
    unfold regset_ren, reg_ren in *.
    intros r.
    specialize (H r).
    specialize (H0 r).
    eapply val_obs_trans;
      by eauto.
  Qed.

  Lemma regset_ren_id:
    forall f rs
      (Hregset_wd: regset_wd f rs)
      (Hf: forall b1 b2, f b1 = Some b2 -> b1 = b2),
      regset_ren f rs rs.
  Proof.
    intros.
    unfold regset_ren, reg_ren.
    intros r.
    specialize (Hregset_wd r).
    destruct (Pregmap.get r rs); constructor.
    simpl in Hregset_wd.
    destruct Hregset_wd as [b' Hfb].
    specialize (Hf _ _ Hfb);
      by subst.
  Qed.

  
  Lemma loader_ren_trans:
    forall f f' f'' loader loader' loader'',
      loader_ren f loader loader'' ->
      loader_ren f' loader loader' ->
      (forall b b' b'' : block,
          f b = Some b'' -> f' b = Some b' -> f'' b' = Some b'') ->
      loader_ren f'' loader' loader''.
  Proof.
    intros.
    unfold loader_ren in *.
    destruct loader, loader', loader''.
    destruct H, H0; split; subst; eauto.
  Qed.

  Lemma loader_ren_id:
    forall f loader
      (Hloader_wd: loader_wd f loader)
      (Hf: forall b1 b2, f b1 = Some b2 -> b1 = b2),
      loader_ren f loader loader.
  Proof.
    intros.
    unfold loader_ren, loader_wd in *.
    destruct loader; split; auto.
    destruct (f sp) eqn:Hfsp;
      [apply Hf in Hfsp;
         by subst | by exfalso].
  Qed.

  Lemma loader_ren_incr:
    forall f f' loader loader',
      loader_ren f loader loader' ->
      ren_incr f f' ->
      loader_ren f' loader loader'.
  Proof.
    intros.
    unfold loader_ren, ren_incr in *.
    destruct loader, loader';
      destruct H;
        by auto.
  Qed.

  Hint Resolve
       loader_ren_incr loader_ren_id loader_ren_trans
       regset_ren_id val_obs_reg val_obs_add : renamings.
  
  Lemma ge_wd_incr :
    forall (f f' : memren) (g : SEM.G),
      ge_wd f g -> ren_domain_incr f f' -> ge_wd f' g.
  Proof.
    intros.
    unfold ge_wd in *.
    destruct H;
      split;
      intros b Hget;
        by eauto.
  Qed.

  Lemma ge_wd_domain :
    forall (f f' : memren) (m : mem) (g : SEM.G),
      ge_wd f g -> domain_memren f m -> domain_memren f' m -> ge_wd f' g.
  Proof.
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
  Qed.

  Lemma core_wd_incr :
    forall (f f' : memren) (c : DryMachine.ThreadPool.code),
      core_wd f c -> ren_domain_incr f f' -> core_wd f' c.
  Proof.
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
  Qed.
  
  Lemma core_wd_domain :
    forall (f f' : memren) (m : mem) (c : DryMachine.ThreadPool.code),
      core_wd f c ->
      domain_memren f m -> domain_memren f' m -> core_wd f' c.
  Proof.
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
  Qed.
  
  Lemma at_external_wd :
    forall (f : memren) (c : DryMachine.ThreadPool.code)
      (ef : external_function) (sig : signature) 
      (args : seq val),
      core_wd f c ->
      at_external SEM.Sem c = Some (ef, sig, args) -> valid_val_list f args.
  Proof.
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
  Qed.
  
  Lemma after_external_wd :
    forall (c c' : state) (f : memren) (ef : external_function)
      (sig : signature) (args : seq val) (ov : option val),
      at_external SEM.Sem c = Some (ef, sig, args) ->
      core_wd f c ->
      valid_val_list f args ->
      after_external SEM.Sem ov c = Some c' -> core_wd f c'.
  Proof.
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
  Admitted.
  
  Lemma initial_core_wd :
    forall (f : memren) (vf arg : val) (c_new : state),
      initial_core SEM.Sem the_ge vf [:: arg] = Some c_new ->
      valid_val f arg -> ge_wd f the_ge -> core_wd f c_new.
  Proof.
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
  Qed.
  
  Lemma ge_inj_id :
    forall (f : memren) (g : SEM.G),
      ge_wd f g ->
      (forall b1 b2 : block, f b1 = Some b2 -> b1 = b2) -> ge_inj f g g.
  Proof.
    intros.
    unfold ge_inj.
    unfold ge_wd in *.
    destruct H.
    repeat (split; auto);
      intros b b' Hf;
      specialize (H0 _ _ Hf); subst;
      reflexivity.
  Qed.
  
  Lemma core_inj_ext :
    forall (c c' : DryMachine.ThreadPool.code) (f : memren),
      core_inj f c c' ->
      match at_external SEM.Sem c with
      | Some (ef, sig, vs) =>
        match at_external SEM.Sem c' with
        | Some (ef', sig', vs') =>
          ef = ef' /\ sig = sig' /\ val_obs_list f vs vs'
        | None => False
        end
      | None =>
        match at_external SEM.Sem c' with
        | Some _ => False
        | None => True
        end
      end.
  Proof.
    intros c c' f Hinj.
    simpl.
    unfold core_inj in Hinj.
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
  Qed.

  Lemma core_inj_after_ext :
    forall (c : DryMachine.ThreadPool.code) (cc : state)
      (c' : DryMachine.ThreadPool.code) (ov1 : option val) 
      (f : memren),
      core_inj f c c' ->
      match ov1 with
      | Some v1 => valid_val f v1
      | None => True
      end ->
      after_external SEM.Sem ov1 c = Some cc ->
      exists (ov2 : option val) (cc' : state),
        after_external SEM.Sem ov2 c' = Some cc' /\
        core_inj f cc cc' /\
        match ov1 with
        | Some v1 =>
          match ov2 with
          | Some v2 => val_obs f v1 v2
          | None => False
          end
        | None => match ov2 with
                 | Some _ => False
                 | None => True
                 end
        end.
  Proof.
    intros c cc c' ov1 f Hinj Hov1 Hafter_external.
    simpl in *.
    unfold core_inj in Hinj.
    unfold Asm_after_external in Hafter_external.
    destruct c; try discriminate.
    destruct c'; try by exfalso.
    destruct Hinj as (? & ? & ? & ?).
    subst.
    simpl.
    assert (Hov:
              forall v v',
                val_obs f v v' ->
                regset_ren f
                           (set_regs (loc_external_result (ef_sig f1))
                                     (encode_long (sig_res (ef_sig f1)) v) rs) # PC <- 
                           (rs RA)
                           (set_regs (loc_external_result (ef_sig f1))
                                     (encode_long (sig_res (ef_sig f1)) v') rs0) # PC <-
                           (rs0 RA)).
    { intros.
      intros r.
      unfold regset_ren, reg_ren in *.
      do 2 rewrite Pregmap.gsspec.
      destruct (Pregmap.elt_eq r PC); subst;
      simpl;
      first by eauto.
      (* it's easier to do the case analysis than try to write a lemma
    for set_regs (are the registers unique and more similar problems)*)
      destruct (loc_external_result (ef_sig f1)) as [|r' regs].
      do 2 rewrite set_regs_empty_2;
        first by eauto.
      unfold regset_ren, reg_ren in *.
      destruct (sig_res (ef_sig f1)) as [ty|];
        try destruct ty;
        simpl;
        try do 2 rewrite set_regs_empty_1;
        try do 2 rewrite Pregmap.gsspec;
        try (destruct (Pregmap.elt_eq r r'); subst; eauto);
        destruct regs as [|r'' regs''];
        simpl;
        try (do 2 rewrite Pregmap.gsspec);
        repeat match goal with
               | [|- context[match Pregmap.elt_eq ?X ?X with _ => _ end]] =>
                 rewrite Coqlib2.if_true; auto
               | [H: ?X <> ?Y|- context[match Pregmap.elt_eq ?X ?Y with _ => _ end]] =>
                 rewrite Coqlib2.if_false; auto
               | [|- val_obs _ (Val.hiword _) (Val.hiword _)] =>
                 eapply val_obs_hiword
               | [|- context[set_regs _ [::] _]] =>
                 rewrite set_regs_empty_1
               end; eauto;
        do 4 rewrite Pregmap.gsspec;
        repeat match goal with
               | [|- context[match ?Expr with _ => _ end]] =>
                 destruct Expr; subst; eauto
               | [|- val_obs _ (Val.loword _) (Val.loword _)] =>
                 eapply val_obs_loword
               | [|- val_obs _ (Val.hiword _) (Val.hiword _)] =>
                 eapply val_obs_hiword
               end; eauto.
    }
    simpl in Hafter_external.
    inversion Hafter_external.
    destruct ov1 as [v1 |];
      inversion H3; subst.
    exists (Some (val_obsC f v1)).
    eexists; split; eauto.
    simpl.
    split.
    split; auto.
    eapply Hov.
    all: try (eapply val_obsC_correct; eauto).
    exists None.
    eexists; split; eauto.
    simpl.
    split; auto.
    split; auto.
    eapply Hov;
      by constructor.
  Qed.

  Lemma core_inj_halted :
    forall (c c' : DryMachine.ThreadPool.code) (f : memren),
      core_inj f c c' ->
      match halted SEM.Sem c with
      | Some v =>
        match halted SEM.Sem c' with
        | Some v' => val_obs f v v'
        | None => False
        end
      | None =>
        match halted SEM.Sem c' with
        | Some _ => False
        | None => True
        end
      end.
  Proof.
    intros.
    simpl.
    unfold core_inj in *.
    destruct (Asm_halted c) eqn:Hhalted;
      unfold Asm_halted in Hhalted;
      destruct c; try discriminate;
      destruct c'; try discriminate;
      simpl;
      unfold loader_ren in *;
      repeat match goal with
             | [H: _ /\ _ |- _] => destruct H
             | [H: context[match ?Expr with _ => _ end] |- _] =>
               destruct Expr eqn:?
             | [H: Some _ = Some _ |- _] => inversion H; clear H
             end; auto;
      subst; try discriminate; try (by exfalso);
      unfold regset_ren, reg_ren in *;
      try (erewrite <- ren_cmp_bool with (v := rs PC); eauto;
           rewrite Heqo);
      eauto;
      simpl in Heql0.
    destruct (rs EDX) eqn:?; simpl in *; inversion Heql0;
    subst;
    erewrite get_reg_renC with (r := EDX); eauto;
    rewrite Heqv0; simpl;
    try constructor.
    erewrite get_reg_renC with (f := f) (rs := rs) (rs' := rs0); eauto.
    destruct (rs EAX) eqn:Heax; subst;
    simpl;
    try constructor.
    specialize (H EAX).
    unfold Pregmap.get in *.
    rewrite Heax in H. inversion H; subst.
    rewrite H2;
      by constructor.
    specialize (H EDX).
    unfold Pregmap.get in H.
    rewrite Heqv0 in H.
    inversion H; subst.
    rewrite H2.
    simpl;
      by constructor.
  Qed.
  
  Lemma core_inj_init :
    forall (vf vf' : val) (arg arg' : seq val) (c_new : state)
      (f fg : memren),
      val_obs_list f arg arg' ->
      val_obs f vf vf' ->
      ge_wd fg the_ge ->
      ge_inj fg the_ge the_ge ->
      ren_incr fg f ->
      initial_core SEM.Sem the_ge vf arg = Some c_new ->
      exists c_new' : state,
        initial_core SEM.Sem the_ge vf' arg' = Some c_new' /\
        core_inj f c_new c_new'.
  Proof.
    intros vf vf' arg arg' c_new f fg Harg Hvf Hge_wd Hge_inj Hincr Hinit.
    simpl in *.
    unfold Asm_initial_core in *.
    destruct vf; try discriminate.
    inversion Hvf; subst.
    destruct (Int.eq_dec i Int.zero); subst; try discriminate.
    unfold Genv.find_funct_ptr in *.
    destruct (Maps.PTree.get b (genv_funs the_ge)) eqn:Hget; try discriminate.
    destruct f0; try discriminate.
    destruct Hge_wd as [Hge_wd1 Hge_wd2].
    specialize (Hge_wd1 b ltac:(rewrite Hget; eauto)).
    unfold ge_inj in Hge_inj.
    destruct Hge_inj as (? & ? & ? &?).
    assert (Hfg: fg b = Some b2).
    destruct (fg b) eqn:Hfg;
      [apply Hincr in Hfg; rewrite Hfg in H2; inversion H2; by subst
      | by exfalso].
    specialize (H1 _ _ Hfg).
    rewrite <- H1.
    rewrite Hget.
    match goal with
    | [H: context[match ?Expr with _ => _ end] |- _] =>
      destruct Expr eqn:Hguard
    end; try discriminate.
    move/andP:Hguard => [Hguard1 Hguard2].
    move/andP:Hguard1 => [Hguard1 Hguard3].
    eexists.
    do 2 rewrite Bool.andb_if.
    repeat rewrite if_true.
    split; eauto.
    inversion Hinit.
    simpl.
    repeat (split; auto).
    erewrite <- zlength_obs; eauto.
    erewrite <- vals_defined_obs; eauto.
    erewrite <- val_has_type_list_obs; eauto.
  Qed.
  
  Lemma core_inj_id :
    forall (c : DryMachine.ThreadPool.code) (f : memren),
      core_wd f c ->
      (forall b1 b2 : block, f b1 = Some b2 -> b1 = b2) -> core_inj f c c.
  Proof.
    intros c f Hcore_wd Hid.
    unfold core_inj, core_wd in *.
    destruct c;
      repeat match goal with
             | [ |- _ /\ _] => split
             | [H: _ /\ _ |- _] => destruct H
             | [|- regset_ren _ _ _] =>
               eapply regset_ren_id
             | [|- loader_ren _ _ _] =>
               eapply loader_ren_id
             | [H: forall _ _, _ |- f ?X = Some ?X]  =>
               destruct (f X) eqn:Hf;
                 [eapply H in Hf; by subst | by exfalso]
             | [|- val_obs_list _ _ _] =>
               eapply ValObsEq.val_obs_list_id
             end; eauto.
  Qed.

  Lemma core_inj_trans :
    forall (c c' c'' : DryMachine.ThreadPool.code) (f f' f'' : memren),
      core_inj f c c'' ->
      core_inj f' c c' ->
      (forall b b' b'' : block,
          f b = Some b'' -> f' b = Some b' -> f'' b' = Some b'') ->
      core_inj f'' c' c''.
  Proof.
    intros.
    unfold core_inj in *.
    destruct c; destruct c'; (try by exfalso);
    destruct c''; (try by exfalso);
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [|- _ /\ _] => split
           | [|- regset_ren _ _ _] =>
             eapply regset_ren_trans; eauto 
           | [|- loader_ren _ _ _] =>
             eapply loader_ren_trans; eauto
           | [|- val_obs_list _ _ _] =>
             eapply val_obs_list_trans; eauto
           end; subst; eauto.
  Qed.


  (** ** Proof that related states take related steps*)

  Import MemObsEq.

  Lemma find_funct_ptr_ren:
    forall (g : genv) b1 b2 ofs (f fg : memren) fn
      (Hge_inj: ge_inj fg g g)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Hobs_eq: val_obs f (Vptr b1 ofs) (Vptr b2 ofs))
      (Hget: Genv.find_funct_ptr g b1 = Some fn),
      Genv.find_funct_ptr g b2 = Some fn.
  Proof.
    intros.
    unfold Genv.find_funct_ptr in *.
    assert (Hfg: fg b1 = Some b2).
    { inversion Hobs_eq; subst.
      destruct Hge_wd as [H1 H2].
      specialize (H1 b1 ltac:(erewrite Hget; eauto)).
      destruct (fg b1) eqn:Hfg; try by exfalso.
      apply Hincr in Hfg.
      rewrite Hfg in H0; inversion H0; by subst.
    }
    destruct Hge_inj as (_ & _ & Hfn & _).
    specialize (Hfn _ _ Hfg);
      by rewrite <- Hfn.
  Qed.

  (** Executing an instruction in related states results in related
  states: 1. The renaming function is extended to accommodate newly
  allocated blocks. 2. The extension to the renaming only relates
  newly allocated blocks 3. The nextblock of the two memories is
  increased by the same amount of blocks 4. Any newly allocated block
  on the second memory is mapped by a new block on the first memory
  (computable inverse) 5. If the initial nextblocks are equal and the
  two memories were related by an id renaming, then the new memories
  are still related by an (extended) id renaming*)
  Lemma exec_instr_ren:
    forall (g : genv) (fn : function) (i : instruction) (rs rs' rs2: regset)
      (m m' m2 : mem) (f fg: memren)
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hrs_eq: regset_ren f rs rs')
      (Hge_inj: ge_inj fg g g)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Hexec: exec_instr g fn i rs m = Next rs2 m2),
    exists f' rs2' m2',
      exec_instr g fn i rs' m' = Next rs2' m2' /\
      regset_ren f' rs2 rs2' /\
      mem_obs_eq f' m2 m2' /\
      ren_incr f f' /\
      ren_separated f f' m m' /\
      ((exists p : positive,
           Mem.nextblock m2 = (Mem.nextblock m + p)%positive /\
           Mem.nextblock m2' = (Mem.nextblock m' + p)%positive) \/
       Mem.nextblock m2 = Mem.nextblock m /\
       Mem.nextblock m2' = Mem.nextblock m') /\
      (forall b0 : block,
          Mem.valid_block m2' b0 ->
          ~ Mem.valid_block m' b0 ->
          f'
            (Z.to_pos
               match (- Z.pos_sub (Mem.nextblock m') (Mem.nextblock m))%Z with
               | 0%Z => Z.pos b0
               | Z.pos y' => Z.pos (b0 + y')
               | Z.neg y' => Z.pos_sub b0 y'
               end) = Some b0 /\
          f
            (Z.to_pos
               match (- Z.pos_sub (Mem.nextblock m') (Mem.nextblock m))%Z with
               | 0%Z => Z.pos b0
               | Z.pos y' => Z.pos (b0 + y')
               | Z.neg y' => Z.pos_sub b0 y'
               end) = None) /\
      (Mem.nextblock m = Mem.nextblock m' ->
       (forall b1 b3 : block, f b1 = Some b3 -> b1 = b3) ->
       forall b1 b0 : block, f' b1 = Some b0 -> b1 = b0).
  Proof.
    Admitted.
  
  Lemma corestep_obs_eq:
    forall (cc cf cc' : Asm_coop.state) (mc mf mc' : mem) f fg,
      mem_obs_eq f mc mf ->
      core_inj f cc cf ->
      ge_inj fg the_ge the_ge ->
      ge_wd fg the_ge ->
      ren_incr fg f ->
      corestep SEM.Sem the_ge cc mc cc' mc' ->
      exists (cf' : Asm_coop.state) (mf' : mem) (f' : Renamings.memren),
        corestep SEM.Sem the_ge cf mf cf' mf' /\
        core_inj f' cc' cf' /\
        mem_obs_eq f' mc' mf' /\
        ren_incr f f' /\
        ren_separated f f' mc mf /\
        ((exists p : positive,
             Mem.nextblock mc' = (Mem.nextblock mc + p)%positive /\
             Mem.nextblock mf' = (Mem.nextblock mf + p)%positive) \/
         Mem.nextblock mc' = Mem.nextblock mc /\
         Mem.nextblock mf' = Mem.nextblock mf) /\
        (forall b : block,
            Mem.valid_block mf' b ->
            ~ Mem.valid_block mf b ->
            let bz :=
                (Z.pos b - (Z.pos (Mem.nextblock mf) - Z.pos (Mem.nextblock mc)))%Z in
            f' (Z.to_pos bz) = Some b /\ f (Z.to_pos bz) = None) /\
        (Mem.nextblock mc = Mem.nextblock mf ->
         (forall b1 b2 : block, f b1 = Some b2 -> b1 = b2) ->
         forall b1 b2 : block, f' b1 = Some b2 -> b1 = b2).
  Proof with (eauto with renamings).
    intros cc cf cc' mc mf mc' f fg Hobs_eq Hcore_inj Hge_inj Hge_wd Hincr Hcorestep.
    destruct cc as [rs loader | |]; simpl in *;
    destruct cf as [rsF loaderF | |]; try by exfalso.
    - destruct Hcore_inj as [Hrs_ren Hloader_ren].
      inversion Hcorestep; subst.
      + assert (Hpc' := get_reg_ren PC Hrs_ren H1).
        destruct Hpc' as [v' [Hpc' Hpc_obs]].
        inversion Hpc_obs; subst. rewrite <- H0 in Hpc_obs.
        assert (Hfun := find_funct_ptr_ren Hge_inj Hge_wd Hincr Hpc_obs H2).
        destruct (exec_instr_ren _ _ Hobs_eq Hrs_ren Hge_inj Hge_wd Hincr H7)
          as (f' & rsF' & mF' & Hexec' & Hrs_ren' & Hobs_eq' & Hincr' & Hsep
              & Hnextblocks & Hinverse & Hid_extend).
        exists (State rsF' loaderF), mF', f'.
        repeat match goal with
               | [ |- _ /\ _] =>
                split; simpl; eauto with renamings
               end.
        econstructor...
      + assert (Hpc' := get_reg_ren PC Hrs_ren H1).
        destruct Hpc' as [v' [Hpc' Hpc_obs]].
        inversion Hpc_obs; subst. rewrite <- H0 in Hpc_obs.
        assert (Hfun := find_funct_ptr_ren Hge_inj Hge_wd Hincr Hpc_obs H2).

        Lemma eval_builtin_args_ren:
          forall (g : genv) (rs rs' : regset) (f fg: memren) (m m' : mem)
            (args : seq (builtin_arg preg)) (vargs : seq val)
            (Hmem_obs_eq: mem_obs_eq f m m')
            (Hrs_ren: regset_ren f rs rs')
            (Hge_inj: ge_inj fg g g)
            (Hge_wd: ge_wd fg g)
            (Hincr: ren_incr fg f)
            (Heval: eval_builtin_args g rs (rs ESP) m args vargs),
          exists vargs',
            eval_builtin_args g rs' (rs' ESP) m' args vargs' /\
            val_obs_list f vargs vargs'.
        Proof.
          intros.
          induction Heval; subst.
          exists [::].
          split;
            by constructor.
          

          Lemma eval_builtin_arg_ren:
            forall (g : genv) (rs rs' : regset) (f fg: memren) (m m' : mem)
              (arg : builtin_arg preg) (varg : val)
              (Hmem_obs_eq: mem_obs_eq f m m')
              (Hrs_ren: regset_ren f rs rs')
              (Hge_inj: ge_inj fg g g)
              (Hge_wd: ge_wd fg g)
              (Hincr: ren_incr fg f)
              (Heval: eval_builtin_arg g rs (rs ESP) m arg varg),
            exists varg',
              eval_builtin_arg g rs' (rs' ESP) m' arg varg' /\
              val_obs f varg varg'.
          Proof with (eauto with renamings).
            intros.
            inversion Heval; subst;
            try (by (eexists; split;
                     (econstructor || eauto with renamings))).
            
            
            
            
            
  
End X86Inj.    






