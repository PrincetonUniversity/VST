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

  Import Genv.
  Definition ge_ren f (g g' : genv) :=
    (genv_public g) = (genv_public g') /\
    (genv_symb g) = (genv_symb g') /\
    (forall b b', f b = Some b' ->
             Maps.PTree.get b (genv_funs g) =
             Maps.PTree.get b' (genv_funs g')) /\
    (forall b b', f b = Some b' ->
             Maps.PTree.get b (genv_vars g) =
             Maps.PTree.get b' (genv_vars g')).
  
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

  Lemma get_reg_ren:
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

  Instance x86_inj : CoreInj :=
    {| CoreInjections.core_wd := X86WD.core_wd;
       CoreInjections.ge_wd := X86WD.ge_wd;
       core_inj := core_ren;
       ge_inj := ge_ren |}.
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
  - (* ge_id *)
    intros.
    unfold ge_ren.
    unfold ge_wd in *.
    destruct H.
    repeat (split; auto);
    intros b b' Hf;
    specialize (H0 _ _ Hf); subst;
    reflexivity.
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
  - (* core_inj_after_ext *)
    intros.
    simpl in *.
    unfold core_ren in Hinj.
    unfold Asm_after_external in H.
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
    simpl in H0.
    inversion H0.
    destruct ov1 as [v1 |];
      inversion H5; subst.
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
  - (* core_inj_halted *)
    intros.
    simpl.
    unfold core_ren in *.
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
    erewrite get_reg_ren with (r := EDX); eauto;
    rewrite Heqv0; simpl;
    try constructor.
    erewrite get_reg_ren with (f := f) (rs := rs) (rs' := rs0); eauto.
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
  - (* core_inj_init *)
    intros.
    simpl in *.
    unfold Asm_initial_core in *.
    destruct vf; try discriminate.
    inversion Hf'; subst.
    destruct (Int.eq_dec i Int.zero); subst; try discriminate.
    unfold Genv.find_funct_ptr in *.
    destruct (Maps.PTree.get b (genv_funs the_ge)) eqn:Hget; try discriminate.
    destruct f0; try discriminate.
    destruct Hge_wd as [Hge_wd1 Hge_wd2].
    specialize (Hge_wd1 b ltac:(rewrite Hget; eauto)).
    unfold ge_ren in Hge_id.
    destruct Hge_id as (? & ? & ? &?).
    assert (Hfg: fg b = Some b2).
    destruct (fg b) eqn:Hfg;
      [apply Hincr in Hfg; rewrite Hfg in H2; inversion H2; by subst
      | by exfalso].
    specialize (H1 _ _ Hfg).
    rewrite <- H1.
    rewrite Hget.

          Lemma val_has_type_obs:
        forall f v v' ty
          (Hval_obs: val_obs f v v'),
          val_casted.val_has_type_func v ty <-> val_casted.val_has_type_func v' ty.
      Proof.
        intros.
        destruct v; inversion Hval_obs; subst; simpl;
          by tauto.
      Qed.
      
    Lemma val_has_type_list_obs:
      forall f vs vs' ts
        (Hval_obs: val_obs_list f vs vs'),
        val_casted.val_has_type_list_func vs ts <->
        val_casted.val_has_type_list_func vs' ts.
    Proof.
      intros.
      generalize dependent vs'.
      generalize dependent ts.
      induction vs;
      intros. inversion Hval_obs; subst.
      simpl; destruct ts; split;
        by auto.
      inversion Hval_obs; subst.
      destruct ts; simpl; first by split; auto.
      split; intros; move/andP:H=>[H H'];
      apply/andP.
      split;
        [erewrite <- val_has_type_obs; eauto |
         destruct (IHvs ts _ H3); eauto].
      split;
        [erewrite val_has_type_obs; eauto |
         destruct (IHvs ts _ H3); eauto].
    Qed.

    Lemma vals_defined_obs:
      forall f vs vs'
        (Hval_obs: val_obs_list f vs vs'),
        val_casted.vals_defined vs <-> val_casted.vals_defined vs'.
    Proof.
      intros.
      induction Hval_obs;
        simpl; try tauto.
      destruct v; inversion H;
        by tauto.
    Qed.

    Lemma zlength_obs:
      forall f v v'
        (Hval_obs: val_obs_list f v v'),
        Zlength v = Zlength v'.
    Proof.
      induction 1; simpl; auto.
      do 2 rewrite Zlength_cons;
        by rewrite IHHval_obs.
    Qed.

    
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
  - (* core_inj_id *)

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
    
    Lemma val_obs_list_id :
      forall f vs
        (Hvalid: valid_val_list f vs)
        (Hf: forall b1 b2, f b1 = Some b2 -> b1 = b2),
        val_obs_list f vs vs.
    Proof.
      intros.
      induction vs; first by constructor.
      inversion Hvalid; subst.
      constructor;
        [eapply val_obs_id; eauto | eauto].
    Qed.
    intros.
    unfold core_ren, core_wd in *.
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
               eapply val_obs_list_id
             end; eauto.
  - (* core_inj_trans *)
    intros.
    unfold core_ren in *.
    
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


    
    
    
    
    
    
    

    
    



    
    


    
    

    

    
    
    

    