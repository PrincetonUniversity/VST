(** * Injections on X86 cores*)

Require Import VST.sepcomp.semantics.
Require Import VST.concurrency.common.core_semantics.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.

Require Import compcert.lib.Coqlib.
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
Require Import VST.concurrency.common.addressFiniteMap.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.
Require Import VST.concurrency.sc_drf.mem_obs_eq.
Require Import VST.concurrency.memory_lemmas.
Require Import compcert.x86.Asm.
Require Import VST.concurrency.common.Asm_core VST.concurrency.common.Asm_event.
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.common.core_semantics.

Import ValObsEq Renamings MemObsEq event_semantics.

Set Bullet Behavior "Strict Subproofs".

(** ** Well defined X86 cores *)
Module X86WD.
  Import MemoryWD Genv ValueWD.
  Section X86WD.
    Variable f: memren.

    Definition regset_wd rs : Prop :=
      forall r, valid_val f (Pregmap.get r rs).

    Definition core_wd c : Prop :=
      match c with State rs _ => regset_wd rs end.

    Definition ge_wd (the_ge: genv) : Prop :=
      (forall b, Maps.PTree.get b (genv_defs the_ge) ->
            f b) /\
      (forall id ofs v, Senv.symbol_address the_ge id ofs = v ->
                   valid_val f v).

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

  Lemma core_wd_incr :
    forall f1 f2 rs
      (Hwd: core_wd f1 rs)
      (Hincr: ren_domain_incr f1 f2),
      core_wd f2 rs.
  Proof.
    destruct rs; intros; eapply regset_wd_incr; eauto.
  Qed.

  Lemma regset_wd_set:
    forall f rs r v
      (H: valid_val f v)
      (Hrs: regset_wd f rs),
      regset_wd f (rs # r <- v).
  Proof.
    intros.
    intro r'.
    rewrite Pregmap.gsspec.
    destruct (Pregmap.elt_eq r' r); subst; auto.
  Qed.

  Lemma regset_wd_set_res:
    forall f br rs v
      (H: valid_val f v)
      (Hrs: regset_wd f rs),
      regset_wd f (set_res br v rs).
  Proof.
    induction br; auto; simpl; intros.
    - apply regset_wd_set; auto.
    - apply IHbr2, IHbr1; auto with wd.
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

  Lemma core_wd_domain :
    forall f1 f2 m rs
      (Hwd: core_wd f1 rs)
      (Hdomain1: domain_memren f1 m)
      (Hdomain2: domain_memren f2 m),
      core_wd f2 rs.
  Proof.
    destruct rs; intros; eapply regset_wd_domain, Hwd; eauto.
  Qed.

  Lemma longofwords_valid_val:
    forall f v1 v2,
      valid_val f v1 -> valid_val f v2 ->
      valid_val f (Val.longofwords v1 v2).
  Proof.
    intros.
    unfold Val.longofwords.
    destruct v1; try constructor.
    destruct v2; constructor.
  Qed.

(*
  Lemma decode_longs_valid_val:
    forall f vals tys,
      valid_val_list f vals ->
      valid_val_list f (val_casted.decode_longs tys vals).
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
    inv H3.
    constructor; auto.
    apply longofwords_valid_val; auto.
  Qed.
*)

  Hint Extern 1 (valid_val _ (@Pregmap.set _ _ _ _ _)) => eapply regset_wd_set : wd.
  Hint Resolve regset_wd_set regset_wd_set_res : wd.

  (*NOTE: Do i use that?*)
  Lemma valid_val_reg_set:
    forall f rs r r' v,
      valid_val f v ->
      regset_wd f rs ->
      valid_val f (rs # r <- v r').
  Proof.
    intros.
    eauto with wd.
  Qed.

  Lemma regset_comm:
    forall (rs: Pregmap.t val) r r' v,
      (rs # r <- v) # r' <- v = (rs # r' <- v) # r <- v.
  Proof.
    intros.
    unfold Pregmap.set.
    extensionality r''.
    destruct (PregEq.eq r'' r'), (PregEq.eq r'' r); auto.
  Qed.

  Lemma undef_regs_comm:
    forall regs rs r,
      undef_regs regs (rs # r <- Vundef) =
      (undef_regs regs rs) # r <- Vundef.
  Proof.
    intros.
    generalize dependent rs.
    induction regs; intros. simpl. auto.
    simpl.
    specialize (IHregs (rs # a <- Vundef)).
    rewrite <- IHregs.
    apply f_equal.
      by rewrite regset_comm.
  Qed.

  Lemma regset_wd_undef:
    forall f rs regs
      (Hrs_wd: regset_wd f rs),
      regset_wd f (undef_regs regs rs).
  Proof with eauto with wd.
    intros.
    induction regs as [|r regs]; simpl; auto.
    intros r'.
    rewrite undef_regs_comm;
      rewrite Pregmap.gsspec;
      unfold Pregmap.get;
      destruct (Pregmap.elt_eq r' r); simpl...
  Qed.

  Hint Extern 0 (valid_val _ (undef_regs _ _ # _ <- _ _)) => eapply regset_wd_set : wd.

  Hint Resolve regset_wd_domain
       valid_val_list_incr valid_val_domain
       valid_val_list_domain regset_wd_undef : wd.

  Lemma valid_symb:
    forall f fg g id i
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_domain_incr fg f),
      valid_val f (symbol_address g id i).
  Proof with eauto with wd.
    intros.
    destruct Hge_wd as (H1 & H2).
    unfold symbol_address, Senv.symbol_address in *;
      simpl in *.
    specialize (H2 id i _ ltac:(reflexivity)).
    destruct (find_symbol g id); auto.
    eapply valid_val_incr; eauto.
  Qed.

  Hint Resolve valid_symb : wd.

  Lemma valid_val_cmpu:
    forall f ptr c v1 v2,
      valid_val f (Val.cmpu ptr c v1 v2).
  Proof with eauto with wd.
    intros.
    destruct v1,v2; simpl; auto;
    unfold Val.cmpu, Val.cmpu_bool...
  Qed.

  Hint Immediate valid_val_cmpu :wd.

  Lemma valid_val_cmplu:
    forall f ptr c v1 v2,
      valid_val f (Val.maketotal (Val.cmplu ptr c v1 v2)).
  Proof with eauto with wd.
    intros.
    destruct v1,v2; simpl; auto;
    unfold Val.cmpu, Val.cmpu_bool...
  Qed.

  Hint Immediate valid_val_cmplu :wd.

  Lemma valid_val_addrmode64:
    forall ge rs f fg a,
      ren_domain_incr fg f ->
      ge_wd fg ge ->
      regset_wd f rs ->
      valid_val f (eval_addrmode64 ge a rs).
  Proof.
    intros.
    unfold eval_addrmode64.
    destruct a.
    apply valid_val_addl.
    destruct base; eauto with wd.
    apply valid_val_addl.
    destruct ofs; eauto with wd.
    destruct p. destruct (zeq z 1);
      eauto with wd.
    destruct const; simpl; auto.
    destruct p.
    destruct H0.
    specialize (H2 i i0 _ ltac:(reflexivity)).
    unfold symbol_address, Senv.symbol_address in *. simpl in *.
    eapply valid_val_incr; eauto.
  Qed.

  Lemma valid_val_addrmode:
    forall ge rs f fg a,
      ren_domain_incr fg f ->
      ge_wd fg ge ->
      regset_wd f rs ->
      valid_val f (eval_addrmode ge a rs).
  Proof.
    intros.
    unfold eval_addrmode.
    destruct a.
    apply valid_val_add.
    destruct base; eauto with wd.
    apply valid_val_add.
    destruct ofs; eauto with wd.
    destruct p. destruct (zeq z 1);
      eauto with wd.
    destruct const; simpl; auto.
    destruct p.
    destruct H0.
    specialize (H2 i i0 _ ltac:(reflexivity)).
    unfold symbol_address, Senv.symbol_address in *. simpl in *.
    eapply valid_val_incr; eauto.
  Qed.

  Lemma valid_val_compare_ints:
    forall f rs m v1 v2 r,
      regset_wd f rs ->
      valid_val f (compare_ints v1 v2 rs m r).
  Proof with eauto 10 with wd.
    intros.
    unfold compare_ints...
  Qed.

  Hint Resolve valid_val_compare_ints : wd.

  Lemma valid_val_compare_longs:
    forall f rs m v1 v2 r,
      regset_wd f rs ->
      valid_val f (compare_longs v1 v2 rs m r).
  Proof with eauto 10 with wd.
    intros.
    unfold compare_longs...
  Qed.

  Hint Resolve valid_val_compare_longs : wd.

  Lemma regset_wd_compare_ints:
    forall f rs m v1 v2,
      regset_wd f rs ->
      regset_wd f (compare_ints v1 v2 rs m).
  Proof with eauto with wd.
    intros.
    intro r.
    unfold Pregmap.get...
  Qed.

  Lemma regset_wd_compare_longs:
    forall f rs m v1 v2,
      regset_wd f rs ->
      regset_wd f (compare_longs v1 v2 rs m).
  Proof with eauto with wd.
    intros.
    intro r.
    unfold Pregmap.get...
  Qed.

  Lemma valid_val_compare_floats:
    forall f rs v1 v2 r,
      regset_wd f rs ->
      valid_val f (compare_floats v1 v2 rs r).
  Proof with eauto 10 with wd.
    intros.
    unfold compare_floats.
    destruct v1; try (apply regset_wd_undef; eauto with wd).
    destruct v2;
      try (apply regset_wd_undef; eauto with wd).

    eauto 8 with wd.
  Qed.

  Hint Resolve valid_val_compare_floats : wd.

  Lemma regset_wd_compare_floats:
    forall f rs v1 v2,
      regset_wd f rs ->
      regset_wd f (compare_floats v1 v2 rs).
  Proof with eauto with wd.
    intros.
    intro r.
    unfold Pregmap.get...
  Qed.

  Lemma valid_val_compare_floats32:
    forall f rs v1 v2 r,
      regset_wd f rs ->
      valid_val f (compare_floats32 v1 v2 rs r).
  Proof with eauto 10 with wd.
    intros.
    unfold compare_floats32.
    destruct v1; try (apply regset_wd_undef; eauto with wd).
    destruct v2;
      try (apply regset_wd_undef; eauto with wd)...
  Qed.

  Hint Resolve valid_val_compare_floats32 : wd.

  Lemma regset_wd_compare_floats32:
    forall f rs v1 v2,
      regset_wd f rs ->
      regset_wd f (compare_floats32 v1 v2 rs).
  Proof with eauto with wd.
    intros; intro r; unfold Pregmap.get...
  Qed.


  Hint Resolve valid_val_addrmode valid_val_addrmode64
       regset_wd_compare_floats regset_wd_compare_floats32
       regset_wd_compare_ints regset_wd_compare_longs : wd.

End X86WD.

(** ** Injections/Renamings on X86 cores *)

Module X86Inj.

  Import CoreInjections.

(** Injections on registers *)

  Definition reg_ren f (r:PregEq.t) (rs rs' : regset) : Prop :=
    val_obs f (Pregmap.get r rs) (Pregmap.get r rs').

  Definition regset_ren f rs rs' : Prop :=
    forall r, reg_ren f r rs rs'.

  Definition core_inj f c c' :=
    match c, c' with State rs _, State rs' _ => regset_ren f rs rs' end.

  Import ValueWD MemoryWD Genv.
  Include X86WD.

(*
  Lemma decode_longs_val_obs_list:
    forall f (vals vals' : seq val) tys
      (Hobs_eq: val_obs_list f vals vals'),
      val_obs_list f (val_casted.decode_longs tys vals)
                   (val_casted.decode_longs tys vals').
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
*)

  (*
  Lemma set_res_empty_1:
    forall regs rs,
      set_res regs [::] rs = rs.
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
  Qed. *)

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

  Lemma regset_ren_incr:
    forall f f' rs rs'
      (Hrs_ren: regset_ren f rs rs')
      (Hincr: ren_incr f f'),
      regset_ren f' rs rs'.
  Proof with eauto with val_renamings.
    unfold regset_ren, reg_ren in *...
  Qed.

  Lemma regset_ren_set:
    forall f rs rs' v v' r
      (Hrs_ren: regset_ren f rs rs')
      (Hval_obs: val_obs f v v'),
      regset_ren f (rs # r <- v) (rs' # r <- v').
  Proof.
    intros.
    intros r'.
    unfold reg_ren.
    do 2 rewrite Pregmap.gsspec.
    destruct (Pregmap.elt_eq r' r); auto.
    eapply Hrs_ren.
  Qed.

  Lemma regset_ren_init:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      regset_ren f (Pregmap.init v) (Pregmap.init v').
  Proof.
    intros.
    intro r.
    unfold reg_ren.
    unfold Pregmap.init, Pregmap.get;
      auto.
  Qed.

  Lemma regset_ren_set_res:
    forall f br rs rs' v v'
      (Hrs_ren: regset_ren f rs rs')
      (Hval_obs: val_obs f v v'),
      regset_ren f (set_res br v rs) (set_res br v' rs').
  Proof.
    induction br; auto; simpl; intros.
    - apply regset_ren_set; auto.
    - apply IHbr2, val_obs_loword; auto.
      apply IHbr1, val_obs_hiword; auto.
  Qed.

  Lemma gso_undef_regs:
    forall (rs : regset) r regs,
      ~ List.In r regs ->
      (undef_regs regs rs) r = rs r.
  Proof.
    intros.
    induction regs; simpl; auto.
    simpl in H.
    rewrite undef_regs_comm.
    assert (H1: ~ List.In r regs)
      by (intros Hcontra; auto).
    rewrite Pregmap.gso; eauto.
  Qed.

  Lemma valid_val_ge_id:
    forall fg f b i
      (Hvalid: valid_val fg (Vptr b i))
      (Hincr: ren_incr fg f)
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2),
      f b = Some b.
  Proof.
    intros.
    destruct Hvalid as [b' Hfg'].
    assert (Heq := Hfg _ _ Hfg'); subst.
    apply Hincr in Hfg';
      by auto.
  Qed.

  Hint Resolve
       val_obs_reg regset_ren_set regset_ren_set_res : reg_renamings.
  Hint Rewrite gso_undef_regs : reg_renamings.

  Hint Resolve valid_val_ge_id  : ge_renamings.
  Hint Constructors eval_builtin_arg : renamings.
  Hint Unfold Vone Vzero nextinstr nextinstr_nf : renamings.

  Lemma val_obs_symb:
    forall f fg g id i
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2),
      val_obs f (symbol_address g id i) (symbol_address g id i).
  Proof with eauto with ge_renamings renamings val_renamings.
    intros.
    destruct Hge_wd as (H1 & H2).
    unfold symbol_address, Senv.symbol_address in *;
      simpl in *.
    specialize (H2 id i _ ltac:(reflexivity)).
    destruct (find_symbol g id)...
  Qed.

  Hint Resolve val_obs_symb : ge_renamings.

  Lemma regset_ren_undef:
    forall f rs rs' regs
      (Hrs_ren: regset_ren f rs rs'),
      regset_ren f (undef_regs regs rs) (undef_regs regs rs').
  Proof with eauto with renamings reg_renamings val_renamings.
    intros.
    induction regs as [|r regs]; simpl; auto.
    intros r'. unfold reg_ren.
    do 2 rewrite undef_regs_comm;
      do 2 rewrite Pregmap.gsspec;
      unfold Pregmap.get;
      destruct (Pregmap.elt_eq r' r)...
  Qed.

  Hint Resolve regset_ren_undef : reg_renamings.

  Lemma ge_wd_incr :
    forall (f f' : memren) (g : genv),
      ge_wd f g -> ren_domain_incr f f' -> ge_wd f' g.
  Proof with (eauto with renamings val_renamings).
    intros.
    unfold ge_wd in *.
    destruct H as (? & ?);
      repeat split;
      intros...
  Qed.

  Lemma ge_wd_domain :
    forall (f f' : memren) (m : mem) (g : genv),
      ge_wd f g -> domain_memren f m -> domain_memren f' m -> ge_wd f' g.
  Proof.
    intros.
    unfold ge_wd in *.
    unfold domain_memren in *.
    destruct H as (Hf & Hv);
      repeat split;
      intros;
      try destruct (H0 b), (H1 b);
      try specialize (Hf _ ltac:(eauto));
      try specialize (Hv _ ltac:(eauto));
      try specialize (Hs id ofs v ltac:(eauto));
      eauto.
    eapply valid_val_domain; eauto.
  Qed.

  Lemma get_extcall_arg_wd : forall f rs m l v
    (Hm : valid_mem m)
    (Hdom : domain_memren f m)
    (Hrs : regset_wd f rs)
    (Hv : get_extcall_arg rs m l = Some v),
    valid_val f v.
  Proof.
    destruct l; unfold get_extcall_arg; intros.
    - inv Hv.
      apply Hrs.
    - destruct sl; try discriminate.
      eapply loadv_wd in Hv; eauto.
  Qed.

  Lemma get_extcall_arguments_wd : forall f rs m l v
    (Hm : valid_mem m)
    (Hdom : domain_memren f m)
    (Hrs : regset_wd f rs)
    (Hv : get_extcall_arguments rs m l = Some v),
    valid_val_list f v.
  Proof.
    induction l; simpl; intros.
    - inv Hv; constructor.
    - destruct a.
      + destruct (get_extcall_arg _ _ _) eqn: Harg; inv Hv.
        destruct (get_extcall_arguments _ _ _); inv H0.
        constructor; [eapply get_extcall_arg_wd|]; eauto.
      + destruct (get_extcall_arg _ _ _) eqn: Harg1; inv Hv.
        destruct (get_extcall_arg _ _ rlo) eqn: Harg2; inv H0.
        destruct (get_extcall_arguments _ _ _); inv H1.
        constructor; auto.
        apply longofwords_valid_val; eapply get_extcall_arg_wd; eauto.
  Qed.

  Lemma at_external_wd :
    forall the_ge m (f : memren) c
      (ef : external_function)
      (args : seq val),
      valid_mem m ->
      domain_memren f m ->
      core_wd f c ->
      semantics.at_external (Asm_core_sem the_ge) c m = Some (ef, args) -> valid_val_list f args.
  Proof.
    intros.
    destruct c; simpl in *.
    pose proof (H1 PC) as HPC.
    unfold Pregmap.get in HPC.
    destruct r; try discriminate.
    destruct (Ptrofs.eq_dec _ _); try discriminate.
    destruct (find_funct_ptr _ _); try discriminate.
    destruct f0; try discriminate.
    destruct (get_extcall_arguments _ _ _) eqn: Hargs; inv H2.
    eapply get_extcall_arguments_wd; eauto.
  Qed.

  Lemma valid_val_hiword:
    forall f v,
      valid_val f v ->
      valid_val f (Val.hiword v).
  Proof.
    intros.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_loword:
    forall f v,
      valid_val f v ->
      valid_val f (Val.loword v).
  Proof.
    intros.
    destruct v; simpl; auto.
  Qed.

  Hint Resolve valid_val_loword valid_val_loword : wd.

  Lemma after_external_wd :
    forall the_ge m (c c' : state) (f : memren) (ef : external_function)
      (args : seq val) (ov : option val)
      (Hat_external: semantics.at_external (Asm_core_sem the_ge) c m = Some (ef, args))
      (Hcore_wd: core_wd f c)
      (Hvalid_list: valid_val_list f args)
      (Hafter_external: semantics.after_external (Asm_core_sem the_ge) ov c m = Some c')
      (Hov: match ov with
            | Some v => valid_val f v
            | None => True
            end),
      core_wd f c'.
  Proof.
    intros.
    destruct c, c'; simpl in *.
    unfold after_external_regset in *.
    destruct r eqn: HPC; try discriminate.
    destruct (Ptrofs.eq_dec _ _); try discriminate.
    destruct (find_funct_ptr _ _) eqn: Hfind; try discriminate.
    destruct f0; try discriminate.
    simpl in *.
    destruct (get_extcall_arguments _ _ _) eqn: Hargs; inv Hat_external.
    destruct ov; inversion Hafter_external; subst.
    - intros r1.
      unfold regset_wd, Pregmap.get in Hcore_wd.
      assert (Hr := Hcore_wd r1).
      rewrite Pregmap.gsspec.
      destruct (Pregmap.elt_eq r1 PC); subst;
      simpl; first by auto.
      (* it's easier to do the case analysis than try to write a lemma
    for set_regs (are the registers unique and more similar problems)*)
      destruct (loc_external_result (ef_sig ef)) as [|r' regs];
      simpl;
      eapply valid_val_reg_set; eauto.
      eapply valid_val_loword; auto.
      eapply regset_wd_set; eauto.
      eapply valid_val_hiword; auto.
    - repeat (eapply regset_wd_set; eauto).
  Qed.

  Lemma valid_val_nullptr : forall f, valid_val f Vnullptr.
  Proof.
    unfold valid_val, Vnullptr; intro.
    destruct Archi.ptr64; auto.
  Qed.

  Lemma make_arg_wd:
    forall f rs rs' m m' loc arg
      (Hrs_wd: regset_wd f rs)
      (Hmem_wd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Hvalid_val: valid_val f arg)
      (Hmake_args: make_arg rs m loc arg = Some (rs', m')),
      regset_wd f rs' /\ valid_mem m' /\ domain_memren f m'.
  Proof.
    intros.
    unfold make_arg in Hmake_args.
    destruct loc. inv Hmake_args.
    split; auto.
    apply regset_wd_set; now auto.
    destruct ( Mem.storev (chunk_of_type ty) m
                          (Val.offset_ptr (rs RSP) (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos)))
                          arg) eqn:Hstore; try discriminate.
    inv Hmake_args; eauto.
    split; auto.
    eapply storev_wd_domain; eauto.
    unfold mem_wd.val_valid. unfold valid_val in Hvalid_val.
    destruct arg; auto.
    eapply Hdomain.
    destruct Hvalid_val as [? Hvalid_val]; rewrite Hvalid_val;
      now auto.
  Qed.
  
  Lemma make_arguments_wd:
    forall f rs rs' m m' loc args
      (Hrs_wd: regset_wd f rs)
      (Hmem_wd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Hvalid_val: valid_val_list f args)
      (Hmake_args: make_arguments rs m loc args = Some (rs', m')),
      regset_wd f rs' /\ valid_mem m' /\ domain_memren f m'.
  Proof.
    intros f rs rs' m m' loc.
    generalize dependent m'.
    generalize dependent rs'.
    induction loc; intros.
    - destruct args; simpl in Hmake_args.
      inversion Hmake_args; subst; auto.
      discriminate.
    - destruct args;
        simpl in Hmake_args.
      discriminate.
      destruct (make_arguments rs m loc args) eqn:Hmake_args0; try discriminate.
      destruct p as [rs0 m0].
      inversion Hvalid_val; subst.
      specialize (IHloc _ _ _ Hrs_wd Hmem_wd Hdomain H2 Hmake_args0).
      destruct IHloc as [Hrs_wd0 [Hmem_wd0 Hdomain0]].
      destruct a. 
      + eapply make_arg_wd in Hmake_args;
          now eauto.
      + destruct (make_arg rs0 m0 rhi (Val.hiword v)) eqn:Hmake_hi; try discriminate.
        destruct p as [r1 m1].
        eapply make_arg_wd in Hmake_hi; eauto with wd.
        destruct Hmake_hi as [? [? ?]].
        eapply make_arg_wd in Hmake_args;
          now eauto with wd.
  Qed.

  Lemma mem_valid_alloc:
    forall m m' b lo hi f
      (Hdomain: domain_memren f m)
      (Hvalid_mem: valid_mem m)
      (Halloc: Mem.alloc m lo hi = (m', b)),
      valid_mem m' /\
      (exists f', ren_domain_incr f f' /\ domain_memren f' m').
  Proof.
    intros.
    split.
    - unfold valid_mem.
      intros b0 Hvalid0 ofs mv Hget.
      pose proof (Mem.valid_block_alloc_inv _ _ _ _ _ Halloc _ Hvalid0) as H.
      destruct H.
      + subst.
        erewrite MemoryLemmas.val_at_alloc_2; eauto.
      + unfold valid_mem in Hvalid_mem.
        specialize (Hvalid_mem _ H ofs _ ltac:(reflexivity)).
        erewrite MemoryLemmas.val_at_alloc_1 in Hvalid_mem; eauto.
        rewrite Hget in Hvalid_mem.
        destruct mv; auto.
        destruct v; auto.
        simpl in *.
        eapply Mem.valid_block_alloc; eauto.
    - exists (fun b0 => if valid_block_dec m b0 then f b0 else
                  if valid_block_dec m' b0 then Some b else None).
      split.
      + unfold ren_domain_incr.
        intros b0 Hf.
        destruct (valid_block_dec m b0); simpl; auto.
        destruct (valid_block_dec m' b0); simpl; auto.
        erewrite <- (Hdomain b0) in Hf.
          by exfalso.
      + unfold domain_memren.
        intros b0. split; intros.
        * eapply Mem.valid_block_alloc_inv in H; eauto.
          destruct H.
          subst.
          assert (Hinvalid := Mem.fresh_block_alloc _ _ _ _ _ Halloc).
          assert (Hvalid := Mem.valid_new_block _ _ _ _ _ Halloc).
          destruct (valid_block_dec m b); simpl; auto.
          destruct (valid_block_dec m' b); simpl;
            by auto.
          destruct (valid_block_dec m b0); simpl; auto.
          eapply Hdomain; auto.
        * destruct (valid_block_dec m b0);
            simpl in H.
          eapply Mem.valid_block_alloc; eauto.
          destruct (valid_block_dec m' b0); simpl in H; auto.
            by exfalso.
  Qed.

  Lemma initial_core_wd :
    forall the_ge m m' (f fg : memren) (vf : val) args (c_new : state) h,
      valid_mem m ->
      domain_memren f m ->
      initial_core (Asm_core_sem the_ge) h m c_new m' vf args ->
      valid_val_list f args -> ge_wd fg the_ge ->
      ren_domain_incr fg f ->
      valid_mem m' /\
      (exists f', ren_domain_incr f f' /\ domain_memren f' m') /\
      forall f', domain_memren f' m' ->
            core_wd f' c_new.
  Proof.
    intros.
    simpl in *.
    destruct H1 as [H1 ?].
    subst; simpl.
    inv H1.
    simpl.
    assert (Hstk: Mem.valid_block m1 stk)
      by (eapply Mem.valid_new_block; eauto).
    eapply mem_valid_alloc in H6; eauto.
    destruct H6 as [Hvalid_m1 Hf'].
    destruct Hf' as [f' [Hincr' Hren']].
    eapply storev_wd_domain in H7; eauto.
    destruct H7 as [Hvalid_m2 Hmemren2].
    eapply storev_wd_domain in H8; eauto.
    destruct H8 as [Hvalid_m3 Hmemren3].
    eapply make_arguments_wd in H9; eauto.
    destruct H9 as [? [? ?]].
    split; auto.
    split.
    eexists; eauto.
    intros.
    eapply X86WD.regset_wd_domain with (f1 := f'); eauto.
    subst rs0.
    apply regset_wd_set.
    subst sp.
    simpl.
    eapply Hren' in Hstk.
    destruct (f' stk); [eexists; eauto | by exfalso].
    apply regset_wd_set.
    unfold Vnullptr.
    destruct Archi.ptr64; simpl; auto.
    apply regset_wd_set.
    unfold find_funct_ptr in H5.
    unfold find_def in H5.
    destruct (Maps.PTree.get b (genv_defs the_ge)) eqn:Hget; try discriminate.
    destruct g; try discriminate.
    destruct H3 as [Hge_wd _].
    specialize (Hge_wd b ltac:(rewrite Hget; auto)).
    simpl.
    eapply H4 in Hge_wd.
    eapply Hincr' in Hge_wd.
    destruct (f' b); [eexists; eauto| by exfalso].
    unfold Pregmap.init.
    intros r; simpl; auto.
    eapply valid_val_list_incr; eauto.
    all:unfold Vnullptr; destruct (Archi.ptr64); simpl;
      now auto.
  Qed.

  Lemma get_extcall_arg_inj : forall f rs rs' m m' l v,
    regset_ren f rs rs' -> mem_obs_eq f m m' ->
    get_extcall_arg rs m l = Some v ->
    exists v', get_extcall_arg rs' m' l = Some v' /\ val_obs f v v'.
  Proof.
    destruct l; simpl; intros.
    - inv H1.
      eexists; split; eauto.
      apply val_obs_reg; auto.
    - destruct sl; inv H1.
      edestruct loadv_val_obs; eauto; try apply H0.
      specialize (H RSP); hnf in H.
      unfold Pregmap.get in H.
      destruct rs; inv H; constructor; auto.
  Qed.

  Lemma get_extcall_arguments_inj : forall f rs rs' m m' l v,
    regset_ren f rs rs' -> mem_obs_eq f m m' ->
    get_extcall_arguments rs m l = Some v ->
    exists v', get_extcall_arguments rs' m' l = Some v' /\ val_obs_list f v v'.
  Proof.
    induction l; simpl; intros.
    { inv H1; exists nil; split; auto; constructor. }
    destruct a.
    - destruct (get_extcall_arg rs m r) eqn: Hget; try discriminate.
      eapply get_extcall_arg_inj in Hget as (? & -> & ?); eauto.
      destruct (get_extcall_arguments rs m l) eqn: Hargs; inv H1.
      destruct (IHl l0) as (? & -> & ?); auto.
      eexists; split; eauto; constructor; auto.
    - destruct (get_extcall_arg rs m rhi) eqn: Hget; try discriminate.
      eapply get_extcall_arg_inj in Hget as (? & -> & ?); eauto.
      destruct (get_extcall_arg rs m rlo) eqn: Hget; try discriminate.
      eapply get_extcall_arg_inj in Hget as (? & -> & ?); eauto.
      destruct (get_extcall_arguments rs m l) eqn: Hargs; inv H1.
      destruct (IHl l0) as (? & -> & ?); auto.
      eexists; split; eauto; constructor; auto.
      apply val_obs_longofwords; auto.
  Qed.

  Lemma get_extcall_arg_inj' : forall f rs rs' m m' l,
    regset_ren f rs rs' -> mem_obs_eq f m m' ->
    get_extcall_arg rs m l = None ->
    get_extcall_arg rs' m' l = None.
  Proof.
    destruct l; simpl; intros.
    - discriminate.
    - destruct sl; auto.
      eapply loadv_None_obs; eauto; try apply H0.
      specialize (H RSP); hnf in H.
      unfold Pregmap.get in H.
      destruct rs; inv H; constructor; auto.
  Qed.

  Lemma get_extcall_arguments_inj' : forall f rs rs' m m' l,
    regset_ren f rs rs' -> mem_obs_eq f m m' ->
    get_extcall_arguments rs m l = None ->
    get_extcall_arguments rs' m' l = None.
  Proof.
    induction l; simpl; intros.
    { inv H1; exists nil; split; auto; constructor. }
    destruct a.
    - destruct (get_extcall_arg rs m r) eqn: Hget;
        [|eapply get_extcall_arg_inj' in Hget as ->; eauto].
      destruct (get_extcall_arguments rs m l) eqn: Hargs; inv H1.
      rewrite IHl; auto.
      destruct (get_extcall_arg rs' m' r); auto.
    - destruct (get_extcall_arg rs m rhi) eqn: Hget;
        [|eapply get_extcall_arg_inj' in Hget as ->; eauto].
      destruct (get_extcall_arg rs' m' rhi); auto.
      clear Hget; destruct (get_extcall_arg rs m rlo) eqn: Hget;
        [|eapply get_extcall_arg_inj' in Hget as ->; eauto].
      destruct (get_extcall_arg rs' m' rlo); auto.
      destruct (get_extcall_arguments rs m l) eqn: Hargs; inv H1.
      rewrite IHl; auto.
  Qed.

  Lemma find_funct_ptr_inj : forall g (f fg : memren) b b' h
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f),
    find_funct_ptr g b = Some h -> f b = Some b' -> b' = b.
  Proof.
    intros.
    destruct Hge_wd as [Hge_wd _].
    specialize (Hge_wd b).
    unfold find_funct_ptr, find_def in *.
    destruct (Maps.PTree.get _ _) eqn: Hget; [|discriminate].
    lapply Hge_wd; auto.
    destruct (fg b) eqn: Hb; [|discriminate].
    rewrite (Hincr _ _ Hb) in H0; inv H0.
    specialize (Hfg _ _ Hb); auto.
  Qed.

  Lemma find_funct_ptr_inj' : forall g (f fg : memren) m m' b b' h
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Hmem : mem_obs_eq f m m'),
    find_funct_ptr g b' = Some h -> f b = Some b' -> b' = b.
  Proof.
    intros.
    destruct Hge_wd as [Hge_wd _].
    specialize (Hge_wd b').
    unfold find_funct_ptr, find_def in *.
    destruct (Maps.PTree.get _ _) eqn: Hget; [|discriminate].
    lapply Hge_wd; auto.
    destruct (fg b') eqn: Hb; [|discriminate].
    pose proof (Hincr _ _ Hb).
    specialize (Hfg _ _ Hb); subst.
    intro; eapply Hmem; eauto.
  Qed.

  Lemma core_inj_ext :
    forall the_ge m m' c c' (f fg : memren)
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hincr: ren_incr fg f)
      (Hc : core_wd f c)
      (Hinj : core_inj f c c')
      (Hmem : mem_obs_eq f m m'),
      match semantics.at_external (Asm_core_sem the_ge) c m with
      | Some (ef, vs) =>
        match semantics.at_external (Asm_core_sem the_ge) c' m' with
        | Some (ef', vs') =>
          ef = ef' /\ val_obs_list f vs vs'
        | None => False
        end
      | None =>
        match semantics.at_external (Asm_core_sem the_ge) c' m' with
        | Some _ => False
        | None => True
        end
      end.
  Proof.
    intros.
    destruct c, c'; simpl in *.
    pose proof (Hinj PC) as HPC; unfold reg_ren, Pregmap.get in HPC.
    destruct r, r0; try discriminate; inv HPC; auto.
    destruct (Ptrofs.eq_dec _ _); auto.
    destruct (find_funct_ptr the_ge b) eqn: Hfind.
    - exploit find_funct_ptr_inj; eauto; intro; subst.
      rewrite Hfind.
      destruct f0; auto.
      destruct (get_extcall_arguments _ _ _) eqn: Hargs.
      + eapply get_extcall_arguments_inj in Hargs as (? & -> & ?); eauto.
      + erewrite get_extcall_arguments_inj'; eauto.
    - destruct (find_funct_ptr the_ge b0) eqn: Hfind'; auto.
      exploit find_funct_ptr_inj'; eauto; intro; subst.
      congruence.
  Qed.

  Lemma core_inj_after_ext :
    forall the_ge c cc c' (ov1 : option val) m m'
      (f fg : memren)
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hincr: ren_incr fg f),
      core_inj f c c' ->
      mem_obs_eq f m m' ->
      match ov1 with
      | Some v1 => valid_val f v1
      | None => True
      end ->
      semantics.after_external (Asm_core_sem the_ge) ov1 c m = Some cc ->
      exists (ov2 : option val) (cc' : state),
        semantics.after_external (Asm_core_sem the_ge) ov2 c' m' = Some cc' /\
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
    intros the_ge c cc c' ov1 ??????? Hinj Hmem Hov1 Hafter_external.
    destruct c, c'; simpl in *.
    unfold after_external_regset in *.
    pose proof (Hinj PC) as HPC.
    unfold reg_ren, Pregmap.get in HPC.
    destruct r; try discriminate.
    inv HPC.
    destruct (Ptrofs.eq_dec _ _); try discriminate.
    destruct (find_funct_ptr _ _) eqn: Hfind; try discriminate.
    exploit find_funct_ptr_inj; eauto; intro; subst.
    rewrite Hfind.
    destruct f0; try discriminate.
    assert (Hov:
              forall v v',
                val_obs f v v' ->
                regset_ren f
                           ((set_pair (loc_external_result (ef_sig e)) v r)
                           # PC <- (r RA))
                           ((set_pair (loc_external_result (ef_sig e)) v' r0)
                              # PC <- (r0 RA))).
    { intros.
      intros r1.
      unfold regset_ren, reg_ren in *.
      do 2 rewrite Pregmap.gsspec.
      destruct (Pregmap.elt_eq r1 PC); subst;
      simpl;
      first by eauto.
      destruct (loc_external_result (ef_sig e)) as [|r' regs]; simpl;
      repeat (eapply regset_ren_set; eauto with val_renamings).
    }
    destruct ov1 as [v1 |];
      inversion Hafter_external; subst.
    exists (Some (val_obsC f v1)).
    eexists; split; eauto.
    simpl.
    split.
    eapply Hov.
    all: try (eapply val_obsC_correct; eauto).
    exists None.
    eexists; split; eauto.
    simpl.
    split; auto.
    apply regset_ren_set; auto.
    apply Hinj.
  Qed.

  Lemma core_inj_halted :
    forall the_ge c c' (f : memren),
      core_inj f c c' -> forall v,
      halted (Asm_core_sem the_ge) c v <-> halted (Asm_core_sem the_ge) c' v.
  Proof.
    intros.
    simpl.
    destruct c, c'; simpl in *.
    pose proof (H PC) as HPC; pose proof (H RAX) as HRAX.
    unfold reg_ren, Pregmap.get in *.
    split; intro Hfinal; inv Hfinal.
    - erewrite H2, H4 in *.
      inv HPC; inv HRAX.
      constructor; auto.
    - erewrite H2, H4 in *.
      inv HRAX.
      constructor; auto.
      unfold Vnullptr in *.
      destruct Archi.ptr64; inv HPC; auto.
  Qed.

  Lemma val_obs_inj : forall f v v1 v2, val_obs f v v1 -> val_obs f v v2 -> v1 = v2.
  Proof.
    intros; inv H; inv H0; auto.
    congruence.
  Qed.

  Lemma val_obs_list_inj : forall f v v1 v2, val_obs_list f v v1 -> val_obs_list f v v2 -> v1 = v2.
  Proof.
    intros; revert dependent v2; induction H; inversion 1; auto; subst.
    f_equal; auto.
    eapply val_obs_inj; eauto.
  Qed.

  Lemma make_arg_inj:
    forall (f : memren) (rs rs1 rs' : regset) (m m1 m' : mem) l
      (arg arg' : val)
      (Hrs: regset_ren f rs rs')
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hval_obs_list: val_obs f arg arg')
      (Hmake: make_arg rs m l arg = Some (rs1, m1)),
    exists rs1' m1',
      make_arg rs' m' l arg' = Some (rs1', m1') /\
      regset_ren f rs1 rs1' /\
      mem_obs_eq f m1 m1'.
  Proof.
    intros.
    unfold make_arg in *.
    destruct l.
    + inv Hmake; do 2 eexists; split; now eauto with val_renamings reg_renamings.
    + destruct (Mem.storev (chunk_of_type ty) m
                           (Val.offset_ptr
                              (rs RSP)
                              (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos))) arg) eqn:Hstore; try discriminate.
      inv Hmake.
      eapply storev_val_obs
        with (vptr2 := Val.offset_ptr (rs' RSP) (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos)))
        in Hstore; eauto.
      destruct Hstore as [m1' [Hstore' Hmem_obs_eq1]].
      exists rs', m1'.
      rewrite Hstore'.
      now auto.
      unfold Val.offset_ptr in *.
      destruct (rs1 RSP) eqn:HRSP; simpl in Hstore; try discriminate.
      specialize (Hrs RSP).
      unfold reg_ren in Hrs.
      unfold Pregmap.get in Hrs.
      rewrite HRSP in Hrs.
      inv Hrs.
      econstructor;
        now auto.
  Qed.

  Lemma make_arguments_inj:
    forall (f : memren) (l : seq (rpair Locations.loc)) (rs rs1 rs' : regset) (m m1 m' : mem) 
      (arg arg' : seq val)
      (Hrs: regset_ren f rs rs')
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hval_obs_list: val_obs_list f arg arg')
      (Hmake: make_arguments rs m l arg = Some (rs1, m1)),
    exists rs1' m1',
      make_arguments rs' m' l arg' = Some (rs1', m1') /\
      regset_ren f rs1 rs1' /\
      mem_obs_eq f m1 m1'.
  Proof.
    induction l; intros.
    - simpl in Hmake.
      destruct arg; inv Hmake.
      inv Hval_obs_list.
      do 2 eexists; simpl; now eauto.
    - simpl in Hmake.
      destruct arg; try discriminate.
      destruct (make_arguments rs m l arg) eqn:Hmake_args0; try discriminate.
      destruct p as [rs0 m0].
      inv Hval_obs_list.
      destruct (IHl _ _ _ _ _ _ _ _ Hrs Hmem_obs_eq H3 Hmake_args0)
        as [rs0' [m0' [Hmake_args0' [Hregset_ren0' Hmem_obs_eq0']]]].
      destruct a.
      + eapply make_arg_inj in Hmake; eauto.
        destruct Hmake as [rs1' [m1' [Hmake1' [Hrs1' Hmem1']]]].
        exists rs1', m1'.
        split; eauto.
        simpl.
        rewrite Hmake_args0'.
        assumption.
      + destruct (make_arg rs0 m0 rhi (Val.hiword v)) eqn:Hmake_hi; try discriminate.
        destruct p.
        eapply make_arg_inj with (arg' := Val.hiword v') in Hmake_hi; eauto with val_renamings.
        destruct Hmake_hi as [? [? [? [? ?]]]].
        eapply make_arg_inj with (arg' := Val.loword v') in Hmake; eauto with val_renamings.
        destruct Hmake as [? [? [? [? ?]]]].
        do 2 eexists;
          split; eauto.
        simpl. rewrite Hmake_args0'.
        rewrite H.
        assumption.
  Qed.

  (*TODO: move to memorylemmas*)
  Lemma nextblock_storev :
    forall chunk  (m1 : mem) (vptr v : val) (m2 : mem),
      Mem.storev chunk m1 vptr v = Some m2 ->
      Mem.nextblock m2 = Mem.nextblock m1.
  Proof.
    intros.
    unfold Mem.storev in H.
    destruct vptr; try discriminate.
    erewrite Mem.nextblock_store; eauto.
  Qed.
  
  Lemma core_inj_init :
    forall the_ge m1 m1' m2 vf vf' arg arg' c_new f fg h
      (Hge_wd: ge_wd fg the_ge)
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hincr: ren_incr fg f)
      (Harg: val_obs_list f arg arg')
      (Hvf: val_obs f vf vf')
      (Hmem_obs_eq: mem_obs_eq f m1 m1')
      (Hinit: initial_core (Asm_core_sem the_ge) h m1 c_new m2 vf arg),
    exists c_new' m2' f',
            initial_core (Asm_core_sem the_ge) h m1' c_new' m2' vf' arg'
            /\ core_inj f' c_new c_new'
            /\ mem_obs_eq f' m2 m2'
            /\ ren_incr f f'
            /\ ren_separated f f' m1 m1'
            /\ ((exists p, ((Mem.nextblock m2 = Mem.nextblock m1 + p)%positive /\
                      (Mem.nextblock m2' = Mem.nextblock m1' + p)%positive)))
            /\ (forall b,
                  Mem.valid_block m2' b ->
                  ~ Mem.valid_block m1' b ->
                  let bz := ((Zpos b) - ((Zpos (Mem.nextblock m1')) -
                                         (Zpos (Mem.nextblock m1))))%Z in
                  f' (Z.to_pos bz) = Some b /\
                  f (Z.to_pos bz) = None)
            /\ (Mem.nextblock m1 = Mem.nextblock m1' ->
               (forall b1 b2, f b1 = Some b2 -> b1 = b2) ->
               forall b1 b2, f' b1 = Some b2 -> b1 = b2)
            /\ (forall b2, (~exists b1, f' b1 = Some b2) ->
                     forall ofs, permissions.permission_at m1' b2 ofs Cur =
                            permissions.permission_at m2' b2 ofs Cur).
  Proof.
    intros.
    simpl in Hinit.
    destruct Hinit as [Hinit ?]; subst.
    inv Hinit.
    inv Hvf.
    exploit find_funct_ptr_inj; eauto; intro; subst.
    assert (Hnext23: Mem.nextblock m2 = Mem.nextblock m3)
      by(eapply nextblock_storev in H1; eauto).
    assert (Hnext34: Mem.nextblock m3 = Mem.nextblock m4)
      by (eapply nextblock_storev in H2; eauto).
    assert (Hnext4: Mem.nextblock m4 = Mem.nextblock m).
    { eapply X86SEMAxioms.make_arguments_unchanged_on in H3.
      destruct H3 as [_ [_ Hvalid_eq]].
      unfold Mem.valid_block, Plt in Hvalid_eq.
      destruct (Pos.lt_total (Mem.nextblock m4) (Mem.nextblock m)); auto.
      exfalso.
      pose proof (proj1 (Hvalid_eq (Mem.nextblock m4)) H3).
      zify; omega.
      destruct H3; auto.
      exfalso.
      pose proof (proj2 (Hvalid_eq (Mem.nextblock m)) H3).
      zify; omega.
    }

    remember (Mem.alloc m1' 0 (3 * size_chunk Mptr)) eqn:Halloc'.
    destruct p as [m2' stk'].
    symmetry in Halloc'.
    destruct (alloc_obs_eq Hmem_obs_eq H0 Halloc') as
        (f' & Hf' & Hmem_obs_eq1' & Hincr' & Hsep & Hnextblock & Hinverse & Hid).
    pose (Vptr stk' Ptrofs.zero) as sp'.
    assert (Hval_sp: val_obs f' sp sp')
      by (subst sp sp';
          econstructor; now eauto).
    assert(Hvnull: val_obs f' Vnullptr Vnullptr)
      by (unfold Vnullptr; destruct (Archi.ptr64); econstructor).
    eapply storev_val_obs with (vptr2 := Val.offset_ptr sp' (Ptrofs.repr (2 * size_chunk Mptr)))
                               (v2 := Vnullptr) in H1; eauto with val_renamings.
    destruct H1 as [m3' [Hstorev3' Hmem_obs_eq3']].
    eapply storev_val_obs with (vptr2 := (Val.offset_ptr sp' Ptrofs.zero))
                               (v2 := Vnullptr) in H2; eauto with val_renamings.
    destruct H2 as [m4'  [Hstorev4' Hmem_obs_eq4']].
    pose ((((Pregmap.init Vundef) # PC <- (Vptr b Ptrofs.zero)) # RA <- Vnullptr) # RSP <- sp') as rs0'.
    assert (Hregset: regset_ren f' rs0 rs0').
    { subst rs0 rs0'.
      eapply regset_ren_set; subst sp sp'; eauto.
      eapply regset_ren_set; eauto.
      eapply regset_ren_set; eauto;
        econstructor;
        now eauto.
    }
    eapply make_arguments_inj in H3; eauto using val_obs_list_incr.
    destruct H3 as [rs' [m' [Hmake_args' [Hregs' Hmem_obs_eq']]]].
    assert (Hnext23': Mem.nextblock m2' = Mem.nextblock m3')
      by(eapply nextblock_storev in Hstorev3'; eauto).
    assert (Hnext34': Mem.nextblock m3' = Mem.nextblock m4')
      by (eapply nextblock_storev in Hstorev4'; eauto).
    assert (Hnext4': Mem.nextblock m4' = Mem.nextblock m').
    { eapply X86SEMAxioms.make_arguments_unchanged_on in Hmake_args'.
      destruct Hmake_args' as [_ [_ Hvalid_eq]].
      unfold Mem.valid_block, Plt in Hvalid_eq.
      destruct (Pos.lt_total (Mem.nextblock m4') (Mem.nextblock m')); auto.
      exfalso.
      pose proof (proj1 (Hvalid_eq (Mem.nextblock m4')) H1).
      zify; omega.
      destruct H1; auto.
      exfalso.
      pose proof (proj2 (Hvalid_eq (Mem.nextblock m')) H1).
      zify; omega.
    }
    exists (State rs' m'), m', f'.
    simpl.
    repeat match goal with
           | [ |- _ /\ _] =>
             split; simpl; eauto with renamings reg_renamings
           end; try (econstructor; now eauto).
    rewrite <- Hnext4', <- Hnext34', <- Hnext23'.
    rewrite <- Hnext4, <- Hnext34, <- Hnext23.
    eassumption.
    intros b0 Hvalidm' Hinvalidm1'.
    unfold Mem.valid_block in *.
    rewrite <- Hnext4', <- Hnext34', <- Hnext23' in Hvalidm'.
    now eauto.
    intros b2 Hunmapped ofs.
    eapply X86SEMAxioms.make_arguments_unchanged_on in Hmake_args'.
    destruct Hmake_args' as [_ [Hperm_Eq _]].
    erewrite <- Hperm_Eq.
    eapply MemoryLemmas.mem_storev_store in Hstorev4'.
    destruct Hstorev4' as [? [? [? Hstore4']]].
    eapply Mem.store_access in Hstore4'.
    eapply MemoryLemmas.mem_storev_store in Hstorev3'.
    destruct Hstorev3' as [? [? [? Hstore3']]].
    eapply Mem.store_access in Hstore3'.
    unfold permissions.permission_at in *.
    erewrite Hstore4', Hstore3'.
    pose proof (MemoryLemmas.permission_at_alloc_4 _ _ _ _ _ b2 ofs Halloc') as Hperm_alloc.
    unfold permissions.permission_at in Hperm_alloc.
    eapply Hperm_alloc.
    intros Hcontra.
    subst.
    apply Hunmapped.
    eexists;
      now eauto.
  Qed.

  Lemma core_inj_id :
    forall c (f : memren),
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
             | [H: forall _ _, _ |- f ?X = Some ?X]  =>
               destruct (f X) eqn:Hf;
                 [eapply H in Hf; by subst | by exfalso]
             | [|- val_obs_list _ _ _] =>
               eapply ValObsEq.val_obs_list_id
             end; eauto.
  Qed.

  Lemma core_inj_trans :
    forall c c' c'' (f f' f'' : memren),
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
           | [|- val_obs_list _ _ _] =>
             eapply val_obs_list_trans; eauto
           end; subst; eauto.
  Qed.

  (** ** Proof that related states take related steps*)

  Import MemObsEq MemoryLemmas.

  Lemma find_funct_ptr_ren:
    forall (g : genv) b1 b2 ofs (f fg : memren) fn
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Hobs_eq: val_obs f (Vptr b1 ofs) (Vptr b2 ofs))
      (Hget: Genv.find_funct_ptr g b1 = Some fn),
      b1 = b2.
  Proof.
    intros.
    unfold Genv.find_funct_ptr in *.
    destruct (find_def g b1) as [[|]|] eqn:Hfind; try discriminate.
    destruct Hge_wd.
    unfold find_def in *.
    specialize (H b1 ltac:(rewrite Hfind; auto)).
    destruct (fg b1) eqn:Hfg'; try by exfalso.
    assert (Heq := Hfg _ _ Hfg'); subst b.
    inversion Hobs_eq; subst.
    apply Hincr in Hfg'.
    rewrite Hfg' in H2; inversion H2;
      by subst.
  Qed.

  Lemma symb_val_obs:
    forall f fg g id ofs
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f),
      val_obs f (Senv.symbol_address g id ofs) (Senv.symbol_address g id ofs).
  Proof with eauto with renamings.
    intros.
    destruct Hge_wd as (? & ?).
    unfold Senv.symbol_address in *.
    specialize (H0 id ofs _ ltac:(reflexivity)).
    destruct (Senv.find_symbol g id) eqn:Hsymb; constructor.
    destruct H0 as [b' Hfg'].
    assert (Heq := Hfg _ _ Hfg'); subst...
  Qed.

  Lemma eval_builtin_arg_ren:
    forall (g : genv) (rs rs' : regset) (f fg: memren) (m m' : mem)
      (arg : builtin_arg preg) (varg : val)
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hrs_ren: regset_ren f rs rs')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Heval: eval_builtin_arg g rs (rs RSP) m arg varg),
    exists varg',
      eval_builtin_arg g rs' (rs' RSP) m' arg varg' /\
      val_obs f varg varg'.
  Proof with eauto with renamings reg_renamings val_renamings.
    intros.
    destruct Hmem_obs_eq.
    pose proof (injective weak_obs_eq0).
    induction Heval; subst;
    try by (eexists; split)...
    - eapply loadv_val_obs with (vptr2 := Val.offset_ptr (rs' RSP) ofs) in H...
      destruct H as (varg' & Hload' & Hval_obs)...
    - assert (Hb: val_obs f (Senv.symbol_address g id ofs)
                        (Senv.symbol_address g id ofs))
        by (eapply symb_val_obs; eauto).
      eapply loadv_val_obs with (vptr2 := Senv.symbol_address g id ofs) in H;
        eauto.
      destruct H as (varg' & Hload' & Hval_obs)...
    - assert (Hb: val_obs f (Senv.symbol_address g id ofs)
                          (Senv.symbol_address g id ofs))
        by (eapply symb_val_obs; eauto)...
    - destruct IHHeval1 as (vhi' & ? & ?), IHHeval2 as (vlo' & ? & ?)...
    - destruct IHHeval1 as (vhi' & ? & ?), IHHeval2 as (vlo' & ? & ?).
      eexists; split; [constructor; eauto|].
      destruct Archi.ptr64...
  Qed.

  Lemma eval_builtin_args_ren:
    forall (g : genv) (rs rs' : regset) (f fg: memren) (m m' : mem)
      (args : seq (builtin_arg preg)) (vargs : seq val)
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hrs_ren: regset_ren f rs rs')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Heval: eval_builtin_args g rs (rs RSP) m args vargs),
    exists vargs',
      eval_builtin_args g rs' (rs' RSP) m' args vargs' /\
      val_obs_list f vargs vargs'.
  Proof.
    intros.
    generalize dependent vargs.
    induction args; intros.
    inversion Heval; subst;
    exists [::]; split; by constructor.
    inversion Heval; subst.
    eapply eval_builtin_arg_ren in H1; eauto.
    destruct H1 as (varg' & Heval' & Hval_obs).
    destruct (IHargs _ H3) as (vargs' & Heval_args' & Hobs_list).
    exists (varg' :: vargs');
      split; econstructor; eauto.
  Qed.

  Lemma block_is_volatile_ren:
    forall g fg f b1 b2
      (Hfg: forall b1 b2 : block, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Hf: f b1 = Some b2)
      (Hinjective: forall b1 b1' b2, f b1 = Some b2 -> f b1' = Some b2 ->
                                b1 = b1')
      (Hvolatile: Senv.block_is_volatile g b1 = false),
      Senv.block_is_volatile g b2 = false.
  Proof.
    intros.
    destruct Hge_wd as (H1 & H2).
    unfold Senv.block_is_volatile in *. simpl in *.
    unfold block_is_volatile, find_var_info in *.
    destruct (find_def g b1) as [[|]|] eqn:Hfind; try discriminate;
    unfold find_def in *.
    specialize (H1 b1 ltac:(rewrite Hfind; auto)).
    destruct (fg b1) eqn:Hfg'; try by exfalso.
    assert (Heq:= Hfg _ _ Hfg'); subst b.
    apply Hincr in Hfg'.
    rewrite Hf in Hfg'; inversion Hfg';
    subst. rewrite Hfind. reflexivity.
    unfold find_def in *.
    specialize (H1 b1 ltac:(rewrite Hfind; auto)).
    destruct (fg b1) eqn:Hfg'; try by exfalso.
    assert (Heq:= Hfg _ _ Hfg'); subst b.
    apply Hincr in Hfg'.
    rewrite Hf in Hfg'; inversion Hfg';
    subst. rewrite Hfind. assumption.
    destruct (Maps.PTree.get b2 (genv_defs g)) as [[|]|] eqn:Hget2; auto.
    specialize (H1 b2 ltac:(rewrite Hget2; auto)).
    destruct (fg b2) eqn:Hfg'; try by exfalso.
    assert (Heq:= Hfg _ _ Hfg'); subst b.
    apply Hincr in Hfg'.
    assert (b1 = b2)
      by (eapply Hinjective; eauto); subst b2.
      by congruence.
  Qed.

  Lemma val_obs_addrmode32:
    forall f fg g (a : addrmode) rs rs'
      (Hrs_ren: regset_ren f rs rs')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f),
      val_obs f (eval_addrmode32 g a rs) (eval_addrmode32 g a rs').
  Proof with eauto 10 with val_renamings reg_renamings ge_renamings.
    intros.
    unfold eval_addrmode32.
    destruct a, base, ofs, const; autounfold with renamings;
    try destruct p; try destruct p0;
    try match goal with
        | [|- context[match ?Expr with _ => _ end]] =>
          destruct Expr
        end...
  Qed.

  Lemma val_obs_addrmode64:
    forall f fg g (a : addrmode) rs rs'
      (Hrs_ren: regset_ren f rs rs')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f),
      val_obs f (eval_addrmode64 g a rs) (eval_addrmode64 g a rs').
  Proof with eauto 10 with val_renamings reg_renamings ge_renamings.
    intros.
    unfold eval_addrmode64.
    destruct a, base, ofs, const; autounfold with renamings;
    try destruct p; try destruct p0;
    try match goal with
        | [|- context[match ?Expr with _ => _ end]] =>
          destruct Expr
        end...
  Qed.

  Lemma val_obs_addrmode:
    forall f fg g (a : addrmode) rs rs'
      (Hrs_ren: regset_ren f rs rs')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f),
      val_obs f (eval_addrmode g a rs) (eval_addrmode g a rs').
  Proof.
    intros.
    unfold eval_addrmode.
    destruct Archi.ptr64; [eapply val_obs_addrmode64 | eapply val_obs_addrmode32]; eauto.
  Qed.

  Lemma compare_ints_ren:
    forall f v1 v2 v1' v2' rs rs' m m'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2')
      (Hrs_ren: regset_ren f rs rs')
      (Hmem_obs_eq: mem_obs_eq f m m'),
      regset_ren f (compare_ints v1 v2 rs m)
                 (compare_ints v1' v2' rs' m').
  Proof with eauto 15 with reg_renamings val_renamings.
    intros.
    assert (Hinjective := injective (weak_obs_eq Hmem_obs_eq)).
    unfold compare_ints...
  Qed.

  Lemma compare_longs_ren:
    forall f v1 v2 v1' v2' rs rs' m m'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2')
      (Hrs_ren: regset_ren f rs rs')
      (Hmem_obs_eq: mem_obs_eq f m m'),
      regset_ren f (compare_longs v1 v2 rs m)
                 (compare_longs v1' v2' rs' m').
  Proof with eauto 15 with reg_renamings val_renamings.
    intros.
    assert (Hinjective := injective (weak_obs_eq Hmem_obs_eq)).
    unfold compare_longs...
  Qed.

  Lemma compare_floats32_ren:
    forall f rs rs' v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2')
      (Hrs_ren: regset_ren f rs rs'),
      regset_ren f (compare_floats32 v1 v2 rs)
                 (compare_floats32 v1' v2' rs').
  Proof with eauto 10 with reg_renamings val_renamings.
    intros.
    unfold compare_floats32;
      destruct v1; inversion Hval_obs; subst;
      destruct v2; inversion Hval_obs'; subst...
  Qed.

  Lemma compare_floats_ren:
    forall f rs rs' v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2')
      (Hrs_ren: regset_ren f rs rs'),
      regset_ren f (compare_floats v1 v2 rs)
                 (compare_floats v1' v2' rs').
  Proof with eauto 10 with reg_renamings val_renamings.
    intros.
    unfold compare_floats;
      destruct v1; inversion Hval_obs; subst;
      destruct v2; inversion Hval_obs'; subst...
  Qed.

  Lemma eval_testcond_ren:
    forall f (c : testcond) rs rs'
      (Hrs_ren: regset_ren f rs rs'),
      eval_testcond c rs = eval_testcond c rs'.
  Proof.
    intros.
    unfold eval_testcond.
    destruct c;
      unfold regset_ren, reg_ren, Pregmap.get in *;
      repeat match goal with
             | [|- match (?Rs ?R) with _ => _ end = _] =>
               pose proof (Hrs_ren R);
                 destruct (Rs R);
                 match goal with
                 | [H: val_obs _ _ _ |- _] =>
                   inv H
                 end
             end; auto.
  Qed.

  Lemma val_obs_testcond:
    forall f c rs rs'
      (Hrs_ren: regset_ren f rs rs'),
      val_obs f (Val.of_optbool (eval_testcond c rs))
              (Val.of_optbool (eval_testcond c rs')).
  Proof with eauto with val_renamings.
    intros.
    erewrite eval_testcond_ren; eauto.
    destruct (eval_testcond c rs') as [[|]|];
      unfold Val.of_optbool, Vtrue, Vfalse...
  Qed.

  Hint Resolve compare_floats_ren compare_floats32_ren
       compare_ints_ren compare_longs_ren : reg_renamings.
  Hint Resolve val_obs_addrmode32 val_obs_addrmode64 val_obs_addrmode val_obs_testcond : val_renamings.

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
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
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
       forall b1 b0 : block, f' b1 = Some b0 -> b1 = b0) /\
      (forall b2 : block,
          ~ (exists b1 : block, f' b1 = Some b2) ->
          forall ofs : Z,
            permissions.permission_at m' b2 ofs Cur = permissions.permission_at m2' b2 ofs Cur).
  Proof with eauto 8 with renamings ge_renamings reg_renamings val_renamings.
    intros.
    assert (Hinjective := injective (weak_obs_eq Hmem_obs_eq)).
    assert (Hstrong_obs := strong_obs_eq Hmem_obs_eq).
    destruct i; simpl in *;
    unfold goto_label in *;
    repeat match goal with
           | [H: context[match eval_testcond _ rs with _ => _ end] |- _] =>
             erewrite eval_testcond_ren with (rs := rs) (rs' := rs') in H; eauto
           end;
    repeat match goal with
        | [H1: context[match (rs ?R) with _ => _ end] |- _] =>
          pose proof (Hrs_eq R); unfold reg_ren, Pregmap.get in *;
          destruct (rs R);
          match goal with
          | [H2: val_obs _ _ _ |- _] =>
            inv H2
          end
    end; auto;
    repeat match goal with
           | [H: match ?Expr with _ => _ end = _ |- _] =>
             destruct Expr eqn:?
           end; try discriminate;
    try match goal with
        | [H: exec_store ?G ?CHUNK ?M ?A ?RS ?RS0 _ = _ |- _] =>
          unfold exec_store in *;
            destruct (Mem.storev CHUNK M (eval_addrmode G A RS) (RS RS0)) eqn:?;
                     inv H; exists f
        | [H: exec_load ?G ?CHUNK ?M ?A ?RS ?RD = _ |- _] =>
          unfold exec_load in *;
            destruct (Mem.loadv CHUNK M (eval_addrmode G A RS)) eqn:?;
                     inv H; exists f
        | [H: Next _ _ = Next _ _, H2: Mem.alloc _ _ _ = _  |- _] =>
          inv H
        | [H: Next _ _ = Next _ _ |- _] =>
          inv H; exists f
        end;
    try match goal with
        | [H: Mem.loadv _ _ (eval_addrmode ?G ?A rs) = _ |- _] =>
          eapply loadv_val_obs with
          (f := f) (mf := m') (vptr2 := eval_addrmode G A rs') in H;
            eauto with val_renamings reg_renamings;
            destruct H as [? [? ?]]
        | [H: Mem.storev _ _ (eval_addrmode ?G ?A rs) (rs ?R) = _ |- _] =>
          pose proof (nextblock_storev _ _ _ _ H);
            eapply storev_val_obs with
            (vptr2 := eval_addrmode g a rs') (v2 := rs' R) in H;
            eauto with val_renamings reg_renamings;
            destruct H as [? [Hstore' ?]];
            rewrite Hstore';
            pose proof (nextblock_storev _ _ _ _ Hstore')
        | [H: Val.divs _ _ = _, H2: Val.mods _ _ = _ |- _] =>
          erewrite divs_ren with (v1' := rs' EAX) (v2' := rs' # EDX <- Vundef r1) in H;
            eauto with reg_renamings val_renamings;
            erewrite mods_ren with (v1' := rs' EAX) (v2' := rs' # EDX <- Vundef r1)
              in H2; eauto with reg_renamings val_renamings
        | [H: Val.divu _ _ = _, H2: Val.modu _ _ = _ |- _] =>
          erewrite divu_ren with (v1' := rs' EAX) (v2' := rs' # EDX <- Vundef r1) in H;
            eauto with reg_renamings val_renamings;
            erewrite modu_ren with (v1' := rs' EAX) (v2' := rs' # EDX <- Vundef r1)
              in H2; eauto with reg_renamings val_renamings
        end;
    repeat match goal with
        | [|- exists _ _, _ ] => do 2 eexists; split; first by eauto
        | [|- _ /\ _] => split; eauto 3 with renamings
        | [H: Mem.loadv _ _ _ = _ |- _] =>
          rewrite H; clear H
        | [H: Val.divu _ _ = _ |- _] =>
          rewrite H
        | [H: Val.modu _ _ = _ |- _] =>
          rewrite H
        | [H: Val.divs _ _ = _ |- _] =>
          rewrite H
        | [H: Val.mods _ _ = _ |- _] =>
          rewrite H
        | [|- regset_ren _ _ _] =>
          unfold nextinstr_nf, nextinstr, Vone, Vzero;
            eauto 20 with reg_renamings ge_renamings val_renamings
        | [|- forall _, _] => intros
           end; try (by exfalso);
    repeat match goal with
           | [H: Mem.nextblock ?X = Mem.nextblock ?Y,
                 H2: Mem.valid_block ?X _ |- _] =>
             unfold Mem.valid_block in *;
               rewrite H in H2;
               try by exfalso
           | [|- regset_ren _ _ _] =>
               autorewrite with reg_renamings;
               first by eauto 25 with reg_renamings val_renamings
             | [ |- ~ List.In _ _] =>
               compute; intros ?
             | [H: _ \/ _ |- _] =>
               destruct H; try discriminate;
               try auto
           end;
    (* unmapped blocks*)
    repeat match goal with
           | [|- permissions.permission_at _ _ _ _ = _] =>
             do 2 rewrite <- permissions.getCurPerm_correct
           | [H: Mem.storev _ _ _ _ = _ |- _] =>
             destruct (mem_storev_store _ _ _ _ _ H) as (? & ? & ? & ?);
               erewrite mem_store_cur by eauto;
               reflexivity
           end.
    (* Cleaning up some cases manually, to avoid overcomplicating automation*)
    apply regset_ren_set.
    apply regset_ren_undef.
    apply regset_ren_set...
    apply val_obs_offset_ptr...
    repeat match goal with
           | [|- val_obs _ (undef_regs _ _ _) _] =>
             rewrite gso_undef_regs
           | [|- val_obs _ _ (undef_regs _ _ _)] =>
             rewrite gso_undef_regs
           | [ |- ~ List.In _ _] =>
             compute; intros ?
           | [H: _ \/ _ |- _] =>
             destruct H; try discriminate;
             try auto
           end.
    erewrite Pregmap.gso by congruence...
    apply regset_ren_set.
    apply regset_ren_undef.
    apply regset_ren_set...
    apply val_obs_offset_ptr...
    repeat match goal with
           | [|- val_obs _ (undef_regs _ _ _) _] =>
             rewrite gso_undef_regs
           | [|- val_obs _ _ (undef_regs _ _ _)] =>
             rewrite gso_undef_regs
           | [ |- ~ List.In _ _] =>
             compute; intros ?
           | [H: _ \/ _ |- _] =>
             destruct H; try discriminate;
             try auto
           end.
    erewrite Pregmap.gso by congruence...
    erewrite !Pregmap.gso in * by discriminate.
    pose proof (Hrs_eq PC) as HPC.
    unfold reg_ren, Pregmap.get in HPC; rewrite Heqv in HPC; inv HPC.
    repeat match goal with
        | [|- exists _ _, _ ] => do 2 eexists; split; first by eauto
        | [|- _ /\ _] => split; eauto 3 with renamings
        | [|- regset_ren _ _ _] =>
          unfold nextinstr_nf, nextinstr, Vone, Vzero;
            eauto 20 with reg_renamings ge_renamings val_renamings
        | [|- forall _, _] => intros
           end; try (by exfalso).
    (* Allocation case*)
    destruct (Mem.alloc m' 0 sz) as [m0' b'] eqn:Halloc'.
    destruct (alloc_obs_eq Hmem_obs_eq Heqp Halloc') as
        (f' & Hf' & Hmem_obs_eq' & Hincr' & Hsep & Hnextblock & Hinverse & Hid).
    exists f'.
    pose proof (Mem.nextblock_store _ _ _ _ _ _ Heqo) as Hnext.
    eapply store_val_obs with (f := f') (mf := m0') (b2 := b') in Heqo...
    destruct Heqo as [m1' [Hstore' ?]].
    pose proof (Mem.nextblock_store _ _ _ _ _ _ Hstore') as Hnext'.
    pose proof (Mem.nextblock_store _ _ _ _ _ _ Heqo0) as Hnext0.
    eapply store_val_obs with (f := f') (mf := m1') (b2 := b') in Heqo0...
    destruct Heqo0 as [m2' [Hstore'' ?]].
    pose proof (Mem.nextblock_store _ _ _ _ _ _ Hstore'') as Hnext0'.
    unfold nextinstr. eexists. exists m2'.
    unfold Mem.valid_block in *.
    rewrite Hstore' Hstore''.
    rewrite Hnext0' Hnext0 Hnext Hnext'.
    repeat match goal with
           | [|- exists _ _, _ ] => do 2 eexists; split; first by eauto
           | [|- _ /\ _] => split; eauto 3 with renamings
           | [|- regset_ren _ _ _] =>
             unfold nextinstr_nf, nextinstr, Vone, Vzero;
               eauto 20 using regset_ren_incr
               with reg_renamings ge_renamings val_renamings
           | [|- forall _, _] => intros
           end; try (by exfalso).
    assert (b2 <> b')
      by (intros Hcontra; subst;
          eauto).
    erewrite permission_at_alloc_4 with (m := m') (m' := m0'); eauto.
    do 2 rewrite <- permissions.getCurPerm_correct.
    erewrite mem_store_cur by eauto.
    erewrite mem_store_cur by eauto.
    reflexivity.
    (* Free case *)
    pose proof (Mem.nextblock_free _ _ _ _ _ Heqo1) as Hnb.
    eapply mem_free_obs in Heqo1...
    destruct Heqo1 as [m2' [Hfree' ?]].
    pose proof (Mem.nextblock_free _ _ _ _ _ Hfree') as Hnb'.
    rewrite Hfree'.
    eapply loadv_val_obs with
    (f := f) (mf := m') (vptr2 := Val.offset_ptr (Vptr b2 i) ofs_ra) in Heqo;
      eauto with val_renamings reg_renamings;
      destruct Heqo as [? [Hload' ?]].
    eapply loadv_val_obs with
    (f := f) (mf := m') (vptr2 := Val.offset_ptr (Vptr b2 i) ofs_link) in Heqo0;
      eauto with val_renamings reg_renamings;
      destruct Heqo0 as [? [Hload2' ?]].
    rewrite Hload' Hload2'.
    eexists; exists m2'.
    unfold nextinstr, Mem.valid_block.
    rewrite Hnb' Hnb.
    repeat match goal with
           | [|- exists _ _, _ ] => do 2 eexists; split; first by eauto
           | [|- _ /\ _] => split; eauto 3 with renamings
           | [|- regset_ren _ _ _] =>
             unfold nextinstr_nf, nextinstr, Vone, Vzero;
               eauto 20 with reg_renamings ge_renamings val_renamings
           | [|- forall _, _] => intros
           end; try (by exfalso).
    assert (b2 <> b0)
      by (intros Hcontra; subst; eauto).
    erewrite permission_at_free_2 by eauto.
    reflexivity.
  Qed.

  Lemma extcall_arg_reg:
    forall f rs rs' m m' locs arg
      (Hrs_ren: regset_ren f rs rs')
      (Hobs_eq: mem_obs_eq f m m')
      (Harg: extcall_arg rs m locs arg),
    exists arg',
      extcall_arg rs' m' locs arg' /\
      val_obs f arg arg'.
  Proof with eauto with reg_renamings val_renamings.
    intros.
    inversion Harg; subst.
    exists (rs' (preg_of r)).
    split...
    constructor.
    pose proof (strong_obs_eq Hobs_eq).
    pose proof (injective (weak_obs_eq Hobs_eq)).
    eapply loadv_val_obs in H0...
    destruct H0 as [arg' [Hloadv' Hval_obs]].
    exists arg'; split; auto.
    econstructor; eauto.
  Qed.

  Lemma extcall_arg_pair_ren:
    forall f rs rs' m m' locs arg
      (Hrs_ren: regset_ren f rs rs')
      (Hobs_eq: mem_obs_eq f m m')
      (Harg: extcall_arg_pair rs m locs arg),
    exists arg',
      extcall_arg_pair rs' m' locs arg' /\
      val_obs f arg arg'.
  Proof with eauto with reg_renamings val_renamings.
    intros.
    inversion Harg; subst.
    eapply extcall_arg_reg in H; eauto.
    destruct H as [arg' [Harg' Hobs_arg]].
    exists arg'.
    split...
    constructor; auto.
    eapply extcall_arg_reg in H; eauto.
    eapply extcall_arg_reg in H0; eauto.
    destruct H as [vhi' [Hhi' Hobs_hi]].
    destruct H0 as [vlo' [Hlo' Hobs_lo]].
    exists (Val.longofwords vhi' vlo').
    split...
    constructor; auto.
  Qed.

  Lemma extcall_arguments_ren:
    forall f m m' ef args rs rs'
      (Hexternal: extcall_arguments rs m (ef_sig ef) args)
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hrs_ren: regset_ren f rs rs'),
    exists args',
      extcall_arguments rs' m' (ef_sig ef) args' /\
      val_obs_list f args args'.
  Proof.
    intros.
    unfold extcall_arguments in *.
    generalize dependent (Conventions1.loc_arguments (ef_sig ef)).
    induction args; intros.
    - inversion Hexternal; subst.
      exists [::].
      split;
        constructor.
    - inversion Hexternal; subst.
      destruct (IHargs _ H3) as [args' [Hls' Hobs']].
      eapply extcall_arg_pair_ren in H2; eauto.
      destruct H2 as [arg' [Harg Hval_obs]].
      exists (arg' :: args'); split;
      constructor; eauto.
  Qed.

  Lemma core_inj_wd:
    forall f c c',
      core_inj f c c' ->
      core_wd f c.
  Proof.
    intros.
    destruct c,c'; simpl in *.
    unfold regset_wd, regset_ren in *.
    intros. specialize (H r1).
    unfold reg_ren, valid_val in *.
    destruct (Pregmap.get r1 r); auto.
    inv H; now eauto.
  Qed.

  Lemma corestep_obs_eq:
    forall the_ge (Hsafe : safe_genv the_ge) (cc cf cc' : state) (mc mf mc' : mem) f fg,
      mem_obs_eq f mc mf ->
      core_inj f cc cf ->
      (forall b1 b2, fg b1 = Some b2 -> b1 = b2) ->
      ge_wd fg the_ge ->
      ren_incr fg f ->
      corestep (Asm_core_sem the_ge) cc mc cc' mc' ->
      exists (cf' : state) (mf' : mem) (f' : Renamings.memren),
        corestep (Asm_core_sem the_ge) cf mf cf' mf' /\
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
         forall b1 b2 : block, f' b1 = Some b2 -> b1 = b2) /\
        (forall b2 : block,
            ~ (exists b1 : block, f' b1 = Some b2) ->
            forall ofs : Z,
              permissions.permission_at mf b2 ofs Cur = permissions.permission_at mf' b2 ofs Cur).
  Proof with (eauto with renamings reg_renamings val_renamings).
   intros the_ge ? cc cf cc' mc mf mc' f fg
          Hobs_eq Hcore_inj Hfg Hge_wd Hincr Hcorestep.
    destruct cc as [rs], cf as [rsF], cc' as [rs'].
    inv Hcorestep.
    rename m1 into mc'.
    assert (Smallstep.at_external (part_semantics the_ge) (set_mem (State rsF m0) mf) = None) as Hext.
    { exploit core_inj_ext; eauto using core_inj_wd.
      simpl in *;rewrite H0; clear H0.
      destruct (rsF PC); auto.
      destruct (Ptrofs.eq_dec _ _); auto.
      destruct (find_funct_ptr _ _); auto.
      destruct f0; auto.
      destruct (get_extcall_arguments _ _ _); auto; contradiction. }
    inv H.
    - assert (Hpc' := get_reg_ren PC Hcore_inj H5).
      destruct Hpc' as [v' [Hpc' Hpc_obs]].
      inversion Hpc_obs; subst. rewrite <- H1 in Hpc_obs.
      assert (Hfun := find_funct_ptr_ren Hfg Hge_wd Hincr Hpc_obs H7); subst b2.
      destruct (exec_instr_ren _ _ Hobs_eq Hcore_inj Hfg Hge_wd Hincr H9)
        as (f' & rsF' & mF' & Hexec' & Hrs_ren' & Hobs_eq' & Hincr' & Hsep
            & Hnextblocks & Hinverse & Hid_extend & Hunmapped).
      exists (State rsF' mF'), mF', f'.
      repeat match goal with
             | [ |- _ /\ _] =>
               split; simpl; eauto with renamings reg_renamings
             end.
      econstructor...
      econstructor...
    - exploit Hsafe; eauto.
      assert (Hpc' := get_reg_ren PC Hcore_inj H5).
      destruct Hpc' as [v' [Hpc' Hpc_obs]].
      inversion Hpc_obs; subst. rewrite <- H1 in Hpc_obs.
      assert (Hfun := find_funct_ptr_ren Hfg Hge_wd Hincr Hpc_obs H6); subst b2.
      eapply eval_builtin_args_ren in H9 as (args' & ? & ?); eauto.
      (* We need Hsafe to give us that external calls behave the same even
         on injected arguments. *)
      destruct ef;
               try (intros (_ & _ & Hcontra);
                    now exfalso).
      + (* EF_malloc case*)
        pose proof H10 as Hext_call.
        simpl in H10.
        inv H10.
        remember (Mem.alloc mf (- size_chunk Mptr) (Ptrofs.unsigned sz)) as p eqn:HallocF.
        destruct p as [mf' b0F].
        symmetry in HallocF.
        destruct (alloc_obs_eq Hobs_eq H4 HallocF)
          as [f' [Hb0 [Hobs_eq' [Hincr' [Hsep [Hnextblock_eq [Hmap_spec Hunchanged_map]]]]]]].
        pose proof H8 as Hstore.
        eapply store_val_obs with (v2 := Vptrofs sz) in H8; eauto.
        destruct H8 as [mf'' [HstoreF Hobs_eq'']].
        exists (State (nextinstr_nf
                    (set_res res (Vptr b0F Ptrofs.zero)
                             (undef_regs (List.map preg_of (Machregs.destroyed_by_builtin
                                                              EF_malloc)) rsF))) mf''), mf'', f'.
        repeat match goal with
               | [|- _ /\ _] => split
               end; eauto.
        * (* injected machine steps *)
          simpl.
          econstructor; eauto.
          simpl.
          eapply Asm.exec_step_builtin; eauto.
          simpl.
          inv H2.
          inv H13.
          assert (v' = Vptrofs sz)
            by (unfold Vptrofs in *;
                destruct Archi.ptr64; inv H11; reflexivity); subst.
          econstructor.
          eauto.
          eauto.
        * (* injection on cores is preserved *)
          simpl.
          unfold nextinstr_nf, nextinstr.
          eauto 15 using regset_ren_incr with reg_renamings val_renamings renamings.
        * (* nextblock relation *)
          eapply Mem.nextblock_store in Hstore.
          eapply Mem.nextblock_store in HstoreF.
          rewrite Hstore HstoreF.
          destruct Hnextblock_eq as [? [? ?]].
          left; eexists; now eauto.
        * intros b1 Hvalid'' Hinvalid.
          simpl.
          eapply Hmap_spec; eauto.
          eapply Mem.store_valid_block_2;
            now eauto.
        * intros b2 Hunmapped ofs0.
          assert (b2 <> b0F)
            by (intros Hcontra; subst;
                eapply Hunmapped; eexists; eauto).
          erewrite permission_at_alloc_4 by eauto.
          unfold permissions.permission_at.
          erewrite Mem.store_access with (m2 := mf'') by eauto.
          reflexivity.
        * econstructor.
      + (*EF_free*)
        pose proof H10 as Hext_call.
        simpl in H10.
        inv H10.
        inv H2. inv H14.
        inv H12.
        destruct (mem_free_obs _ _ _ Hobs_eq H13 H9) as [mf' [HfreeF Hobs_eq']].
        eapply load_val_obs with (mf := mf) in H4; eauto.
        destruct H4 as [vF [HloadF Hval_obs]].
        assert (vF = Vptrofs sz)
          by (unfold Vptrofs in *;
              destruct (Archi.ptr64); inv Hval_obs; reflexivity); subst.
        exists (State (nextinstr_nf
                    (set_res res Vundef
                             (undef_regs (List.map preg_of
                                                   (Machregs.destroyed_by_builtin EF_free)) rsF)))
                 mf'), mf', f.
        repeat match goal with
               | [|- _ /\ _] => split
               end; eauto.
        * (* injected machine steps *)
          simpl.
          econstructor; eauto.
          simpl.
          eapply Asm.exec_step_builtin; eauto.
          simpl.
          econstructor;
            now eauto.
        * (* injection on cores is preserved *)
          simpl.
          unfold nextinstr_nf, nextinstr.
          eauto 15 using regset_ren_incr with reg_renamings val_renamings renamings.
        * (*ren_incr *)
          eauto using ren_incr_refl.
        * eauto using ren_separated_refl.
        * (* nextblock relation *)
          eapply Mem.nextblock_free in HfreeF.
          eapply Mem.nextblock_free in H9.
          rewrite H9 HfreeF.
          right; now eauto.
        * intros b1 Hvalid'' Hinvalid.
          exfalso.
          eapply Hinvalid.
          eapply Mem.valid_block_free_2; eauto.
        * intros b1 Hunmmaped ofs0.
          erewrite permission_at_free_2; eauto.
          intros Hcontra.
          subst. now eauto.
        * destruct Hobs_eq.
          destruct weak_obs_eq0.
          now eauto.
        * destruct Hobs_eq;
            now eauto.
      + (* EF_memcpy *)
        pose proof H10 as Hext_call.
        simpl in H10.
        inv H10.
        inv H2.
        inv H19.
        inv H17.
        inv H20.
        inv H16.
        eapply loadbytes_val_obs with (f := f) (mf := mf) in H14; eauto.
        destruct H14 as [mv' [HloadbytesF Hmemval_obs]].
        pose proof H15 as Hstore.
        eapply storebytes_val_obs with (mv2 := mv') in H15; eauto.
        destruct H15 as [mf'' [HstoreF Hobs_eq'']].
        exists (State (nextinstr_nf
                    (set_res res Vundef
                             (undef_regs (List.map preg_of (Machregs.destroyed_by_builtin
                                                              (EF_memcpy sz al)))
                                         rsF))) mf''), mf'', f.
        repeat match goal with
               | [|- _ /\ _] => split
               end; eauto.
        * (* injected machine steps *)
          simpl.
          econstructor; eauto.
          simpl.
          eapply Asm.exec_step_builtin; eauto.
          simpl.
          econstructor; eauto.
          destruct H13 as [Hneq | ?]; [|now auto].
          left.
          intros Hcontra.
          subst.
          eapply Hneq.
          eapply (injective (weak_obs_eq Hobs_eq));
            now eauto.
        * (* injection on cores is preserved *)
          simpl.
          unfold nextinstr_nf, nextinstr.
          eauto 15 using regset_ren_incr with reg_renamings val_renamings renamings.
        * (*ren_incr *)
          eauto using ren_incr_refl.
        * eauto using ren_separated_refl.
        * (* nextblock relation *)
          eapply Mem.nextblock_storebytes in Hstore.
          eapply Mem.nextblock_storebytes in HstoreF.
          rewrite Hstore HstoreF.
          right; now auto.
        * intros b1 Hvalid'' Hinvalid.
          simpl.
          exfalso.
          eapply Hinvalid.
          eapply Mem.storebytes_valid_block_2;
            now eauto.
        * intros b1 Hunmapped ofs0.
          unfold permissions.permission_at.
          erewrite Mem.storebytes_access with (m2 := mf'') by eauto.
          reflexivity.
        * now eapply (injective (weak_obs_eq Hobs_eq)).
        * destruct Hobs_eq;
            now auto.
    - simpl in H0.
      rewrite H5 in H0.
      destruct (Ptrofs.eq_dec _ _); [|contradiction].
      rewrite H6 in H0.
      apply get_extcall_arguments_spec in H8; rewrite H8 in H0; discriminate.
  Qed.

  (** Coresteps maintain well-definedness *)

  Lemma extcall_arg_valid:
    forall f rs m locs arg
      (Hrs_wd: regset_wd f rs)
      (Hmem_wd : valid_mem m)
      (Hobs_eq: domain_memren f m)
      (Harg: extcall_arg rs m locs arg),
      valid_val f arg.
  Proof with eauto with wd.
    intros.
    inversion Harg; subst.
    eauto.
    eapply loadv_wd in H0; eauto.
  Qed.


  Lemma valid_val_longofwords:
    forall f hi lo,
      valid_val f hi ->
      valid_val f lo ->
      valid_val f (Val.longofwords hi lo).
  Proof.
    intros. unfold Val.longofwords.
    destruct hi, lo; simpl; auto.
  Qed.

  Hint Resolve valid_val_longofwords : wd.

  Lemma extcall_arg_pair_valid:
    forall f rs m locs arg
      (Hrs_wd: regset_wd f rs)
      (Hmem_wd : valid_mem m)
      (Hobs_eq: domain_memren f m)
      (Harg: extcall_arg_pair rs m locs arg),
      valid_val f arg.
  Proof with eauto with wd.
    intros.
    inversion Harg; subst;
    eapply extcall_arg_valid in H; eauto.
    eapply extcall_arg_valid in H0; eauto...
  Qed.

  Lemma extcall_arguments_valid:
    forall f m ef args rs
      (Hexternal: extcall_arguments rs m (ef_sig ef) args)
      (Hrs_wd: regset_wd f rs)
      (Hmem_wd : valid_mem m)
      (Hobs_eq: domain_memren f m),
      valid_val_list f args.
  Proof.
    intros.
    unfold extcall_arguments in *.
    generalize dependent (Conventions1.loc_arguments (ef_sig ef)).
    induction args; intros; constructor.
    inversion Hexternal; subst.
    eapply extcall_arg_pair_valid; eauto.
    inversion Hexternal; subst.
    eauto.
  Qed.

  Lemma free_wd_domain :
  forall (m m' : mem) b lo hi (f : memren),
    domain_memren f m ->
    Mem.free m b lo hi = Some m' ->
    valid_mem m ->
    valid_mem m' /\ domain_memren f m'.
Proof.
  intros.
  pose proof (Mem.valid_block_free_2 _ _ _ _ _ H0).
  split.
  unfold valid_mem.
  intros.
  erewrite <- mem_free_contents in H4; eauto.
  specialize (H1 b0 (H2 _ H3) ofs mv H4).
  destruct mv; auto.
  destruct v; auto.
  simpl in *.
  eapply Mem.valid_block_free_1; eauto.
  split; destruct (H b0); eauto using Mem.valid_block_free_1.
Qed.

 Lemma exec_instr_wd:
    forall (g : genv) (fn : function) (i : instruction) (rs rs': regset)
      (m m' : mem) (f fg: memren) loader
      (Hmem_wd: valid_mem m)
      (Hrs_wd: regset_wd f rs)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_domain_incr fg f)
      (Hdomain: domain_memren f m)
      (Hexec: exec_instr g fn i rs m = Next rs' m'),
      valid_mem m' /\
      (exists f' : memren, ren_domain_incr f f' /\ domain_memren f' m') /\
      (forall f' : memren,
          domain_memren f' m' -> core_wd f' (State rs' loader)).
  Proof with eauto 10 with wd.
    intros.
    destruct i; simpl in *;
    unfold goto_label in *;
    repeat match goal with
           | [H: match ?Expr with _ => _ end = _ |- _] =>
             destruct Expr eqn:?
           end; try discriminate;
    try match goal with
        | [H: exec_store ?G ?CHUNK ?M ?A ?RS ?RS0 _ = _ |- _] =>
          unfold exec_store in H;
            destruct (Mem.storev CHUNK M (eval_addrmode G A RS) (RS RS0)) eqn:?;
                     inv H
        | [H: exec_load ?G ?CHUNK ?M ?A ?RS ?RD = _ |- _] =>
          unfold exec_load in H;
            destruct (Mem.loadv CHUNK M (eval_addrmode G A RS)) eqn:?;
                     inv H
        | [H: Next _ _ = Next _ _ |- _] =>
          inv H
        end;
    try match goal with
        | [H: Mem.storev _ _ (eval_addrmode ?G ?A rs) (rs ?R) = _ |- _] =>
          eapply storev_wd_domain in H; destruct H
        end;
      repeat match goal with
             | [H: Mem.loadv _ _ (eval_addrmode ?G ?A rs) = _ |- _] =>
               eapply loadv_wd in H;
                 eauto
             | [H: Stuck = Next _ _ |- _] => discriminate
             | [H: Mem.alloc _ _ _ = _ |- _ /\ _] =>
               idtac
             | [H: Mem.free _ _ _ _ = _ |- _] =>
               eapply free_wd_domain in H; eauto;
               destruct H
             | [|- _ /\ _] =>
               split
             | [H: Mem.alloc _ _ _ = _ |- _] =>
               idtac
             | [|- exists _, _ /\ _] => eexists
             | [|- forall _, _] => intros
             end;
      unfold nextinstr, nextinstr_nf;
      try match goal with
          | [H: domain_memren ?F ?M, H1: ren_domain_incr ?FG ?F,
                                         H2: domain_memren ?F2 ?M |- _] =>
            assert (ren_domain_incr ?FG ?F2) by
                (eapply domain_memren_incr with (f'' := F2) (f' := F);
                  eauto)
          end; unfold nextinstr, nextinstr_nf;
      (* first steps are done manually to speed up eauto*)
      repeat match goal with
          | [|- regset_wd _ (@Pregmap.set _ _ _ _)] =>
            apply regset_wd_set
          | [|- valid_val _ (Val.add _ _)] =>
            apply valid_val_add
          | [|- valid_val _ (Val.addl _ _)] =>
            apply valid_val_addl
          | [|- valid_val _ (Val.offset_ptr _ _)] =>
            apply valid_val_offset_ptr
          | [|- regset_wd _ (undef_regs _ _)] =>
            eapply regset_wd_undef
          | [|- valid_val _ (@Pregmap.set _ _ _ _ _)] =>
            eapply regset_wd_set
          | [|- valid_val _ (undef_regs _ _ _)] =>
            eapply regset_wd_undef
          | [|- mem_wd.val_valid _ _] =>
            eapply wd_val_valid
          | [H: _ = Vptr ?B _ |- valid_val _ (Vptr ?B _)] =>
            eapply valid_val_offset;
              erewrite <- H; eauto with wd
          end;
      eauto 4 with wd.
    (* Allocation case*)
    assert (Hnew: Mem.valid_block m0 b)
      by (eapply Mem.valid_new_block; eauto).
    repeat match goal with
           | [H: Mem.alloc _ _ _ = _ |- _] =>
             eapply mem_valid_alloc in H; eauto;
             destruct H as [? [f'' [? ?]]]
           | [H1: valid_mem ?M, H: Mem.store _ ?M _ _ _ = _ |- _] =>
             eapply store_wd_domain in H; eauto;
             destruct H
           end.
    split; auto.
    split. eexists; split; eauto.
    intros.
    assert (ren_domain_incr f f') by
        (eapply domain_memren_incr with (f' := f'');
          eauto).
    Hint Resolve valid_val_incr regset_wd_incr : wd_alloc.
    eauto 2 with wd wd_alloc.
    assert (domain_memren f' m0) by
        (eapply domain_memren_trans; eauto).
    apply regset_wd_set.
    apply valid_val_offset_ptr; eauto 2 with wd.
    apply regset_wd_set; eauto with wd wd_alloc.
    apply regset_wd_set.
    simpl. destruct (H8 b). specialize (H9 Hnew).
    destruct (f' b); try by exfalso. eauto.
    eauto with wd wd_alloc.
    eapply wd_val_valid; eauto with wd wd_alloc.
    eapply wd_val_valid; eauto with wd wd_alloc.
    (* left-overs from free case*)
    eapply valid_val_domain with (f := f); eauto.
    unfold Mem.loadv in *; simpl in *.
    eapply valid_mem_load with (m := m); eauto.
    eapply valid_val_domain with (f := f); eauto.
    unfold Mem.loadv in *; simpl in *.
    eapply valid_mem_load with (m := m); eauto.
    eapply valid_val_domain with (f := f); eauto.
    unfold Mem.loadv in *; simpl in *.
    eapply valid_mem_load with (m := m); eauto.
  Qed.


  (** Well-definedness of state is retained. *)
  Lemma corestep_wd:
    forall the_ge (Hsafe : safe_genv the_ge) c m c' m' f fg
      (Hwd: core_wd f c)
      (Hmem_wd: valid_mem m)
      (Hge_wd: ge_wd fg the_ge)
      (Hincr: ren_domain_incr fg f)
      (Hdomain: domain_memren f m)
      (Hcorestep: corestep (Asm_core_sem the_ge) c m c' m'),
      valid_mem m' /\
      (exists f', ren_domain_incr f f' /\ domain_memren f' m') /\
      forall f', domain_memren f' m' ->
            core_wd f' c'.
  Proof with eauto 3 with wd.
    intros.
    destruct c;
      simpl in *.
    inv Hcorestep.
    inv H.
    - eapply exec_instr_wd; eauto.
    - exploit Hsafe; eauto.
      destruct ef; try (intros (? & ? &?) ; exfalso; now auto).
      + (* EF_malloc case*) 
        intros.
        simpl in H7.
        inversion H7; subst.
        pose proof H1 as Halloc.
        eapply mem_valid_alloc in H1; eauto.
        destruct H1 as [Hvalid' [f' [Hincr' Hren']]].
        eapply store_wd_domain in H2; eauto.
        destruct H2.
        assert (Hvalid_b0: valid_val f' (Vptr b0 Ptrofs.zero)).
        { eapply Mem.valid_new_block in Halloc.
          unfold valid_val.
          destruct (Hren' b0) as [? ?].
          specialize (H8 Halloc).
          destruct (f' b0); [eexists | exfalso]; now eauto. }
        split; eauto.
        split; [eexists; eauto | intros ].
        eapply X86WD.regset_wd_domain with (f1 := f'); eauto.
        apply regset_wd_set...
        apply valid_val_offset_ptr...
        rewrite gso_undef_regs.
        apply regset_wd_set_res...
        eapply X86WD.regset_wd_undef...
        eapply X86WD.regset_wd_incr;
          eauto.
        simpl. intros Hcontra.
        repeat match goal with
               | [H: ?A \/ ?B |- _] =>
                 destruct H; try discriminate
               end; auto.
        eapply X86WD.regset_wd_undef...
        apply regset_wd_set_res...
        eapply X86WD.regset_wd_undef...
        eapply X86WD.regset_wd_incr;
          eauto.
      + (* EF_free case*)
        intros _.
        simpl in H7.
        inversion H7; subst.
        pose proof H2 as Hfree.
        pose proof H as Hload.
        eapply free_wd_domain in Hfree; eauto.
        destruct Hfree.
        split; eauto.
        split; [eexists; eauto using ren_domain_incr_refl |].
        intros.
        apply regset_wd_set...
        apply valid_val_offset_ptr...
        rewrite gso_undef_regs.
        apply regset_wd_set_res...
        simpl. intros Hcontra.
        repeat match goal with
               | [H: ?A \/ ?B |- _] =>
                 destruct H; try discriminate
               end; auto.
        eapply X86WD.regset_wd_undef...
      + (* EF_memcpy case*) 
        intros.
        simpl in H7.
        inversion H7; subst.
        eapply valid_mem_loadbytes in H12; eauto.
        eapply storebytes_wd_domain in H13; eauto.
        destruct H13.
        split; eauto.
        split.
        exists f; split; eauto using ren_domain_incr_refl.
        intros.
        eapply X86WD.regset_wd_domain with (f1 := f'); eauto.
        apply regset_wd_set...
        apply valid_val_offset_ptr...
        rewrite gso_undef_regs.
        apply regset_wd_set_res...
        simpl. intros Hcontra.
        repeat match goal with
               | [H: ?A \/ ?B |- _] =>
                 destruct H; try discriminate
               end; auto.
        eapply X86WD.regset_wd_undef...
        apply regset_wd_set_res...
    - simpl in *.
      rewrite H3 in H0.
      destruct (Ptrofs.eq_dec _ _); [|contradiction].
      rewrite H4 in H0.
      apply get_extcall_arguments_spec in H5; rewrite H5 in H0; discriminate.
  Qed.

  Section Inj.

  Import X86Context.

  Context (the_program : program). 
  Notation the_ge := (@the_ge the_program).
  Context (Hsafe : safe_genv the_ge).

  Instance X86Inj : @CoreInj (@X86Sem the_program Hsafe) :=
    @Build_CoreInj (@X86Sem the_program Hsafe) core_wd ge_wd ge_wd_incr ge_wd_domain
      core_wd_incr core_wd_domain (at_external_wd the_ge) (@after_external_wd the_ge) (@initial_core_wd the_ge)
      core_inj _ (@core_inj_after_ext the_ge)
      (core_inj_halted the_ge) (@core_inj_init the_ge) core_inj_id core_inj_trans (corestep_obs_eq Hsafe) (corestep_wd Hsafe).
  Proof.
    intros; eapply core_inj_ext; eauto using core_inj_wd.
    
  Defined.

  End Inj.

End X86Inj.
