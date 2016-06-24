Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

Require Import Coqlib.
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

    Definition ge_wd (the_ge: genv) : Prop :=
      (forall b, Maps.PTree.get b (genv_funs the_ge) ->
            f b) /\
      (forall b, Maps.PTree.get b (genv_vars the_ge) ->
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

  Import MemoryWD Genv.
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
       loader_ren_incr loader_ren_id loader_ren_trans
       val_obs_reg regset_ren_set : reg_renamings.
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
    destruct Hge_wd as (H1 & H2 & H3).
    unfold symbol_address, Senv.symbol_address in *;
      simpl in *.
    specialize (H3 id i _ ltac:(reflexivity)).
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
    forall (f f' : memren) (g : SEM.G),
      ge_wd f g -> ren_domain_incr f f' -> ge_wd f' g.
  Proof with (eauto with renamings val_renamings).
    intros.
    unfold ge_wd in *.
    destruct H as (? & ? & ?);
      repeat split;
      intros...
  Qed.

  Lemma ge_wd_domain :
    forall (f f' : memren) (m : mem) (g : SEM.G),
      ge_wd f g -> domain_memren f m -> domain_memren f' m -> ge_wd f' g.
  Proof.
    intros.
    unfold ge_wd in *.
    unfold domain_memren in *.
    destruct H as (Hf & Hv & Hs);
      repeat split;
      intros;
      try destruct (H0 b), (H1 b);
      try specialize (Hf _ ltac:(eauto));
      try specialize (Hv _ ltac:(eauto));
      try specialize (Hs id ofs v ltac:(eauto));
      eauto.
    eapply valid_val_domain; eauto.
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
    forall vf vf' arg arg' c_new f fg
      (Harg: val_obs_list f arg arg')
      (Hvf: val_obs f vf vf')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hincr: ren_incr fg f)
      (Hinit: initial_core SEM.Sem the_ge vf arg = Some c_new),
      exists c_new' : state,
        initial_core SEM.Sem the_ge vf' arg' = Some c_new' /\
        core_inj f c_new c_new'.
  Proof.
    intros.
    simpl in *.
    unfold Asm_initial_core in *.
    destruct vf; try discriminate.
    inversion Hvf; subst.
    destruct (Int.eq_dec i Int.zero); subst; try discriminate.
    unfold Genv.find_funct_ptr in *.
    destruct (Maps.PTree.get b (genv_funs the_ge)) eqn:Hget; try discriminate.
    destruct f0; try discriminate.
    destruct Hge_wd as (Hge_wd1 & Hge_wd2 & Hge_wd3).
    specialize (Hge_wd1 b ltac:(rewrite Hget; eauto)).
    assert (Hfg_b: b = b2).
    { destruct (fg b) eqn:Hfg'.
      assert (b = b0)
        by (apply Hfg in Hfg'; by subst).
      subst b0.
      apply Hincr in Hfg'. rewrite H2 in Hfg'; by inversion Hfg'.
        by exfalso.
    } subst b2.
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
    destruct Hge_wd.
    specialize (H b1 ltac:(rewrite Hget; auto)).
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
    destruct Hge_wd as (? & ? & ?).
    unfold Senv.symbol_address in *.
    specialize (H1 id ofs _ ltac:(reflexivity)).
    destruct (Senv.find_symbol g id) eqn:Hsymb; constructor.
    destruct H1 as [b' Hfg'].
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
      (Heval: eval_builtin_arg g rs (rs ESP) m arg varg),
    exists varg',
      eval_builtin_arg g rs' (rs' ESP) m' arg varg' /\
      val_obs f varg varg'.
  Proof with eauto with renamings reg_renamings val_renamings.
    intros.
    destruct Hmem_obs_eq.
    induction Heval; subst;
    try by (eexists; split)...
    -
      eapply loadv_val_obs with (vptr2 := Val.add (rs' ESP) (Vint ofs)) in H...
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
  Qed.
  
  Lemma eval_builtin_args_ren:
    forall (g : genv) (rs rs' : regset) (f fg: memren) (m m' : mem)
      (args : seq (builtin_arg preg)) (vargs : seq val)
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hrs_ren: regset_ren f rs rs')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f)
      (Heval: eval_builtin_args g rs (rs ESP) m args vargs),
    exists vargs',
      eval_builtin_args g rs' (rs' ESP) m' args vargs' /\
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

  Lemma eventval_valid_ge:
    forall fg g ev chunk v
      (Hge_wd: ge_wd fg g)
      (Hevent_val: eventval_match g ev (type_of_chunk chunk) v),
      valid_val fg v.
  Proof with eauto with renamings val_renamings.
    intros.
    inversion Hevent_val; subst; try rewrite H1;
    try by (eexists; split)...
    destruct Hge_wd as (? & ? &?).
    unfold Senv.symbol_address in H4.
    specialize (H4 id ofs _ ltac:(reflexivity)).
    rewrite H2 in H4.
    assumption.
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
    destruct Hge_wd as (H1 & H2 & H3).
    unfold Senv.block_is_volatile in *. simpl in *.
    unfold block_is_volatile, find_var_info in *.
    destruct (Maps.PTree.get b1 (genv_vars g)) eqn:Hget.
    specialize (H2 b1 ltac:(rewrite Hget; auto)).
    destruct (fg b1) eqn:Hfg'; try by exfalso.
    assert (Heq:= Hfg _ _ Hfg'); subst b.
    apply Hincr in Hfg'.
    rewrite Hf in Hfg'; inversion Hfg';
    subst.
    rewrite Hget.
    assumption.
    destruct (Maps.PTree.get b2 (genv_vars g)) eqn:Hget2; auto.
    specialize (H2 b2 ltac:(rewrite Hget2; auto)).
    destruct (fg b2) eqn:Hfg'; try by exfalso.
    assert (Heq:= Hfg _ _ Hfg'); subst b.
    apply Hincr in Hfg'.
    assert (b1 = b2)
      by (eapply Hinjective; eauto); subst b2.
      by congruence.
  Qed.

  Lemma val_obs_addrmode:
    forall f fg g (a : addrmode) rs rs'
      (Hrs_ren: regset_ren f rs rs')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg g)
      (Hincr: ren_incr fg f),
      val_obs f (eval_addrmode g a rs) (eval_addrmode g a rs').
  Proof with eauto 10 with val_renamings reg_renamings ge_renamings.
    intros.
    unfold eval_addrmode.
    destruct a, base, ofs, const; autounfold with renamings;
    try destruct p; try destruct p0;
    try match goal with
        | [|- context[match ?Expr with _ => _ end]] =>
          destruct Expr
        end...
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
  
      Lemma compare_floats32_ren:
      forall f rs rs' v1 v2 v1' v2'
        (Hval_obs: val_obs f v1 v1')
        (Hval_obs': val_obs f v2 v2')
        (Hrs_ren: regset_ren f rs rs'),
        regset_ren f (compare_floats32 v1 v2 rs)
                   (compare_floats32 v1' v2' rs').
    Proof with eauto with reg_renamings.
      intros.
      unfold compare_floats32;
        destruct v1; inversion Hval_obs; subst;
        destruct v2; inversion Hval_obs'; subst...
      admit.
    Admitted.
    
    Lemma compare_floats_ren:
      forall f rs rs' v1 v2 v1' v2'
        (Hval_obs: val_obs f v1 v1')
        (Hval_obs': val_obs f v2 v2')
        (Hrs_ren: regset_ren f rs rs'),
        regset_ren f (compare_floats v1 v2 rs)
                   (compare_floats v1' v2' rs').
    Proof with eauto with reg_renamings.
      intros.
      unfold compare_floats;
        destruct v1; inversion Hval_obs; subst;
        destruct v2; inversion Hval_obs'; subst...
      admit.
    Admitted.
    
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
         compare_ints_ren : reg_renamings.
    Hint Resolve val_obs_addrmode val_obs_testcond : val_renamings.


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

    Lemma alloc_obs_eq:
      forall f m m' sz m2 m2' b b'
        (Hobs_eq: mem_obs_eq f m m')
        (Halloc: Mem.alloc m 0 sz = (m2, b))
        (Halloc': Mem.alloc m' 0 sz = (m2', b')),
      exists f',
        f' b = Some b' /\
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
                 match - Z.pos_sub (Mem.nextblock m') (Mem.nextblock m) with
                 | 0 => Z.pos b0
                 | Z.pos y' => Z.pos (b0 + y')
                 | Z.neg y' => Z.pos_sub b0 y'
                 end) = Some b0 /\
            f
              (Z.to_pos
                 match - Z.pos_sub (Mem.nextblock m') (Mem.nextblock m) with
                 | 0 => Z.pos b0
                 | Z.pos y' => Z.pos (b0 + y')
                 | Z.neg y' => Z.pos_sub b0 y'
                 end) = None) /\
        (Mem.nextblock m = Mem.nextblock m' ->
         (forall b1 b3 : block, f b1 = Some b3 -> b1 = b3) ->
         forall b1 b0 : block, f' b1 = Some b0 -> b1 = b0).
    Proof.
      intros.
      exists (fun b => if valid_block_dec m b then f b else
                 if valid_block_dec m2 b then Some b' else None).
      split.
      { destruct (valid_block_dec m b); simpl.
        apply Mem.alloc_result in Halloc.
        unfold Mem.valid_block in *.
        subst.
        exfalso;
          by apply Pos.lt_irrefl in v.
        destruct (valid_block_dec m2 b); first by reflexivity.
        apply Mem.valid_new_block in Halloc;
          by exfalso.        
      } split.
      { constructor.
        - (*weak_mem_obs_eq*)
          constructor.
          + (*domain_invalid*)
            intros b1 Hinvalid.
            assert (Hinvalid0: ~ Mem.valid_block m b1)
              by (intro; eapply Mem.valid_block_alloc in H; eauto).
            destruct (valid_block_dec m b1); try by exfalso.
            destruct (valid_block_dec m2 b1); try by exfalso.
            reflexivity.
          + (*domain_valid*)
            intros b1 Hvalid.
            (* by case analysis on whether this is the fresh block or an older one*)
            pose proof (Mem.valid_block_alloc_inv _ _ _ _ _ Halloc _ Hvalid) as H.
            destruct H as [Heq | Hvalid0].
            * subst.
              assert (Hinvalid := Mem.fresh_block_alloc _ _ _ _ _ Halloc).
              destruct (valid_block_dec m b); try by exfalso.
              destruct (valid_block_dec m2 b); try by exfalso.
              simpl; eexists; reflexivity.
            * destruct (valid_block_dec m b1); try by exfalso.
              simpl;
                by apply (domain_valid (weak_obs_eq Hobs_eq)).
          + (*Codomain valid*)
            intros b1 b2 Hmapped.
            destruct (valid_block_dec m b1); simpl in *.
            * apply (codomain_valid (weak_obs_eq Hobs_eq)) in Hmapped.
              eapply Mem.valid_block_alloc; eauto.
            * destruct (valid_block_dec m2 b1); simpl in *; try discriminate.
              inv Hmapped.
              eapply Mem.valid_new_block;
                by eauto.
          + (* injective *)
            intros b1 b1' b2 Hf1 Hf1'.
            destruct (valid_block_dec m b1); simpl in *.
            * destruct (valid_block_dec m b1'); simpl in *;
              first by (eapply (injective (weak_obs_eq Hobs_eq)); eauto).
              exfalso.
              destruct (valid_block_dec m2 b1'); simpl in *; try discriminate.
              inv Hf1'.            
              apply (codomain_valid (weak_obs_eq Hobs_eq)) in Hf1.
              apply Mem.fresh_block_alloc in Halloc'.
              auto.
            * destruct (valid_block_dec m b1'); simpl in *.
              destruct (valid_block_dec m2 b1); simpl in *; try discriminate.
              inv Hf1.
              apply (codomain_valid (weak_obs_eq Hobs_eq)) in Hf1'.
              apply Mem.fresh_block_alloc in Halloc';
                by auto.
              destruct (valid_block_dec m2 b1); simpl in *; try discriminate.
              destruct (valid_block_dec m2 b1'); simpl in *; try discriminate.
              inv Hf1; inv Hf1'.
              eapply Mem.valid_block_alloc_inv in v0; eauto.
              eapply Mem.valid_block_alloc_inv in v; eauto.
              destruct v, v0; subst; eauto; try by exfalso.
          + (* m permissions are higher than m' permissions *)
            intros. erewrite alloc_perm_eq by eauto.
            apply permissions.po_refl.
        - constructor;
          first by (intros; erewrite <- alloc_perm_eq; eauto).
          intros.
          destruct (valid_block_dec m b1); simpl in *.
          + erewrite <- val_at_alloc_1; eauto.
            erewrite <- val_at_alloc_1 with (m' := m2')
              by (eauto; eapply (codomain_valid (weak_obs_eq Hobs_eq)); eauto).
            assert (Heq := permission_at_alloc_1 ofs Halloc v).
            unfold permissions.permission_at in Heq.
            pose proof (val_obs_eq (strong_obs_eq Hobs_eq) _ ofs Hrenaming).
            unfold Mem.perm in *.
            rewrite Heq in H.
            specialize (H Hperm).
            eapply memval_obs_eq_incr; eauto.
            destruct (valid_block_dec m b1); try by exfalso.
            simpl; auto.
            intros b1' b2' Hf'.
            destruct (valid_block_dec m b1'); simpl. auto.
            apply (domain_invalid (weak_obs_eq Hobs_eq)) in n; by congruence.
          + destruct (valid_block_dec m2 b1); simpl in *; try discriminate.
            inv Hrenaming.
            eapply Mem.valid_block_alloc_inv in v; eauto.
            destruct v as [? | ?]; try by exfalso.
            subst.
            erewrite val_at_alloc_2; eauto.
            erewrite val_at_alloc_2; eauto.
            constructor.
      } split.
      { intros ? ? ?.
        destruct (valid_block_dec m b0); simpl; auto.
        apply (domain_invalid (weak_obs_eq Hobs_eq)) in n; by congruence.
      } split.
      { intros ? ? Hf Hf'.
        destruct (valid_block_dec m b1); simpl in *; try congruence.
        destruct (valid_block_dec m2 b1); simpl in *; try congruence.
        inv Hf'.
        split; auto.
        intro Hcontra.
        apply Mem.fresh_block_alloc in Halloc';
          auto.
      } split.
      { left. exists 1%positive.
        erewrite Mem.nextblock_alloc; eauto.
        erewrite Mem.nextblock_alloc with (m2 := m2'); eauto.
        do 2 rewrite Pplus_one_succ_r; split; reflexivity.
      } split.
      { intros b1 Hvalid2' Hinvalid'.
        eapply Mem.valid_block_alloc_inv in Hvalid2'; eauto.
        destruct Hvalid2'; subst; try by exfalso.
        assert (Hle: (Mem.nextblock m <= Mem.nextblock m')%positive)
          by admit. (*pigeon hole or extra invariant *)
        match goal with
        | [|- context[match proj_sumbool (valid_block_dec ?M ?Expr) with _ => _ end]] =>
          destruct (valid_block_dec M Expr)
        end.
        - exfalso.
          apply Pos.lt_eq_cases in Hle.
          destruct Hle as [Hlt | Heq].
          +  rewrite Z.pos_sub_gt in v; auto.
             simpl in v.
             unfold Mem.valid_block, Plt in *.
             rewrite <- Pos.le_nlt in Hinvalid'.
             assert (H := le_sub Hlt Hinvalid').
             erewrite Pos.le_nlt in H.
             auto.
          + rewrite Heq in v.
            rewrite Z.pos_sub_diag in v. simpl in v.
            unfold Mem.valid_block in *.
            rewrite Heq in v.
            auto.
        - simpl.
          match goal with
          | [|- context[match proj_sumbool (valid_block_dec ?M ?Expr) with _ => _ end]] =>
            destruct (valid_block_dec M Expr)
          end; simpl.
          + split; auto.
            apply (domain_invalid (weak_obs_eq Hobs_eq)); auto.
          + exfalso.
            apply Mem.alloc_result in Halloc'. subst b'.
            apply Pos.lt_eq_cases in Hle.
            destruct Hle as [Hlt | Heq]. 
            * rewrite Z.pos_sub_gt in n0; auto.
              simpl in n0.
              unfold Mem.valid_block, Plt in *.
              rewrite <- Pos.le_nlt in n0.
              erewrite Mem.nextblock_alloc in n0 by eauto.
              clear - Hlt n0.
              assert (Hcontra := lt_sub_bound Hlt).
              erewrite Pos.le_nlt in n0. auto.
            * rewrite Heq in n0.
              rewrite Z.pos_sub_diag in n0. simpl in n0.
              unfold Mem.valid_block, Plt in *.
              rewrite <- Heq in n0.
              erewrite Mem.nextblock_alloc with (m2 := m2) in n0 by eauto.
              zify; omega.
      }
      { intros Hnext Hid b1 b2.
        destruct (valid_block_dec m b1); simpl; auto.
        destruct (valid_block_dec m2 b1); simpl; intros; try discriminate.
        inv H.
        assert (b1 = b).
        { clear - Halloc n v.
          unfold Mem.valid_block, Plt in *.
          erewrite Mem.nextblock_alloc in v; eauto.
          rewrite <- Pos.le_nlt in n.
          apply Pos.lt_eq_cases in n; destruct n.
          exfalso. zify. omega.
          rewrite H in v.
          apply Mem.alloc_result in Halloc; subst; auto.
        } subst b1.
        apply Mem.alloc_result in Halloc'. subst.
        apply Mem.alloc_result in Halloc; subst; auto.
      }
    Admitted. 

    
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
       forall b1 b0 : block, f' b1 = Some b0 -> b1 = b0).
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
           end.
    (* Cleaning up some cases manually, to avoid overcomplicating automation*)
    apply regset_ren_set.
    apply regset_ren_undef.
    apply regset_ren_set...
    apply val_obs_add...
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
    apply val_obs_add...
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
    (* Free case *)
    pose proof (Mem.nextblock_free _ _ _ _ _ Heqo1) as Hnb.
    eapply mem_free_obs in Heqo1...
    destruct Heqo1 as [m2' [Hfree' ?]].
    pose proof (Mem.nextblock_free _ _ _ _ _ Hfree') as Hnb'.
    rewrite Hfree'.
    eapply loadv_val_obs with
    (f := f) (mf := m') (vptr2 := Val.add (Vptr b2 i) (Vint ofs_ra)) in Heqo;
      eauto with val_renamings reg_renamings;
      destruct Heqo as [? [Hload' ?]].
    eapply loadv_val_obs with
    (f := f) (mf := m') (vptr2 := Val.add (Vptr b2 i) (Vint ofs_link)) in Heqo0;
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
    eapply loadv_val_obs in H0...
    destruct H0 as [arg' [Hloadv' Hval_obs]].
    exists arg'; split; auto.
    econstructor; eauto.
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
      eapply extcall_arg_reg in H2; eauto.
      destruct H2 as [arg' [Harg Hval_obs]].
      exists (arg' :: args'); split;
      constructor; eauto.
  Qed.

   Lemma load_frame_store_args_rec_obs:
        forall f m m2 m' stk stk' args args' tys ofs
          (Hmem_obs_eq: mem_obs_eq f m m')
          (Hargs: val_obs_list f args args')
          (Hf: f stk = Some stk')
          (Hload_frame: load_frame.store_args_rec m stk ofs args tys = Some m2),
        exists m2',
          load_frame.store_args_rec m' stk' ofs args' tys = Some m2' /\
          mem_obs_eq f m2 m2'.
      Proof with eauto with val_renamings reg_renamings.
        intros.
        generalize dependent tys.
        generalize dependent args'.
        generalize dependent ofs.
        generalize dependent m'.
        generalize dependent m.
        induction args; intros.
        - unfold load_frame.store_args in *.
          simpl in *. destruct tys; intros; try discriminate.
          inv Hargs; inv Hload_frame.
          simpl. eexists; split; eauto.
        - unfold load_frame.store_args in *.
          inv Hargs.
          destruct tys; simpl in *; try discriminate;
          destruct t0;
          match goal with
          | [H: match ?Expr with _ => _ end = _ |- _] =>
            destruct Expr eqn:Hload_frame_rec
          end; try discriminate; subst;
          unfold load_frame.store_stack in *;
          try( eapply storev_val_obs in Hload_frame_rec;
               eauto with val_renamings reg_renamings;
               destruct Hload_frame_rec as [mf' [Hstorev' Hobs_eq']];
               rewrite Hstorev';
               eapply IHargs; eauto).
          repeat match goal with
                 | [H: match ?Expr with _ => _ end = _ |- _] =>
                   destruct Expr eqn:?
                 end; try discriminate; subst.
          inversion H1; subst.
          eapply storev_val_obs in Heqo...
          destruct Heqo as [m0' [Hstore0' Hmem_obs_eq0']].
          eapply storev_val_obs in Heqo0...
          destruct Heqo0 as [m2' [Hstore' Hmem_obs_eq']].
          rewrite Hstore0' Hstore'.
          eauto.
      Qed.
      
      Lemma load_frame_store_args_obs:
        forall f m m2 m' stk stk' args args' tys
          (Hmem_obs_eq: mem_obs_eq f m m')
          (Hargs: val_obs_list f args args')
          (Hf: f stk = Some stk')
          (Hload_frame: load_frame.store_args m stk args tys = Some m2),
        exists m2',
          load_frame.store_args m' stk' args' tys = Some m2' /\
          mem_obs_eq f m2 m2'.
      Proof.
        intros.
        unfold load_frame.store_args in *.
        eapply load_frame_store_args_rec_obs; eauto.
      Qed.

      Lemma load_frame_store_args_rec_nextblock:
        forall args m m2 stk ofs tys
          (Hload_frame: load_frame.store_args_rec m stk ofs args tys = Some m2),
          Mem.nextblock m2 = Mem.nextblock m.
      Proof.
        intro args.
        induction args; intros; simpl in *.
        destruct tys; inv Hload_frame; auto.
        destruct tys; try discriminate;
        destruct t0;
        repeat match goal with
               | [H: match ?Expr with _ => _ end = _ |- _] =>
                 destruct Expr eqn:?; try discriminate;
                   unfold load_frame.store_stack in *
               | [H: Mem.storev _ _ _ _ = _ |- _] =>
                 eapply nextblock_storev in H
               | [H: ?Expr = ?Expr2 |- context[?Expr2]] =>
                 rewrite <- H
               end;
        eauto.
      Qed.
      
      Lemma load_frame_store_nextblock:
        forall m m2 stk args tys
          (Hload_frame: load_frame.store_args m stk args tys = Some m2),
          Mem.nextblock m2 = Mem.nextblock m.
      Proof.
        intros.
        unfold load_frame.store_args in *.
        eapply load_frame_store_args_rec_nextblock; eauto.
      Qed.
      
  Lemma corestep_obs_eq:
    forall (cc cf cc' : Asm_coop.state) (mc mf mc' : mem) f fg,
      mem_obs_eq f mc mf ->
      core_inj f cc cf ->
      (forall b1 b2, fg b1 = Some b2 -> b1 = b2) ->
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
  Proof with (eauto with renamings reg_renamings val_renamings).
    intros cc cf cc' mc mf mc' f fg Hobs_eq Hcore_inj Hfg Hge_wd Hincr Hcorestep.
    destruct cc as [rs loader | |]; simpl in *;
    destruct cf as [rsF loaderF | |]; try by exfalso.
    - destruct Hcore_inj as [Hrs_ren Hloader_ren].
      inversion Hcorestep; subst; try (by exfalso).
      + assert (Hpc' := get_reg_ren PC Hrs_ren H1).
        destruct Hpc' as [v' [Hpc' Hpc_obs]].
        inversion Hpc_obs; subst. rewrite <- H0 in Hpc_obs.
        assert (Hfun := find_funct_ptr_ren Hfg Hge_wd Hincr Hpc_obs H2); subst b2.
        destruct (exec_instr_ren _ _ Hobs_eq Hrs_ren Hfg Hge_wd Hincr H7)
          as (f' & rsF' & mF' & Hexec' & Hrs_ren' & Hobs_eq' & Hincr' & Hsep
              & Hnextblocks & Hinverse & Hid_extend).
        exists (State rsF' loaderF), mF', f'.
        repeat match goal with
               | [ |- _ /\ _] =>
                 split; simpl; eauto with renamings reg_renamings
               end.
        econstructor...
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
    - destruct Hcore_inj as [Hf [Hargs [? ?]]]; subst.
      inversion Hcorestep; subst.
      destruct (Mem.alloc mf 0 (4*z)) as [mf' stk'] eqn:Halloc'.
      destruct (alloc_obs_eq Hobs_eq H7 Halloc') as
          (f' & Hf' & Hmem_obs_eq' & Hincr' & Hsep & Hnextblock & Hinverse & Hid).
      assert (regset_ren f'
                         ((((Pregmap.init Vundef) # PC <- (Vptr f0 Int.zero)) # RA <- Vzero)
                            # ESP <- (Vptr stk Int.zero))
                         ((((Pregmap.init Vundef) # PC <- (Vptr f1 Int.zero)) # RA <- Vzero)
                            # ESP <- (Vptr stk' Int.zero))).
      { eapply regset_ren_set...
        eapply regset_ren_set.
        eapply regset_ren_set...
        apply regset_ren_init...
        unfold Vzero...
      }
      assert (load_frame.args_len_rec args0 tys0 = Some z).
      { clear - Hargs H6.
        generalize dependent tys0.
        generalize dependent args0.
        generalize dependent z.
        induction args; intros;
        inversion Hargs; subst.
        simpl. destruct tys0; simpl in *; inv H6; auto.
        destruct tys0. simpl in *.
        discriminate.
        simpl in *; destruct t0; 
        destruct (load_frame.args_len_rec args tys0) eqn:?;
                 try discriminate; 
        try (specialize (IHargs _ _ H3 _ Heqo);
              rewrite IHargs; auto);
        destruct a; inv H1; try discriminate;
        auto.
      }
      assert (Hobs_list: val_obs_list f' args args0)
        by (eauto using val_obs_list_incr).
      assert (Hnb := load_frame_store_nextblock _ _ _ _ H8).
      eapply load_frame_store_args_obs in H8; eauto.
      destruct H8 as [m2' [Hload_frame' Hobs_eq']].
      assert (Hnb' := load_frame_store_nextblock _ _ _ _ Hload_frame').

      exists (State ((((Pregmap.init Vundef) # PC <- (Vptr f1 Int.zero)) # RA <- Vzero)
                  # ESP <- (Vptr stk' Int.zero)) (mk_load_frame stk' retty0)), m2', f'.
      unfold Mem.valid_block in *.
      rewrite Hnb Hnb'.
      repeat match goal with
             | [ |- _ /\ _] =>
               split; simpl; eauto
             end.
      econstructor; eauto.
    - inversion Hcorestep; by exfalso.
  Qed.
        
End X86Inj.    






