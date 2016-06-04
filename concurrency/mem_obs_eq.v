Require Import compcert.lib.Axioms.
Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.dry_context.

Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).

Module MemoryWD.
  
(** Valid memories are the ones that do not contain any dangling pointers*)
Definition valid_mem m :=
  forall b,
    Mem.valid_block m b ->
    forall ofs mv,
      Maps.ZMap.get ofs (Mem.mem_contents m) # b = mv ->
      match mv with
      | Fragment v q n =>
        mem_wd.val_valid v m
      | _ => True
      end.

Definition valid_val (f: meminj) (v : val) : Prop :=
  match v with
  | Vptr b _ =>
    exists b', f b = Some (b',0%Z)
  | _ => True
  end.

Definition valid_memval (f: meminj) (mv : memval) : Prop :=
  match mv with
  | Fragment v _ _ =>
    valid_val f v
  | _ => True
  end.

Definition domain_meminj (f: meminj) m :=
  forall b, Mem.valid_block m b <-> isSome (f b).

Lemma valid_val_incr:
  forall f f' v
    (Hvalid: valid_val f v)
    (Hincr: inject_incr f f'),
    valid_val f' v.
Proof.
  intros.
  unfold valid_val in *.
  destruct v; auto.
  destruct Hvalid as [? Hf].
  specialize (Hincr _ _ _ Hf).
    by eexists; eauto.
Qed.

Lemma restrPermMap_domain:
  forall f m p (Hlt: permMapLt p (getMaxPerm m)),
    domain_meminj f m <-> domain_meminj f (restrPermMap Hlt).
Proof.
  intros.
  unfold domain_meminj.
  split; intros; specialize (H b);
  erewrite restrPermMap_valid in *;
    by auto.
Qed.

Lemma restrPermMap_val_valid:
  forall m p (Hlt: permMapLt p (getMaxPerm m)) v,
    mem_wd.val_valid v m <-> mem_wd.val_valid v (restrPermMap Hlt).
Proof.
  intros; split; unfold mem_wd.val_valid;
    by destruct v.
Qed.

Lemma restrPermMap_mem_valid :
  forall m p (Hlt: permMapLt p (getMaxPerm m)),
    valid_mem m <-> valid_mem (restrPermMap Hlt).
Proof.
  intros.
  split; intros Hvalid b;
  specialize (Hvalid b);
  erewrite restrPermMap_valid in *; simpl; intros Hb ofs mv Hmv;
  specialize (Hvalid Hb ofs mv Hmv);
  destruct mv; auto.
Qed.

End MemoryWD.

Module MemoryLemmas.

  (*TODO: see if we can reuse that for gsoMem_obs_eq.*)
  Lemma store_contents_other:
    forall m m' b b' ofs ofs' v chunk
      (Hstore: Mem.store chunk m b ofs v = Some m')
      (Hstable: ~ Mem.perm m b' ofs' Cur Writable),
      Maps.ZMap.get ofs' (Mem.mem_contents m') # b' =
      Maps.ZMap.get ofs' (Mem.mem_contents m) # b'.
  Proof.
    intros.
    erewrite Mem.store_mem_contents; eauto.
    simpl.
    destruct (Pos.eq_dec b b') as [Heq | Hneq];
      [| by erewrite Maps.PMap.gso by auto].
    subst b'.
    rewrite Maps.PMap.gss.
    destruct (Z_lt_le_dec ofs' ofs) as [Hlt | Hge].
    erewrite Mem.setN_outside by (left; auto);
      by reflexivity.
    destruct (Z_lt_ge_dec
                ofs' (ofs + (size_chunk chunk)))
      as [Hlt | Hge'].
    (* case the two addresses coincide - contradiction*)
    apply Mem.store_valid_access_3 in Hstore.
    unfold Mem.valid_access in Hstore. simpl in Hstore.
    destruct Hstore as [Hcontra _].
    unfold Mem.range_perm in Hcontra.
    specialize (Hcontra ofs' (conj Hge Hlt));
      by exfalso.
    erewrite Mem.setN_outside by (right; rewrite size_chunk_conv in Hge';
                                    by rewrite encode_val_length);
      by auto.
  Qed.

End MemoryLemmas.

(** ** Injections on values*)
Module ValObsEq.
  Import MemoryWD.
  
  (** Strong injections on values *)
  Inductive val_obs (mi : meminj) : val -> val -> Prop :=
    obs_int : forall i : int, val_obs mi (Vint i) (Vint i)
  | obs_long : forall i : int64, val_obs mi (Vlong i) (Vlong i)
  | obs_float : forall f : Floats.float,
      val_obs mi (Vfloat f) (Vfloat f)
  | obs_single : forall f : Floats.float32,
      val_obs mi (Vsingle f) (Vsingle f)
  | obs_ptr : forall (b1 b2 : block) (ofs : int),
      mi b1 = Some (b2,0%Z) ->
      val_obs mi (Vptr b1 ofs) (Vptr b2 ofs)
  | obs_undef : val_obs mi Vundef Vundef.

  (** Strong injections on memory values*)
  Inductive memval_obs_eq (f : meminj) : memval -> memval -> Prop :=
  | memval_obs_byte : forall n : byte,
      memval_obs_eq f (Byte n) (Byte n)
  | memval_obs_frag : forall (v1 v2 : val) (q : quantity) (n : nat)
                        (Hval_obs: val_obs f v1 v2),
      memval_obs_eq f (Fragment v1 q n) (Fragment v2 q n)
  | memval_obs_undef : memval_obs_eq f Undef Undef.

  
  Inductive val_obs_list (mi : meminj) : seq val -> seq val -> Prop :=
    val_obs_list_nil : val_obs_list mi [::] [::]
  | val_obs_list_cons : forall (v v' : val) (vl vl' : seq val),
                       val_obs mi v v' ->
                       val_obs_list mi vl vl' ->
                       val_obs_list mi (v :: vl) (v' :: vl').

  Lemma val_obs_trans:
    forall (v v' v'' : val) (f f' f'' : meminj),
      val_obs f v v'' ->
      val_obs f' v v' ->
      (forall b b' b'' : block,
          f b = Some (b'', 0%Z) ->
          f' b = Some (b', 0%Z) ->
          f'' b' = Some (b'', 0%Z)) -> 
      val_obs f'' v' v''.
  Proof.
    intros v v' v'' f f' f'' Hval'' Hval' Hf.
    inversion Hval'; subst; inversion Hval''; subst;
      by (constructor; eauto).
  Qed.

  Lemma memval_obs_trans:
    forall (v v' v'' : memval) (f f' f'' : meminj),
      memval_obs_eq f v v'' ->
      memval_obs_eq f' v v' ->
      (forall b b' b'' : block,
          f b = Some (b'', 0%Z) ->
          f' b = Some (b', 0%Z) ->
          f'' b' = Some (b'', 0%Z)) -> 
      memval_obs_eq f'' v' v''.
  Proof.
    intros v v' v'' f f' f'' Hval'' Hval' Hf.
    inversion Hval'; subst; inversion Hval''; subst;
    try constructor.
    eapply val_obs_trans;
      by eauto.
  Qed.
 
  Lemma val_obs_list_trans:
    forall (vs vs' vs'' : seq val) (f f' f'' : meminj),
      val_obs_list f vs vs'' ->
      val_obs_list f' vs vs' ->
      (forall b b' b'' : block,
          f b = Some (b'', 0%Z) ->
          f' b = Some (b', 0%Z) ->
          f'' b' = Some (b'', 0%Z)) ->
      val_obs_list f'' vs' vs''.
  Proof.
    intros vs vs' vs'' f f' f'' Hobs Hobs' Hf.
    generalize dependent vs''.
    induction Hobs'; subst; intros;
    inversion Hobs; subst. constructor.
    constructor; auto.
      by eapply val_obs_trans; eauto.
  Qed.

  (** Two values that are equal are related by the id injection on a valid memory*)
  Lemma val_obs_id:
    forall f v
      (Hvalid: valid_val f v)
      (Hid: forall b b', f b = Some (b',0%Z) -> b = b'),
      val_obs f v v.
  Proof.
    intros.
    destruct v; constructor.
    destruct Hvalid as [b' Hf].
    specialize (Hid _ _ Hf);
      by subst.
  Qed.
  
  Lemma memval_obs_eq_id:
    forall f mv
      (Hvalid: valid_memval f mv)
      (Hid: forall b b', f b = Some (b',0%Z) -> b = b'),
                    memval_obs_eq f mv mv.
  Proof.
    intros.
    destruct mv;
    econstructor;
    eapply val_obs_id;
      by eauto.
  Qed.

End ValObsEq.
  
(** ** Injections between memories *)
Module MemObsEq.

  Import ValObsEq SEM MemoryWD.

  (* A compcert injection would not work because it allows permissions to go up *)
  (* Moreover, we require that undefined values are matched by the target memory,
     unlike compcert injections *)
  
  (** Weak injection between memories *)
  Record weak_mem_obs_eq (f : meminj) (mc mf : mem) :=
    {
      domain_invalid: forall b, ~(Mem.valid_block mc b) -> f b = None;
      domain_valid: forall b, Mem.valid_block mc b -> exists b', f b = Some (b',0%Z);
      codomain_valid: forall b1 b2, f b1 = Some (b2,0%Z) -> Mem.valid_block mf b2;
      injective: forall b1 b1' b2, f b1 = Some (b2,0%Z) ->
                              f b1' = Some(b2,0%Z) ->
                              b1 = b1';
      perm_obs_weak :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z)),
          Mem.perm_order''
            (permission_at mc b1 ofs Cur)
            (permission_at mf b2 ofs Cur)}.

 

  (** Strong injection between memories *)
  Record strong_mem_obs_eq (f : meminj) (mc mf : mem) :=
    { perm_obs_strong :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z)),
            permission_at mf b2 ofs Cur =
            (permission_at mc b1 ofs Cur);
      val_obs_eq :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z))
          (Hperm: Mem.perm mc b1 ofs Cur Readable),
          memval_obs_eq f (Maps.ZMap.get ofs mc.(Mem.mem_contents)#b1)
                        (Maps.ZMap.get ofs mf.(Mem.mem_contents)#b2)}.

  
  (** Strong injection between memories *)
  Record mem_obs_eq (f : meminj) (mc mf : mem) :=
    { weak_obs_eq : weak_mem_obs_eq f mc mf;
      strong_obs_eq : strong_mem_obs_eq f mc mf }.

  Lemma weak_obs_eq_domain_inj:
    forall f m m',
      weak_mem_obs_eq f m m' ->
      domain_meminj f m.
  Proof.
    intros f m m' Hobs_eq.
    destruct Hobs_eq.
    intros b.
    split; intros Hb.
    specialize (domain_valid0 _ Hb).
    destruct (domain_valid0) as [? H].
    rewrite H;
      by auto.
    destruct (valid_block_dec m b); auto.
    apply domain_invalid0 in n.
    rewrite n in Hb;
      by exfalso.
  Qed.

  Corollary mem_obs_eq_domain_inj:
    forall f m m',
      mem_obs_eq f m m' ->
      domain_meminj f m.
  Proof.
    intros f m m' H; destruct H;
    eapply weak_obs_eq_domain_inj;
      by eauto.
  Qed.
  
  Definition max_inv mf := forall b ofs, Mem.valid_block mf b ->
                                    permission_at mf b ofs Max = Some Freeable.
  
  Lemma sim_valid_access:
    forall (mf m1f : mem) 
      (b1 b2 : block) (ofs : int)
      (Hm1f: m1f = makeCurMax mf)
      (HmaxF: max_inv mf)
      (Hvalidb2: Mem.valid_block mf b2)
      (Halign: (4 | Int.intval ofs)%Z),
      Mem.valid_access m1f Mint32 b2 (Int.intval ofs) Freeable.
  Proof.          
    unfold Mem.valid_access. simpl. split; try assumption.
    unfold Mem.range_perm. intros ofs0 Hbounds. subst m1f.
    specialize (HmaxF _ ofs0 Hvalidb2).
    unfold Mem.perm.
    assert (Hperm := makeCurMax_correct mf b2 ofs0 Cur).
    rewrite HmaxF in Hperm.
    unfold permission_at in Hperm.
    unfold Mem.perm.
    rewrite <- Hperm.
    simpl;
      by constructor.
  Qed.

  Lemma mf_align :
    forall (m : mem) (f : meminj) (b1 b2 : block) (delta : Z) (chunk : memory_chunk)
      (ofs : Z) (p : permission),
      f b1 = Some (b2, 0%Z) ->
      Mem.range_perm m b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | 0%Z)%Z.
  Proof.
    intros.
      by apply mem_wd.align_chunk_0.
  Qed.

  Lemma weak_mem_obs_eq_f :
    forall mc mf f b1 b2 delta,
      weak_mem_obs_eq f mc mf ->
      f b1 = Some (b2,delta) ->
      delta = 0%Z.
  Proof.
    intros mc mf f b1 b2 delta Hweak Hf.
    destruct (valid_block_dec mc b1) as [Hvalid | Hinvalid].
    apply (domain_valid Hweak) in Hvalid.
    destruct Hvalid as [? Hf'].
    rewrite Hf' in Hf.
    inversion Hf;
      by subst.
    apply (domain_invalid Hweak) in Hinvalid.
      by congruence.
  Qed.

  Lemma val_obs_eq_inj :
    forall f v1 v2,
      val_obs f v1 v2 ->
      val_inject f v1 v2 /\
      (v1 = Vundef -> v2 = Vundef).
  Proof.
    intros f v1 v2 Hobs_eq.
    inversion Hobs_eq;
      try (split; [constructor | auto]).
    subst.
    split; try congruence.
    eapply Val.inject_ptr with (delta := 0%Z); eauto.
      by rewrite Int.add_zero.
  Qed.
  
  Lemma memval_obs_eq_inj :
    forall f mv1 mv2,
      memval_obs_eq f mv1 mv2 ->
      memval_inject f mv1 mv2
      /\ (mv1 = Undef -> mv2 = Undef).
  Proof.
    intros f mv1 mv2 Hobs_eq.
    inversion Hobs_eq;
      split; try constructor; try auto.
    inversion Hval_obs; subst; try constructor.
      by eapply val_obs_eq_inj.
        by congruence.
  Qed.
  
  Theorem mem_obs_eq_mem_inj:
    forall mc mf f,
      mem_obs_eq f mc mf ->
      max_inv mf ->
      Mem.mem_inj f mc mf.
  Proof.
    intros mc mf f Hobs_eq HmaxF.
    destruct Hobs_eq as [Hweak [HpermStrong Hval]].
    constructor.
    - intros b1 b2 delta ofs k p Hf Hperm.
      assert (delta = 0%Z)
        by (eapply (weak_mem_obs_eq_f _ Hweak Hf); eauto); subst.
      rewrite Zplus_0_r.
      specialize (HpermStrong _ _ ofs Hf).
      unfold Mem.perm in *.
      unfold permission_at in HpermStrong.
      rewrite po_oo in Hperm. rewrite po_oo.
      destruct k.
      apply (codomain_valid Hweak) in Hf.
      specialize (HmaxF _ ofs Hf). unfold permission_at in HmaxF.
      rewrite HmaxF.
      simpl;
        by constructor.
      rewrite HpermStrong. eauto.
    - intros b1 b2 delta chunk ofs p Hf _.
      assert (delta = 0%Z)
        by (eapply (weak_mem_obs_eq_f _ Hweak Hf); eauto);
        subst;
          by apply mem_wd.align_chunk_0.
    - intros b1 ofs b2 delta Hf Hreadable.
      assert (delta = 0%Z)
        by (eapply (weak_mem_obs_eq_f _ Hweak Hf); eauto);
        subst.
      specialize (Hval _ _ _ Hf Hreadable).
      rewrite Zplus_0_r.
      eapply memval_obs_eq_inj; eauto.
      
  Qed.

  Lemma memval_obs_eq_incr:
    forall (mc mf : mem) (f f': meminj) 
      (b1 b2 : block) (ofs : Z)
      (Hf': f' b1 = Some (b2, 0%Z))
      (Hincr: inject_incr f f')
      (Hobs_eq: memval_obs_eq f (Maps.ZMap.get ofs (Mem.mem_contents mc) # b1)
                              (Maps.ZMap.get ofs (Mem.mem_contents mf) # b2)),
      memval_obs_eq f' (Maps.ZMap.get ofs (Mem.mem_contents mc) # b1)
                    (Maps.ZMap.get ofs (Mem.mem_contents mf) # b2).
  Proof.
    intros.
    inversion Hobs_eq;
      constructor.
    inversion Hval_obs; subst; constructor.
    apply Hincr in H1.
      by auto.
  Qed.

  (* Don't really care about this right now*)
  (* Lemma mem_inj_dillute: *)
  (*   forall mc mf f, *)
  (*     Mem.mem_inj f mc mf -> *)
  (*     Mem.mem_inj f mc (makeCurMax mf). *)
  (* Admitted. *)


  (* Proof as in compcert*)
  Lemma proj_bytes_obs:
    forall (f : meminj) (vl vl' : seq memval),
      Coqlib.list_forall2 (memval_obs_eq f) vl vl' ->
      forall bl : seq byte,
        proj_bytes vl = Some bl -> proj_bytes vl' = Some bl.
  Proof.
    induction 1; simpl. intros. congruence.
    inversion H; subst; try congruence.
    destruct (proj_bytes al); intros.
    inversion H; subst; rewrite (IHlist_forall2 l); auto.
    congruence.
  Qed.

  Lemma proj_bytes_obs_none:
    forall (f : meminj) (vl vl' : seq memval),
      Coqlib.list_forall2 (memval_obs_eq f) vl vl' ->
      proj_bytes vl = None -> proj_bytes vl' = None.
  Proof.
    induction 1; simpl. intros.  congruence.
    inversion H; subst; try congruence.
    destruct (proj_bytes al); intros.
    discriminate.
      by rewrite (IHlist_forall2 (Logic.eq_refl _)).
  Qed.
  
  Lemma check_value_obs:
    forall f vl vl',
      Coqlib.list_forall2 (memval_obs_eq f) vl vl' ->
      forall v v' q n,
        check_value n v q vl = true ->
        val_obs f v v' -> v <> Vundef ->
        check_value n v' q vl' = true.
  Proof.
    induction 1; intros; destruct n; simpl in *; auto.
    inversion H; subst; auto.
    apply Bool.andb_true_iff in H1.
    destruct H1.
    apply Bool.andb_true_iff in H1.
    destruct H1.
    apply Bool.andb_true_iff in H1.
    destruct H1.
    apply Coqlib.proj_sumbool_true in H1.
    apply Coqlib.proj_sumbool_true in H6.
    assert (n = n0) by (apply beq_nat_true; auto). subst v1 q0 n0.
    replace v2 with v'.
    unfold Coqlib.proj_sumbool; rewrite ! Coqlib.dec_eq_true.
    rewrite <- beq_nat_refl. simpl; eauto.
    inversion H2; subst; try discriminate; inversion Hval_obs; subst; congruence.
  Qed.

  (*TODO: Lennart can you prove this lemma?*)
  Lemma proj_value_obs:
    forall f q vl1 vl2,
      Coqlib.list_forall2 (memval_obs_eq f) vl1 vl2 ->
      val_obs f (proj_value q vl1) (proj_value q vl2).
  Proof.
    intros f q vl1 v2 Hlst. unfold proj_value.
    inversion Hlst; subst. constructor.
    inversion H; subst; try constructor.
    
    destruct (check_value (size_quantity_nat q) v1 q (Fragment v1 q0 n :: al)) eqn:B.
    destruct (Val.eq v1 Vundef).
    subst v1.
    inversion Hval_obs.
    subst v2.
    destruct (check_value (size_quantity_nat q) Vundef q
                          (Fragment Vundef q0 n :: bl));
      by auto.
    erewrite check_value_obs; eauto.
    (*TODO: need a lemma about check_value being false, and obs_eq*)
    admit.
  Admitted.
  
  Lemma load_result_obs:
    forall f chunk v1 v2,
      val_obs f v1 v2 ->
      val_obs f (Val.load_result chunk v1) (Val.load_result chunk v2).
  Proof.
    intros. inversion H; destruct chunk; simpl; econstructor; eauto.
  Qed.
  
  Lemma decode_val_inject:
    forall f vl1 vl2 chunk,
      Coqlib.list_forall2 (memval_obs_eq f) vl1 vl2 ->
      val_obs f (decode_val chunk vl1) (decode_val chunk vl2).
  Proof.
    intros f vl1 vl2 chunk Hobs_eq.
    unfold decode_val.
    destruct (proj_bytes vl1) as [bl1|] eqn:PB1.
    eapply proj_bytes_obs with (vl' := vl2) in PB1; eauto.
    rewrite PB1.
    destruct chunk; constructor.
    destruct (proj_bytes vl2) eqn:PB2.
    exfalso.
    eapply proj_bytes_obs_none with (f := f) (vl := vl1) in PB1;
      eauto.
      by congruence.
      destruct chunk; try constructor;
      apply load_result_obs;
      apply proj_value_obs; auto.
  Qed.
  
  
  Lemma load_valid_block:
    forall (m : mem) (b : block) (ofs : int),
      Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.one) ->
      Mem.valid_block m b.
  Proof.
    intros m b ofs Hload.
    apply Mem.load_valid_access in Hload.
    apply Mem.valid_access_valid_block with (chunk:=Mint32) (ofs:= Int.intval ofs).
    eapply Mem.valid_access_implies; eauto.
    constructor.
  Qed.

  (*TODO: prove this, should be easy once we have the lemmas above*)
  Lemma load_val_obs:
    forall (mc mf : mem) (f:meminj)
      (b1 b2 : block) chunk (ofs : Z) v1
      (Hload: Mem.load chunk mc b1 ofs = Some v1)
      (Hf: f b1 = Some (b2, 0%Z))
      (Hobs_eq: strong_mem_obs_eq f mc mf),
    exists v2,
      Mem.load chunk mf b2 ofs = Some v2 /\
      val_obs f v1 v2.
  Proof.
  Admitted.

  (** ** Lemmas about [Mem.store] and [mem_obs_eq]*)
  
  Lemma store_val_obs:
    forall (mc mc' mf : mem) (f:meminj)
      (b1 b2 : block) chunk (ofs : Z) v1 v2
      (Hload: Mem.store chunk mc b1 ofs v1 = Some mc')
      (Hf: f b1 = Some (b2, 0%Z))
      (Hval_obs_eq: val_obs f v1 v2)
      (Hobs_eq: strong_mem_obs_eq f mc mf),
    exists mf',
      Mem.store chunk mf b2 ofs v2 = Some mf' /\
      strong_mem_obs_eq f mc' mf'.
  Proof.
    Admitted.
 
End MemObsEq.

Module CoreInjections.

  Import SEM ValObsEq.
  Class CodeInj :=
    { core_inj: meminj -> C -> C -> Prop;
      core_wd : meminj -> C -> Prop;
      core_wd_incr : forall f f' c,
          core_wd f c ->
          inject_incr f f' ->
          core_wd f' c;
      core_inj_ext: 
        forall c c' f (Hinj: core_inj f c c'),
          match at_external Sem c, at_external Sem c' with
          | Some (ef, sig, vs), Some (ef', sig', vs') =>
            ef = ef' /\ sig = sig' /\ Coqlib.list_forall2 (val_obs f) vs vs'
          | None, None => True
          | _, _ => False
          end;
      core_inj_after_ext: 
        forall c cc c' ov1 f (Hinj: core_inj f c c'),
          after_external Sem ov1 c = Some cc ->
          exists ov2 cc',
            after_external Sem ov2 c' = Some cc' /\
            core_inj f cc cc' /\
            match ov1 with
            | Some v1 => match ov2 with
                        | Some v2 => val_obs f v1 v2
                        | _ => False
                        end
            | None => match ov2 with
                     | None => True
                     | _ => False
                     end
            end;
      core_inj_halted:
        forall c c' f (Hinj: core_inj f c c'),
          match halted Sem c, halted Sem c' with
          | Some v, Some v' => val_obs f v v'
          | None, None => True
          | _, _ => False
          end;
      core_inj_init:
        forall vf arg arg' c_new f
          (Hf: val_obs_list f arg arg')
          (Hinit: initial_core Sem the_ge vf arg = Some c_new),
        exists c_new',
          initial_core Sem the_ge vf arg' = Some c_new' /\
          core_inj f c_new c_new';
      core_inj_id: forall c f,
          core_wd f c -> 
          (forall b1 b2, f b1 = Some (b2,0%Z) -> b1 = b2) ->
          core_inj f c c;
      core_inj_trans:
        forall c c' c'' (f f' f'' : meminj)
          (Hcore_inj: core_inj f c c'')
          (Hcore_inj': core_inj f' c c')
          (Hf: forall b b' b'',
              f b = Some (b'',0%Z) ->
              f' b = Some (b',0%Z) ->
              f'' b' = Some (b'',0%Z)),
          core_inj f'' c' c''
    }.

End CoreInjections.