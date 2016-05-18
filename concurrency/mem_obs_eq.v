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
(** ** Injections between memories *)
Module MemObsEq.

  Import SEM. 

  (* A compcert injection would not work because it allows permissions to go up *)
  (* Moreover, we require that undefined values are matched by the target memory,
     unlike compcert injections *)
  
  (** Weak injection between memories *)
  Record weak_mem_obs_eq (f : meminj) (mc mf : M) :=
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

  Inductive memval_obs_eq (f : meminj) : memval -> memval -> Prop :=
  | memval_obs_byte : forall n : byte,
      memval_obs_eq f (Byte n) (Byte n)
  | memval_obs_frag : forall (v1 v2 : val) (q : quantity) (n : nat)
                        (Hval_obs: val_obs f v1 v2),
      memval_obs_eq f (Fragment v1 q n) (Fragment v2 q n)
  | memval_obs_undef : memval_obs_eq f Undef Undef.
  
  (** Strong injection between memories *)
  Record mem_obs_eq (f : meminj) (mc mf : M) :=
    {
      weak_obs_eq : weak_mem_obs_eq f mc mf;
      perm_obs_strong :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z)),
          Mem.perm_order''
            (permission_at mf b2 ofs Cur)
            (permission_at mc b1 ofs Cur);
      val_obs_eq :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z))
          (Hperm: Mem.perm mc b1 ofs Cur Readable),
          memval_obs_eq f (Maps.ZMap.get ofs mc.(Mem.mem_contents)#b1)
                        (Maps.ZMap.get ofs mf.(Mem.mem_contents)#b2)}.

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
    destruct Hobs_eq as [Hweak HpermStrong Hval].
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
      eapply po_trans;
        by eauto.
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

  (* Don't really care about this right now*)
  Lemma mem_inj_dillute:
    forall mc mf f,
      Mem.mem_inj f mc mf ->
      Mem.mem_inj f mc (makeCurMax mf).
  Admitted.


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
      (* (HmaxF: max_inv mf) *)
      (Hinj: mem_obs_eq f mc mf),
    exists v2,
      Mem.load chunk mf b2 ofs = Some v2 /\
      val_obs f v1 v2.
  Proof.
  Admitted.

End MemObsEq.
