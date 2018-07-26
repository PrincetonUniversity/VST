(** ** Memories equal up to alpha-renaming *)

Require Import compcert.lib.Axioms.
Require Import VST.concurrency.common.sepcomp. Import SepComp.

Require Import VST.concurrency.common.pos.

Require Import compcert.lib.Coqlib.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Memory.
Require Import VST.concurrency.memory_lemmas.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.semantics.
Require Import VST.sepcomp.mem_wd.

(** ** Block renamings*)
Module Renamings.
  Definition memren := block -> option block.

  Definition ren_incr f1 f2 :=
    forall (b b' : block),
      f1 b = Some b' -> f2 b = Some b'.

  Definition ren_separated (f f' : memren) m1 m2 :=
    forall (b1 b2 : block),
      f b1 = None ->
      f' b1 = Some b2 ->
      ~ Mem.valid_block m1 b1 /\ ~ Mem.valid_block m2 b2.

  Definition ren_domain_incr (f1 f2: memren) :=
    forall b,
      f1 b -> f2 b.

  (** Defining the domain of a renaming with respect to a memory*)
  Definition domain_memren (f: memren) m :=
    forall b, Mem.valid_block m b <-> isSome (f b).

  Lemma restrPermMap_domain:
    forall f m p (Hlt: permMapLt p (getMaxPerm m)),
      domain_memren f m <-> domain_memren f (restrPermMap Hlt).
  Proof.
    intros.
    unfold domain_memren.
    split; intros; specialize (H b);
      erewrite restrPermMap_valid in *;
        by auto.
  Qed.

  Lemma domain_memren_incr:
    forall f f' f'' m,
      domain_memren f' m ->
      domain_memren f'' m ->
      ren_domain_incr f f' <-> ren_domain_incr f f''.
  Proof.
    intros.
    unfold domain_memren in *;
      split; intros Hincr b Hf;
        apply Hincr in Hf;
        destruct (H b), (H0 b);
          by eauto.
  Qed.

  Lemma domain_memren_trans:
    forall f f' m m',
      domain_memren f m ->
      domain_memren f m' ->
      domain_memren f' m' ->
      domain_memren f' m.
  Proof.
    intros.
    split;
      destruct (H b), (H0 b), (H1 b); auto.
  Qed.

  Lemma ren_incr_domain_incr:
    forall f f',
      ren_incr f f' ->
      ren_domain_incr f f'.
  Proof.
    intros f f' Hincr b Hf.
    destruct (f b) as [b'|] eqn:Hfb; try by exfalso.
    specialize (Hincr b b' Hfb);
      by rewrite Hincr.
  Qed.

  Lemma ren_domain_incr_refl:
    forall f,
      ren_domain_incr f f.
  Proof.
    intros.
    unfold ren_domain_incr;
      by auto.
  Qed.

  Lemma ren_domain_incr_trans:
    forall f f' f'',
      ren_domain_incr f f' ->
      ren_domain_incr f' f'' ->
      ren_domain_incr f f''.
  Proof.
    intros.
    unfold ren_domain_incr;
      by auto.
  Qed.

  Lemma ren_incr_trans:
    forall f f' f'',
      ren_incr f f' ->
      ren_incr f' f'' ->
      ren_incr f f''.
  Proof.
    intros.
    unfold ren_incr;
      by auto.
  Qed.

  Lemma ren_incr_refl:
    forall f,
      ren_incr f f.
  Proof.
    unfold ren_incr; auto.
  Qed.

  Lemma ren_separated_refl:
    forall f m m',
      ren_separated f f m m'.
  Proof.
    unfold ren_separated.
      by congruence.
  Qed.

  (** Results about id injections*)
  Definition id_ren m :=
    fun b => if is_left (valid_block_dec m b) then Some b else None.

  Hint Unfold id_ren.

  Lemma id_ren_correct:
    forall m (b1 b2 : block), (id_ren m) b1 = Some b2 -> b1 = b2.
  Proof.
    intros. unfold id_ren in *.
    destruct (valid_block_dec m b1); simpl in *;
      by inversion H.
  Qed.

  Lemma id_ren_domain:
    forall m, domain_memren (id_ren m) m.
  Proof.
    unfold id_ren, domain_memren.
    intros.
    destruct (valid_block_dec m b); simpl;
      split; intuition.
  Qed.

  Lemma id_ren_validblock:
    forall m b
      (Hvalid: Mem.valid_block m b),
      id_ren m b = Some b.
  Proof.
    intros.
    eapply id_ren_domain in Hvalid.
    destruct (id_ren m b) eqn:Hid.
    apply id_ren_correct in Hid;
      by subst.
      by exfalso.
  Qed.

  Lemma id_ren_invalidblock:
    forall m b
      (Hinvalid: ~ Mem.valid_block m b),
      id_ren m b = None.
  Proof.
    intros.
    assert (Hnot:= iffLRn (id_ren_domain m b) Hinvalid).
    destruct (id_ren m b) eqn:Hid;
      first by exfalso.
      by reflexivity.
  Qed.

  Lemma is_id_ren :
    forall f m
      (Hdomain: domain_memren f m)
      (Hf_id: forall b1 b2, f b1 = Some b2 -> b1 = b2),
      f = id_ren m.
  Proof.
    intros. extensionality b.
    assert (Hdomain_id := id_ren_domain m).
    destruct (f b) eqn:Hf, (id_ren m b) eqn:Hid;
      try (assert (H:= id_ren_correct _ _ Hid));
      try (specialize (Hf_id b _ Hf));
      subst; auto.
    assert (Hid': ~ id_ren m b0)
      by (rewrite Hid; auto).
    assert (Hf': f b0)
      by (rewrite Hf; auto).
    apply (proj2 (Hdomain b0)) in Hf'.
    apply (iffRLn (Hdomain_id b0)) in Hid';
      by exfalso.
    assert (Hid': id_ren m b0)
      by (rewrite Hid; auto).
    assert (Hf': ~ f b0)
      by (rewrite Hf; auto).
    apply (proj2 (Hdomain_id b0)) in Hid'.
    apply (iffRLn (Hdomain b0)) in Hf';
      by exfalso.
  Qed.

  Lemma id_ren_restr:
    forall pmap m (Hlt: permMapLt pmap (getMaxPerm m)),
      id_ren m = id_ren (restrPermMap Hlt).
  Proof.
    intros.
    extensionality b.
    unfold id_ren.
    destruct (valid_block_dec m b), (valid_block_dec (restrPermMap Hlt) b); simpl; auto.
    erewrite restrPermMap_valid in n; by exfalso.
    erewrite restrPermMap_valid in v; by exfalso.
  Qed.


  Lemma incr_domain_id:
    forall m f f'
      (Hincr: ren_incr f f')
      (Hf_id: forall b b', f b = Some b' -> b = b')
      (Hdomain_f: domain_memren f' m),
      ren_incr f (id_ren m).
  Proof.
    intros.
    intros b1 b2 Hf.
    assert (b1 = b2)
      by (eapply Hf_id in Hf; by subst).
    subst b2.
    apply Hincr in Hf.
    destruct (Hdomain_f b1).
    specialize (H0 ltac:(rewrite Hf; auto)).
    assert (Hdomain_id := id_ren_domain m).
    apply Hdomain_id in H0.
    destruct (id_ren m b1) eqn:Hid; try by exfalso.
    apply id_ren_correct in Hid;
      by subst.
  Qed.

  Hint Immediate ren_incr_refl ren_separated_refl : renamings.

  Hint Resolve id_ren_correct id_ren_domain id_ren_validblock
       id_ren_invalidblock : id_renamings.

End Renamings.

(** ** Well-Defined values with respect to a renaming*)
Module ValueWD.

  Import Renamings.

  Hint Immediate ren_domain_incr_refl : wd.

  (** Valid values are the ones that have no pointers outside the domain of f*)
  Definition valid_val (f: memren) (v : val) : Prop :=
    match v with
    | Vptr b _ =>
      exists b', f b = Some b'
    | _ => True
    end.

  Inductive valid_val_list (f: memren) : seq val -> Prop :=
  | vs_nil: valid_val_list f [::]
  | vs_cons: forall v vs,
      valid_val f v ->
      valid_val_list f vs ->
      valid_val_list f (v :: vs).

  Definition valid_memval (f: memren) (mv : memval) : Prop :=
    match mv with
    | Fragment v _ _ =>
      valid_val f v
    | _ => True
    end.

  Inductive valid_memval_list (f : memren) : seq memval -> Prop :=
  |  mvs_nil : valid_memval_list f [::]
  | mvs_cons : forall (v : memval) (vs : seq memval),
      valid_memval f v ->
      valid_memval_list f vs -> valid_memval_list f (v :: vs).

  Lemma valid_val_incr:
    forall f f' v
      (Hvalid: valid_val f v)
      (Hincr: ren_domain_incr f f'),
      valid_val f' v.
  Proof.
    intros.
    unfold valid_val in *.
    destruct v; auto.
    destruct Hvalid as [? Hf].
    assert (Hfb: f b)
      by (rewrite Hf; auto).
    specialize (Hincr b Hfb).
    destruct (f' b) eqn:Hf'; try by exfalso.
      by eexists; eauto.
  Qed.

  Lemma valid_val_list_incr:
    forall f f' vs
      (Hvalid: valid_val_list f vs)
      (Hincr: ren_domain_incr f f'),
      valid_val_list f' vs.
  Proof.
    intros.
    induction vs;
      first by constructor.
    inversion Hvalid; subst.
    constructor; eauto.
    eapply valid_val_incr;
      by eauto.
  Qed.

  Lemma valid_val_domain:
    forall f f' m v,
      valid_val f v ->
      domain_memren f m ->
      domain_memren f' m ->
      valid_val f' v.
  Proof.
    intros.
    destruct v; auto.
    destruct H as [b' Hf].
    unfold domain_memren in *.
    destruct (H0 b).
    destruct (H1 b).
    rewrite Hf in H2.
    specialize (H2 ltac:(auto)).
    specialize (H3 H2).
    destruct (f' b) eqn:Hf'; try by exfalso.
    econstructor; eauto.
  Qed.

  Lemma valid_val_list_domain:
    forall f f' m vs
      (Hvalid: valid_val_list f vs)
      (Hdomain: domain_memren f m)
      (Hdomain': domain_memren f' m),
      valid_val_list f' vs.
  Proof.
    intros.
    induction vs; first by constructor.
    inversion Hvalid; subst.
    constructor; [eapply valid_val_domain|];
      by eauto.
  Qed.

  Lemma ofs_val_lt :
    forall ofs chunk v,
      ofs < ofs + Z.of_nat (length (encode_val chunk v)).
  Proof.
    destruct chunk, v; simpl; try omega;
    try (rewrite length_inj_bytes encode_int_length;
         simpl; omega);
    destruct Archi.ptr64; simpl;
      omega.
  Qed.

  (** Lemmas about the well-definedness of the various value
  constructors*)

  Lemma valid_val_int:
    forall f n,
      valid_val f (Vint n).
  Proof.
    simpl; auto.
  Qed.

  Lemma valid_val_long:
    forall f n,
      valid_val f (Vlong n).
  Proof.
    simpl; auto.
  Qed.

  Lemma valid_val_one:
    forall f, valid_val f Vone.
  Proof.
    simpl; auto.
  Qed.

  Lemma valid_val_single:
    forall f n,
      valid_val f (Vsingle n).
  Proof.
    simpl; auto.
  Qed.

  Lemma valid_val_float:
    forall f n,
      valid_val f (Vfloat n).
  Proof.
    simpl; auto.
  Qed.

  Lemma valid_val_hiword:
    forall f v,
      valid_val f (Val.hiword v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_loword:
    forall f v,
      valid_val f (Val.loword v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_add:
    forall f v1 v2,
      valid_val f v1 ->
      valid_val f v2 ->
      valid_val f (Val.add v1 v2).
  Proof.
    intros.
    destruct v1, v2; simpl in *; auto.
  Qed.

  Lemma valid_val_addl:
    forall f v1 v2,
      valid_val f v1 ->
      valid_val f v2 ->
      valid_val f (Val.addl v1 v2).
  Proof.
    intros.
    destruct v1, v2; simpl in *; auto.
  Qed.

  Lemma valid_val_offset_ptr:
    forall f v ofs,
      valid_val f v ->
      valid_val f (Val.offset_ptr v ofs).
  Proof.
    intros.
    destruct v; simpl in *; auto.
  Qed.

  Lemma valid_val_sub:
    forall f v1 v2,
      valid_val f v1 ->
      valid_val f v2 ->
      valid_val f (Val.sub v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
      destruct v2; simpl; auto.
    destruct (Archi.ptr64);
      [now simpl |
       destruct (eq_block b b0); simpl; auto].
  Qed.

  Lemma valid_val_subl:
    forall f v1 v2,
      valid_val f v1 ->
      valid_val f v2 ->
      valid_val f (Val.subl v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
      destruct v2; simpl; auto.
    destruct (Archi.ptr64);
      [destruct (eq_block b b0); simpl; auto | now simpl].
  Qed.

  Lemma valid_val_mul:
    forall f v1 v2,
      valid_val f (Val.mul v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_mulhu:
    forall f v1 v2,
      valid_val f (Val.mulhu v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_mull:
    forall f v1 v2,
      valid_val f (Val.mull v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_mullhu:
    forall f v1 v2,
      valid_val f (Val.mullhu v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_and:
    forall f v1 v2,
      valid_val f (Val.and v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_or:
    forall f v1 v2,
      valid_val f (Val.or v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_xor:
    forall f v1 v2,
      valid_val f (Val.xor v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_andl:
    forall f v1 v2,
      valid_val f (Val.andl v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_orl:
    forall f v1 v2,
      valid_val f (Val.orl v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_xorl:
    forall f v1 v2,
      valid_val f (Val.xorl v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_intoffloat:
    forall f v,
      valid_val f (Val.maketotal (Val.intoffloat v)).
  Proof.
    destruct v; simpl; auto; unfold Val.maketotal;
    unfold option_map;
    match goal with
    | [|- context[match match ?Expr with _ => _ end with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_intofsingle:
    forall f v,
      valid_val f (Val.maketotal (Val.intofsingle v)).
  Proof.
    destruct v; simpl; auto; unfold Val.maketotal;
    unfold option_map;
    match goal with
    | [|- context[match match ?Expr with _ => _ end with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_singleofint:
    forall f v,
      valid_val f (Val.maketotal (Val.singleofint v)).
  Proof.
    destruct v; simpl; auto; unfold Val.maketotal;
    unfold option_map;
    match goal with
    | [|- context[match match ?Expr with _ => _ end with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_floatofint:
    forall f v,
      valid_val f (Val.maketotal (Val.floatofint v)).
  Proof.
    destruct v; simpl; auto; unfold Val.maketotal;
    unfold option_map;
    match goal with
    | [|- context[match match ?Expr with _ => _ end with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_longoffloat:
    forall f v,
      valid_val f (Val.maketotal (Val.longoffloat v)).
  Proof.
    destruct v; simpl; auto; unfold Val.maketotal;
    unfold option_map;
    match goal with
    | [|- context[match match ?Expr with _ => _ end with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_longofsingle:
    forall f v,
      valid_val f (Val.maketotal (Val.longofsingle v)).
  Proof.
    destruct v; simpl; auto; unfold Val.maketotal;
    unfold option_map;
    match goal with
    | [|- context[match match ?Expr with _ => _ end with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_singleoflong:
    forall f v,
      valid_val f (Val.maketotal (Val.singleoflong v)).
  Proof.
    destruct v; simpl; auto; unfold Val.maketotal;
    unfold option_map;
    match goal with
    | [|- context[match match ?Expr with _ => _ end with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_floatoflong:
    forall f v,
      valid_val f (Val.maketotal (Val.floatoflong v)).
  Proof.
    destruct v; simpl; auto; unfold Val.maketotal;
    unfold option_map;
    match goal with
    | [|- context[match match ?Expr with _ => _ end with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_singleoffloat:
    forall f v,
      valid_val f (Val.singleoffloat v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_floatofsingle:
    forall f v,
      valid_val f (Val.floatofsingle v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_neg:
    forall f v,
      valid_val f (Val.neg v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_negl:
    forall f v,
      valid_val f (Val.negl v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_sign_ext:
    forall f v n,
      valid_val f (Val.sign_ext n v).
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Lemma valid_val_longofintu:
    forall f v,
      valid_val f (Val.longofintu v).
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Lemma valid_val_longofint:
    forall f v,
      valid_val f (Val.longofint v).
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Lemma valid_val_zero_ext:
    forall f v n,
      valid_val f (Val.zero_ext n v).
  Proof.
    intros.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_mulhs:
    forall f v1 v2,
      valid_val f (Val.mulhs v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_mullhs:
    forall f v1 v2,
      valid_val f (Val.mullhs v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_undef:
    forall f,
      valid_val f Vundef.
  Proof.
    simpl; auto.
  Qed.

  Lemma valid_val_shl:
    forall f v1 v2,
      valid_val f (Val.shl v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto;
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_shru:
    forall f v1 v2,
      valid_val f (Val.shru v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto;
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_shr:
    forall f v1 v2,
      valid_val f (Val.shr v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto;
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_ror:
    forall f v1 v2,
      valid_val f (Val.ror v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto;
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_shll:
    forall f v1 v2,
      valid_val f (Val.shll v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto;
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_shrlu:
    forall f v1 v2,
      valid_val f (Val.shrlu v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto;
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_shrl:
    forall f v1 v2,
      valid_val f (Val.shrl v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto;
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_rorl:
    forall f v1 v2,
      valid_val f (Val.rorl v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto;
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr
    end; simpl; auto.
  Qed.

  Lemma valid_val_addf:
    forall f v1 v2,
      valid_val f (Val.addf v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_mulf:
    forall f v1 v2,
      valid_val f (Val.mulf v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_subf:
    forall f v1 v2,
      valid_val f (Val.subf v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_divf:
    forall f v1 v2,
      valid_val f (Val.divf v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_addfs:
    forall f v1 v2,
      valid_val f (Val.addfs v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_mulfs:
    forall f v1 v2,
      valid_val f (Val.mulfs v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_subfs:
    forall f v1 v2,
      valid_val f (Val.subfs v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_divfs:
    forall f v1 v2,
      valid_val f (Val.divfs v1 v2).
  Proof.
    intros.
    destruct v1; simpl; auto;
    destruct v2; simpl; auto.
  Qed.

  Lemma valid_val_negf:
    forall f v,
      valid_val f (Val.negf v).
  Proof.
    intros.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_absf:
    forall f v,
      valid_val f (Val.absf v).
  Proof.
    intros.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_negfs:
    forall f v,
      valid_val f (Val.negfs v).
  Proof.
    intros.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_absfs:
    forall f v,
      valid_val f (Val.absfs v).
  Proof.
    intros.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_divu:
    forall f v1 v2 v,
      Val.divu v1 v2 = Some v ->
      valid_val f v.
  Proof.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    destruct (Int.eq i0 Int.zero); try discriminate.
    inv H; simpl; auto.
  Qed.

  Lemma valid_val_modu:
    forall f v1 v2 v,
      Val.modu v1 v2 = Some v ->
      valid_val f v.
  Proof.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    destruct (Int.eq i0 Int.zero); try discriminate.
    inv H; simpl; auto.
  Qed.

  Lemma valid_val_divs:
    forall f v1 v2 v,
      Val.divs v1 v2 = Some v ->
      valid_val f v.
  Proof.
    intros.
    destruct v1, v2; simpl in *; try discriminate;
    match goal with
    | [H: context[match ?Expr with _ => _ end] |- _] =>
      destruct Expr
    end; try discriminate.
    inv H; simpl; auto.
  Qed.

  Lemma valid_val_mods:
    forall f v1 v2 v,
      Val.mods v1 v2 = Some v ->
      valid_val f v.
  Proof.
    intros.
    destruct v1, v2; simpl in *; try discriminate;
    match goal with
    | [H: context[match ?Expr with _ => _ end] |- _] =>
      destruct Expr
    end; try discriminate.
    inv H; simpl; auto.
  Qed.

  Lemma valid_val_divlu:
    forall f v1 v2 v,
      Val.divlu v1 v2 = Some v ->
      valid_val f v.
  Proof.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    destruct (Int64.eq i0 Int64.zero); try discriminate.
    inv H; simpl; auto.
  Qed.

  Lemma valid_val_modlu:
    forall f v1 v2 v,
      Val.modlu v1 v2 = Some v ->
      valid_val f v.
  Proof.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    destruct (Int64.eq i0 Int64.zero); try discriminate.
    inv H; simpl; auto.
  Qed.

  Lemma valid_val_divls:
    forall f v1 v2 v,
      Val.divls v1 v2 = Some v ->
      valid_val f v.
  Proof.
    intros.
    destruct v1, v2; simpl in *; try discriminate;
    match goal with
    | [H: context[match ?Expr with _ => _ end] |- _] =>
      destruct Expr
    end; try discriminate.
    inv H; simpl; auto.
  Qed.

  Lemma valid_val_modls:
    forall f v1 v2 v,
      Val.modls v1 v2 = Some v ->
      valid_val f v.
  Proof.
    intros.
    destruct v1, v2; simpl in *; try discriminate;
    match goal with
    | [H: context[match ?Expr with _ => _ end] |- _] =>
      destruct Expr
    end; try discriminate.
    inv H; simpl; auto.
  Qed.

  Lemma valid_val_notint:
    forall f v,
      valid_val f (Val.notint v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_notl:
    forall f v,
      valid_val f (Val.notl v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_vzero:
    forall f,
      valid_val f (Vzero).
  Proof.
    simpl; auto.
  Qed.

  Lemma valid_val_of_optbool:
    forall f b,
      valid_val f (Val.of_optbool b).
  Proof.
    destruct b as [[|] |]; simpl; auto.
  Qed.


  Lemma valid_val_offset:
    forall f b ofs ofs',
      valid_val f (Vptr b ofs) ->
      valid_val f (Vptr b ofs').
  Proof.
    intros. unfold valid_val in *.
    auto.
  Qed.

  Lemma valid_val_sub_overflow:
    forall f v1 v2,
      valid_val f (Val.sub_overflow v1 v2).
  Proof.
    destruct v1,v2; simpl; auto.
  Qed.

  Lemma valid_val_subl_overflow:
    forall f v1 v2,
      valid_val f (Val.subl_overflow v1 v2).
  Proof.
    destruct v1,v2; simpl; auto.
  Qed.

  Lemma valid_val_negative:
    forall f v,
      valid_val f (Val.negative v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_negativel:
    forall f v,
      valid_val f (Val.negativel v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma valid_val_of_bool:
    forall f b,
      valid_val f (Val.of_bool b).
  Proof.
    destruct b; simpl; auto.
  Qed.

  Hint Resolve valid_val_sub valid_val_subl : wd.
  Hint Immediate  valid_val_int valid_val_long valid_val_one valid_val_undef
       valid_val_single valid_val_float valid_val_hiword valid_val_loword
       valid_val_add valid_val_addl valid_val_offset_ptr
       valid_val_mul valid_val_mulhu valid_val_mulhs
       valid_val_mull valid_val_mullhu valid_val_mullhs
       valid_val_and valid_val_or valid_val_xor
       valid_val_andl valid_val_orl valid_val_xorl
       valid_intoffloat valid_intofsingle
       valid_singleofint valid_floatofint
       valid_longoffloat valid_longofsingle
       valid_singleoflong valid_floatoflong
       valid_val_singleoffloat valid_val_floatofsingle
       valid_val_neg valid_val_negl valid_val_longofintu valid_val_longofint valid_val_sign_ext valid_val_zero_ext
       valid_val_divu valid_val_modu
       valid_val_divs valid_val_mods
       valid_val_divlu valid_val_modlu
       valid_val_divls valid_val_modls
       valid_val_notint valid_val_notl valid_val_vzero
       valid_val_shl valid_val_shru valid_val_shr
       valid_val_shll valid_val_shrlu valid_val_shrl
       valid_val_ror valid_val_rorl valid_val_addf valid_val_mulf
       valid_val_subf valid_val_divf
       valid_val_addfs valid_val_mulfs
       valid_val_subfs valid_val_divfs
       valid_val_negf valid_val_absf
       valid_val_negfs valid_val_absfs
       valid_val_of_optbool valid_val_sub_overflow valid_val_subl_overflow
       valid_val_negative valid_val_negativel valid_val_of_bool : wd.
End ValueWD.

(** ** Well-defined Memories*)
Module MemoryWD.

  Import Renamings MemoryLemmas ValueWD.
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

  Lemma wd_val_valid:
    forall v m f
      (Hdomain: domain_memren f m),
      mem_wd.val_valid v m <-> valid_val f v.
  Proof.
    intros.
    unfold mem_wd.val_valid, valid_val.
    destruct v; try tauto.
    split.
    intro H.
    apply Hdomain in H.
    destruct (f b) as [b0|];
      by [exists b0; eauto | intuition].
    intros (b' & H).
    assert (H': f b)
      by (rewrite H; auto);
      by apply Hdomain in H'.
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

  Lemma inj_bytes_type:
    forall bs mv,
      In mv (inj_bytes bs) ->
      match mv with
      | Byte _ => True
      | _ => False
      end.
  Proof.
    induction bs; intros; simpl in *;
    first  by exfalso.
    destruct H.
    rewrite <- H; auto.
    eapply IHbs; eauto.
  Qed.

  Lemma decode_val_wd:
    forall f (vl : seq memval) (chunk : memory_chunk),
      valid_memval_list f vl ->
      valid_val f (decode_val chunk vl).
  Proof.
    intros.
    unfold decode_val.
    destruct (proj_bytes vl) as [bl|] eqn:PB1;
      destruct chunk; simpl; auto;
      match goal with
      | [|- context[proj_value ?Q ?V]] =>
        destruct (proj_value Q V) eqn:?
      end; simpl; auto;
        try (destruct (Archi.ptr64); simpl; auto);
      repeat match goal with
             | [H: proj_value ?Q ?V = _ |- _] =>
               destruct (proj_value Q V) eqn:?;
                        unfold  proj_value in *
             | [H: match ?Expr with _ => _ end = _ |- _] =>
               destruct Expr eqn:?; try discriminate
             | [H: Vptr _ _ = Vptr _ _ |- _ ] =>
               inversion H; clear H
             end; subst;
      inversion H; subst;
      inversion H2; eexists; eauto.
  Qed.

  Lemma getN_wd :
    forall (f : memren) (m : mem) b,
      Mem.valid_block m b ->
      valid_mem m ->
      domain_memren f m ->
      forall (n : nat) (ofs : Z),
        valid_memval_list f (Mem.getN n ofs (Mem.mem_contents m) # b).
  Proof.
    induction n; intros; simpl;
    constructor.
    unfold valid_mem in H0.
    specialize (H0 _ H ofs _ ltac:(reflexivity)).
    destruct (ZMap.get ofs (Mem.mem_contents m) # b); simpl; auto.
    erewrite <- wd_val_valid; eauto.
    eauto.
  Qed.

  Lemma valid_val_encode:
    forall v m chunk
      (Hval_wd: mem_wd.val_valid v m),
    forall v',
      List.In v' (encode_val chunk v) ->
      match v' with
      | Undef => True
      | Byte _ => True
      | Fragment v'' _ _ =>
        mem_wd.val_valid v'' m
      end.
  Proof.
    intros.
    destruct v'; auto.
    destruct v, chunk; simpl in *;
    repeat (match goal with
            | [H: _ \/ _ |- _] =>
              destruct H
            | [H: False |- _] =>
                by exfalso
            | [H: _ = _ |- _] =>
              inversion H; subst; clear H
            |[H: In _ (if Archi.ptr64 then _ else _) |- _ ] =>
             destruct Archi.ptr64; simpl in H
            end); simpl; auto;
      apply inj_bytes_type in H;
      now exfalso.
  Qed.

  Lemma valid_val_store:
    forall v m m' chunk b ofs v'
      (Hvalid: mem_wd.val_valid v m)
      (Hstore: Mem.store chunk m b ofs v' = Some m'),
      mem_wd.val_valid v m'.
  Proof.
    intros.
    destruct v; simpl; auto.
    eapply Mem.store_valid_block_1; eauto.
  Qed.

  Transparent  Mem.storebytes.
  Lemma valid_val_storebytes:
    forall v m m' b ofs mv
      (Hmem: mem_wd.val_valid v m)
      (Hstore: Mem.storebytes m b ofs mv = Some m'),
      mem_wd.val_valid v m'.
  Proof.
    intros.
    destruct v; simpl; auto.
    eapply Mem.storebytes_valid_block_1; eauto.
  Qed.


  Lemma storebytes_wd_domain:
    forall (m m' : mem) mv b ofs f
      (Hdomain: domain_memren f m)
      (Hmval_wd: valid_memval_list f mv)
      (Hstore: Mem.storebytes m b ofs mv = Some m')
      (Hmem_wd: valid_mem m),
      valid_mem m' /\ domain_memren f m'.
  Proof.
    intros.
    unfold valid_mem in *.
    destruct mv.
    - unfold Mem.storebytes in Hstore.
      destruct (Mem.range_perm_dec m b ofs (ofs + Z.of_nat (length [::]))); try discriminate.
      inv Hstore.
      unfold domain_memren, mem_wd.val_valid, Mem.valid_block in *. simpl.
      split; eauto.
      intros.
      eapply Hmem_wd with (ofs := ofs0); eauto.
      rewrite <- H0.
      destruct (Pos.eq_dec b b0); subst.
      rewrite Maps.PMap.gss.
      reflexivity.
      rewrite Maps.PMap.gso;
        now eauto.
    - split.
      { intros b0 Hvalid ofs0 mv0 Hget; subst.
        eapply Mem.storebytes_valid_block_2 in Hvalid; eauto.
        rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hstore).
        destruct (Pos.eq_dec b b0) as [Heq | Hneq].
        - (*case it's the same block*)
          subst.
          rewrite Maps.PMap.gss.
          destruct (Intv.In_dec ofs0
                                (ofs,
                                 (ofs + Z.of_nat (length (m0 ::mv)))%Z)).
          
          + apply Mem.setN_in with (c:= (Mem.mem_contents m) # b0) in i.
            destruct (ZMap.get ofs0
                               (Mem.setN (m0 :: mv) ofs (Mem.mem_contents m) # b0));
              simpl; auto.
            
            Lemma In_valid_memval_list:
            forall f mvs mv,
              valid_memval_list f mvs ->
              In mv mvs ->
              valid_memval f mv.
          Proof.
            induction mvs; intros.
            - simpl in H0.
              now exfalso.
            - simpl in H0.
              inv H.
              destruct H0; subst;
                now eauto.
          Qed.
          
          eapply In_valid_memval_list in Hmval_wd; eauto.
          simpl in Hmval_wd.
          eapply wd_val_valid; eauto.
          unfold domain_memren in *.
          intros b.
          split; intros Hb;
            [eapply Mem.storebytes_valid_block_2 in Hb; eauto|
             eapply Mem.storebytes_valid_block_1; eauto];
          eapply Hdomain; eauto.
        + apply Intv.range_notin in n.
          erewrite Mem.setN_outside by eauto.
          specialize (Hmem_wd _ Hvalid ofs0 _ ltac:(reflexivity)).
          destruct (ZMap.get ofs0 (Mem.mem_contents m) # b0); auto.
          eapply valid_val_storebytes; eauto.
          simpl.
          zify; omega.
      - erewrite Maps.PMap.gso by eauto.
        specialize (Hmem_wd _ Hvalid ofs0 _ ltac:(reflexivity)).
        destruct (ZMap.get ofs0 (Mem.mem_contents m) # b0); subst; auto.
        eapply valid_val_storebytes; eauto. }
    { split.
      intros. eapply Mem.storebytes_valid_block_2 in H; eauto.
      eapply Hdomain; auto.
      intros. eapply Mem.storebytes_valid_block_1; eauto.
      apply Hdomain; auto.
    }
  Qed.

  
  (** Well-definedeness is preserved through storing of a well-defined value *)
  Lemma store_wd_domain:
    forall (m m' : mem) (chunk : memory_chunk) (v : val) b ofs f
      (Hdomain: domain_memren f m)
      (Hstore: Mem.store chunk m b ofs v = Some m')
      (Hval_wd: mem_wd.val_valid v m)
      (Hmem_wd: valid_mem m),
      valid_mem m' /\ domain_memren f m'.
  Proof.
    intros.
    unfold valid_mem in *.
    split.
    { intros b0 Hvalid ofs0 mv Hget.
      eapply Mem.store_valid_block_2 in Hvalid; eauto.
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore) in Hget.
      destruct (Pos.eq_dec b b0) as [Heq | Hneq].
      - (*case it's the same block*)
        subst.
        rewrite Maps.PMap.gss.
        destruct (Intv.In_dec ofs0
                              (ofs,
                               (ofs + Z.of_nat (length (encode_val chunk v)))%Z)).

        + apply Mem.setN_in with (c:= (Mem.mem_contents m) # b0) in i.
          apply valid_val_encode with (m := m) in i; auto.
          destruct (ZMap.get ofs0
                             (Mem.setN (encode_val chunk v) ofs (Mem.mem_contents m) # b0));
            simpl; auto.
          eapply valid_val_store; eauto.
        + apply Intv.range_notin in n.
          erewrite Mem.setN_outside by eauto.
          specialize (Hmem_wd _ Hvalid ofs0 _ ltac:(reflexivity)).
          destruct (ZMap.get ofs0 (Mem.mem_contents m) # b0); auto.
          eapply valid_val_store; eauto.
          simpl.
          apply ofs_val_lt.
      - erewrite Maps.PMap.gso in Hget by eauto.
        specialize (Hmem_wd _ Hvalid ofs0 _ ltac:(reflexivity)).
        destruct (ZMap.get ofs0 (Mem.mem_contents m) # b0); subst; auto.
        eapply valid_val_store; eauto. }
    { split.
      intros. eapply Mem.store_valid_block_2 in H; eauto.
      eapply Hdomain; auto.
      intros. eapply Mem.store_valid_block_1; eauto.
      apply Hdomain; auto.
    }
  Qed.

  Lemma storev_wd_domain:
    forall (m m' : mem) (chunk : memory_chunk) (vptr v : val) f,
      domain_memren f m ->
      Mem.storev chunk m vptr v = Some m' ->
      mem_wd.val_valid v m ->
      valid_mem m ->
      valid_mem m' /\ domain_memren f m'.
  Proof.
    intros.
    destruct vptr; simpl in *; try discriminate.
    eapply store_wd_domain; eauto.
  Qed.

  (** Loading a value from a well-defined memory returns a valid value*)
  Lemma valid_mem_load:
    forall chunk m b ofs v f
      (Hwd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Hload: Mem.load chunk m b ofs = Some v),
      valid_val f v.
  Proof.
    intros.
    unfold valid_mem in Hwd.
    assert (Hvalid: Mem.valid_block m b)
      by (eapply load_valid_block; eauto).
    exploit Mem.load_result; eauto. intro. rewrite H.
    eapply decode_val_wd; eauto.
    apply getN_wd; auto.
  Qed.

  Transparent Mem.loadbytes.
  Lemma valid_mem_loadbytes:
    forall m b ofs sz mv f
      (Hwd: valid_mem m)
      (Hsz: sz >= 0)
      (Hdomain: domain_memren f m)
      (Hload: Mem.loadbytes m b ofs sz = Some mv),
      valid_memval_list f mv.
  Proof.
    intros.
    unfold Mem.loadbytes in Hload.
    destruct (Mem.range_perm_dec m b ofs (ofs+sz) Cur Readable);
      [|discriminate].
    inv Hload.
    unfold Mem.range_perm in r.
    assert (Hsz': sz > 0 \/ sz = 0)
      by omega.
    destruct Hsz'.
    - specialize (r ofs ltac:(omega)).
      eapply Mem.perm_valid_block in r.
      eapply getN_wd; eauto.
    - subst.
      simpl.
      econstructor.
  Qed.

  Lemma loadv_wd:
    forall chunk m vptr v f
      (Hwd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Hload: Mem.loadv chunk m vptr = Some v),
      valid_val f v.
  Proof.
    intros.
    destruct vptr; try discriminate.
    eapply valid_mem_load; eauto.
  Qed.

  Lemma domain_memren_store:
    forall chunk m m' b ofs v f
      (Hdomain: domain_memren f m)
      (Hstore: Mem.store chunk m b ofs v = Some m'),
      domain_memren f m'.
  Proof.
    intros.
    split.
    - intros Hvalid.
      eapply Mem.store_valid_block_2 in Hvalid; eauto.
      edestruct Hdomain; auto.
    - intros Hf.
      eapply Mem.store_valid_block_1; eauto.
      edestruct Hdomain; eauto.
  Qed.

  Lemma domain_memren_storev:
    forall chunk m m' vptr v f
      (Hdomain: domain_memren f m)
      (Hstore: Mem.storev chunk m vptr v = Some m'),
      domain_memren f m'.
  Proof.
    intros.
    unfold Mem.storev in Hstore.
    destruct vptr; try discriminate.
    eapply domain_memren_store; eauto.
  Qed.

End MemoryWD.

(** ** Renamings on values*)
Module ValObsEq.

  Import ValueWD MemoryWD Renamings MemoryLemmas.

  (** Strong injections on values *)
  Inductive val_obs (mi : memren) : val -> val -> Prop :=
    obs_int : forall i : int, val_obs mi (Vint i) (Vint i)
  | obs_long : forall i : int64, val_obs mi (Vlong i) (Vlong i)
  | obs_float : forall f : Floats.float,
      val_obs mi (Vfloat f) (Vfloat f)
  | obs_single : forall f : Floats.float32,
      val_obs mi (Vsingle f) (Vsingle f)
  | obs_ptr : forall (b1 b2 : block) (ofs : ptrofs),
      mi b1 = Some b2 ->
      val_obs mi (Vptr b1 ofs) (Vptr b2 ofs)
  | obs_undef : val_obs mi Vundef Vundef.

  (** Strong injections on memory values*)
  Inductive memval_obs_eq (f : memren) : memval -> memval -> Prop :=
  | memval_obs_byte : forall n : byte,
      memval_obs_eq f (Byte n) (Byte n)
  | memval_obs_frag : forall (v1 v2 : val) (q : quantity) (n : nat)
                        (Hval_obs: val_obs f v1 v2),
      memval_obs_eq f (Fragment v1 q n) (Fragment v2 q n)
  | memval_obs_undef : memval_obs_eq f Undef Undef.


  Inductive val_obs_list (mi : memren) : seq val -> seq val -> Prop :=
    val_obs_list_nil : val_obs_list mi [::] [::]
  | val_obs_list_cons : forall (v v' : val) (vl vl' : seq val),
                       val_obs mi v v' ->
                       val_obs_list mi vl vl' ->
                       val_obs_list mi (v :: vl) (v' :: vl').

  Hint Constructors val_obs : val_renamings.

  Lemma val_obs_incr:
    forall f f' v v'
      (Hval_obs: val_obs f v v')
      (Hincr: ren_incr f f'),
      val_obs f' v v'.
  Proof with eauto with val_renamings.
    intros.
    destruct v; inversion Hval_obs; subst...
  Qed.

  Lemma val_obs_trans:
    forall (v v' v'' : val) (f f' f'' : memren),
      val_obs f v v'' ->
      val_obs f' v v' ->
      (forall b b' b'' : block,
          f b = Some b'' ->
          f' b = Some b' ->
          f'' b' = Some b'') ->
      val_obs f'' v' v''.
  Proof with eauto with val_renamings.
    intros v v' v'' f f' f'' Hval'' Hval' Hf.
    inversion Hval'; subst; inversion Hval''; subst...
  Qed.

  Lemma memval_obs_trans:
    forall (v v' v'' : memval) (f f' f'' : memren),
      memval_obs_eq f v v'' ->
      memval_obs_eq f' v v' ->
      (forall b b' b'' : block,
          f b = Some b'' ->
          f' b = Some b' ->
          f'' b' = Some b'') ->
      memval_obs_eq f'' v' v''.
  Proof.
    intros v v' v'' f f' f'' Hval'' Hval' Hf.
    inversion Hval'; subst; inversion Hval''; subst;
    try constructor.
    eapply val_obs_trans;
      by eauto.
  Qed.

  Lemma val_obs_list_trans:
    forall (vs vs' vs'' : seq val) (f f' f'' : memren),
      val_obs_list f vs vs'' ->
      val_obs_list f' vs vs' ->
      (forall b b' b'' : block,
          f b = Some b'' ->
          f' b = Some b' ->
          f'' b' = Some b'') ->
      val_obs_list f'' vs' vs''.
  Proof.
    intros vs vs' vs'' f f' f'' Hobs Hobs' Hf.
    generalize dependent vs''.
    induction Hobs'; subst; intros;
    inversion Hobs; subst. constructor.
    constructor; auto.
      by eapply val_obs_trans; eauto.
  Qed.

  Lemma val_obs_list_incr:
    forall (vs vs' : seq val) (f f' : memren),
      val_obs_list f vs vs' ->
      ren_incr f f' ->
      val_obs_list f' vs vs'.
  Proof.
    intros.
    induction H;
      constructor;
      eauto using val_obs_incr.
  Qed.

  (** Two values that are equal are related by the id injection on a valid memory*)
  Lemma val_obs_id:
    forall f v
      (Hvalid: valid_val f v)
      (Hid: forall b b', f b = Some b' -> b = b'),
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v...
    destruct Hvalid as [b' Hf].
    specialize (Hid _ _ Hf);
      subst...
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

  Lemma memval_obs_eq_id:
    forall f mv
      (Hvalid: valid_memval f mv)
      (Hid: forall b b', f b = Some b' -> b = b'),
                    memval_obs_eq f mv mv.
  Proof.
    intros.
    destruct mv;
    econstructor;
    eapply val_obs_id;
      by eauto.
  Qed.

  Lemma ren_cmp_bool:
    forall f v v' v0 cmp,
      val_obs f v v' ->
      Val.cmp_bool cmp v v0 = Val.cmp_bool cmp v' v0.
  Proof.
    intros.
    destruct v; inversion H; subst;
      by reflexivity.
  Qed.

  Lemma val_obs_hiword:
    forall f v v',
      val_obs f v v' ->
      val_obs f (Val.hiword v) (Val.hiword v').
  Proof with eauto with val_renamings.
    intros;
    destruct v; inversion H; subst;
    simpl...
  Qed.

  Lemma val_obs_loword:
    forall f v v',
      val_obs f v v' ->
      val_obs f (Val.loword v) (Val.loword v').
  Proof with eauto with val_renamings.
    intros;
    destruct v; inversion H; subst;
    simpl...
  Qed.

  Lemma val_obs_longofwords:
    forall f vhi vhi' vlo vlo'
      (Hobs_hi: val_obs f vhi vhi')
      (Hobs_lo: val_obs f vlo vlo'),
      val_obs f (Val.longofwords vhi vlo) (Val.longofwords vhi' vlo').
  Proof with eauto with val_renamings.
    intros;
    destruct vhi; inversion Hobs_hi; subst; simpl...
    destruct vlo; inversion Hobs_lo...
  Qed.

  Lemma val_obs_load_result:
    forall f v v' chunk
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.load_result chunk v) (Val.load_result chunk v').
  Proof with eauto with val_renamings.
    intros;
    destruct v; inversion Hval_obs; subst;
    destruct chunk; simpl...
  Qed.

  Lemma val_obs_ext:
    forall f v v' n
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.zero_ext n v) (Val.zero_ext n v').
  Proof with eauto with val_renamings.
    intros; destruct v; inversion Hval_obs; subst; simpl...
  Qed.

  Definition val_obsC f v :=
    match v with
    | Vptr b n => match f b with
                 | Some b' => Vptr b' n
                 | None => Vundef
                 end
    | _ => v
    end.

  Lemma val_obsC_correct:
    forall f v,
      valid_val f v ->
      val_obs f v (val_obsC f v).
  Proof.
    intros.
    destruct v; simpl;
    try constructor.
    simpl in H.
    destruct H.
    rewrite H;
      by constructor.
  Qed.

  (* Lemma val_has_type_obs: *)
  (*   forall f v v' ty *)
  (*     (Hval_obs: val_obs f v v'), *)
  (*     val_casted.val_has_type_func v ty <-> val_casted.val_has_type_func v' ty. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct v; inversion Hval_obs; subst; simpl; *)
  (*     by tauto. *)
  (* Qed. *)

  (* Lemma val_has_type_list_obs: *)
  (*   forall f vs vs' ts *)
  (*     (Hval_obs: val_obs_list f vs vs'), *)
  (*     val_casted.val_has_type_list_func vs ts <-> *)
  (*     val_casted.val_has_type_list_func vs' ts. *)
  (* Proof. *)
  (*   intros. *)
  (*   generalize dependent vs'. *)
  (*   generalize dependent ts. *)
  (*   induction vs; *)
  (*     intros. inversion Hval_obs; subst. *)
  (*   simpl; destruct ts; split; *)
  (*     by auto. *)
  (*   inversion Hval_obs; subst. *)
  (*   destruct ts; simpl; first by split; auto. *)
  (*   split; intros; move/andP:H=>[H H']; *)
  (*     apply/andP. *)
  (*   split; *)
  (*     [erewrite <- val_has_type_obs; eauto | *)
  (*      destruct (IHvs ts _ H3); eauto]. *)
  (*   split; *)
  (*     [erewrite val_has_type_obs; eauto | *)
  (*      destruct (IHvs ts _ H3); eauto]. *)
  (* Qed. *)

  (* Lemma vals_defined_obs: *)
  (*   forall f vs vs' *)
  (*     (Hval_obs: val_obs_list f vs vs'), *)
  (*     val_casted.vals_defined vs <-> val_casted.vals_defined vs'. *)
  (* Proof. *)
  (*   intros. *)
  (*   induction Hval_obs; *)
  (*     simpl; try tauto. *)
  (*   destruct v; inversion H; *)
  (*     by tauto. *)
  (* Qed. *)

  Lemma zlength_obs:
    forall f v v'
      (Hval_obs: val_obs_list f v v'),
      Zlength v = Zlength v'.
  Proof.
    induction 1; simpl; auto.
    do 2 rewrite Zlength_cons;
      by rewrite IHHval_obs.
  Qed.

  Lemma val_obs_add:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.add v1 v1') (Val.add v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
      inversion Hval_obs'; subst;
        solve [simpl; eauto with val_renamings ||
                                 destruct Archi.ptr64; simpl; eauto with val_renamings].
  Qed.

  Lemma val_obs_addl:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.addl v1 v1') (Val.addl v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
      inversion Hval_obs'; subst;
        solve [simpl; eauto with val_renamings].
  Qed.

  Lemma val_obs_offset_ptr:
    forall f v1 v2 ofs
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.offset_ptr v1 ofs) (Val.offset_ptr v2 ofs).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst;
        solve [simpl; eauto with val_renamings].
  Qed.

  Lemma val_obs_sign_ext:
    forall f v v' n
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.sign_ext n v) (Val.sign_ext n v').
  Proof with eauto with val_renamings.
    intros; destruct v; inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_longofintu:
    forall f v v'
      (Hobs: val_obs f v v'),
      val_obs f (Val.longofintu v) (Val.longofintu v').
  Proof with eauto with val_renamings.
    intros;
    destruct v; inversion Hobs; subst; simpl...
  Qed.

  Lemma val_obs_longofint:
    forall f v v'
      (Hobs: val_obs f v v'),
      val_obs f (Val.longofint v) (Val.longofint v').
  Proof with eauto with val_renamings.
    intros;
    destruct v; inversion Hobs; subst; simpl...
  Qed.

  Lemma val_obs_singleoffloat:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.singleoffloat v) (Val.singleoffloat v').
  Proof with eauto with val_renamings.
    intros; destruct v; inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_floatofsingle:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.floatofsingle v) (Val.floatofsingle v').
  Proof with eauto with val_renamings.
    intros; destruct v; inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_intoffloat:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.maketotal (Val.intoffloat v))
              (Val.maketotal (Val.intoffloat v')).
  Proof with eauto with val_renamings.
    intros; destruct v; unfold Val.maketotal;
    inversion Hval_obs; subst; simpl...
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr eqn:?
    end...
    unfold Coqlib.option_map in Heqo.
    destruct (Floats.Float.to_int f0); inversion Heqo...
  Qed.

  Lemma val_obs_floatofint:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.maketotal (Val.floatofint v))
              (Val.maketotal (Val.floatofint v')).
  Proof with eauto with val_renamings.
    intros; destruct v; unfold Val.maketotal;
    inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_intofsingle:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.maketotal (Val.intofsingle v))
              (Val.maketotal (Val.intofsingle v')).
  Proof with eauto with val_renamings.
    intros; destruct v; unfold Val.maketotal;
    inversion Hval_obs; subst; simpl...
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr eqn:?
    end...
    unfold Coqlib.option_map in Heqo.
    destruct (Floats.Float32.to_int f0); inversion Heqo...
  Qed.

  Lemma val_obs_singleofint:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.maketotal (Val.singleofint v))
              (Val.maketotal (Val.singleofint v')).
  Proof with eauto with val_renamings.
    intros; destruct v; unfold Val.maketotal;
    inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_longoffloat:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.maketotal (Val.longoffloat v))
              (Val.maketotal (Val.longoffloat v')).
  Proof with eauto with val_renamings.
    intros; destruct v; unfold Val.maketotal;
    inversion Hval_obs; subst; simpl...
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr eqn:?
    end...
    unfold Coqlib.option_map in Heqo.
    destruct (Floats.Float.to_long f0); inversion Heqo...
  Qed.

  Lemma val_obs_floatoflong:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.maketotal (Val.floatoflong v))
              (Val.maketotal (Val.floatoflong v')).
  Proof with eauto with val_renamings.
    intros; destruct v; unfold Val.maketotal;
    inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_longofsingle:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.maketotal (Val.longofsingle v))
              (Val.maketotal (Val.longofsingle v')).
  Proof with eauto with val_renamings.
    intros; destruct v; unfold Val.maketotal;
    inversion Hval_obs; subst; simpl...
    match goal with
    | [|- context[match ?Expr with _ => _ end]] =>
      destruct Expr eqn:?
    end...
    unfold Coqlib.option_map in Heqo.
    destruct (Floats.Float32.to_long f0); inversion Heqo...
  Qed.

  Lemma val_obs_singleoflong:
    forall f v v'
      (Hval_obs: val_obs f v v'),
      val_obs f (Val.maketotal (Val.singleoflong v))
              (Val.maketotal (Val.singleoflong v')).
  Proof with eauto with val_renamings.
    intros; destruct v; unfold Val.maketotal;
    inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_mul:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.mul v1 v1') (Val.mul v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_mull:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.mull v1 v1') (Val.mull v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_mulhs:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.mulhs v1 v1') (Val.mulhs v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_mulhu:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.mulhu v1 v1') (Val.mulhu v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_mullhs:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.mullhs v1 v1') (Val.mullhs v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_mullhu:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.mullhu v1 v1') (Val.mullhu v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_and:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.and v1 v1') (Val.and v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_or:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.or v1 v1') (Val.or v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_xor:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.xor v1 v1') (Val.xor v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_andl:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.andl v1 v1') (Val.andl v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_orl:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.orl v1 v1') (Val.orl v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_xorl:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.xorl v1 v1') (Val.xorl v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_notint:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.notint v1) (Val.notint v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst;
    simpl...
  Qed.

  Lemma val_obs_notl:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.notl v1) (Val.notl v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst;
    simpl...
  Qed.

  Lemma val_obs_shl:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.shl v1 v1') (Val.shl v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
    destruct (Int.ltu i0 Int.iwordsize)...
  Qed.

  Lemma val_obs_shr:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.shr v1 v1') (Val.shr v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
    destruct (Int.ltu i0 Int.iwordsize)...
  Qed.


  Lemma val_obs_shru:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.shru v1 v1') (Val.shru v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
    destruct (Int.ltu i0 Int.iwordsize)...
  Qed.

  Lemma val_obs_ror:
  forall f v1 v2 ofs
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.ror v1 (Vint ofs)) (Val.ror v2 (Vint ofs)).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_shll:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.shll v1 v1') (Val.shll v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
    destruct (Int.ltu i0 Int64.iwordsize')...
  Qed.

  Lemma val_obs_shrl:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.shrl v1 v1') (Val.shrl v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
    destruct (Int.ltu i0 Int64.iwordsize')...
  Qed.

  Lemma val_obs_shrlu:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.shrlu v1 v1') (Val.shrlu v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
    destruct (Int.ltu i0 Int64.iwordsize')...
  Qed.

  Lemma val_obs_rorl:
  forall f v1 v2 ofs
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.rorl v1 (Vint ofs)) (Val.rorl v2 (Vint ofs)).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst; simpl...
  Qed.

  Lemma val_obs_suboverflow:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.sub_overflow v1 v1') (Val.sub_overflow v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_subloverflow:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.subl_overflow v1 v1') (Val.subl_overflow v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_negative:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.negative v1) (Val.negative v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst;
    simpl...
  Qed.

  Lemma val_obs_neg:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.neg v1) (Val.neg v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst;
    simpl...
  Qed.

  Lemma val_obs_negativel:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.negativel v1) (Val.negativel v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst;
    simpl...
  Qed.

  Lemma val_obs_negl:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.negl v1) (Val.negl v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs; subst;
    simpl...
  Qed.

  Lemma val_obs_sub:
    forall f v1 v2 v1' v2'
      (Hinjective: forall b1 b1' b2,
          f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1')
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.sub v1 v1') (Val.sub v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
      inversion Hval_obs'; subst; simpl; eauto with val_renamings;
    destruct Archi.ptr64; simpl...
    destruct (eq_block b b0); subst.
    rewrite H6 in H2; inversion H2; subst.
    destruct (eq_block b2 b2)...
      by exfalso.
      destruct (eq_block b2 b4)...
      subst.
      assert (b0 = b)
        by (eapply Hinjective; eauto).
      subst.
        by exfalso.
  Qed.

  Lemma val_obs_subl:
    forall f v1 v2 v1' v2'
      (Hinjective: forall b1 b1' b2,
          f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1')
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.subl v1 v1') (Val.subl v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
      inversion Hval_obs'; subst; simpl; eauto with val_renamings.
  Qed.

  (** Floating point functions *)
  Lemma val_obs_addf:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.addf v1 v1') (Val.addf v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_addfs:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.addfs v1 v1') (Val.addfs v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_mulf:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.mulf v1 v1') (Val.mulf v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_mulfs:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.mulfs v1 v1') (Val.mulfs v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_negf:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.negf v1) (Val.negf v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs;
    subst; simpl...
  Qed.

  Lemma val_obs_negfs:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.negfs v1) (Val.negfs v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs;
    subst; simpl...
  Qed.

  Lemma val_obs_absf:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.absf v1) (Val.absf v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs;
    subst; simpl...
  Qed.

  Lemma val_obs_absfs:
    forall f v1 v2
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.absfs v1) (Val.absfs v2).
  Proof with eauto with val_renamings.
    intros.
    destruct v1; inversion Hval_obs;
    subst; simpl...
  Qed.

  Lemma val_obs_subf:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.subf v1 v1') (Val.subf v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_subfs:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.subfs v1 v1') (Val.subfs v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_divf:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.divf v1 v1') (Val.divf v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma val_obs_divfs:
    forall f v1 v2 v1' v2'
      (Hval_obs': val_obs f v1' v2')
      (Hval_obs: val_obs f v1 v2),
      val_obs f (Val.divfs v1 v1') (Val.divfs v2 v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl...
  Qed.

  Lemma divu_ren:
    forall f v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2'),
      Val.divu v1 v2 = Val.divu v1' v2'.
  Proof.
    intros.
    destruct v1; inversion Hval_obs; subst;
    destruct v2; inversion Hval_obs'; subst; simpl in *;
    auto.
  Qed.

  Lemma modu_ren:
    forall f v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2'),
      Val.modu v1 v2 = Val.modu v1' v2'.
  Proof.
    intros.
    destruct v1; inversion Hval_obs; subst;
    destruct v2; inversion Hval_obs'; subst; simpl in *;
    auto.
  Qed.

  Lemma val_obs_divu_id:
    forall f v1 v2 v,
      Val.divu v1 v2 = Some v ->
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    destruct (Int.eq i0 Int.zero); try discriminate.
    inversion H...
  Qed.

  Lemma val_obs_modu_id:
    forall f v1 v2 v,
      Val.modu v1 v2 = Some v ->
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    destruct (Int.eq i0 Int.zero); try discriminate.
    inversion H...
  Qed.

  Lemma divs_ren:
    forall f v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2'),
      Val.divs v1 v2 = Val.divs v1' v2'.
  Proof.
    intros.
    destruct v1; inversion Hval_obs; subst;
    destruct v2; inversion Hval_obs'; subst; simpl in *;
    auto.
  Qed.

  Lemma mods_ren:
    forall f v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2'),
      Val.mods v1 v2 = Val.mods v1' v2'.
  Proof.
    intros.
    destruct v1; inversion Hval_obs; subst;
    destruct v2; inversion Hval_obs'; subst; simpl in *;
    auto.
  Qed.

  Lemma val_obs_divs_id:
    forall f v1 v2 v,
      Val.divs v1 v2 = Some v ->
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    match goal with
    | [H: match ?Expr with _ => _ end = _ |- _] =>
      destruct Expr
    end; try discriminate.
    inversion H...
  Qed.

  Lemma val_obs_mods_id:
    forall f v1 v2 v,
      Val.mods v1 v2 = Some v ->
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    match goal with
    | [H: match ?Expr with _ => _ end = _ |- _] =>
      destruct Expr
    end; try discriminate.
    inversion H...
  Qed.

  Lemma divlu_ren:
    forall f v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2'),
      Val.divlu v1 v2 = Val.divlu v1' v2'.
  Proof.
    intros.
    destruct v1; inversion Hval_obs; subst;
    destruct v2; inversion Hval_obs'; subst; simpl in *;
    auto.
  Qed.

  Lemma modlu_ren:
    forall f v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2'),
      Val.modlu v1 v2 = Val.modlu v1' v2'.
  Proof.
    intros.
    destruct v1; inversion Hval_obs; subst;
    destruct v2; inversion Hval_obs'; subst; simpl in *;
    auto.
  Qed.

  Lemma val_obs_divlu_id:
    forall f v1 v2 v,
      Val.divlu v1 v2 = Some v ->
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    destruct (Int64.eq i0 Int64.zero); try discriminate.
    inversion H...
  Qed.

  Lemma val_obs_modlu_id:
    forall f v1 v2 v,
      Val.modlu v1 v2 = Some v ->
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    destruct (Int64.eq i0 Int64.zero); try discriminate.
    inversion H...
  Qed.

  Lemma divls_ren:
    forall f v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2'),
      Val.divls v1 v2 = Val.divls v1' v2'.
  Proof.
    intros.
    destruct v1; inversion Hval_obs; subst;
    destruct v2; inversion Hval_obs'; subst; simpl in *;
    auto.
  Qed.

  Lemma modls_ren:
    forall f v1 v2 v1' v2'
      (Hval_obs: val_obs f v1 v1')
      (Hval_obs': val_obs f v2 v2'),
      Val.modls v1 v2 = Val.modls v1' v2'.
  Proof.
    intros.
    destruct v1; inversion Hval_obs; subst;
    destruct v2; inversion Hval_obs'; subst; simpl in *;
    auto.
  Qed.

  Lemma val_obs_divls_id:
    forall f v1 v2 v,
      Val.divls v1 v2 = Some v ->
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    match goal with
    | [H: match ?Expr with _ => _ end = _ |- _] =>
      destruct Expr
    end; try discriminate.
    inversion H...
  Qed.

  Lemma val_obs_modls_id:
    forall f v1 v2 v,
      Val.modls v1 v2 = Some v ->
      val_obs f v v.
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v2; simpl in *; try discriminate.
    match goal with
    | [H: match ?Expr with _ => _ end = _ |- _] =>
      destruct Expr
    end; try discriminate.
    inversion H...
  Qed.

  Lemma val_obs_of_bool:
    forall f b,
      val_obs f (Val.of_bool b) (Val.of_bool b).
  Proof.
    intros.
    destruct b; simpl; constructor.
  Qed.

  Hint Resolve
       val_obs_add val_obs_addl val_obs_offset_ptr valid_val_incr val_obs_incr val_obsC_correct
       val_obs_load_result val_obs_hiword val_obs_loword
       val_obs_longofwords val_obs_load_result val_obs_ext
       val_obs_sign_ext val_obs_longofintu val_obs_longofint val_obs_singleoffloat val_obs_floatofsingle
       val_obs_intoffloat val_obs_floatofint val_obs_intofsingle
       val_obs_singleofint val_obs_longoffloat val_obs_floatoflong val_obs_longofsingle val_obs_singleoflong
       val_obs_neg val_obs_negl val_obs_mul val_obs_mull val_obs_mulhs val_obs_mulhu val_obs_mullhs val_obs_mullhu
       val_obs_and val_obs_sub val_obs_andl val_obs_subl
       val_obs_or val_obs_xor val_obs_orl val_obs_xorl val_obs_notint val_obs_notl
       val_obs_shl val_obs_shr val_obs_shru
       val_obs_shll val_obs_shrl val_obs_shrlu
       val_obs_ror val_obs_suboverflow val_obs_negative
       val_obs_rorl val_obs_subloverflow val_obs_negativel
       val_obs_addf val_obs_addfs val_obs_mulf
       val_obs_mulfs val_obs_negf val_obs_negfs
       val_obs_absf val_obs_absfs val_obs_subf
       val_obs_subfs val_obs_divf val_obs_divfs
       val_obs_divu_id val_obs_modu_id
       val_obs_divs_id val_obs_mods_id
       val_obs_divlu_id val_obs_modlu_id
       val_obs_divls_id val_obs_modls_id val_obs_of_bool : val_renamings.

End ValObsEq.

(** ** Renamings between memories *)
Module MemObsEq.

  Import ValObsEq ValueWD MemoryWD Renamings MemoryLemmas.

  (* A compcert injection would not work because it allows permissions to go up *)
  (* Moreover, we require that undefined values are matched by the
     target memory, unlike compcert injections. Although the latter is
     not neccessary and in retrospect may be a limiting factor. For
     example we would be able to reuse this development for our final
     erasure if we allowed undefined values to become more defined. *)

  (** Weak injection between memories *)
  Record weak_mem_obs_eq (f : memren) (mc mf : mem) :=
    {
      domain_invalid: forall b, ~(Mem.valid_block mc b) -> f b = None;
      domain_valid: forall b, Mem.valid_block mc b -> exists b', f b = Some b';
      codomain_valid: forall b1 b2, f b1 = Some b2 -> Mem.valid_block mf b2;
      injective: forall b1 b1' b2, f b1 = Some b2 ->
                              f b1' = Some b2 ->
                              b1 = b1';
      perm_obs_weak :
        forall b1 b2 ofs (Hrenaming: f b1 = Some b2),
          Mem.perm_order''
            (permission_at mc b1 ofs Cur)
            (permission_at mf b2 ofs Cur)}.



  (** Strong injection between memories *)
  Record strong_mem_obs_eq (f : memren) (mc mf : mem) :=
    { perm_obs_strong :
        forall b1 b2 ofs (Hrenaming: f b1 = Some b2),
            permission_at mf b2 ofs Cur =
            (permission_at mc b1 ofs Cur);
      val_obs_eq :
        forall b1 b2 ofs (Hrenaming: f b1 = Some b2)
          (Hperm: Mem.perm mc b1 ofs Cur Readable),
          memval_obs_eq f (Maps.ZMap.get ofs mc.(Mem.mem_contents)#b1)
                        (Maps.ZMap.get ofs mf.(Mem.mem_contents)#b2)}.


  (** Renaming between memories *)
  Record mem_obs_eq (f : memren) (mc mf : mem) :=
    { weak_obs_eq : weak_mem_obs_eq f mc mf;
      strong_obs_eq : strong_mem_obs_eq f mc mf }.

  Lemma weak_obs_eq_domain_ren:
    forall f m m',
      weak_mem_obs_eq f m m' ->
      domain_memren f m.
  Proof.
    intros f m m' Hobs_eq.
    destruct Hobs_eq.
    intros b. split;
    intros Hb.
    specialize (domain_valid0 _ Hb).
    destruct (domain_valid0) as [? H].
    rewrite H;
      by auto.
    destruct (valid_block_dec m b); auto.
    specialize (domain_invalid0 _ n).
    rewrite domain_invalid0 in Hb;
      by exfalso.
  Qed.

  Corollary mem_obs_eq_domain_ren:
    forall f m m',
      mem_obs_eq f m m' ->
      domain_memren f m.
  Proof.
    intros f m m' H; destruct H;
    eapply weak_obs_eq_domain_ren;
      by eauto.
  Qed.

  Lemma mem_obs_eq_setMaxPerm :
    forall m,
      valid_mem m ->
      mem_obs_eq (id_ren m) m (setMaxPerm m).
  Proof with eauto with renamings id_renamings val_renamings.
    intros.
    constructor; constructor;
      eauto with id_renamings; unfold id_ren; intros;
        repeat match goal with
               | [H: context[valid_block_dec ?M ?B] |- _] =>
                 destruct (valid_block_dec M B); simpl in *
               | [H: _ = Some _ |- _] => inv H; clear H
               end; auto.
    rewrite setMaxPerm_Cur;
      apply po_refl.
    rewrite setMaxPerm_Cur; auto.
    destruct (ZMap.get ofs (Mem.mem_contents m) # b2) eqn:Hget;
      constructor.
    destruct v0; constructor.
    specialize (H _ v _ _ Hget).
    simpl in H.
    (*this gives an anomaly:
  erewrite Coqlib2.if_true with (E:= {Mem.valid_block m b} + {~ Mem.valid_block m b}).
     *)
    destruct (valid_block_dec m b); simpl; tauto.
  Qed.

  Lemma mem_obs_eq_id :
    forall m,
      valid_mem m ->
      mem_obs_eq (id_ren m) m m.
  Proof with eauto with renamings id_renamings val_renamings.
    intros.
    constructor; constructor;
      eauto with id_renamings; unfold id_ren; intros;
        repeat match goal with
               | [H: context[valid_block_dec ?M ?B] |- _] =>
                 destruct (valid_block_dec M B); simpl in *
               | [H: _ = Some _ |- _] => inv H; clear H
               end; auto.
    now apply po_refl.
    destruct (ZMap.get ofs (Mem.mem_contents m) # b2) eqn:Hget;
      constructor.
    destruct v0; constructor.
    specialize (H _ v _ _ Hget).
    simpl in H.
    destruct (valid_block_dec m b); simpl; tauto.
  Qed.

  Lemma mem_obs_eq_extend:
    forall m1 m1' m2' f pmap pmap'
      (Hlt1: permMapLt pmap (getMaxPerm m1))
      (Hlt1': permMapLt pmap' (getMaxPerm m1'))
      (Hlt2': permMapLt pmap' (getMaxPerm m2'))
      (Hmem_obs_eq: mem_obs_eq f (restrPermMap Hlt1) (restrPermMap Hlt1'))
      (Hextend': forall b, Mem.valid_block m1' b -> Mem.valid_block m2' b)
      (Hstable: forall b ofs, Mem.perm (restrPermMap Hlt1') b ofs Cur Readable ->
                         ZMap.get ofs (Mem.mem_contents m1') # b = ZMap.get ofs (Mem.mem_contents m2') # b),
      mem_obs_eq f (restrPermMap Hlt1) (restrPermMap Hlt2').
  Proof.
    intros.
    destruct Hmem_obs_eq.
    constructor.
    destruct weak_obs_eq0.
    econstructor; eauto.
    intros; erewrite restrPermMap_valid.
    eapply Hextend'.
    eapply codomain_valid0; eauto.
    intros.
    rewrite! restrPermMap_Cur.
    specialize (perm_obs_weak0 _ _ ofs Hrenaming).
    rewrite! restrPermMap_Cur in perm_obs_weak0.
    eauto.
    destruct strong_obs_eq0.
    assert (Hperm_eq: forall (b1 b2 : block) (ofs : Z),
               f b1 = Some b2 ->
               permission_at (restrPermMap Hlt2') b2 ofs Cur =
               permission_at (restrPermMap Hlt1) b1 ofs Cur).
    { intros; rewrite! restrPermMap_Cur.
      specialize (perm_obs_strong0 _ _ ofs H).
      rewrite! restrPermMap_Cur in perm_obs_strong0.
      assumption.
    }
    constructor; eauto.
    intros.
    simpl.
    erewrite <- Hstable.
    eapply val_obs_eq0; eauto.
    unfold permission_at, Mem.perm in *.
    erewrite <- perm_obs_strong0 in Hperm; eauto.
  Qed.

  Lemma mapped_dec :
    forall (f : positive -> option positive) m j
      (Hdomain_invalid : forall b, ~ (b < m)%positive -> f b = None)
      (Hdomain_valid : forall b, (b < m)%positive -> exists b', f b = Some b'),
      (exists i, f i = Some j) \/ ~ exists i, f i = Some j.
  Proof.
    intros f m.
    generalize dependent f.
    induction m using Pos.peano_ind.
    - intros.
      right.
      intros (i & Hcontra).
      specialize (Hdomain_invalid i ltac:(zify; omega)).
      now congruence.
    - intros.
      destruct (f m) as [last|] eqn:Hf_last.
      + destruct (Pos.eq_dec last j); subst.
        * left; eexists; eauto.
        * pose (g x := if plt x m then f x else None).
          specialize (IHm g j).
          unfold g in IHm.
          edestruct IHm.
          intros.
          destruct (plt b m); simpl; eauto.
          intros.
          destruct (plt b m); simpl.
          eapply Hdomain_valid. zify; omega.
          exfalso.
          unfold Plt in n0.
          now auto.
          destruct H as [i Hfi].
          destruct (plt i m); simpl in Hfi; try discriminate.
          left; eexists; now eauto.
          right.
          intros (i & Hcontra).
          destruct (plt i m).
          apply H.
          exists i.
          destruct (plt i m); simpl; auto.
          exfalso; auto.
          unfold Plt in n0.
          apply Pos.le_nlt in n0.
          apply Pos.lt_eq_cases in n0.
          destruct n0 as [Hlt | Heq].
          specialize (Hdomain_invalid i ltac:(apply Pos.le_nlt; zify; omega)).
          now congruence.
          subst.
          rewrite Hcontra in Hf_last.
          inv Hf_last; now auto.
      + exfalso.
        destruct (Hdomain_valid m ltac:(zify; omega)).
        congruence.
  Qed.

  Lemma pigeon_positive:
    forall (n m: positive) (f: positive -> option positive),
      (forall i, (i < n)%positive ->
            exists j, (j < m)%positive /\ f i = Some j) ->
      (forall i i' j j',
          f i = Some j -> f i' = Some j' ->
          i<>i' -> j<>j') ->
      (n <= m)%positive.
  Proof.
    induction n using Pos.peano_ind; intros;
      first by (zify; omega).
    assert (Hlast: exists last, f n = Some last /\ (last<m)%positive).
    { destruct (H n) as [last [? ?]]. zify; omega.
      exists last; auto.
    }
    destruct Hlast as [last [Hf_last Hlast_m]].
    destruct m using Pos.peano_ind.
    - exfalso;
        eapply Pos.nlt_1_r;
        now eauto.
    - clear IHm.
      assert (Hmapped: (exists i, f i = Some m) \/ ~ (exists i, f i = Some m))
        by (apply Classical_Prop.classic).
      destruct Hmapped as [Hmapped | Hunmapped].
      + destruct Hmapped as [i Hf].
        pose (g x := if Pos.eq_dec x i then Some last else if Pos.eq_dec x n then Some m else f x).
        specialize (IHn m g).
        assert ((n <= m)%positive);
               [ | zify; omega].
        apply IHn.
        intros. unfold g.
        destruct (Pos.eq_dec i0 i); subst; simpl.
        * exists last; split; eauto.
          assert (last <> m)
            by (apply (H0 _ _ _ _ Hf_last Hf);
                zify; omega).
          zify; omega.
          destruct (Pos.eq_dec i0 n); subst; simpl;
            first by (zify; omega).
          generalize (H i0); intros.
          destruct H2 as [j [? ?]]. zify; omega.
          exists j; split; auto.
          assert (j <> m); [ | zify; omega].
          apply (H0 _ _ _ _ H3 Hf); auto.
          intros.
          unfold g in H1, H2.
          destruct (Pos.eq_dec i0 i); subst; simpl in *; inv H1.
          { destruct (Pos.eq_dec i' i); subst; simpl in *; inv H2.
            - zify; omega.
            - destruct (Pos.eq_dec i' n); subst; simpl in *; inv H4.
              + eapply H0; try eassumption.
              + eapply H0; try eassumption. zify; omega.
          }
          { destruct (Pos.eq_dec i' i); subst; simpl in *; inv H2.
            - destruct (Pos.eq_dec i0 n); subst; simpl in *; inv H5.
              + eapply H0; try eauto.
              + eapply H0; try eassumption.
            - destruct (Pos.eq_dec i0 n); subst; simpl in *; inv H5.
              + destruct (Pos.eq_dec i' n); subst; simpl in *; inv H4;
                eapply H0; eauto.
              + destruct (Pos.eq_dec i' n); subst; simpl in *; inv H4;
                  eapply H0; eauto.
          }
      + assert (n <= m)%positive; [ | zify; omega].
        apply (IHn m f).
        intros.
        destruct (H i). zify; omega. destruct H2; exists x; split; auto.
        assert (x<>m). contradict Hunmapped; subst.
        exists i; subst; auto.
        zify; omega.
        intros.
        apply (H0 _ _ _ _ H1 H2).
        now auto.
  Qed.

  (** If a memory [m] injects into a memory [m'] then [m'] is at least
as big as [m] *)
  Lemma weak_mem_obs_eq_nextblock:
    forall f m m'
      (Hobs_eq: weak_mem_obs_eq f m m'),
      (Mem.nextblock m <= Mem.nextblock m')%positive.
  Proof.
    intros.
    pose proof (domain_valid Hobs_eq).
    pose proof (codomain_valid Hobs_eq).
    pose proof (injective Hobs_eq).
    eapply pigeon_positive with (f := f); eauto.
    intros.
    destruct (H _ H2).
    specialize (H0 _ _ H3).
    unfold Mem.valid_block, Plt in *.
    eexists; split;
      now eauto.
    intros.
    intro Hcontra. subst.
    now eauto.
  Qed.

  Lemma mf_align :
    forall (m : mem) (f : memren) (b1 b2 : block) (delta : Z) (chunk : memory_chunk)
      (ofs : Z) (p : permission),
      f b1 = Some b2 ->
      Mem.range_perm m b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | 0%Z)%Z.
  Proof.
    intros.
      by apply mem_wd.align_chunk_0.
  Qed.

  Lemma memval_obs_eq_incr:
    forall (mc mf : mem) (f f': memren)
      (b1 b2 : block) (ofs : Z)
      (Hf': f' b1 = Some b2)
      (Hincr: ren_incr f f')
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

  (* Proof as in compcert*)
  Lemma proj_bytes_obs:
    forall (f : memren) (vl vl' : seq memval),
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
    forall (f : memren) (vl vl' : seq memval),
      Coqlib.list_forall2 (memval_obs_eq f) vl vl' ->
      proj_bytes vl = None -> proj_bytes vl' = None.
  Proof.
    induction 1; simpl. intros.  congruence.
    inversion H; subst; try congruence.
    destruct (proj_bytes al); intros.
    discriminate.
      by rewrite (IHlist_forall2 (Logic.eq_refl _)).
  Qed.

  Lemma val_obs_equal:
    forall f v1 v1' v2 v2'
      (Hinjective: forall b1 b1' b2, f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1')
      (Hval1: val_obs f v1 v1')
      (Hval2: val_obs f v2 v2'),
      Val.eq v1 v2 <-> Val.eq v1' v2'.
  Proof.
    intros.
    destruct v1; inv Hval1;
    split; intro H;
    match goal with
    | [H: is_true (proj_sumbool (Val.eq ?V1 ?V2)) |- _] =>
      destruct (Val.eq V1 V2)
    end; subst; try (by exfalso);
    inv Hval2; auto;
    match goal with
    | [|- is_true (proj_sumbool (Val.eq ?V1 ?V2))] =>
      destruct (Val.eq V1 V2)
    end; auto.
    rewrite H2 in H4; inv H4; auto.
    specialize (Hinjective _ _ _ H2 H3); subst.
    auto.
  Qed.

  Lemma check_value_obs:
    forall f n vl vl' v v' q
      (Hf: forall b1 b1' b2, f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1'),
      Coqlib.list_forall2 (memval_obs_eq f) vl vl' ->
      val_obs f v v' ->
      check_value n v q vl = check_value n v' q vl'.
  Proof.
    intros f n.
    induction n; intros; simpl in *.
    destruct vl; inv H; auto.
    destruct vl; inv H; auto.
    destruct m; inv H3; auto.
    erewrite IHn; eauto.
    assert (Val.eq v v0 <-> Val.eq v' v2)
      by (eapply val_obs_equal; eauto).
    destruct (Val.eq v v0) eqn:?.
    destruct (Val.eq v' v2); auto.
    exfalso. specialize ((proj1 H) ltac:(auto)); auto.
    destruct (Val.eq v' v2); auto.
    exfalso. specialize ((proj2 H) ltac:(auto)); auto.
  Qed.


  Lemma proj_value_obs:
    forall f q vl1 vl2,
      (forall b1 b1' b2 : block, f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1') ->
      Coqlib.list_forall2 (memval_obs_eq f) vl1 vl2 ->
      val_obs f (proj_value q vl1) (proj_value q vl2).
  Proof.
    intros f q vl1 v2 Hinjective Hlst. unfold proj_value.
    inversion Hlst; subst. constructor.
    inversion H; subst; try constructor.
    erewrite check_value_obs; eauto.
    destruct (check_value (size_quantity_nat q) v2 q (Fragment v2 q0 n :: bl));
      eauto with val_renamings.
  Qed.

  Lemma load_result_obs:
    forall f chunk v1 v2,
      val_obs f v1 v2 ->
      val_obs f (Val.load_result chunk v1) (Val.load_result chunk v2).
  Proof.
    intros. inversion H; destruct chunk; simpl; econstructor; eauto.
  Qed.

  Lemma decode_val_obs:
    forall f vl1 vl2 chunk,
      (forall b1 b1' b2 : block, f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1') ->
      Coqlib.list_forall2 (memval_obs_eq f) vl1 vl2 ->
      val_obs f (decode_val chunk vl1) (decode_val chunk vl2).
  Proof.
    intros f vl1 vl2 chunk Hinjective Hobs_eq.
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

  Lemma valid_access_obs_eq:
    forall f m1 m2 b1 b2 chunk ofs p,
      strong_mem_obs_eq f m1 m2 ->
      f b1 = Some b2 ->
      Mem.valid_access m1 chunk b1 ofs p ->
      Mem.valid_access m2 chunk b2 ofs p.
  Proof.
    intros. destruct H1 as [A B]. constructor; auto.
    intros ofs' Hofs.
    specialize (A ofs' Hofs).
    destruct H.
    specialize (perm_obs_strong0 _ _ ofs' H0).
    unfold permission_at in *.
    unfold Mem.perm in *.
    rewrite perm_obs_strong0; auto.
  Qed.

  Lemma valid_access_obs_eq':
    forall f m1 m2 b1 b2 chunk ofs p,
      strong_mem_obs_eq f m1 m2 ->
      f b1 = Some b2 ->
      Mem.valid_access m2 chunk b2 ofs p ->
      Mem.valid_access m1 chunk b1 ofs p.
  Proof.
    intros. destruct H1 as [A B]. constructor; auto.
    intros ofs' Hofs.
    specialize (A ofs' Hofs).
    destruct H.
    specialize (perm_obs_strong0 _ _ ofs' H0).
    unfold permission_at in *.
    unfold Mem.perm in *.
    rewrite <- perm_obs_strong0; auto.
  Qed.

  Lemma getN_obs:
    forall f m1 m2 b1 b2,
      strong_mem_obs_eq f m1 m2 ->
      f b1 = Some b2 ->
      forall n ofs,
        Mem.range_perm m1 b1 ofs (ofs + Z_of_nat n) Cur Readable ->
        list_forall2 (memval_obs_eq f)
                     (Mem.getN n ofs (m1.(Mem.mem_contents)#b1))
                     (Mem.getN n ofs (m2.(Mem.mem_contents)#b2)).
  Proof.
    induction n; intros; simpl.
    constructor.
    rewrite inj_S in H1.
    destruct H.
    constructor.
    eapply val_obs_eq0; eauto.
    apply H1. omega.
    apply IHn. red; intros; apply H1; omega.
  Qed.

  Transparent Mem.load.
  Lemma load_val_obs:
    forall (mc mf : mem) (f:memren)
      (b1 b2 : block) chunk (ofs : Z) v1
      (Hload: Mem.load chunk mc b1 ofs = Some v1)
      (Hf: f b1 = Some b2)
      (Hinjective: forall b0 b1' b3 : block, f b0 = Some b3 -> f b1' = Some b3 -> b0 = b1')
      (Hobs_eq: strong_mem_obs_eq f mc mf),
    exists v2,
      Mem.load chunk mf b2 ofs = Some v2 /\
      val_obs f v1 v2.
  Proof.
    intros.
    exists (decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs (mf.(Mem.mem_contents)#b2))).
    split. unfold Mem.load. apply pred_dec_true.
    eapply valid_access_obs_eq; eauto.
    eapply Mem.load_valid_access; eauto.
    exploit Mem.load_result; eauto. intro. rewrite H.
    apply decode_val_obs; auto.
    apply getN_obs; auto.
    rewrite <- size_chunk_conv.
    exploit Mem.load_valid_access; eauto. intros [A B]. auto.
  Qed.

  Lemma load_None_obs:
    forall (mc mf : mem) (f:memren)
      (b1 b2 : block) chunk (ofs : Z)
      (Hload: Mem.load chunk mc b1 ofs = None)
      (Hf: f b1 = Some b2)
      (Hinjective: forall b0 b1' b3 : block, f b0 = Some b3 -> f b1' = Some b3 -> b0 = b1')
      (Hobs_eq: strong_mem_obs_eq f mc mf),
    Mem.load chunk mf b2 ofs = None.
  Proof.
    intros.
    unfold Mem.load in *.
    destruct (Mem.valid_access_dec _ _ _ _ _); try discriminate.
    destruct (Mem.valid_access_dec _ _ _ _ _); auto.
    eapply valid_access_obs_eq' in v; eauto; contradiction.
  Qed.
  Opaque Mem.load.

  Lemma loadv_val_obs:
    forall (mc mf : mem) (f:memren)
      (vptr1 vptr2 : val) chunk v1
      (Hload: Mem.loadv chunk mc vptr1 = Some v1)
      (Hf: val_obs f vptr1 vptr2)
      (Hinjective: forall b0 b1' b3 : block, f b0 = Some b3 -> f b1' = Some b3 -> b0 = b1')
      (Hobs_eq: strong_mem_obs_eq f mc mf),
    exists v2,
      Mem.loadv chunk mf vptr2 = Some v2 /\
      val_obs f v1 v2.
  Proof.
    intros.
    unfold Mem.loadv in *.
    destruct vptr1; try discriminate.
    inversion Hf; subst.
    eapply load_val_obs in Hload; eauto.
  Qed.

  Lemma loadv_None_obs:
    forall (mc mf : mem) (f:memren)
      (vptr1 vptr2 : val) chunk
      (Hload: Mem.loadv chunk mc vptr1 = None)
      (Hf: val_obs f vptr1 vptr2)
      (Hinjective: forall b0 b1' b3 : block, f b0 = Some b3 -> f b1' = Some b3 -> b0 = b1')
      (Hobs_eq: strong_mem_obs_eq f mc mf),
      Mem.loadv chunk mf vptr2 = None.
  Proof.
    intros.
    unfold Mem.loadv in *.
    destruct vptr2; auto.
    inv Hf.
    eapply load_None_obs in Hload; eauto.
  Qed.

  Transparent Mem.loadbytes.
  Lemma loadbytes_val_obs:
    forall (mc mf : mem) (f:memren)
      (b1 b2 : block) (ofs sz : Z) mv
      (Hsz: sz >= 0)
      (Hload: Mem.loadbytes mc b1 ofs sz = Some mv)
      (Hf: f b1 = Some b2)
      (Hinjective: forall b0 b1' b3 : block, f b0 = Some b3 -> f b1' = Some b3 -> b0 = b1')
      (Hobs_eq: strong_mem_obs_eq f mc mf),
    exists mv',
      Mem.loadbytes mf b2 ofs sz = Some mv' /\
      list_forall2 (fun a b => memval_obs_eq f a b) mv mv'.
  Proof.
    intros.
    unfold Mem.loadbytes in *.
    destruct (Mem.range_perm_dec mc b1 ofs (ofs + sz) Cur Readable) as [Hperm|]; try discriminate.
    destruct (Mem.range_perm_dec mf b2 ofs (ofs + sz) Cur Readable) as [Hperm'|Hcontra].
    - replace sz with (Z.of_nat (nat_of_Z sz)) in Hperm by (eapply Z2Nat.id; ssromega).
      eapply getN_obs in Hperm; eauto.
      exists (Mem.getN (nat_of_Z sz) ofs (Mem.mem_contents mf) # b2).
      inv Hload.
      split;
        now auto.
    - unfold Mem.range_perm in *.
      exfalso.
      eapply Hcontra.
      intros ofs0 Hofs0.
      specialize (Hperm _ Hofs0).
      destruct Hobs_eq as [Hperm_eq _].
      unfold Mem.perm, permission_at in *.
      erewrite Hperm_eq by eauto.
      now auto.
  Qed.
  Opaque Mem.loadbytes.
  
  (** ** Lemmas about [Mem.store] and [mem_obs_eq]*)

  Lemma encode_val_obs_eq:
    forall (f : memren) (v1 v2 : val) (chunk : memory_chunk),
      val_obs f v1 v2 ->
      list_forall2 (memval_obs_eq f) (encode_val chunk v1)
                   (encode_val chunk v2).
  Proof.
    intros.
    destruct v1; inversion H; subst; destruct chunk;
    simpl; repeat constructor; auto.
  Qed.

  Lemma setN_obs_eq :
    forall (access : Z -> Prop) (f : memren) (vl1 vl2 : seq memval),
      list_forall2 (memval_obs_eq f) vl1 vl2 ->
      forall (p : Z) (c1 c2 : ZMap.t memval),
        (forall q : Z,
            access q ->
            memval_obs_eq f (ZMap.get q c1) (ZMap.get q c2)) ->
        forall q : Z,
          access q ->
          memval_obs_eq f (ZMap.get q (Mem.setN vl1 p c1))
                        (ZMap.get q (Mem.setN vl2 p c2)).
  Proof.
    induction 1; intros; simpl.
    auto.
    apply IHlist_forall2; auto.
    intros. erewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
    rewrite ZMap.gss. auto.
    rewrite ZMap.gso. auto. unfold ZIndexed.t in *. omega.
  Qed.


  (** Storing related values on related memories results in related memories*)
  Transparent Mem.store.
  Lemma store_val_obs:
    forall (mc mc' mf : mem) (f:memren)
      (b1 b2 : block) chunk (ofs: Z) v1 v2
      (Hstore: Mem.store chunk mc b1 ofs v1 = Some mc')
      (Hf: f b1 = Some b2)
      (Hval_obs_eq: val_obs f v1 v2)
      (Hobs_eq: mem_obs_eq f mc mf),
    exists mf',
      Mem.store chunk mf b2 ofs v2 = Some mf' /\
      mem_obs_eq f mc' mf'.
  Proof.
    intros.
    pose proof (strong_obs_eq Hobs_eq) as Hstrong_obs_eq.
    assert (HvalidF: Mem.valid_access mf chunk b2 ofs Writable).
      by (eapply valid_access_obs_eq; eauto with mem).
    destruct (Mem.valid_access_store _ _ _ _ v2 HvalidF) as [mf' HstoreF].
    exists mf'; split. auto.
    constructor.
    { pose proof (weak_obs_eq Hobs_eq).
      inversion H.
      constructor; simpl; auto; intros.
      eapply domain_invalid0. intro Hcontra.
      eapply Mem.store_valid_block_1 in Hcontra; eauto.
      eapply Mem.store_valid_block_2 in H0; eauto.
      eapply Mem.store_valid_block_1; eauto.
      assert (H1 := mem_store_cur _ _ _ _ _ _ Hstore b0 ofs0).
      assert (H2 := mem_store_cur _ _ _ _ _ _ HstoreF b3 ofs0).
      do 2 rewrite getCurPerm_correct in H1.
      do 2 rewrite getCurPerm_correct in H2.
      rewrite <- H1.
      rewrite <- H2.
      eauto.
    }
    { destruct Hstrong_obs_eq.
      constructor.
      - intros.
        assert (H1 := mem_store_cur _ _ _ _ _ _ Hstore b0 ofs0).
        assert (H2 := mem_store_cur _ _ _ _ _ _ HstoreF b3 ofs0).
        do 2 rewrite getCurPerm_correct in H1.
        do 2 rewrite getCurPerm_correct in H2.
        rewrite <- H1.
        rewrite <- H2.
        eauto.
      - intros.
        eapply Mem.perm_store_2 in Hperm; eauto.
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ HstoreF).
        clear Hstore HstoreF.
        destruct (Pos.eq_dec b1 b0).
        + subst.
          assert (b2 = b3)
            by (rewrite Hrenaming in Hf; inversion Hf; subst; auto).
          subst b3.
          do 2 rewrite Maps.PMap.gss.
          destruct (Intv.In_dec ofs0
                                (ofs,
                                 (ofs + Z.of_nat (length (encode_val chunk v1)))%Z)).
          * apply setN_obs_eq with
            (access := fun ofs => Mem.perm mc b0 ofs Cur Readable); auto.
            eapply encode_val_obs_eq; eauto.
          * apply Intv.range_notin in n.
            simpl in n.
            erewrite Mem.setN_outside by eauto.
            apply encode_val_obs_eq with (chunk := chunk) in Hval_obs_eq.
            apply list_forall2_length in Hval_obs_eq. rewrite Hval_obs_eq in n.
            erewrite Mem.setN_outside by eauto.
            eauto.
            clear.
            simpl.
            apply ofs_val_lt.
        + rewrite Maps.PMap.gso; auto.
          rewrite Maps.PMap.gso; auto.
          intros Hcontra. subst.
          pose proof (injective (weak_obs_eq Hobs_eq)).
          specialize (H _ _ _ Hrenaming Hf). auto.
    }
  Qed.
  Opaque Mem.store.

  Lemma storev_val_obs:
    forall (mc mc' mf : mem) (f:memren)
      (vptr1 vptr2: val) chunk v1 v2
      (Hstore: Mem.storev chunk mc vptr1 v1 = Some mc')
      (Hf: val_obs f vptr1 vptr2)
      (Hval_obs_eq: val_obs f v1 v2)
      (Hobs_eq: mem_obs_eq f mc mf),
    exists mf',
      Mem.storev chunk mf vptr2 v2 = Some mf' /\
      mem_obs_eq f mc' mf'.
  Proof.
    intros.
    unfold Mem.storev in *.
    destruct vptr1; try discriminate.
    inversion Hf; subst.
    eapply store_val_obs in Hstore; eauto.
  Qed.

  Transparent Mem.storebytes.
  Lemma storebytes_val_obs:
    forall (mc mc' mf : mem) (f:memren)
      (b1 b2 : block) (ofs: Z) mv1 mv2
      (Hstore: Mem.storebytes mc b1 ofs mv1 = Some mc')
      (Hf: f b1 = Some b2)
      (Hval_obs_eq: list_forall2 (fun a b => memval_obs_eq f a b) mv1 mv2)
      (Hobs_eq: mem_obs_eq f mc mf),
    exists mf',
      Mem.storebytes mf b2 ofs mv2 = Some mf' /\
      mem_obs_eq f mc' mf'.
  Proof.
    intros.
    unfold Mem.storebytes in *.
    destruct (Mem.range_perm_dec mc b1 ofs (ofs + Z.of_nat (length mv1)) Cur Writable)
      as [Hperm|]; try discriminate.
    inv Hstore.
    destruct (Mem.range_perm_dec mf b2 ofs (ofs + Z.of_nat (length mv2)) Cur Writable)
      as [Hperm'|Hcontra].
    - eexists.
      split; [reflexivity|].
      destruct Hobs_eq.
      destruct weak_obs_eq0, strong_obs_eq0.
      econstructor; econstructor; eauto.
      intros.
      unfold Mem.perm in Hperm0.
      simpl in Hperm0.
      simpl.
      destruct (Pos.eq_dec b1 b0).
      + subst.
        assert (b2 = b3)
          by (rewrite Hrenaming in Hf; inversion Hf; subst; auto).
        subst b3.
        do 2 rewrite Maps.PMap.gss.
        (* destruct (Intv.In_dec ofs0 *)
        (*                       (ofs, *)
        (*                        (ofs + Z.of_nat (length (encode_val chunk v1)))%Z)). *)
        apply setN_obs_eq with
            (access := fun ofs => Mem.perm mc b0 ofs Cur Readable);
          now auto.
      + rewrite Maps.PMap.gso; auto.
        rewrite Maps.PMap.gso; auto.
        intros Hcontra. subst.
        specialize (injective0 _ _ _ Hrenaming Hf).
        now auto.
    - unfold Mem.range_perm in *.
      exfalso.
      eapply Hcontra.
      intros ofs0 Hofs0.
      eapply list_forall2_length in Hval_obs_eq.
      rewrite <- Hval_obs_eq in Hofs0.
      specialize (Hperm _ Hofs0).
      destruct Hobs_eq as [_ Hstrong_obs_eq].
      destruct Hstrong_obs_eq as [Hperm_eq _].
      unfold Mem.perm, permission_at in *.
      erewrite Hperm_eq by eauto.
      now auto.
  Qed.
  Opaque Mem.storebytes.

  Lemma mem_obs_eq_storeF:
    forall f mc mf mf' chunk b ofs v pmap pmap2
      (Hlt: permMapLt pmap (getMaxPerm mf))
      (Hlt': permMapLt pmap (getMaxPerm mf'))
      (Hlt2: permMapLt pmap2 (getMaxPerm mf))
      (Hstore: Mem.store chunk (restrPermMap Hlt2) b ofs v = Some mf')
      (Hdisjoint: permMapCoherence pmap pmap2 \/ permMapsDisjoint pmap pmap2)
      (Hobs_eq: mem_obs_eq f mc (restrPermMap Hlt)),
      mem_obs_eq f mc (restrPermMap Hlt').
  Proof.
    intros.
    destruct Hobs_eq as [Hweak_obs_eq Hstrong_obs_eq].
    destruct Hweak_obs_eq.
    constructor.
    (* weak_obs_eq *)
    constructor; auto.
    intros b1 b2 Hf.
    erewrite restrPermMap_valid.
    specialize (codomain_valid0 _ _ Hf).
    erewrite restrPermMap_valid in codomain_valid0.
    eapply Mem.store_valid_block_1;
      by eauto.
    intros b1 b2 ofs0 Hf.
    specialize (perm_obs_weak0 _ _ ofs0 Hf).
    rewrite restrPermMap_Cur in perm_obs_weak0;
      by rewrite restrPermMap_Cur.
    destruct Hstrong_obs_eq.
    constructor.
    intros b1 b2 ofs0 Hf.
    specialize (perm_obs_strong0 _ _ ofs0 Hf).
    rewrite restrPermMap_Cur in perm_obs_strong0;
      by rewrite restrPermMap_Cur.
    intros b1 b2 ofs0 Hf Hperm.
    simpl.
    specialize (perm_obs_strong0 _ _ ofs0 Hf).
    rewrite restrPermMap_Cur in perm_obs_strong0.
    assert (Hstable: ~ Mem.perm (restrPermMap Hlt2) b2 ofs0 Cur Writable).
    { intros Hcontra.
      assert (Hcur := restrPermMap_Cur Hlt2 b2 ofs0).
      unfold Mem.perm in *.
      unfold permission_at in *.
      rewrite <- perm_obs_strong0 in Hperm.
      rewrite Hcur in Hcontra.
      destruct Hdisjoint as [Hdisjoint | Hdisjoint];
      specialize (Hdisjoint b2 ofs0);
      clear - Hdisjoint Hcontra Hperm.
      destruct (pmap # b2 ofs0) as [p1|];
        destruct (pmap2 # b2 ofs0) as [p2|];
        simpl in *; inversion Hperm; inversion Hcontra; subst;
          auto.
      eapply perm_order_clash; eauto.
    }
    erewrite store_contents_other with (m := restrPermMap Hlt2) (m' := mf')
      by eauto.
    simpl;
      by auto.
  Qed.

  Lemma mem_obs_eq_disjoint_lock:
    forall f  mc mf mc' mf' pmap pmapF bl1 bl2 ofsl sz
      (Hf: f bl1 = Some bl2)
      (Hlt: permMapLt pmap (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (Hlt': permMapLt pmap (getMaxPerm mc'))
      (HltF': permMapLt pmapF (getMaxPerm mf'))
      (Hvb : forall b : block, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      (HvbF : forall b : block, Mem.valid_block mf b <-> Mem.valid_block mf' b)
      (Hobs_eq: mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hlock: forall ofs, Intv.In ofs (ofsl, ofsl + sz)%Z ->
                     memval_obs_eq f (ZMap.get ofs (Mem.mem_contents mc') # bl1)
                                   (ZMap.get ofs (Mem.mem_contents mf') # bl2))
      (Hstable: forall b ofs,
          (b <> bl1 \/ (b = bl1 /\ ~ Intv.In ofs (ofsl, ofsl + sz)%Z)) ->
          Mem.perm (restrPermMap Hlt) b ofs Cur Readable ->
          ZMap.get ofs (Mem.mem_contents mc) # b = ZMap.get ofs (Mem.mem_contents mc') # b)
      (HstableF: forall b ofs,
          (b <> bl2 \/ (b = bl2 /\  ~ Intv.In ofs (ofsl, ofsl + sz)%Z)) ->
          Mem.perm (restrPermMap HltF) b ofs Cur Readable ->
          ZMap.get ofs (Mem.mem_contents mf) # b = ZMap.get ofs (Mem.mem_contents mf') # b),
      mem_obs_eq f (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
    intros.
    destruct Hobs_eq as [Hweak_obs_eq Hstrong_obs_eq].
    constructor.
    - destruct Hweak_obs_eq.
      constructor; intros; eauto.
      + eapply domain_invalid0.
        erewrite restrPermMap_valid in *.
        intro Hcontra; eapply Hvb in Hcontra.
        now auto.
      + erewrite restrPermMap_valid in H.
        erewrite <- Hvb in H.
        now eauto.
      + erewrite restrPermMap_valid.
        apply HvbF.
        eapply codomain_valid0;
          now eauto.
      + rewrite! restrPermMap_Cur.
        specialize (perm_obs_weak0 _ _ ofs Hrenaming).
        rewrite! restrPermMap_Cur in perm_obs_weak0.
        assumption.
    - destruct Hstrong_obs_eq.
      constructor.
      + intros.
        rewrite! restrPermMap_Cur.
        specialize (perm_obs_strong0 _ _ ofs Hrenaming).
        rewrite! restrPermMap_Cur in perm_obs_strong0.
        assumption.
      + intros.
        unfold Mem.perm in *.
        pose proof (restrPermMap_Cur Hlt b1 ofs) as Hpmap.
        pose proof (restrPermMap_Cur Hlt' b1 ofs) as Hpmap'.
        unfold permission_at in *.
        rewrite Hpmap' in Hperm.
        rewrite <- Hpmap in Hperm.
        specialize (val_obs_eq0 _ _ ofs Hrenaming Hperm).
        simpl in val_obs_eq0; simpl.
        destruct (Pos.eq_dec b1 bl1).
        * subst.
          assert (b2 = bl2)
            by (rewrite Hf in Hrenaming; inversion Hrenaming; by subst);
            subst.
          destruct (Intv.In_dec ofs (ofsl, ofsl +sz)%Z);
            first by (eapply Hlock; eauto).
          erewrite <- Hstable by auto.
          erewrite <- HstableF.
          assumption.
          right; auto.
          erewrite perm_obs_strong0 by eauto.
          assumption.
        * erewrite <- Hstable by auto.
          erewrite <- HstableF.
          assumption.
          left. intro Hcontra.
          eapply (injective Hweak_obs_eq) in Hf;
            subst b2; eauto.
          erewrite perm_obs_strong0 by eauto.
          assumption.
  Qed.

  Lemma mem_obs_eq_changePerm:
    forall mc mf rmap rmapF rmap' rmapF' f
      (Hlt: permMapLt rmap (getMaxPerm mc))
      (HltF: permMapLt rmapF (getMaxPerm mf))
      (Hlt': permMapLt rmap' (getMaxPerm mc))
      (HltF': permMapLt rmapF' (getMaxPerm mf))
      (Hrmap: forall b1 b2 ofs,
          f b1 = Some b2 ->
          rmap' # b1 ofs = rmapF' # b2 ofs)
      (Hobs_eq: mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hnew: forall b ofs, Mem.perm_order' (rmap' # b ofs) Readable ->
                      Mem.perm_order' (rmap # b ofs) Readable),
      mem_obs_eq f (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
    intros.
    destruct Hobs_eq.
    constructor.
    - destruct weak_obs_eq0.
      constructor; eauto.
      intros.
      rewrite! restrPermMap_Cur.
      erewrite Hrmap by eauto.
      now apply po_refl.
    - destruct strong_obs_eq0.
      constructor.
      intros.
      rewrite! restrPermMap_Cur.
      erewrite Hrmap by eauto.
      reflexivity.
      intros.
      unfold Mem.perm in Hperm.
      pose proof (restrPermMap_Cur Hlt' b1 ofs) as Heq.
      unfold permission_at in Heq.
      rewrite Heq in Hperm.
      specialize (Hnew _ _ Hperm).
      simpl.
      eapply val_obs_eq0; eauto.
      unfold Mem.perm.
      pose proof (restrPermMap_Cur Hlt b1 ofs) as Heq'.
      unfold permission_at in Heq'.
      rewrite Heq'.
      assumption.
  Qed.

  Lemma weak_mem_obs_eq_store:
    forall mc mf mc' mf' rmap rmapF bl1 bl2 f
      (Hlt: permMapLt rmap (getMaxPerm mc))
      (HltF: permMapLt rmapF (getMaxPerm mf))
      (Hlt2: permMapLt rmap (getMaxPerm mc'))
      (Hlt2F: permMapLt rmapF (getMaxPerm mf'))
      (Hf: f bl1 = Some bl2)
      (Hinjective: forall b1 b1' b2 : block, f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1')
      (Hobs_eq: weak_mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b),
      weak_mem_obs_eq f (restrPermMap Hlt2) (restrPermMap Hlt2F).
  Proof.
    intros.
    destruct Hobs_eq.
    constructor;
      try (intros b1; erewrite restrPermMap_valid);
      try (erewrite <- Hvb');
      try (erewrite <- Hvb);
      try by eauto.
      intros b1 b2 Hf1. erewrite restrPermMap_valid.
      erewrite <- HvbF.
      specialize (codomain_valid0 _ _ Hf1);
        by erewrite restrPermMap_valid in codomain_valid0.
      intros b1 b2 ofs0 Hf1.
      do 2 rewrite restrPermMap_Cur.
      specialize (perm_obs_weak0 _ _ ofs0 Hf1).
      rewrite! restrPermMap_Cur in perm_obs_weak0.
      assumption.
  Qed.

  (*TODO: Generalize what is stored, chunk, value, etc.*)
  Lemma strong_mem_obs_eq_store:
    forall mc mf mc' mf' rmap rmapF bl1 bl2 ofsl f v
      (Hlt: permMapLt rmap (getMaxPerm mc))
      (HltF: permMapLt rmapF (getMaxPerm mf))
      (Hlt2: permMapLt rmap (getMaxPerm mc'))
      (Hlt2F: permMapLt rmapF (getMaxPerm mf'))
      (Hf: f bl1 = Some bl2)
      (Hinjective: forall b1 b1' b2 : block, f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1')
      (Hobs_eq: strong_mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hstore: Mem.mem_contents mc' = PMap.set bl1 (Mem.setN (encode_val Mint32 (Vint v)) ofsl (Mem.mem_contents mc) # bl1)
                                               (Mem.mem_contents mc))
      (HstoreF: Mem.mem_contents mf' = PMap.set bl2 (Mem.setN (encode_val Mint32 (Vint v)) ofsl (Mem.mem_contents mf) # bl2)
                                                (Mem.mem_contents mf))
      (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b),
      strong_mem_obs_eq f (restrPermMap Hlt2) (restrPermMap Hlt2F).
  Proof.
    intros.
    assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
      by (intros; split; intros Hinvalid Hcontra;
            by apply Hvb in Hcontra).
    (** proof of [strong_mem_obs_eq]*)
    destruct Hobs_eq.
    constructor.
    - intros b1 b2 ofs0 Hf1.
      specialize (perm_obs_strong0 _ _ ofs0 Hf1).
      erewrite! restrPermMap_Cur in *.
      assumption.
    - intros b1 b2 ofs0 Hf1 Hperm.
      unfold Mem.perm in *.
      assert (Hperm_eq2 := restrPermMap_Cur Hlt2 b1 ofs0).
      assert (Hperm_eq := restrPermMap_Cur Hlt b1 ofs0).
      unfold permission_at in Hperm_eq, Hperm_eq2.
      rewrite Hperm_eq2 in Hperm.
      specialize (val_obs_eq0 _ _ ofs0 Hf1).
      rewrite Hperm_eq in val_obs_eq0.
      specialize (val_obs_eq0 Hperm).
      simpl.
      rewrite Hstore HstoreF.
      destruct (Pos.eq_dec b1 bl1) as [Heq | Hneq];
        [| assert (b2 <> bl2)
           by (intros Hcontra; subst;
               apply Hneq; eapply Hinjective; eauto);
           subst;
           erewrite! Maps.PMap.gso by auto;
           assumption].
      subst bl1.
      assert (b2 = bl2)
        by (rewrite Hf1 in Hf; inversion Hf; by subst); subst bl2.
      rewrite! Maps.PMap.gss.
      destruct (Z_lt_le_dec ofs0 ofsl) as [Hofs_lt | Hofs_ge].
      erewrite! Mem.setN_outside by (left; auto);
        by assumption.
      destruct (Z_lt_ge_dec
                  ofs0 (ofsl + (size_chunk Mint32)))
        as [Hofs_lt | Hofs_ge'].

      apply setN_obs_eq with (access := fun q => q = ofs0);
        eauto using encode_val_obs_eq, val_obs.
      intros; subst; assumption.

      erewrite! Mem.setN_outside by (right; rewrite size_chunk_conv in Hofs_ge';
                                       by rewrite encode_val_length);
        by auto.
  Qed.

  Corollary mem_obs_eq_store :
    forall (mc mf mc' mf' : mem) (rmap rmapF : access_map) (bl1 bl2 : block) (ofsl : Z) f v
      (Hlt : permMapLt rmap (getMaxPerm mc)) (HltF : permMapLt rmapF (getMaxPerm mf))
      (Hlt2 : permMapLt rmap (getMaxPerm mc'))
      (Hlt2F : permMapLt rmapF (getMaxPerm mf'))
      (Hfl: f bl1 = Some bl2)
      (Hinjective: forall b1 b1' b2 : block,
          f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1')
      (Hmem_obs_eq: mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hcontents: Mem.mem_contents mc' =
                  PMap.set bl1 (Mem.setN (encode_val Mint32 (Vint v)) ofsl
                                         (Mem.mem_contents mc) # bl1) (Mem.mem_contents mc))
      (HcontentsF: Mem.mem_contents mf' =
                   PMap.set bl2 (Mem.setN (encode_val Mint32 (Vint v)) ofsl
                                          (Mem.mem_contents mf) # bl2) (Mem.mem_contents mf))
      (Hvb: forall b : block, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      (HvbF: forall b : block, Mem.valid_block mf b <-> Mem.valid_block mf' b),
      mem_obs_eq f (restrPermMap Hlt2) (restrPermMap Hlt2F).
  Proof.
    intros;
      destruct Hmem_obs_eq;
      constructor;
      eauto using weak_mem_obs_eq_store, strong_mem_obs_eq_store.
  Qed.


  Lemma alloc_perm_eq:
    forall f m m' lo hi m2 m2' b b'
      (Hobs_eq: mem_obs_eq f m m')
      (Halloc: Mem.alloc m lo hi = (m2, b))
      (Halloc': Mem.alloc m' lo hi = (m2', b'))
      b1 b2 ofs
      (Hf: (if proj_sumbool (valid_block_dec m b1)
            then f b1
            else if proj_sumbool (valid_block_dec m2 b1)
                 then Some b' else None) = Some b2),
      permission_at m2 b1 ofs Cur =
      permission_at m2' b2 ofs Cur.
  Proof.
    intros.
    destruct (valid_block_dec m b1); simpl in Hf.
    - assert (H := perm_obs_strong (strong_obs_eq Hobs_eq) _ ofs Hf).
      erewrite <- permission_at_alloc_1; eauto.
      erewrite <- permission_at_alloc_1 with (m' := m2'); eauto.
      eapply (codomain_valid (weak_obs_eq Hobs_eq));
        by eauto.
    - destruct (valid_block_dec m2 b1); simpl in *; try discriminate.
      inv Hf.
      eapply Mem.valid_block_alloc_inv in v; eauto.
      destruct v; subst; try (by exfalso).
      destruct (zle lo ofs), (zlt ofs hi);
        [erewrite permission_at_alloc_2 by eauto;
         erewrite permission_at_alloc_2 by eauto;
         reflexivity | | |];
        erewrite permission_at_alloc_3 by (eauto; omega);
        erewrite permission_at_alloc_3 by (eauto; omega);
        auto.
  Qed.

Lemma setPermBlock_var_eq:
    forall f bl1 bl2 ofsl b1 b2 ofs pmap pmap' p
      (Hf: f b1 = Some b2)
      (Hfl: f bl1 = Some bl2)
      (Hinjective: forall b1 b1' b2 : block,
          f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1')
      (Hperm: pmap # b1 ofs = pmap' # b2 ofs),
      (setPermBlock_var p bl1 ofsl pmap
                    lksize.LKSIZE_nat) # b1 ofs =
      (setPermBlock_var p bl2 ofsl pmap'
                    lksize.LKSIZE_nat) # b2 ofs.
  Proof.
    intros.
    destruct (Pos.eq_dec b1 bl1).
    - subst.
      assert (b2 = bl2)
        by (rewrite Hf in Hfl; inversion Hfl; subst; auto).
      subst.
      destruct (Intv.In_dec ofs (ofsl, (ofsl + lksize.LKSIZE)%Z)).
      + erewrite setPermBlock_var_same by eauto.
        erewrite setPermBlock_var_same by eauto.
        reflexivity.
      + apply Intv.range_notin in n.
        simpl in n.
        erewrite setPermBlock_var_other_1 by eauto.
        erewrite setPermBlock_var_other_1 by eauto.
        eauto.
        simpl.
        eapply Z.lt_add_pos_r.
        now apply lksize.LKSIZE_pos.
    - erewrite setPermBlock_var_other_2 by eauto.
      assert (b2 <> bl2)
        by (intros Hcontra;
            subst; specialize (Hinjective _ _ _ Hf Hfl); subst; auto).
      erewrite setPermBlock_var_other_2 by eauto.
      eauto.
  Qed.

  Lemma setPermBlock_var_weak_obs_eq:
    forall (f : block -> option block) (bl1 bl2 : block) (ofsl : Z)
      (pmap pmapF : access_map) (mc mf : mem) p (Hlt : permMapLt pmap (getMaxPerm mc))
      (HltF : permMapLt pmapF (getMaxPerm mf))
      (Hfl: f bl1 = Some bl2)
      (Hweak_obs_eq: weak_mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hlt' : permMapLt (setPermBlock_var p bl1 ofsl pmap lksize.LKSIZE_nat) (getMaxPerm mc))
      (HltF' : permMapLt (setPermBlock_var p bl2 ofsl pmapF lksize.LKSIZE_nat) (getMaxPerm mf)),
      weak_mem_obs_eq f (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
    intros.
    destruct Hweak_obs_eq.
    constructor; eauto.
    intros.
    rewrite! restrPermMap_Cur.
    specialize (perm_obs_weak0 _ _ ofs Hrenaming).
    rewrite! restrPermMap_Cur in perm_obs_weak0.
    destruct (Pos.eq_dec bl1 b1).
    + subst.
      assert (b2 = bl2) by (rewrite Hrenaming in Hfl; inversion Hfl; by subst);
        subst.
      destruct (Intv.In_dec ofs (ofsl, ofsl + lksize.LKSIZE)%Z).
      * erewrite! setPermBlock_var_same
          by (unfold lksize.LKSIZE in i;
              simpl in *;
              auto).
        now apply po_refl.
      * erewrite! setPermBlock_var_other_1; eauto;
          by (apply Intv.range_notin in n; eauto;
              simpl in *; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
    + assert (bl2 <> b2)
        by (intros ?; subst; apply n; eauto).
      erewrite! setPermBlock_var_other_2 by assumption.
      assumption.
  Qed.

  Lemma setPermBlock_var_obs_eq:
    forall f bl1 bl2 ofsl pmap pmapF mc mf p
      (Hlt: permMapLt pmap (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (Hfl: f bl1 = Some bl2)
      (Hval_obs_eq: forall ofs0, (ofsl <= ofs0 < ofsl + Z.of_nat (lksize.LKSIZE_nat))%Z ->
                            memval_obs_eq f (ZMap.get ofs0 (Mem.mem_contents mc) # bl1)
                                          (ZMap.get ofs0 (Mem.mem_contents mf) # bl2))
      (Hobs_eq: mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hlt': permMapLt (setPermBlock_var p bl1 ofsl pmap lksize.LKSIZE_nat) (getMaxPerm mc))
      (HltF': permMapLt (setPermBlock_var p bl2 ofsl pmapF lksize.LKSIZE_nat) (getMaxPerm mf)),
      mem_obs_eq f (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
    intros.
    destruct Hobs_eq.
    constructor;
      first by (eapply setPermBlock_var_weak_obs_eq; eauto).
    destruct strong_obs_eq0.
    constructor.
    - intros b1 b2 ofs Hf.
      specialize (perm_obs_strong0 _ _ ofs Hf).
      erewrite! restrPermMap_Cur in *.
      pose proof (injective weak_obs_eq0).
      erewrite <- setPermBlock_var_eq; eauto.
    - intros.
      simpl.
      pose proof (restrPermMap_Cur Hlt' b1 ofs).
      unfold permission_at in H.
      unfold Mem.perm in *.
      rewrite H in Hperm.
      destruct (Pos.eq_dec bl1 b1).
      + subst.
        destruct (Intv.In_dec ofs (ofsl, ofsl + lksize.LKSIZE)%Z).
        erewrite! setPermBlock_var_same in Hperm
          by (unfold lksize.LKSIZE in i;
              simpl in *;
              auto).
        rewrite Hfl in Hrenaming; inversion Hrenaming; subst.
        eapply Hval_obs_eq;
          by eauto.
        erewrite! setPermBlock_var_other_1 in Hperm
          by (apply Intv.range_notin in n; eauto;
              simpl in *; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
          eapply val_obs_eq0; eauto.
        pose proof (restrPermMap_Cur Hlt b1 ofs) as Heq.
        unfold permission_at in Heq. rewrite Heq.
        assumption.
      + erewrite! setPermBlock_var_other_2 in Hperm by eauto.
        eapply val_obs_eq0; eauto.
        pose proof (restrPermMap_Cur Hlt b1 ofs) as Heq.
        unfold permission_at in Heq. rewrite Heq.
        assumption.
  Qed.

  Lemma setPermBlock_weak_obs_eq:
    forall (f : block -> option block) (bl1 bl2 : block) (ofsl : Z)
      (pmap pmapF : access_map) (mc mf : mem) (p : option permission) (Hlt : permMapLt pmap (getMaxPerm mc))
      (HltF : permMapLt pmapF (getMaxPerm mf))
      (Hfl: f bl1 = Some bl2)
      (Hweak_obs_eq: weak_mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hlt' : permMapLt (setPermBlock p bl1 ofsl pmap lksize.LKSIZE_nat) (getMaxPerm mc))
      (HltF' : permMapLt (setPermBlock p bl2 ofsl pmapF lksize.LKSIZE_nat) (getMaxPerm mf)),
      weak_mem_obs_eq f (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
    intros.
    assert (Hlt2' : permMapLt (setPermBlock_var (fun _ => p) bl1 ofsl pmap lksize.LKSIZE_nat) (getMaxPerm mc))
      by (rewrite <- setPermBlock_setPermBlock_var; auto).
    assert (HltF2' : permMapLt (setPermBlock_var (fun _ => p) bl2 ofsl pmapF lksize.LKSIZE_nat) (getMaxPerm mf))
      by (rewrite <- setPermBlock_setPermBlock_var; auto).
    erewrite restrPermMap_irr' with (Hlt' :=  Hlt2')
      by (eapply setPermBlock_setPermBlock_var; eauto).
    erewrite restrPermMap_irr' with (Hlt' :=  HltF2')
      by (eapply setPermBlock_setPermBlock_var; eauto).
    eapply setPermBlock_var_weak_obs_eq;
      now eauto.
  Qed.

  Lemma setPermBlock_obs_eq:
    forall f bl1 bl2 ofsl pmap pmapF mc mf p
      (Hlt: permMapLt pmap (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (Hfl: f bl1 = Some bl2)
      (Hval_obs_eq: forall ofs0, (ofsl <= ofs0 < ofsl + Z.of_nat (lksize.LKSIZE_nat))%Z ->
                            memval_obs_eq f (ZMap.get ofs0 (Mem.mem_contents mc) # bl1)
                                          (ZMap.get ofs0 (Mem.mem_contents mf) # bl2))
      (Hobs_eq: mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hlt': permMapLt (setPermBlock p bl1 ofsl pmap lksize.LKSIZE_nat) (getMaxPerm mc))
      (HltF': permMapLt (setPermBlock p bl2 ofsl pmapF lksize.LKSIZE_nat) (getMaxPerm mf)),
      mem_obs_eq f (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
    intros.
    assert (Hlt2' : permMapLt (setPermBlock_var (fun _ => p) bl1 ofsl pmap lksize.LKSIZE_nat) (getMaxPerm mc))
      by (rewrite <- setPermBlock_setPermBlock_var; auto).
    assert (HltF2' : permMapLt (setPermBlock_var (fun _ => p) bl2 ofsl pmapF lksize.LKSIZE_nat) (getMaxPerm mf))
      by (rewrite <- setPermBlock_setPermBlock_var; auto).
    erewrite restrPermMap_irr' with (Hlt' :=  Hlt2')
      by (eapply setPermBlock_setPermBlock_var; eauto).
    erewrite restrPermMap_irr' with (Hlt' :=  HltF2')
      by (eapply setPermBlock_setPermBlock_var; eauto).
    eapply setPermBlock_var_obs_eq;
      now eauto.
  Qed.

  Lemma mem_free_obs_perm:
    forall f m m' m2 m2' lo hi b1 b2
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hf: f b1 = Some b2)
      (Hfree: Mem.free m b1 lo hi = Some m2)
      (Hfree': Mem.free m' b2 lo hi = Some m2') b0 b3 ofs
      (Hf0: f b0 = Some b3),
      permissions.permission_at m2 b0 ofs Cur =
      permissions.permission_at m2' b3 ofs Cur.
  Proof.
    intros.
    pose proof (injective (weak_obs_eq Hmem_obs_eq)) as Hinjective.
    pose proof (perm_obs_strong (strong_obs_eq Hmem_obs_eq)) as Hperm_eq.
    eapply Mem.free_result in Hfree.
    eapply Mem.free_result in Hfree'.
    subst.
    specialize (Hperm_eq _ _ ofs Hf0).
    unfold permissions.permission_at, Mem.unchecked_free in *. simpl.
    destruct (Pos.eq_dec b0 b1) as [Heq | Hneq].
    - subst.
      assert (b2 = b3)
        by (rewrite Hf0 in Hf; by inv Hf).
      subst b3.
      do 2 rewrite Maps.PMap.gss.
      rewrite Hperm_eq.
      reflexivity.
    - rewrite Maps.PMap.gso; auto.
      rewrite Maps.PMap.gso; auto.
      intros Hcontra.
      subst.
      apply Hneq; eapply Hinjective; eauto.
  Qed.

  Transparent Mem.free.

  Lemma mem_free_obs:
    forall f m m' lo hi b1 b2 m2
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hf: f b1 = Some b2)
      (Hfree: Mem.free m b1 lo hi = Some m2),
    exists m2',
      Mem.free m' b2 lo hi = Some m2' /\
      mem_obs_eq f m2 m2'.
  Proof.
    intros.
    assert (Hfree': Mem.free m' b2 lo hi  = Some (Mem.unchecked_free m' b2 lo hi)).
    { unfold Mem.free.
      destruct (Mem.range_perm_dec m' b2 lo hi Cur Freeable); auto.
      apply Mem.free_range_perm in Hfree.
      unfold Mem.range_perm in *.
      destruct Hmem_obs_eq as [_ [HpermEq _]].
      unfold Mem.perm, permissions.permission_at in *.
      exfalso.
      apply n. intros ofs Hofs.
      specialize (HpermEq _ _ ofs Hf).
      rewrite HpermEq;
        auto.
    }
    - eexists; split; eauto.
      constructor.
      + (*weak_obs_eq*)
        inversion Hmem_obs_eq as [Hweak_obs_eq Hstrong_obs_eq].
        destruct Hweak_obs_eq.
        assert (Heq_nb := Mem.nextblock_free _ _ _ _ _ Hfree).
        constructor; simpl; unfold Mem.valid_block; try (rewrite Heq_nb);
        auto.
        intros.
        erewrite mem_free_obs_perm with (b1 := b1) (b0 := b0); eauto.
        apply permissions.po_refl.
      + constructor.
        intros.
        erewrite mem_free_obs_perm with (b1 := b1) (b0 := b0); eauto.
        intros.
        erewrite <- mem_free_contents; eauto.
        erewrite <- mem_free_contents with (m2 := Mem.unchecked_free m' b2 lo hi);
          eauto.
        apply (val_obs_eq (strong_obs_eq Hmem_obs_eq)); auto.
        eapply Mem.perm_free_3; eauto.
  Qed.
  Opaque Mem.free.

  Lemma alloc_obs_eq:
    forall f m m' lo hi m2 m2' b b'
      (Hobs_eq: mem_obs_eq f m m')
      (Halloc: Mem.alloc m lo hi = (m2, b))
      (Halloc': Mem.alloc m' lo hi = (m2', b')),
    exists f',
      f' b = Some b' /\
      mem_obs_eq f' m2 m2' /\
      ren_incr f f' /\
      ren_separated f f' m m' /\
      (exists p : positive,
           Mem.nextblock m2 = (Mem.nextblock m + p)%positive /\
           Mem.nextblock m2' = (Mem.nextblock m' + p)%positive) /\
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
          assert (Heq := permission_at_alloc_1 _ _ _ _ _ _ ofs Halloc v Cur).
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
    { exists 1%positive.
      erewrite Mem.nextblock_alloc; eauto.
      erewrite Mem.nextblock_alloc with (m2 := m2'); eauto.
      do 2 rewrite Pplus_one_succ_r; split; reflexivity.
    } split.
    { intros b1 Hvalid2' Hinvalid'.
      eapply Mem.valid_block_alloc_inv in Hvalid2'; eauto.
      destruct Hvalid2'; subst; try by exfalso.
      assert (Hle: (Mem.nextblock m <= Mem.nextblock m')%positive)
        by (eapply weak_mem_obs_eq_nextblock; destruct Hobs_eq; eauto).
      (* We either need to keep this as an extra invariant or make a
      pigeon hole argument. Since f maps every valid block of memory m
      to a valid block of memory m', it has to be that memory m' is at
      least as big as memory m', because f is injective so no two
      blocks can be mapped to the same location*)
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
           assert (H := threads_lemmas.le_sub Hlt Hinvalid').
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
            assert (Hcontra := threads_lemmas.lt_sub_bound Hlt).
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
  Qed.
  
  Lemma valid_pointer_ren:
    forall f m m' b1 b2 ofs
      (Hmem_obs_eq: mem_obs_eq f m m')
      (Hf: f b1 = Some b2),
      Mem.valid_pointer m b1 ofs = Mem.valid_pointer m' b2 ofs.
  Proof.
    intros.
    unfold Mem.valid_pointer in *.
    destruct Hmem_obs_eq as [_ [Hperm_eq _]].
    specialize (Hperm_eq _ _ ofs Hf).
    unfold permissions.permission_at in *.
    unfold Coqlib.proj_sumbool in *.
    destruct (Mem.perm_dec m b1 ofs Cur Nonempty);
      destruct (Mem.perm_dec m' b2 ofs Cur Nonempty); auto.
    unfold Mem.perm in *. rewrite Hperm_eq in n.
      by exfalso.
      unfold Mem.perm in *. rewrite Hperm_eq in p.
        by exfalso.
  Qed.

  Lemma val_obs_cmpu:
    forall f v1 v2 v1' v2' m m' (comp : comparison)
      (Hval_obs': val_obs f v2 v2')
      (Hval_obs: val_obs f v1 v1')
      (Hmem_obs_eq: mem_obs_eq f m m'),
      val_obs f (Val.cmpu (Mem.valid_pointer m) comp v1 v2)
              (Val.cmpu (Mem.valid_pointer m') comp v1' v2').
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl; eauto with val_renamings;
    unfold Val.cmpu,Val.of_optbool, Val.cmpu_bool, Vtrue, Vfalse...
    - destruct (Int.cmpu comp i0 i2)...
    - assert (Int.eq i0 Int.zero &&
                     (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs)
                      || Mem.valid_pointer m b1 (Ptrofs.unsigned ofs - 1))
              = Int.eq i0 Int.zero &&
                       (Mem.valid_pointer m' b2 (Ptrofs.unsigned ofs)
                        || Mem.valid_pointer m' b2 (Ptrofs.unsigned ofs - 1))).
      { destruct (Int.eq i0 Int.zero); simpl; try reflexivity.
        erewrite valid_pointer_ren; eauto.
        erewrite valid_pointer_ren with (ofs := (Ptrofs.unsigned ofs - 1)%Z);
          eauto.
      }
      rewrite H.
      repeat match goal with
             | [|- context[match ?Expr with _ => _ end]] =>
               destruct Expr eqn:?
             end...
    - assert (Int.eq i1 Int.zero &&
                     (Mem.valid_pointer m b (Ptrofs.unsigned i0)
                      || Mem.valid_pointer m b (Ptrofs.unsigned i0 - 1))
              = Int.eq i1 Int.zero &&
                       (Mem.valid_pointer m' b0 (Ptrofs.unsigned i0)
                        || Mem.valid_pointer m' b0 (Ptrofs.unsigned i0 - 1))).
      { destruct (Int.eq i1 Int.zero); simpl; try reflexivity.
        erewrite valid_pointer_ren; eauto.
        erewrite valid_pointer_ren with (ofs := (Ptrofs.unsigned i0 - 1)%Z);
          eauto.
      }
      rewrite H.
      repeat match goal with
             | [|- context[match ?Expr with _ => _ end]] =>
               destruct Expr eqn:?
             end...
    - assert (Hequiv: (eq_block b b3) <-> (eq_block b0 b4)).
      { split.
        - intros Heq.
          destruct (eq_block b b3); subst.
          + rewrite H4 in H0; inversion H0; subst.
            destruct (eq_block b0 b0); auto.
          + by exfalso.
        - intros Heq.
          destruct (eq_block b b3); subst.
          + rewrite H4 in H0; inversion H0; subst.
            destruct (eq_block b0 b0); auto.
          + destruct (eq_block b0 b4); subst; auto.
            assert (Hinjective := injective (weak_obs_eq Hmem_obs_eq)).
            specialize (Hinjective _ _ _ H4 H0); subst.
              by exfalso.
      }
      destruct (eq_block b b3) eqn:Hb;
        destruct (eq_block b0 b4) eqn:Hb0; simpl in *; subst;
        destruct Hequiv; try (by exfalso; eauto).
      assert (Hif: (Mem.valid_pointer m b3 (Ptrofs.unsigned i0)
                    || Mem.valid_pointer m b3 (Ptrofs.unsigned i0 - 1))
                     &&
                     (Mem.valid_pointer m b3 (Ptrofs.unsigned ofs0)
                      || Mem.valid_pointer m b3 (Ptrofs.unsigned ofs0 - 1))
                   =
                   (Mem.valid_pointer m' b4 (Ptrofs.unsigned i0)
                    || Mem.valid_pointer m' b4 (Ptrofs.unsigned i0 - 1))
                     &&
                     (Mem.valid_pointer m' b4 (Ptrofs.unsigned ofs0)
                      || Mem.valid_pointer m' b4 (Ptrofs.unsigned ofs0 - 1))).
      { erewrite valid_pointer_ren; eauto.
        erewrite valid_pointer_ren with
        (m := m) (b1:=b3) (ofs := (Ptrofs.unsigned i0 - 1)%Z); eauto.
        erewrite valid_pointer_ren with
        (m := m) (b1:=b3) (ofs := Ptrofs.unsigned ofs0); eauto.
        erewrite valid_pointer_ren with
        (m := m) (b1:=b3) (ofs := (Ptrofs.unsigned ofs0 - 1)%Z); eauto.
      }
      rewrite Hif.
      repeat match goal with
             | [|- context[match ?Expr with _ => _ end]] =>
               destruct Expr eqn:?
             end...
      erewrite valid_pointer_ren; eauto.
      erewrite valid_pointer_ren with (b1 := b3); eauto.
      repeat match goal with
             | [|- context[match ?Expr with _ => _ end]] =>
               destruct Expr eqn:?
             end...
  Qed.

  Hint Resolve val_obs_cmpu : val_renamings.

  Lemma val_obs_cmplu:
    forall f v1 v2 v1' v2' m m' (comp : comparison)
      (Hval_obs': val_obs f v2 v2')
      (Hval_obs: val_obs f v1 v1')
      (Hmem_obs_eq: mem_obs_eq f m m'),
      val_obs f (Val.maketotal (Val.cmplu (Mem.valid_pointer m) comp v1 v2))
              (Val.maketotal (Val.cmplu (Mem.valid_pointer m') comp v1' v2')).
  Proof with eauto with val_renamings.
    intros.
    destruct v1, v1'; inversion Hval_obs;
    inversion Hval_obs'; subst; simpl; eauto with val_renamings;
    unfold Val.cmpu,Val.of_optbool, Val.cmpu_bool, Vtrue, Vfalse...
  Qed.

  Hint Resolve val_obs_cmplu : val_renamings.

  Lemma mem_obs_eq_of_weak_strong:
    forall m m' f pmap1 pmap1' pmap2 pmap2'
      (Hlt1: permMapLt pmap1 (getMaxPerm m))
      (Hlt2: permMapLt pmap2 (getMaxPerm m'))
      (Hlt1': permMapLt pmap1' (getMaxPerm m))
      (Hlt2': permMapLt pmap2' (getMaxPerm m'))
      (Hstrong_obs: strong_mem_obs_eq f (restrPermMap Hlt1) (restrPermMap Hlt2))
      (Hweak: weak_mem_obs_eq f (restrPermMap Hlt1') (restrPermMap Hlt2')),
      mem_obs_eq f (restrPermMap Hlt1) (restrPermMap Hlt2).
  Proof.
    intros.
    destruct Hweak.
    constructor; auto.
    constructor; intros.
    - specialize (domain_invalid0 b).
      erewrite restrPermMap_valid in H, domain_invalid0;
        eauto.
    - specialize (domain_valid0 b).
      erewrite restrPermMap_valid in H, domain_valid0;
        eauto.
    - specialize (codomain_valid0 _ _ H);
      erewrite restrPermMap_valid in *;
      eauto.
    - eauto.
    - destruct Hstrong_obs as [Hpermeq _].
      specialize (Hpermeq _ _ ofs Hrenaming).
      rewrite Hpermeq;
        apply po_refl.
  Qed.

End MemObsEq.

Module CoreInjections.

  Import ValObsEq ValueWD MemoryWD Renamings MemObsEq event_semantics.

  Section CoreInjections.

    Context {Sem : Semantics}.

    Class CoreInj :=
      { (** Pointers in the core are well-defined *)
        core_wd : memren -> semC -> Prop;
        (** Pointers in the global env are well-defined *)
        ge_wd : memren -> semG -> Prop;

        ge_wd_incr: forall f f' (g : semG),
            ge_wd f g ->
            ren_domain_incr f f' ->
            ge_wd f' g;

        ge_wd_domain : forall f f' m (g : semG),
            ge_wd f g ->
            domain_memren f m ->
            domain_memren f' m ->
            ge_wd f' g;

        core_wd_incr : forall f f' c,
            core_wd f c ->
            ren_domain_incr f f' ->
            core_wd f' c;

        core_wd_domain : forall f f' m c,
            core_wd f c ->
            domain_memren f m ->
            domain_memren f' m ->
            core_wd f' c;

        at_external_wd:
          forall m (f : memren) c
            (ef : external_function)
            (args : seq val),
            valid_mem m ->
            domain_memren f m ->
            core_wd f c ->
            at_external semSem c m = Some (ef, args) -> 
            valid_val_list f args;

        after_external_wd:
          forall m (c c' : semC) (f : memren) (ef : external_function)
            (args : seq val) (ov : option val)
            (Hat_external: at_external semSem c m = Some (ef, args))
            (Hcore_wd: core_wd f c)
            (Hvalid_list: valid_val_list f args)
            (Hafter_external: after_external semSem ov c m = Some c')
            (Hov: match ov with
                  | Some v => valid_val f v
                  | None => True
                  end),
            core_wd f c';

        (*LENB: modified to account for the fact that a stack block is allocated. Cf the similarly modified 
  core_inj_init later in this file
  initial_core_wd:
    forall the_ge m (f : memren) (vf arg : val) (c_new : C) om h,
      valid_mem m ->
      domain_memren f m ->
      initial_core SEM h the_ge m vf [:: arg] = Some (c_new, om) ->
      valid_val f arg -> ge_wd f the_ge -> core_wd f c_new.*)

        initial_core_wd :
          forall m m' (f fg : memren) (vf : val) args (c_new:semC) h,
            valid_mem m ->
            domain_memren f m ->
            initial_core semSem h m c_new m' vf args ->
            valid_val_list f args ->
            ge_wd fg the_ge ->
            ren_domain_incr fg f ->
            valid_mem m' /\
            (exists f', ren_domain_incr f f' /\ domain_memren f' m') /\
            forall f', domain_memren f' m' ->
                  core_wd f' c_new;

        (** Renamings on cores *)
        core_inj: memren -> semC -> semC -> Prop;

        core_inj_ext:
          forall m m' c c' (f fg : memren)
            (Hfg: (forall b1 b2, fg b1 = Some b2 -> b1 = b2))
            (Hge_wd: ge_wd fg the_ge)
            (Hincr: ren_incr fg f),
            valid_mem m ->
            (* domain_memren f m -> *)
            core_inj f c c' ->
            mem_obs_eq f m m' ->
            match at_external semSem c m with
            | Some (ef, vs) =>
              match at_external semSem c' m' with
              | Some (ef', vs') =>
                ef = ef' /\ val_obs_list f vs vs'
              | None => False
              end
            | None =>
              match at_external semSem c' m' with
              | Some _ => False
              | None => True
              end
            end;

        (* This is not quite right.  Instead of letting ov1 freely float Some/None,
        it should be determined by the return type of the signature for the
        external function *)    
        (* Nick: There was no signature back when I wrote this, but it doesn't matter, this only specifies that they will have similar return values, not what the return value is *)
        core_inj_after_ext:
          forall c cc c' (ov1 : option val) m m'
            (f fg : memren)
            (Hfg: (forall b1 b2, fg b1 = Some b2 -> b1 = b2))
            (Hge_wd: ge_wd fg the_ge)
            (Hincr: ren_incr fg f),
            core_inj f c c' ->
            mem_obs_eq f m m' -> 
            match ov1 with
            | Some v1 => valid_val f v1
            | None => True
            end ->
            after_external semSem ov1 c m = Some cc ->
            exists (ov2 : option val) (cc' : semC),
              after_external semSem ov2 c' m' = Some cc' /\
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
              end;

        core_inj_halted:
          forall c c' f (Hinj: core_inj f c c') v,
            halted semSem c v <-> halted semSem c' v;

        core_inj_init:
          forall m1 m1' m2 vf vf' arg arg' c_new f fg h
            (Hge_wd: ge_wd fg the_ge)
            (Hfg: (forall b1 b2, fg b1 = Some b2 -> b1 = b2))
            (Hincr: ren_incr fg f)
            (Harg: val_obs_list f arg arg')
            (Hvf: val_obs f vf vf')
            (Hmem: mem_obs_eq f m1 m1')
            (Hinit: initial_core semSem h m1 c_new m2 vf arg),
          (* (Hf: forall b b', f b = Some b' -> Mem.valid_block m b), *)
          exists c_new' m2' f',
            initial_core semSem h m1' c_new' m2' vf' arg'
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
                     forall ofs, permission_at m1' b2 ofs Cur = permission_at m2' b2 ofs Cur);

        core_inj_id: forall c f,
            core_wd f c ->
            (forall b1 b2, f b1 = Some b2 -> b1 = b2) ->
            core_inj f c c;

        core_inj_trans:
          forall c c' c'' (f f' f'' : memren)
            (Hcore_inj: core_inj f c c'')
            (Hcore_inj': core_inj f' c c')
            (Hf: forall b b' b'',
                f b = Some b'' ->
                f' b = Some b' ->
                f'' b' = Some b''),
            core_inj f'' c' c'';

        corestep_obs_eq:
          forall cc cf cc' mc mf mc' f fg
            (Hobs_eq: mem_obs_eq f mc mf)
            (Hcode_eq: core_inj f cc cf)
            (Hfg: (forall b1 b2, fg b1 = Some b2 -> b1 = b2))
            (Hge_wd: ge_wd fg the_ge)
            (Hincr: ren_incr fg f)
            (Hstep: corestep semSem cc mc cc' mc'),
          exists cf' mf' f',
            corestep semSem cf mf cf' mf'
            /\ core_inj f' cc' cf'
            /\ mem_obs_eq f' mc' mf'
            /\ ren_incr f f'
            /\ ren_separated f f' mc mf
            /\ ((exists p, ((Mem.nextblock mc' = Mem.nextblock mc + p)%positive /\
                      (Mem.nextblock mf' = Mem.nextblock mf + p)%positive))
               \/ ((Mem.nextblock mc' = Mem.nextblock mc) /\
                  (Mem.nextblock mf' = Mem.nextblock mf)))
            /\ (forall b,
                  Mem.valid_block mf' b ->
                  ~ Mem.valid_block mf b ->
                  let bz := ((Zpos b) - ((Zpos (Mem.nextblock mf)) -
                                         (Zpos (Mem.nextblock mc))))%Z in
                  f' (Z.to_pos bz) = Some b /\
                  f (Z.to_pos bz) = None)
            /\ (Mem.nextblock mc = Mem.nextblock mf ->
               (forall b1 b2, f b1 = Some b2 -> b1 = b2) ->
               forall b1 b2, f' b1 = Some b2 -> b1 = b2)
            /\ (forall b2, (~exists b1, f' b1 = Some b2) ->
                     forall ofs, permission_at mf b2 ofs Cur = permission_at mf' b2 ofs Cur);

        (* Starting from a wd state, we get a new valid memory and the fact
     that there exists some renaming whose domain is the same as the
     new memory and additionally that the new core is well defined
     with respect to all renamings with the same domain.  Note that we
     cannot say anything about the codomain, i.e. that f' is an
     extension of f.*)
        corestep_wd:
          forall c m c' m' f fg
            (Hwd: core_wd f c)
            (Hmem_wd: valid_mem m)
            (Hge_wd: ge_wd fg the_ge)
            (Hincr: ren_domain_incr fg f)
            (Hdomain: domain_memren f m)
            (Hcorestep: corestep semSem c m c' m'),
            valid_mem m' /\
            (exists f', ren_domain_incr f f' /\ domain_memren f' m') /\
            forall f', domain_memren f' m' ->
                  core_wd f' c'
      }.

End CoreInjections.

End CoreInjections.

Module ThreadPoolInjections.

  Import ValObsEq ValueWD MemoryWD Renamings CoreInjections.
  Import ThreadPool HybridMachine DryHybridMachine.

  Section ThreadPoolInjections.
    Existing Instance dryResources.
    Context {asmSem : Semantics}
            {tpool : ThreadPool.ThreadPool}
            {CI: CoreInj}.

  (** Renamings on Thread Pools *)

  (*not clear what should happen with vf. Normally it should be in the
genv and hence should be mapped to itself, but let's not expose this
here, this seems to have changed.*)
  Definition ctl_inj f cc cf : Prop :=
    match cc, cf with
    | Kinit vf arg, Kinit vf' arg' =>
      val_obs f vf vf' /\ val_obs f arg arg'
    | Krun c, Krun c' => core_inj f c c'
    | Kblocked c, Kblocked c' => core_inj f c c'
    | Kresume c arg, Kresume c' arg' => core_inj f c c' /\ val_obs f arg arg'
    | _, _  => False
    end.

  (*Again we do not require that the first argument to Kinit is valid
  as we never map it, although maybe we should, seems to have changed as well..*)
  Definition ctl_wd f t : Prop :=
    match t with
    | Krun c => core_wd f c
    | Kblocked c => core_wd f c
    | Kresume c v => core_wd f c /\ valid_val f v
    | Kinit vf v => valid_val f vf /\ valid_val f v
    end.

  Lemma ctl_wd_incr : forall f f' c,
      ctl_wd f c ->
      ren_domain_incr f f' ->
      ctl_wd f' c.
  Proof.
    intros f f' c Hwd Hincr.
    destruct c; simpl in *;
    repeat match goal with
           | [H: _ /\ _ |- _] =>
             destruct H
           | [ |- _] => split
           end;
    try (eapply core_wd_incr; eauto);
    try (eapply valid_val_incr; eauto).
  Qed.

  Lemma ctl_inj_trans:
    forall c c' c'' (f f' f'' : memren)
      (Hcore_inj: ctl_inj f c c'')
      (Hcore_inj': ctl_inj f' c c')
      (Hf: forall b b' b'',
          f b = Some b'' ->
          f' b = Some b' ->
          f'' b' = Some b''),
      ctl_inj f'' c' c''.
  Proof.
    intros.
    destruct c, c', c''; simpl in *; try (by exfalso);
    try (destruct Hcore_inj, Hcore_inj'; split);
    try (eapply core_inj_trans; eauto);
    eapply val_obs_trans;
      by eauto.
  Qed.

  Definition tp_wd (f: memren) (tp : t) : Prop :=
    forall i (cnti: containsThread tp i),
      ctl_wd f (getThreadC cnti).

  Lemma tp_wd_incr : forall f f' tp,
      tp_wd f tp ->
      ren_domain_incr f f' ->
      tp_wd f' tp.
  Proof.
    intros.
    intros i cnti.
    specialize (H i cnti).
    eapply ctl_wd_incr;
      by eauto.
  Qed.

  Lemma ctl_wd_domain:
    forall f f' m (c : ctl),
      ctl_wd f c ->
      domain_memren f m ->
      domain_memren f' m ->
      ctl_wd f' c.
  Proof.
    intros f f' m c Hwd Hf Hf'.
    destruct c; simpl in *;
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [|- _ /\ _] => split
           | [|- core_wd _ _] => eapply core_wd_domain; eauto
           | [|- valid_val _ _] => eapply valid_val_domain; eauto
           end.
  Qed.

  Lemma tp_wd_domain:
    forall f f' m (tp : t),
      tp_wd f tp ->
      domain_memren f m ->
      domain_memren f' m ->
      tp_wd f' tp.
  Proof.
    intros.
    intros i cnti.
    specialize (H i cnti).
    destruct (getThreadC cnti); simpl in *;
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [|- _ /\ _] => split
           | [|- core_wd _ _] => eapply core_wd_domain; eauto
           | [|- valid_val _ _] => eapply valid_val_domain; eauto
           end.
  Qed.

  Lemma tp_wd_lockSet:
    forall tp f addr rmap
      (Htp_wd: tp_wd f tp),
      tp_wd f (updLockSet tp addr rmap).
  Proof.
    intros.
    intros i cnti'.
    assert (cnti := cntUpdateL' addr rmap cnti').
    specialize (Htp_wd _ cnti).
      by rewrite gLockSetCode.
  Qed.

  Lemma tp_wd_remLock :
    forall (tp : t) (f : memren) (addr : address)
      (Htp_wd: tp_wd f tp),
      tp_wd f (remLockSet tp addr).
  Proof.
    intros.
    intros i cnti'.
    assert (cnti := cntRemoveL' addr cnti').
    specialize (Htp_wd _ cnti);
      by rewrite gRemLockSetCode.
  Qed.

  Lemma ctl_inj_id:
    forall f c,
      ctl_wd f c ->
      (forall b1 b2, f b1 = Some b2 -> b1 = b2) ->
      ctl_inj f c c.
  Proof.
    intros.
    destruct c; simpl in *;
    repeat match goal with
           |[H: _ /\ _ |- _] =>
            destruct H
           |[|- _ /\ _] => split; auto
           |[|- core_inj _ _ _] =>
            eapply core_inj_id; eauto
           |[|- val_obs _ _ _] =>
            eapply val_obs_id; eauto
           end.
  Qed.

End ThreadPoolInjections.

End ThreadPoolInjections.
