(** * Erasure from FineConc to a non-angelic SC machine*)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.memory_lemmas.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.erased_machine.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.sc_drf.fineConc_safe.
Require Import VST.concurrency.sc_drf.executions.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".


(** The erasure removes permissions and angels from the machine
(i.e. making it a bare machine) and also allows some values to become
more defined. See [val_erasure] and [memval_erasure] for a precise
account of that. *)

(** ** Erasure of Values*)
Module ValErasure.

  Definition isPointer (v : val) :=
    match v with
    | Vptr _ _ => true
    | _ => false
    end.
  
  Definition val_erasure v1 v2 : Prop :=
    match v1, v2 with
    | Vundef, _ => True
    | v1, v2 => v1 = v2
    end.

  Definition optionval_erasure (v1 v2 : option val) : Prop :=
    match v1, v2 with
    | Some v1, Some v2 => val_erasure v1 v2
    | None, None => True
    | _, _ => False
    end.

  Definition memval_erasure mv1 mv2 : Prop :=
    match mv1, mv2 with
    | Undef, _ => True
    | Fragment v1 q1 n1, Fragment v2 q2 n2 =>
      val_erasure v1 v2 /\ q1 = q2 /\ n1 = n2
    | mv1, mv2 => mv1 = mv2
    end.

  Inductive val_erasure_list : seq.seq val -> seq.seq val -> Prop :=
    val_erasure_nil : val_erasure_list [::] [::]
  | val_erasure_cons : forall (v v' : val) (vl vl' : seq.seq val),
      val_erasure v v' ->
      val_erasure_list vl vl' ->
      val_erasure_list (v :: vl) (v' :: vl').

  Inductive memval_erasure_list : seq.seq memval -> seq.seq memval -> Prop :=
    memval_erasure_nil : memval_erasure_list [::] [::]
  | memval_erasure_cons : forall (mv mv' : memval) (mvl mvl' : seq.seq memval),
      memval_erasure mv mv' ->
      memval_erasure_list mvl mvl' ->
      memval_erasure_list (mv :: mvl) (mv' :: mvl').

  Lemma val_erasure_refl:
    forall v, val_erasure v v.
  Proof.
    destruct v; simpl; auto.
  Qed.

  Lemma memval_erasure_refl:
    forall mval,
      memval_erasure mval mval.
  Proof.
    intros; destruct mval; constructor;
    eauto using val_erasure_refl.
  Qed.

  Hint Immediate memval_erasure_refl val_erasure_refl : val_erasure.
  Hint Constructors memval_erasure_list val_erasure_list : val_erasure.

  Lemma val_erasure_list_refl:
    forall vs, val_erasure_list vs vs.
  Proof with eauto with val_erasure.
    induction vs; simpl...
  Qed.

  (* TODO: is that still used? *)
  (*Lemma val_erasure_list_decode:
    forall vals vals' typs,
      val_erasure_list vals vals' ->
      val_erasure_list (val_casted.decode_longs typs vals)
                       (val_casted.decode_longs typs vals').
  Proof.
    intros.
    generalize dependent vals.
    generalize dependent vals'.
    induction typs; intros; simpl;
    first by constructor.
    destruct vals;
      destruct a; inversion H; subst;
      try constructor; eauto.
    destruct vals; inversion H4; subst.
    constructor.
    unfold Val.longofwords.
    destruct v;
      constructor; eauto;
      inv H2; try constructor.
    unfold val_erasure in H3.
    destruct v0; subst; auto;
    constructor.
  Qed. *)

  Lemma memval_erasure_list_refl:
    forall vs, memval_erasure_list vs vs.
  Proof with eauto with val_erasure.
    induction vs; simpl...
  Qed.

  Hint Immediate memval_erasure_list_refl : val_erasure.

  (** ** Lemmas about erased values*)

  Definition isDefined v :=
    match v with
    | Vundef => false
    | _ => true
    end.

  Lemma val_erasure_add_result:
    forall v1 v1' v2 v2' v,
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      Val.add v1 v2 = v ->
      isDefined v ->
      Val.add v1' v2' = v.
  Proof.
    intros.
    destruct v1,v2; simpl in *; subst; simpl in *;
    try (by exfalso); auto.
  Qed.

  Lemma isPointer_isDefined:
    forall v, isPointer v -> isDefined v.
  Proof.
    unfold isPointer, isDefined;
    destruct v; auto.
  Qed.

  Lemma val_erasure_add:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.add v1 v2) (Val.add v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
      inv H; inv H0; try (destruct Archi.ptr64); simpl;
        now auto.
  Qed.

  Lemma val_erasure_mul:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.mul v1 v2) (Val.mul v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_mul_result:
    forall v1 v2 v1' v2' v,
      val_erasure v1 v1'->
      val_erasure v2 v2' ->
      Val.mul v1 v2 = v ->
      isDefined v ->
      Val.mul v1' v2' = v.
  Proof.
    intros.
    destruct v1,v2; simpl in *; subst; simpl in *;
    try by exfalso.
    reflexivity.
  Qed.

  Lemma val_erasure_hiword:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.hiword v) (Val.hiword v').
  Proof.
    intros;
    destruct v; simpl; inv H; auto.
  Qed.

  Lemma val_erasure_loword:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.loword v) (Val.loword v').
  Proof.
    intros;
    destruct v; simpl; inv H; auto.
  Qed.

  Lemma val_erasure_cmp_bool:
    forall c v1 v1',
      v1 <> Vundef ->
      val_erasure v1 v1' ->
      Val.cmp_bool c v1 Vzero = Val.cmp_bool c v1' Vzero.
  Proof.
    intros.
    destruct v1; try congruence.
  Qed.

  Lemma val_erasure_zero_ext:
    forall v v' n,
      val_erasure v v' ->
      val_erasure (Val.zero_ext n v) (Val.zero_ext n v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_sign_ext:
    forall v v' n,
      val_erasure v v' ->
      val_erasure (Val.sign_ext n v) (Val.sign_ext n v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_singleoffloat:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.singleoffloat v) (Val.singleoffloat v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_floatofsingle:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.floatofsingle v) (Val.floatofsingle v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_intoffloat:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.maketotal (Val.intoffloat v))
                  (Val.maketotal (Val.intoffloat v')).
  Proof.
    intros.
    destruct v; inv H; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_floatofint:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.maketotal (Val.floatofint v))
                  (Val.maketotal (Val.floatofint v')).
  Proof.
    intros.
    destruct v; inv H; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_intofsingle:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.maketotal (Val.intofsingle v))
                  (Val.maketotal (Val.intofsingle v')).
  Proof.
    intros.
    destruct v; inv H; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_singleofint:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.maketotal (Val.singleofint v))
                  (Val.maketotal (Val.singleofint v')).
  Proof.
    intros.
    destruct v; inv H; simpl; eauto using val_erasure_refl.
  Qed.


  Lemma val_erasure_neg:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.neg v) (Val.neg v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_notint:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.notint v) (Val.notint v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_negative:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.negative v) (Val.negative v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_sub_overflow:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.sub_overflow v1 v2) (Val.sub_overflow v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_sub:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.sub v1 v2) (Val.sub v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
      inv H; inv H0; simpl; auto;
        try (destruct Archi.ptr64); simpl; auto;
          destruct (eq_block b b0); simpl;
            now auto.
  Qed.

  Lemma val_erasure_mulhu:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.mulhu v1 v2) (Val.mulhu v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_mulhs:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.mulhs v1 v2) (Val.mulhs v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_and:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.and v1 v2) (Val.and v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_or:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.or v1 v2) (Val.or v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_xor:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.xor v1 v2) (Val.xor v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_shl:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.shl v1 v2) (Val.shl v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_shr:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.shr v1 v2) (Val.shr v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_shru:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.shru v1 v2) (Val.shru v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_ror:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.ror v1 v2) (Val.ror v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_divu_result:
    forall v1 v2 v1' v2' v,
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      Val.divu v1 v2 = Some v ->
      Val.divu v1' v2' = Some v.
  Proof.
    destruct v1,v2; intros;
    inv H; inv H0; simpl in *; eauto using val_erasure_refl;
    try discriminate.
  Qed.

  Lemma val_erasure_modu_result:
    forall v1 v2 v1' v2' v,
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      Val.modu v1 v2 = Some v ->
      Val.modu v1' v2' = Some v.
  Proof.
    destruct v1,v2; intros;
    inv H; inv H0; simpl in *; eauto using val_erasure_refl;
    try discriminate.
  Qed.

  Lemma val_erasure_divs_result:
    forall v1 v2 v1' v2' v,
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      Val.divs v1 v2 = Some v ->
      Val.divs v1' v2' = Some v.
  Proof.
    destruct v1,v2; intros;
    inv H; inv H0; simpl in *; eauto using val_erasure_refl;
    try discriminate.
  Qed.

  Lemma val_erasure_mods_result:
    forall v1 v2 v1' v2' v,
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      Val.mods v1 v2 = Some v ->
      Val.mods v1' v2' = Some v.
  Proof.
    destruct v1,v2; intros;
    inv H; inv H0; simpl in *; eauto using val_erasure_refl;
    try discriminate.
  Qed.

  Lemma val_erasure_addf:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.addf v1 v2) (Val.addf v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_addfs:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.addfs v1 v2) (Val.addfs v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_subf:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.subf v1 v2) (Val.subf v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_subfs:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.subfs v1 v2) (Val.subfs v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_mulf:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.mulf v1 v2) (Val.mulf v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_mulfs:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.mulfs v1 v2) (Val.mulfs v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_divf:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.divf v1 v2) (Val.divf v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_divfs:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.divfs v1 v2) (Val.divfs v1' v2').
  Proof.
    destruct v1,v2; intros;
    simpl; auto;
    inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_negf:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.negf v) (Val.negf v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_negfs:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.negfs v) (Val.negfs v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_absf:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.absf v) (Val.absf v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_absfs:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.absfs v) (Val.absfs v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma inj_bytes_erasure :
    forall (bl : seq.seq byte),
      memval_erasure_list (inj_bytes bl) (inj_bytes bl).
  Proof.
    induction bl;
    simpl; constructor; auto.
    constructor.
  Qed.

  Lemma inj_value_erasure :
    forall (v1 v2 : val) (q : quantity),
      val_erasure v1 v2 ->
      memval_erasure_list (inj_value q v1) (inj_value q v2).
  Proof with eauto with val_erasure.
    intros.
    destruct v1; inv H; simpl...
    destruct q; simpl; unfold inj_value; simpl;
    repeat (econstructor; simpl; auto).
  Qed.

  Lemma repeat_Undef_erasure_self :
    forall (n : nat),
      memval_erasure_list (list_repeat n Undef) (list_repeat n Undef).
  Proof.
    eauto with val_erasure.
  Qed.

  Lemma repeat_Undef_inject_encode_val :
    forall (chunk : memory_chunk) (v : val),
      memval_erasure_list (list_repeat (size_chunk_nat chunk) Undef)
                         (encode_val chunk v).
  Proof with eauto with val_erasure.
    intros.
    destruct v, chunk; simpl; unfold inj_value; simpl;
    repeat econstructor...
  Qed.

  Lemma val_erasure_encode_val:
    forall chunk v v',
      val_erasure v v' ->
      memval_erasure_list (encode_val chunk v) (encode_val chunk v').
  Proof.
    intros.
    destruct v; inversion H; subst; simpl; destruct chunk;
    auto using inj_bytes_erasure,  inj_value_erasure, repeat_Undef_erasure_self,
    repeat_Undef_inject_encode_val.
    unfold encode_val. destruct v'; apply inj_value_erasure; auto.
    unfold encode_val. destruct v'; apply inj_value_erasure; auto.
    try (destruct Archi.ptr64); simpl;
      repeat (econstructor; eauto).
    try (destruct Archi.ptr64); simpl;
      repeat (econstructor; eauto).
  Qed.

  Lemma val_defined_add_1:
    forall v1 v2 v,
      Val.add v1 v2 = v ->
      isDefined v ->
      isDefined v1.
  Proof.
    intros. destruct v1,v2; subst; simpl; auto.
  Qed.

  Lemma val_defined_add_2:
    forall v1 v2 v,
      Val.add v1 v2 = v ->
      isDefined v ->
      isDefined v2.
  Proof.
    intros. destruct v1,v2; subst; simpl; auto.
  Qed.

   (*TODO: move to other file *)
  Lemma val_erasure_offset_ptr:
    forall v v' z
      (Hval_erasure: val_erasure v v'),
      val_erasure (Val.offset_ptr v z) (Val.offset_ptr v' z).
  Proof.
    intros.
    destruct v; simpl; auto.
    inv Hval_erasure.
    reflexivity.
  Qed.

  Lemma val_erasure_longofintu:
    forall v v'
      (Hval_erasure: val_erasure v v'),
      val_erasure (Val.longofintu v) (Val.longofintu v').
  Proof.
    intros.
    destruct v; simpl; auto.
    inv Hval_erasure.
    reflexivity.
  Qed.

  Lemma val_erasure_longofint:
    forall v v'
      (Hval_erasure: val_erasure v v'),
      val_erasure (Val.longofint v) (Val.longofint v').
  Proof.
    intros.
    destruct v; simpl; auto.
    inv Hval_erasure.
    reflexivity.
  Qed.

  Lemma val_erasure_longoffloat:
    forall v v'
      (Hval_erasure: val_erasure v v'),
      val_erasure (Val.maketotal (Val.longoffloat v)) (Val.maketotal (Val.longoffloat v')).
  Proof.
    intros.
    destruct v; inv Hval_erasure; simpl;
      eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_floatoflong:
    forall v v'
      (Hval_erasure: val_erasure v v'),
      val_erasure (Val.maketotal (Val.floatoflong v)) (Val.maketotal (Val.floatoflong v')).
  Proof.
    intros.
    destruct v; inv Hval_erasure; simpl;
      eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_longofsingle:
    forall v v'
      (Hval_erasure: val_erasure v v'),
      val_erasure (Val.maketotal (Val.longofsingle v)) (Val.maketotal (Val.longofsingle v')).
  Proof.
    intros.
    destruct v; inv Hval_erasure; simpl;
      eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_longofwords:
    forall v1 v1' v2 v2'
      (Hval_erasure: val_erasure v1 v1')
      (Hval_erasure: val_erasure v2 v2'),
      val_erasure (Val.longofwords v1 v2) (Val.longofwords v1' v2').
  Proof.
    intros.
    destruct v1, v2; simpl in *; subst;
      now auto.
  Qed.

  Lemma val_erasure_singleoflong:
    forall v v'
      (Hval_erasure: val_erasure v v'),
      val_erasure (Val.maketotal (Val.singleoflong v)) (Val.maketotal (Val.singleoflong v')).
  Proof.
    intros.
    destruct v; inv Hval_erasure; simpl;
      eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_negl:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.negl v) (Val.negl v').
  Proof.
    intros.
    destruct v; inv H; simpl; auto.
  Qed.

  Lemma val_erasure_addl:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.addl v1 v2) (Val.addl v1' v2').
  Proof.
    unfold Val.addl.
    assert (Harch: Archi.ptr64 = false) by auto.
    rewrite Harch.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_subl:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.subl v1 v2) (Val.subl v1' v2').
  Proof.
    unfold Val.subl.
    assert (Harch: Archi.ptr64 = false) by auto.
    rewrite Harch.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_subl_overflow:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.subl_overflow v1 v2) (Val.subl_overflow v1' v2').
  Proof.
    unfold Val.subl_overflow.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl;
          now auto.
  Qed.

  Lemma val_erasure_mull:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.mull v1 v2) (Val.mull v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_mullhs:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.mullhs v1 v2) (Val.mullhs v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_mullhu:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.mullhu v1 v2) (Val.mullhu v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_shrl:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.shrl v1 v2) (Val.shrl v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_andl:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.andl v1 v2) (Val.andl v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_orl:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.orl v1 v2) (Val.orl v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_xorl:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.xorl v1 v2) (Val.xorl v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; auto.
  Qed.

  Lemma val_erasure_notl:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.notl v) (Val.notl v').
  Proof.
    destruct v; intros;
      simpl; auto;
        inv H; simpl; auto.
  Qed.

  Lemma val_erasure_shll:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.shll v1 v2) (Val.shll v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_shrlu:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.shrlu v1 v2) (Val.shrlu v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_rorl:
    forall v1 v2 v1' v2',
      val_erasure v1 v1' ->
      val_erasure v2 v2' ->
      val_erasure (Val.rorl v1 v2) (Val.rorl v1' v2').
  Proof.
    destruct v1,v2; intros;
      simpl; auto;
        inv H; inv H0; simpl; eauto using val_erasure_refl.
  Qed.

  Lemma val_erasure_negativel:
    forall v v',
      val_erasure v v' ->
      val_erasure (Val.negativel v) (Val.negativel v').
  Proof.
    intros.
    destruct v; inv H; simpl; now auto.
  Qed.

  
  Hint Resolve val_defined_add_1 val_defined_add_2 : val_defined.

  Hint Extern 0 (val_erasure (Vint _) (Vint _)) => reflexivity : val_erasure.
  Hint Resolve val_erasure_ror val_erasure_shru val_erasure_shr
       val_erasure_shl val_erasure_xor val_erasure_or val_erasure_and
       val_erasure_mulhs val_erasure_mulhu val_erasure_sub
       val_erasure_neg val_erasure_singleofint val_erasure_singleoffloat
       val_erasure_intofsingle val_erasure_floatofint val_erasure_intoffloat
       val_erasure_floatofsingle val_erasure_singleoffloat val_erasure_sign_ext
       val_erasure_zero_ext val_erasure_negative val_erasure_notint
       val_erasure_sub_overflow val_erasure_encode_val
       val_erasure_hiword val_erasure_loword
       val_erasure_add val_erasure_add_result isPointer_isDefined
       val_erasure_mul_result val_erasure_mul
       val_erasure_addf val_erasure_subf val_erasure_mulf
       val_erasure_divf val_erasure_negf val_erasure_absf
       val_erasure_addfs val_erasure_subfs val_erasure_mulfs
       val_erasure_divfs val_erasure_negfs val_erasure_absfs
       val_erasure_offset_ptr val_erasure_longofintu val_erasure_longofint
       val_erasure_longoffloat val_erasure_longofsingle val_erasure_singleoflong
       val_erasure_floatoflong val_erasure_longofwords
       val_erasure_negl val_erasure_addl val_erasure_subl val_erasure_subl_overflow
       val_erasure_mull val_erasure_mullhs val_erasure_mullhu val_erasure_shrl
       val_erasure_andl val_erasure_orl val_erasure_xorl val_erasure_notl val_erasure_shll
       val_erasure_shrlu val_erasure_rorl val_erasure_negativel : val_erasure.

  Hint Immediate val_erasure_refl : val_erasure.

End ValErasure.

(** ** Erasure of Traces*)
Module TraceErasure.
  Import ValErasure event_semantics.

  Inductive mem_event_erasure : mem_event -> mem_event -> Prop :=
  | WriteErasure: forall b ofs mvals mvals',
      memval_erasure_list mvals mvals' ->
      mem_event_erasure (Write b ofs mvals) (Write b ofs mvals')
  | ReadErasure: forall b ofs sz mvals mvals',
      memval_erasure_list mvals mvals' ->
      mem_event_erasure (Read b ofs sz mvals) (Read b ofs sz mvals')
  | AllocErasure: forall b ofs sz,
      mem_event_erasure (Alloc b ofs sz) (Alloc b ofs sz)
  | FreeErasure: forall ls,
      mem_event_erasure (Free ls) (Free ls).

  Inductive mem_event_list_erasure: list mem_event -> list mem_event -> Prop :=
  | nilMemEvent: mem_event_list_erasure nil nil
  | consMemEvent: forall mev mev' ls ls'
                   (Hev_erasure: mem_event_erasure mev mev')
                   (Hls_erasure: mem_event_list_erasure ls ls'),
      mem_event_list_erasure (mev :: ls) (mev' :: ls').

  (** Removing the footprints from a [sync_event] *)
  Definition eraseSyncEvent ev :=
    match ev with
    | Events.release addr _ => Events.release addr None
    | Events.acquire addr _ => Events.acquire addr None
    | Events.spawn addr _ _ => Events.spawn addr None None
    | _ => ev
    end.

  Inductive event_erasure : Events.machine_event -> Events.machine_event -> Prop :=
  | InternalErasure: forall tid mev mev',
      mem_event_erasure mev mev' ->
      event_erasure (Events.internal tid mev) (Events.internal tid mev')
  | ExternalErasure: forall tid ev,
      event_erasure (Events.external tid ev)
                    (Events.external tid (eraseSyncEvent ev)).

  Inductive trace_erasure : list Events.machine_event ->
                            list Events.machine_event -> Prop :=
  | NilErasure: trace_erasure nil nil
  | ConsErasure: forall ev ev' tr tr'
                   (Hev_erasure: event_erasure ev ev')
                   (Htr_erasure: trace_erasure tr tr'),
      trace_erasure (ev :: tr) (ev' :: tr').

  Lemma mem_event_list_erasure_cat:
    forall tr1 tr1' tr2 tr2',
      mem_event_list_erasure tr1 tr1' ->
      mem_event_list_erasure tr2 tr2' ->
      mem_event_list_erasure (tr1 ++ tr2) (tr1' ++ tr2').
  Proof.
    induction tr1 as [|ev tr1]; intros; inv H.
    simpl; auto.
    simpl.
    constructor; eauto.
  Qed.

  Lemma trace_erasure_cat:
    forall tr1 tr1' tr2 tr2',
      trace_erasure tr1 tr1' ->
      trace_erasure tr2 tr2' ->
      trace_erasure (tr1 ++ tr2) (tr1' ++ tr2').
  Proof.
    induction tr1 as [|ev tr1]; intros; inv H.
    simpl; auto.
    simpl.
    constructor; eauto.
  Qed.

  Lemma trace_erasure_map:
    forall ev ev' tid,
      mem_event_list_erasure ev ev' ->
      trace_erasure (map [eta Events.internal tid] ev)
                    (map [eta Events.internal tid] ev').
  Proof.
    induction 1;
    simpl; constructor; auto.
    constructor; auto.
  Qed.


  Hint Resolve trace_erasure_cat trace_erasure_map : trace_erasure.
  Hint Constructors trace_erasure event_erasure : trace_erasure.

End TraceErasure.

(** ** Memory Erasure*)
Module MemErasure.

  Import ValErasure.

  (** The values of the erased memory may be more defined and its
       permissions are top.*)
  (** In retrospect setting the permissions to top was a bad
  choice. It should have been that the permissions of the erased
  memory are above the permissions of the other memory. This would
  make it more reusable and it wouldn't need a second definition for
  free. *)

  Local Notation "a # b" := (PMap.get b a) (at level 1).

  Record mem_erasure (m m': mem) :=
    { perm_le:
        forall b ofs k,
          Mem.valid_block m' b ->
          (Mem.mem_access m')#b ofs k = Some Freeable;
      erased_contents: forall b ofs,
          memval_erasure (ZMap.get ofs ((Mem.mem_contents m) # b))
                        (ZMap.get ofs ((Mem.mem_contents m') # b));
      erased_nb: Mem.nextblock m = Mem.nextblock m'
    }.

  Lemma mem_erasure_restr:
    forall m m' pmap (Hlt: permMapLt pmap (getMaxPerm m)),
      mem_erasure m m' ->
      mem_erasure (restrPermMap Hlt) m'.
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.

  Lemma mem_erasure_dilute_1:
    forall m m',
      mem_erasure m m' ->
      mem_erasure (setMaxPerm m) m'.
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.

  Lemma getN_erasure:
    forall m1 m2 b
      (Herase: forall (b : positive) (ofs : ZIndexed.t),
          memval_erasure (ZMap.get ofs (Mem.mem_contents m1) # b)
                         (ZMap.get ofs (Mem.mem_contents m2) # b)),
    forall n ofs,
      memval_erasure_list
        (Mem.getN n ofs (m1.(Mem.mem_contents)#b))
        (Mem.getN n ofs (m2.(Mem.mem_contents)#b)).
  Proof.
    induction n; intros; simpl.
    constructor.
    constructor.
    eapply Herase; eauto.
    apply IHn.
  Qed.

  Lemma proj_bytes_erasure:
    forall vl vl',
      memval_erasure_list vl vl' ->
      forall bl,
        proj_bytes vl = Some bl ->
        proj_bytes vl' = Some bl.
  Proof.
    induction 1; simpl. congruence.
    intros.
    destruct mv; simpl in H; try discriminate.
    subst.
    destruct (proj_bytes mvl) eqn:Hproj; try discriminate.
    inv H1.
    erewrite IHmemval_erasure_list by eauto.
    reflexivity.
  Qed.

  Lemma proj_bytes_not_erasure:
    forall vl vl',
      memval_erasure_list vl vl' ->
      proj_bytes vl = None -> proj_bytes vl' <> None -> In Undef vl.
  Proof.
    induction 1; simpl; intros.
    congruence.
    destruct mv; simpl in *; subst; try discriminate; auto.
    destruct (proj_bytes mvl) eqn:Hproj; try discriminate.
    destruct (proj_bytes mvl'); try congruence.
    right; eapply IHmemval_erasure_list; eauto; congruence.
    destruct mv'; subst; congruence.
  Qed.

  Lemma check_value_erasure:
    forall vl vl',
      memval_erasure_list vl vl' ->
      forall v v' q n,
        check_value n v q vl = true ->
        val_erasure v v' -> v <> Vundef ->
        check_value n v' q vl' = true.
  Proof.
    induction 1; intros; destruct n; simpl in *; auto.
    destruct mv; try discriminate.
    simpl in H. destruct mv'; try discriminate.
    destruct H as [? [? ?]]; subst.

    InvBooleans; assert (n = n1) by (apply beq_nat_true; auto). subst.
    replace v1 with v'.
    unfold proj_sumbool; rewrite ! dec_eq_true. rewrite <- beq_nat_refl. simpl; eauto.
    destruct v0; simpl in *; subst; congruence.
  Qed.

  Lemma proj_value_erasure:
    forall q vl1 vl2,
      memval_erasure_list vl1 vl2 ->
      val_erasure (proj_value q vl1) (proj_value q vl2).
  Proof.
    intros. unfold proj_value.
    inv H; simpl; auto.
    destruct mv; simpl in *; auto.
    destruct mv'; try discriminate.
    destruct H0 as [? [? ?]]; subst.
    destruct (check_value (size_quantity_nat q) v q (Fragment v q1 n0 :: mvl)) eqn:B; auto.
    destruct (Val.eq v Vundef). subst; auto.
    assert (v = v0)
      by (destruct v; simpl in *; congruence; auto).
    subst.
    erewrite check_value_erasure with (vl := (Fragment v0 q1 n0 :: mvl));
      eauto with val_erasure.
    simpl; auto.
  Qed.

  Lemma load_result_erasure:
    forall chunk v1 v2,
      val_erasure v1 v2 ->
      val_erasure (Val.load_result chunk v1) (Val.load_result chunk v2).
  Proof.
    intros. destruct v1; inv H; destruct chunk; simpl; econstructor; eauto.
  Qed.

  Lemma decode_val_erasure:
    forall vl1 vl2 chunk,
      memval_erasure_list vl1 vl2 ->
      val_erasure (decode_val chunk vl1) (decode_val chunk vl2).
  Proof.
    intros. unfold decode_val.
    pose proof H as H'.
    destruct (proj_bytes vl1) as [bl1|] eqn:PB1.
    - exploit proj_bytes_erasure; eauto. intros PB2. rewrite PB2.
      destruct chunk; simpl; auto.
    - assert (A: forall q fn,
                 val_erasure (Val.load_result chunk (proj_value q vl1))
                             (match proj_bytes vl2 with
                              | Some bl => fn bl
                              | None => Val.load_result chunk (proj_value q vl2)
                              end)).
      { intros. destruct (proj_bytes vl2) as [bl2|] eqn:PB2.
        rewrite proj_value_undef. destruct chunk; simpl; auto.
        eapply proj_bytes_not_erasure; eauto. congruence.
        apply load_result_erasure. apply proj_value_erasure; auto.
      }
      destruct chunk; simpl; eauto;
        destruct (Archi.ptr64); simpl; eauto.
      eapply proj_value_erasure with (q := Q64) in H;
      destruct (proj_value Q64 vl1) eqn:Hproj_val1;
        simpl; eauto;
          destruct (proj_value Q64 vl2); simpl in *;
            try (discriminate);
            inv H.
      + specialize (A Q64 (fun bl => Vlong (Int64.repr (decode_int bl))));
          erewrite Hproj_val1 in A;
          simpl in A;
          destruct (proj_bytes vl2);
          now eauto.
      + specialize (A Q64 (fun bl => Vlong (Int64.repr (decode_int bl)))).
          erewrite Hproj_val1 in A.
          destruct (Archi.ptr64); simpl in A.
          * destruct (proj_bytes vl2) eqn:Hproj_bytes2;
            try discriminate.
            reflexivity.
          * destruct (proj_bytes vl2) eqn:Hcontra; auto.
            eapply proj_bytes_not_erasure in PB1; eauto.
            eapply proj_value_undef with (q := Q64) in PB1.
            now congruence.
            intros ?;
                   now congruence.
  Qed.

  Lemma mem_load_erased:
    forall chunk m m' b ofs v
      (Hload: Mem.load chunk m b ofs = Some v)
      (Herased: mem_erasure m m'),
    exists v',
      Mem.load chunk m' b ofs = Some v' /\
      val_erasure v v'.
  Proof.
    intros.
    inversion Herased.
    assert (Hreadable := Mem.load_valid_access _ _ _ _ _ Hload).
    destruct Hreadable.
    assert (Hreadable': Mem.valid_access m' chunk b ofs Readable).
    { split; auto.
      intros ? ?.
      unfold Mem.perm.
      rewrite perm_le0.
      simpl; constructor.
      eapply MemoryLemmas.load_valid_block in Hload.
      unfold Mem.valid_block in *. simpl in *.
      rewrite <- erased_nb0; auto.
    }
    exists (decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs
                                  (m'.(Mem.mem_contents)#b))).
    Transparent Mem.load.
    unfold Mem.load. split.
    apply pred_dec_true; auto.
    exploit Mem.load_result; eauto. intro. rewrite H1.
    apply decode_val_erasure; auto.
    apply getN_erasure; auto.
    Opaque Mem.load.
  Qed.

  Lemma setN_erasure :
    forall (vl1 vl2 : seq.seq memval),
      memval_erasure_list vl1 vl2 ->
      forall (p : Z) (c1 c2 : ZMap.t memval),
        (forall q : Z,
            memval_erasure (ZMap.get q c1) (ZMap.get q c2)) ->
        forall q : Z,
          memval_erasure (ZMap.get q (Mem.setN vl1 p c1))
                        (ZMap.get q (Mem.setN vl2 p c2)).
  Proof.
    induction 1; intros; simpl.
    auto.
    apply IHmemval_erasure_list; auto.
    intros. erewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
    rewrite ZMap.gss. auto.
    rewrite ZMap.gso. auto. unfold ZIndexed.t in *. omega.
  Qed.

  Lemma mem_store_erased:
    forall chunk m m' b ofs v v' m2
      (Hstore: Mem.store chunk m b ofs v = Some m2)
      (Herased: mem_erasure m m')
      (Hval_erasure: val_erasure v v') ,
    exists m2', Mem.store chunk m' b ofs v' = Some m2'
           /\ mem_erasure m2 m2'.
  Proof.
    intros.
    destruct Herased.
    assert (Haccess := Mem.store_valid_access_3 _ _ _ _ _ _ Hstore).
    assert (Hvalid := Mem.valid_access_valid_block
                        _ _ _ _ (Mem.valid_access_implies
                                   _ _ _ _ _ Nonempty Haccess ltac:(constructor))).
    destruct Haccess.
    assert (Haccess' : Mem.valid_access m' chunk b ofs Writable).
    { split; auto.
      intros ? ?.
      unfold Mem.perm.
      rewrite perm_le0.
      simpl; constructor.
      unfold Mem.valid_block in *. simpl in *.
      rewrite <- erased_nb0; auto.
    }
    destruct (Mem.valid_access_dec m' chunk b ofs Writable); try by exfalso.
    destruct (Mem.valid_access_store _ _ _ _ v' Haccess') as [m2' Hstore'].
    exists m2'. split; auto.
    constructor.
    - intros.
      assert (Heq1 := MemoryLemmas.mem_store_max _ _ _ _ _ _ Hstore' b0 ofs0).
      assert (Heq2 := MemoryLemmas.mem_store_cur _ _ _ _ _ _ Hstore' b0 ofs0).
      do 2 rewrite getMaxPerm_correct in Heq1.
      do 2 rewrite getCurPerm_correct in Heq2.
      unfold permission_at in *.
      eapply Mem.store_valid_block_2 in H1; eauto.
      destruct k;
        [rewrite <- Heq1 | rewrite <- Heq2];
        eauto.
    - intros.
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore').
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore).
      rewrite ! PMap.gsspec.
      destruct (peq b0 b). subst b0.
      apply setN_erasure.
      apply val_erasure_encode_val; auto. intros. eauto.
      eauto.
    - erewrite Mem.nextblock_store with (m1 := m) by eauto.
      erewrite Mem.nextblock_store with (m2 := m2') (m1 := m') by eauto.
      eauto.
  Qed.

  Lemma mem_loadv_erased:
    forall chunk m m' vptr v
      (Hload: Mem.loadv chunk m vptr = Some v)
      (Herased: mem_erasure m m'),
    exists v',
      Mem.loadv chunk m' vptr = Some v' /\
      val_erasure v v'.
  Proof.
    intros.
    destruct vptr; try discriminate.
    simpl in *.
    eapply mem_load_erased; eauto.
  Qed.

  Lemma mem_storev_erased:
    forall chunk m m' vptr v v' m2
      (Hstore: Mem.storev chunk m vptr v = Some m2)
      (Herased: mem_erasure m m')
      (Hval_erasure: val_erasure v v') ,
    exists m2', Mem.storev chunk m' vptr v' = Some m2'
           /\ mem_erasure m2 m2'.
  Proof.
    intros.
    destruct vptr; try discriminate.
    simpl in *.
    eapply mem_store_erased; eauto.
  Qed.

  Lemma mem_erasure_valid_pointer:
    forall m m' b ofs,
      mem_erasure m m' ->
      Mem.valid_pointer m b ofs ->
      Mem.valid_pointer m' b ofs.
  Proof.
    intros.
    unfold Mem.valid_pointer in *.
    destruct H.
    destruct Mem.perm_dec; try by exfalso.
    assert (Mem.valid_block m' b).
    { destruct (valid_block_dec m' b); auto.
      unfold Mem.valid_block in *.
      rewrite <- erased_nb0 in n.
      eapply Mem.nextblock_noaccess with (ofs := ofs) (k := Cur) in n.
      unfold Mem.perm in p.
      clear H0.
      rewrite n in p.
      simpl in p.
        by exfalso.
    }
    specialize (perm_le0 _ ofs Cur H).
    unfold is_true.
    apply proj_sumbool_is_true.
    unfold Mem.perm.
    rewrite perm_le0.
    simpl; constructor.
  Qed.

  Lemma mem_erasure_valid_pointer_guard:
    forall m m' b ofs ofs',
      mem_erasure m m' ->
      Mem.valid_pointer m' b ofs
      || Mem.valid_pointer m' b ofs' = false ->
      Mem.valid_pointer m b ofs
      || Mem.valid_pointer m b ofs'= false.
  Proof.
    intros.
    apply orb_false_iff in H0. destruct H0.
    apply orb_false_iff.
    split;
      match goal with
      | [|- Mem.valid_pointer m b ?Ofs = _] =>
        destruct (Mem.valid_pointer m b Ofs) eqn:Hptr
      end; auto;
      eapply mem_erasure_valid_pointer in Hptr; eauto.
  Qed.

  Lemma val_erasure_cmpu:
    forall v1 v2 v1' v2' m m' cmp
      (Hval_erasure: val_erasure v1 v1')
      (Hval_erasure2: val_erasure v2 v2')
      (Hmem: mem_erasure m m'),
      val_erasure (Val.cmpu (Mem.valid_pointer m) cmp v1 v2)
                  (Val.cmpu (Mem.valid_pointer m') cmp v1' v2').
  Proof with eauto with val_erasure.
    intros.
    destruct v1,v2; simpl in *; inv Hval_erasure; auto;
    unfold Val.cmpu, Val.cmpu_bool; simpl; eauto with val_erasure;
    do 2 rewrite andb_if;
    repeat match goal with
           | [|- context[match ?Expr with | _ => _ end]] =>
             destruct Expr eqn:?
           end; simpl; eauto with val_erasure.
    - eapply mem_erasure_valid_pointer_guard in Heqb2; eauto.
      congruence.
    - eapply mem_erasure_valid_pointer_guard in Heqb2; eauto.
      congruence.
    -  subst.
       apply andb_false_iff in Heqb3.
       destruct Heqb3 as [Heqb3 | Heqb3];
         eapply mem_erasure_valid_pointer_guard in Heqb3; eauto;
           congruence.
    - apply andb_false_iff in Heqb3.
      destruct Heqb3 as [Heqb3 | Heqb3]. 
      eapply mem_erasure_valid_pointer in Heqb0; eauto.
      exfalso; now eauto.
      eapply mem_erasure_valid_pointer in Heqb2; eauto.
      exfalso; now eauto.
  Qed.

  Lemma val_erasure_cmplu:
    forall v1 v2 v1' v2' m m' cmp
      (Hval_erasure: val_erasure v1 v1')
      (Hval_erasure2: val_erasure v2 v2')
      (Hmem: mem_erasure m m'),
      val_erasure (Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp v1 v2))
                  (Val.maketotal (Val.cmplu (Mem.valid_pointer m') cmp v1' v2')).
  Proof with eauto with val_erasure.
    intros.
    destruct v1,v2; simpl in *; inv Hval_erasure; auto;
      unfold Val.cmplu, Val.cmplu_bool; simpl; eauto with val_erasure;
        do 2 rewrite andb_if;
        repeat match goal with
               | [|- context[match ?Expr with | _ => _ end]] =>
                 destruct Expr eqn:?
               end; simpl; eauto with val_erasure.
  Qed.

  Hint Resolve val_erasure_cmplu : val_erasure.

  Lemma storev_pointer:
    forall chunk m vptr v m',
      Mem.storev chunk m vptr v = Some m' ->
      isPointer vptr.
  Proof.
    intros. destruct vptr; simpl in *; try discriminate.
    auto.
  Qed.

  Lemma loadv_pointer:
    forall chunk m vptr v,
      Mem.loadv chunk m vptr = Some v ->
      isPointer vptr.
  Proof.
    intros. destruct vptr; simpl in *; try discriminate.
    auto.
  Qed.


  Lemma memval_erasure_list_length:
    forall mv mv',
      memval_erasure_list mv mv' ->
      length mv = length mv'.
  Proof.
    intros.
    induction H; simpl;
      now eauto.
  Qed.
  
   Lemma storebytes_erasure:
    forall m m' b ofs mv mv' m2
      (Hstore: Mem.storebytes m b ofs mv = Some m2)
      (Herased: mem_erasure m m')
      (Hval_erasure: memval_erasure_list mv mv') ,
    exists m2', Mem.storebytes m' b ofs mv' = Some m2'
           /\ mem_erasure m2 m2'.
  Proof.
    intros.
    destruct Herased.
    Transparent Mem.storebytes.
    unfold Mem.storebytes in *.
    destruct (Mem.range_perm_dec m b ofs (ofs + Z.of_nat (length mv)) Cur Writable);
      try discriminate.
    inv Hstore.
    erewrite <- memval_erasure_list_length by eauto.
    eexists.
    split.
    - apply pred_dec_true.
      intros ofs' Hrange.
      specialize (r _ Hrange).
      assert (Mem.valid_block m' b).
      { destruct (valid_block_dec m' b); auto.
        unfold Mem.valid_block in *.
        rewrite <- erased_nb0 in n.
        apply Mem.nextblock_noaccess with (ofs := ofs') (k := Cur) in n.
        unfold Mem.perm in r.
        rewrite n in r. simpl in r; by exfalso.
      }
      apply perm_le0 with (ofs := ofs') (k := Cur) in H.
      unfold Mem.perm. rewrite H. simpl; constructor.
    - econstructor.
      + intros.
        unfold Mem.valid_block, Plt in *.
        simpl in *.
        eauto.
      + intros.
        simpl.
      rewrite ! PMap.gsspec.
      destruct (peq b0 b). subst b0.
      apply setN_erasure;
        now auto.
      now eauto.
      + simpl.
        assumption.
  Qed.
  
  Lemma loadbytes_erasure:
    forall m m' b ofs sz bytes
      (Hmem_erasure: mem_erasure m m')
      (Hloadbytes: Mem.loadbytes m b ofs sz = Some bytes),
    exists bytes',
      Mem.loadbytes m' b ofs sz = Some bytes' /\
      memval_erasure_list bytes bytes'.
  Proof.
    intros.
    Transparent Mem.loadbytes.
    unfold Mem.loadbytes in *.
    destruct (Mem.range_perm_dec m b ofs (ofs + sz) Cur Readable).
    inv Hloadbytes.
    exists (Mem.getN (nat_of_Z sz) ofs (m'.(Mem.mem_contents)#b)).
    split. apply pred_dec_true.
    unfold Mem.range_perm in r.
    intros ofs' Hrange.
    specialize (r _ Hrange).
    assert (Mem.valid_block m' b).
    { destruct (valid_block_dec m' b); auto.
      destruct Hmem_erasure.
      unfold Mem.valid_block in *.
      rewrite <- erased_nb0 in n.
      apply Mem.nextblock_noaccess with (ofs := ofs') (k := Cur) in n.
      unfold Mem.perm in r.
      rewrite n in r. simpl in r; by exfalso.
    }
    apply (perm_le Hmem_erasure) with (ofs := ofs') (k := Cur) in H.
    unfold Mem.perm. rewrite H. simpl; constructor.
    apply getN_erasure; auto.
    destruct Hmem_erasure; auto.
    discriminate.
  Qed.

  Lemma mem_erasure_idempotent:
    forall m m',
      mem_erasure m m' ->
      mem_erasure m (erasePerm m').
  Proof.
    intros.
    destruct H.
    constructor; auto.
    intros.
    unfold Mem.valid_block in *.
    unfold Mem.nextblock, erasePerm in H.
    eapply erasePerm_V with (ofs := ofs) (k := k) in H.
    unfold permission_at in *.
    auto.
  Qed.

  Hint Resolve mem_erasure_idempotent mem_erasure_dilute_1
       mem_erasure_restr: mem_erasure.


 Record mem_erasure' (m m': mem) :=
    { perm_le':
        forall b ofs k,
          Mem.valid_block m b->
          Mem.perm_order'' ((Mem.mem_access m')#b ofs k)
                           ((Mem.mem_access m)#b ofs k);
      erased_contents': forall b ofs,
          memval_erasure (ZMap.get ofs ((Mem.mem_contents m) # b))
                         (ZMap.get ofs ((Mem.mem_contents m') # b));
      erased_nb': Mem.nextblock m = Mem.nextblock m'
    }.

  Lemma mem_erasure'_erase:
    forall m m',
      mem_erasure' m m' ->
      mem_erasure m (erasePerm m').
  Proof.
    intros.
    destruct H.
    constructor; auto.
    intros.
    unfold Mem.valid_block in H.
    simpl in H.
    eapply erasePerm_V in H; eauto.
  Qed.

  Lemma alloc_erasure':
    forall m m' lo hi m2 m2' b b'
      (Herased: mem_erasure m m')
      (Halloc: Mem.alloc m lo hi = (m2, b))
      (Halloc': Mem.alloc m' lo hi = (m2', b')),
      mem_erasure' m2 m2' /\ b = b'.
  Proof.
    intros.
    destruct Herased.
    assert (b = b').
    { apply Mem.alloc_result in Halloc.
      apply Mem.alloc_result in Halloc'.
      subst; auto. }
    subst.
    split; auto.
    constructor.
    - intros.
      destruct (Pos.eq_dec b b').
      + subst.
        destruct (Z_le_dec lo ofs);
          destruct (Z_lt_dec ofs hi).
        * assert (Heq:=
                    memory_lemmas.MemoryLemmas.permission_at_alloc_2 _ _ _ _ _ _ Halloc' ltac:(eauto)).
          unfold permission_at in Heq.
          specialize (Heq k).
          rewrite Heq.
          simpl.
          destruct ((Mem.mem_access m2) # b' ofs k); constructor; auto.
        * apply Znot_lt_ge in n.
          assert (H1:= MemoryLemmas.permission_at_alloc_3 _ _ _ _ _ _ Halloc'
                                                          ltac:(eauto)).
          assert (H2:= MemoryLemmas.permission_at_alloc_3 _ _ _ _ _ _ Halloc ltac:(eauto)).
          unfold permission_at in H1,H2.
          specialize (H1 k). specialize (H2 k).
          rewrite H1 H2.
          simpl. auto.
        * assert (ofs < lo)
            by omega.
          assert (H1:= MemoryLemmas.permission_at_alloc_3 _ _ _ _ _ ofs Halloc'
                                                          ltac:(eauto)).
          assert (H2:= MemoryLemmas.permission_at_alloc_3 _ _ _ _ _ _ Halloc ltac:(eauto)).
          unfold permission_at in H1,H2.
          specialize (H1 k). specialize (H2 k).
          rewrite H1 H2.
          simpl. auto.
        * assert (ofs < lo)
            by omega.
          assert (H1:= MemoryLemmas.permission_at_alloc_3 _ _ _ _ _ ofs Halloc'
                                                          ltac:(eauto)).
          assert (H2:= MemoryLemmas.permission_at_alloc_3 _ _ _ _ _ _ Halloc ltac:(eauto)).
          unfold permission_at in H1,H2.
          specialize (H1 k). specialize (H2 k).
          rewrite H1 H2.
          simpl. auto.
      + eapply Mem.valid_block_alloc_inv in H; eauto.
        destruct H; try by exfalso.
        unfold Mem.valid_block in H.
        rewrite erased_nb0 in H.
        assert (H2:= MemoryLemmas.permission_at_alloc_1 _ _  lo hi _ b ofs
                                                        Halloc' ltac:(eauto)).
        unfold permission_at in H2.
        specialize (H2 k).
        rewrite <-H2.
        erewrite perm_le0; eauto. simpl.
        destruct ((Mem.mem_access m2) # b ofs k); simpl; constructor.
    - intros.
      destruct (Pos.eq_dec b b'). subst.
      erewrite MemoryLemmas.val_at_alloc_2 by eauto.
      simpl; auto.
      erewrite <- MemoryLemmas.val_at_alloc_3 by eauto.
      erewrite <- MemoryLemmas.val_at_alloc_3 with (m' := m2') by eauto.
      eauto.
    - apply Mem.nextblock_alloc in Halloc.
      apply Mem.nextblock_alloc in Halloc'.
      rewrite Halloc' Halloc erased_nb0.
      reflexivity.
  Qed.

  Lemma mem_free_erasure':
    forall m m' lo hi m2 b
      (Herased: mem_erasure m m')
      (Hfree: Mem.free m b lo hi = Some m2),
    exists m2',
      Mem.free m' b lo hi = Some m2' /\
      mem_erasure' m2 m2'.
  Proof.
    intros.
    destruct Herased.
    pose proof (Mem.free_range_perm _ _ _ _ _ Hfree) as Hperm.
    assert (Hfree': Mem.range_perm m' b lo hi Cur Freeable).
    { intros ofs Hrange.
      specialize (Hperm _ Hrange).
      unfold Mem.perm.
      assert (Mem.valid_block m' b).
      { destruct (valid_block_dec m' b); auto.
        unfold Mem.valid_block in *.
        rewrite <- erased_nb0 in n.
        apply Mem.nextblock_noaccess with (ofs := ofs) (k := Cur) in n.
        unfold Mem.perm in Hperm. rewrite n in Hperm.
        simpl in Hperm; by exfalso.
      }
      specialize (perm_le0 _ ofs Cur H).
      rewrite perm_le0.
      simpl; constructor.
    }
    apply Mem.range_perm_free in Hfree'.
    destruct Hfree' as [m2' Hfree'].
    eexists; split; eauto.
    constructor.
    - intros.
      apply Mem.free_result in Hfree.
      apply Mem.free_result in Hfree'.
      subst.
      simpl.
      unfold Mem.unchecked_free, Mem.valid_block in *. simpl in H.
      rewrite erased_nb0 in H.
      destruct (Pos.eq_dec b b0); subst.
      + do 2 rewrite Maps.PMap.gss.
        match goal with
        | [|- context[match ?Expr with | _ => _ end]] =>
          destruct Expr
        end; simpl; auto.
        erewrite perm_le0 by eauto.
        simpl. destruct ((Mem.mem_access m) # b0 ofs k); constructor.
      + do 2 erewrite Maps.PMap.gso by auto.
        erewrite perm_le0 by eauto.
        simpl. destruct ((Mem.mem_access m) # b0 ofs k); constructor.
    - intros.
      erewrite <- MemoryLemmas.mem_free_contents by eauto.
      erewrite <- MemoryLemmas.mem_free_contents with (m2 := m2') by eauto.
      eauto.
    - apply Mem.nextblock_free in Hfree.
      apply Mem.nextblock_free in Hfree'.
      rewrite Hfree Hfree'; auto.
  Qed.

  Lemma mem_store_erased':
    forall chunk m m' b ofs v v' m2
      (Hstore: Mem.store chunk m b ofs v = Some m2)
      (Herased: mem_erasure' m m')
      (Hval_erasure: val_erasure v v') ,
    exists m2', Mem.store chunk m' b ofs v' = Some m2'
           /\ mem_erasure' m2 m2'.
  Proof.
    intros.
    destruct Herased.
    assert (Haccess := Mem.store_valid_access_3 _ _ _ _ _ _ Hstore).
    assert (Hvalid := Mem.valid_access_valid_block
                        _ _ _ _ (Mem.valid_access_implies
                                   _ _ _ _ _ Nonempty Haccess ltac:(constructor))).
    destruct Haccess.
    assert (Haccess' : Mem.valid_access m' chunk b ofs Writable).
    { split; auto.
      intros ? ?.
      specialize (H _ H1).
      unfold Mem.perm in *.
      rewrite po_oo in H.
      rewrite po_oo.
      eapply po_trans; eauto.
    }
    destruct (Mem.valid_access_dec m' chunk b ofs Writable); try by exfalso.
    destruct (Mem.valid_access_store _ _ _ _ v' Haccess') as [m2' Hstore'].
    exists m2'. split; auto.
    constructor.
    - intros.
      assert (Heq1 := MemoryLemmas.mem_store_max _ _ _ _ _ _ Hstore' b0 ofs0).
      assert (Heq2 := MemoryLemmas.mem_store_cur _ _ _ _ _ _ Hstore' b0 ofs0).
      assert (Heq3 := MemoryLemmas.mem_store_max _ _ _ _ _ _ Hstore b0 ofs0).
      assert (Heq4 := MemoryLemmas.mem_store_cur _ _ _ _ _ _ Hstore b0 ofs0).
      do 2 rewrite getMaxPerm_correct in Heq1.
      do 2 rewrite getCurPerm_correct in Heq2.
      do 2 rewrite getMaxPerm_correct in Heq3.
      do 2 rewrite getCurPerm_correct in Heq4.
      unfold permission_at in *.
      eapply Mem.store_valid_block_2 in H1; eauto.
      destruct k;
        [rewrite <- Heq1, <- Heq3 | rewrite <- Heq2, <- Heq4];
        eauto.
    - intros.
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore').
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore).
      rewrite ! PMap.gsspec.
      destruct (peq b0 b). subst b0.
      apply setN_erasure.
      apply val_erasure_encode_val; auto. intros. eauto.
      eauto.
    - erewrite Mem.nextblock_store with (m1 := m) by eauto.
      erewrite Mem.nextblock_store with (m2 := m2') (m1 := m') by eauto.
      eauto.
  Qed.

  Lemma mem_storev_erased':
    forall chunk m m' vptr v v' m2
      (Hstore: Mem.storev chunk m vptr v = Some m2)
      (Herased: mem_erasure' m m')
      (Hval_erasure: val_erasure v v') ,
    exists m2', Mem.storev chunk m' vptr v' = Some m2'
           /\ mem_erasure' m2 m2'.
  Proof.
    intros.
    destruct vptr; try discriminate.
    simpl in *.
    eapply mem_store_erased'; eauto.
  Qed.

  Lemma mem_loadv_erased' :
    forall (chunk : memory_chunk) (m m' : mem) (vptr v : val)
      (Hload: Mem.loadv chunk m vptr = Some v)
      (Herased: mem_erasure' m m'),
      exists v' : val, Mem.loadv chunk m' vptr = Some v' /\ val_erasure v v'.
  Proof.
    intros.
    inversion Herased.
    destruct vptr; try by discriminate.
    simpl in Hload.
    assert (Hreadable := Mem.load_valid_access _ _ _ _ _ Hload).
    destruct Hreadable.
    assert (Hreadable': Mem.valid_access m' chunk b (Ptrofs.unsigned i) Readable).
    { split; auto.
      intros ? ?.
      eapply MemoryLemmas.load_valid_block in Hload.
      specialize (H _ H1).
      unfold Mem.perm in *.
      rewrite po_oo in H.
      rewrite po_oo.
      eapply po_trans; eauto.
    }
    exists (decode_val chunk (Mem.getN (size_chunk_nat chunk) (Ptrofs.unsigned i)
                                  (m'.(Mem.mem_contents)#b))).
    Transparent Mem.load.
    unfold Mem.load. split.
    apply pred_dec_true; auto.
    exploit Mem.load_result; eauto. intro. rewrite H1.
    apply decode_val_erasure; auto.
    apply getN_erasure; auto.
    Opaque Mem.load.
  Qed.

  Lemma mem_erasure_erasure':
    forall m m',
      mem_erasure m m' ->
      mem_erasure' m m'.
  Proof.
    intros. destruct H.
    split; auto.
    intros.
    unfold Mem.valid_block in *.
    rewrite erased_nb0 in H.
    erewrite perm_le0 by eauto.
    simpl. destruct ((Mem.mem_access m) # b ofs k); simpl; constructor.
  Qed.

End MemErasure.

(** ** Erasure of cores *)
Module CoreErasure.
  Import ValErasure MemErasure TraceErasure event_semantics.

  Section CoreErasure.
    Context {Sem: Semantics}.

    Class CoreErasure :=
      { core_erasure : semC -> semC -> Prop;
        core_erasure_refl: forall c, core_erasure c c;

        at_external_erase:
          forall c c' m m' ef vs
            (Hcore_erase: core_erasure c c')
            (Hmem_erase: mem_erasure m m')
            (Hat_ext:at_external semSem c m = Some (ef, vs)),
          exists vs',
            at_external semSem c' m' = Some (ef, vs') /\
            val_erasure_list vs vs';
           
        after_external_erase:
          forall v v' c c' m m' c2
            (HeraseCores: core_erasure c c')
            (HeraseVal: optionval_erasure v v')
            (Hmem_erase: mem_erasure m m')
            (Hafter_external: after_external semSem v c m = Some c2),
          exists c2',
            after_external semSem v' c' m' = Some c2' /\
            core_erasure c2 c2';

        erasure_initial_core:
          forall h v arg v' arg' c m m' m2
            (Hv: val_erasure v v')
            (Harg: val_erasure arg arg')
            (Hmem_erase: mem_erasure m m')
            (Hinit: initial_core semSem h m c m2 v [:: arg]),
            exists c' m2',
              initial_core semSem h m' c' m2' v' [:: arg'] /\
              core_erasure c c' /\
              mem_erasure m2 (erasePerm m2');

        halted_erase:
          forall c c' n
            (HeraseCores: core_erasure c c')
            (Hhalted: halted semSem c n),
            halted semSem c' n;

        evstep_erase:
          forall c1 c1' c2 ev m1 m1' m2
            (HeraseCores: core_erasure c1 c1')
            (Hmem_erasure: mem_erasure m1 m1')
            (Hstep: ev_step semSem c1 m1 ev c2 m2),
          exists c2' m2' ev',
            ev_step semSem c1' m1' ev' c2' m2' /\
            core_erasure c2 c2' /\ mem_erasure m2 (erasePerm m2') /\
            mem_event_list_erasure ev ev'
      }.
  End CoreErasure.
  Hint Resolve core_erasure_refl : erased.
End CoreErasure.

Module ThreadPoolErasure.

  Import HybridMachine HybridMachineSig.
  Import ValErasure CoreErasure threadPool ThreadPool.

  Section ThreadPoolErasure.
    Context {Sem: Semantics}
            {CE: CoreErasure}.

    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachine.dryResources.
    Existing Instance BareMachine.resources.
    Existing Instance AsmContext.bareMach.
    Existing Instance AsmContext.dryFineMach.

    Notation containsThreadF := (@containsThread DryHybridMachine.dryResources Sem OrdinalPool.OrdinalThreadPool).
    Notation containsThreadE := (@containsThread BareMachine.resources Sem OrdinalPool.OrdinalThreadPool).
    
    Definition ctl_erasure c c' : Prop :=
      match c, c' with
      | Kinit vf arg, Kinit vf' arg' =>
        val_erasure vf vf' /\ val_erasure arg arg'
      | Krun c, Krun c' =>
        core_erasure c c'
      | Kblocked c, Kblocked c' =>
        core_erasure c c'
      | Kresume c arg, Kresume c' arg' =>
        core_erasure c c' /\ arg = arg'
      (*we don't use this and our semantics are strange*)
      | _, _  => False
      end.

    Inductive threadPool_erasure tp tp' :=
    | ErasedPool :
        (forall i, containsThreadF tp i <-> containsThreadE tp' i) ->
        (forall i (cnti: containsThreadF tp i)
           (cnti': containsThreadE tp' i),
            ctl_erasure (getThreadC cnti) (getThreadC cnti')) ->
        threadPool_erasure tp tp'.

    Lemma erasedPool_contains:
      forall tp1 tp1'
        (HerasedPool: threadPool_erasure tp1 tp1') i,
        containsThread tp1 i <-> containsThread tp1' i.
    Proof.
      intros.
      inversion HerasedPool;
        now eauto.
    Qed.

    Lemma erasedPool_num_threads:
      forall tp tp'
        (HerasedPool: threadPool_erasure tp tp'),
        OrdinalPool.num_threads tp = OrdinalPool.num_threads tp'.
    Proof.
      intros.
      inversion HerasedPool.
      simpl in *.
      unfold OrdinalPool.containsThread, OrdinalPool.addThread, OrdinalPool.latestThread in *.
      simpl in *.
      assert (n (OrdinalPool.num_threads tp) = n (OrdinalPool.num_threads tp')).
      { pose proof (eqn_leq (OrdinalPool.num_threads tp) (OrdinalPool.num_threads tp')) as Heq.
        apply/eqP.
        erewrite eqn_leq.
        apply/andP.
        split.
        - eapply leq_trans with (OrdinalPool.num_threads tp).
          ssromega.
          assert (Hle:= leq_total (OrdinalPool.num_threads tp) (OrdinalPool.num_threads tp')).
          move/orP:Hle=>Hle.
          destruct Hle; auto.
          rewrite leq_eqVlt in H1.
          move/orP:H1=>[H1 | H1].
          move/eqP:H1=>H1; subst.
          rewrite H1.
          eauto.
          pose proof (proj1 (H (OrdinalPool.num_threads tp')) H1).
          exfalso.
          ssromega.
        - eapply leq_trans with (OrdinalPool.num_threads tp').
          ssromega.
          assert (Hle:= leq_total (OrdinalPool.num_threads tp') (OrdinalPool.num_threads tp)).
          move/orP:Hle=>Hle.
          destruct Hle; auto.
          rewrite leq_eqVlt in H1.
          move/orP:H1=>[H1 | H1].
          move/eqP:H1=>H1; subst.
          rewrite H1.
          eauto.
          pose proof (proj2 (H (OrdinalPool.num_threads tp)) H1).
          exfalso.
          ssromega.
      }
      clear - H1.
      destruct (OrdinalPool.num_threads tp), (OrdinalPool.num_threads tp').
      simpl in *.
      subst.
      apply f_equal.
      erewrite proof_irr by eauto.
      reflexivity.
    Qed.

  Lemma ctl_erasure_refl:
    forall c, ctl_erasure c c.
  Proof with eauto with val_erasure erased.
    destruct c; simpl...
  Qed.

  Lemma erased_updLockSet:
    forall tp tp' addr addr' rmap rmap',
      threadPool_erasure tp tp' ->
      threadPool_erasure (updLockSet tp addr rmap)
                        (updLockSet tp' addr' rmap').
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.

  Lemma erased_updThread:
    forall tp tp' i (cnti: containsThread tp i)
      (cnti': containsThread tp' i) c c' pmap,
      threadPool_erasure tp tp' ->
      ctl_erasure c c' ->
      threadPool_erasure (updThread cnti c pmap)
                         (updThreadC cnti' c').
  Proof.
    intros.
    inversion H.
    constructor; auto.
    intros.
    destruct (i0 == i) eqn:Heq; move/eqP:Heq=>Heq.
    subst. rewrite gssThreadCode.
    rewrite gssThreadCC; now auto.
    rewrite gsoThreadCode; eauto.
    erewrite <- gsoThreadCC with (cntj' := cnti'0) (cntj := cntUpdateC' _ cnti' cnti'0) by eauto.
    now eauto.
  Qed.

  Lemma erased_updThread':
    forall tp tp' i (cnti: containsThread tp i)
      (cnti': containsThread tp' i) c c' pmap pmap',
      threadPool_erasure tp tp' ->
      ctl_erasure c c' ->
      threadPool_erasure (updThread cnti c pmap)
                         (updThread cnti' c' pmap').
  Proof.
    intros.
    inversion H.
    constructor; auto.
    intros.
    destruct (i0 == i) eqn:Heq; move/eqP:Heq=>Heq.
    subst. rewrite! gssThreadCode; now auto.
    rewrite! gsoThreadCode; now eauto.
  Qed.

  Lemma erased_updThreadC:
    forall tp tp' i (cnti: containsThread tp i)
      (cnti': containsThread tp' i) c c',
      threadPool_erasure tp tp' ->
      ctl_erasure c c' ->
      threadPool_erasure (updThreadC cnti c)
                         (updThreadC cnti' c').
  Proof.
    intros.
    inversion H.
    constructor; auto.
    intros.
    destruct (i0 == i) eqn:Heq; move/eqP:Heq=>Heq.
    subst.
    rewrite gssThreadCC.
    rewrite gssThreadCC; now auto.
    erewrite <- gsoThreadCC with (cntj := cntUpdateC' _ cnti cnti0); eauto.
    erewrite <- gsoThreadCC with (cntj' := cnti'0) (cntj := cntUpdateC' _ cnti' cnti'0) by eauto.
    now eauto.
  Qed.

  Lemma erased_addThread:
    forall tp tp' v arg v' arg' pmap pmap',
      threadPool_erasure tp tp' ->
      val_erasure v v' ->
      val_erasure arg arg' ->
      threadPool_erasure (addThread tp v arg pmap)
                        (addThread tp' v' arg' pmap').
  Proof with eauto with val_erasure erased.
    intros.
    inversion H.
    pose proof (erasedPool_num_threads H) as Heq_threads.
    constructor.
    - unfold addThread; simpl.
      unfold OrdinalPool.addThread, OrdinalPool.containsThread; simpl.
      intros.
      rewrite Heq_threads; auto.
      split; now eauto.
    - intros.
      assert (cnti00 := cntAdd' _ _ _ cnti).
      assert (cnti0'0 := cntAdd' _ _ _ cnti').
      destruct cnti00 as [[cnti00 ?] | Heq];
        destruct cnti0'0 as [[cnti0'0 ?] | ?].
      + erewrite gsoAddCode with (cntj := cnti00) by eauto.
        erewrite gsoAddCode with (cntj := cnti0'0) by eauto.
        eauto.
      + exfalso; subst; apply H4.
        unfold latestThread. simpl.
        unfold OrdinalPool.latestThread.
        rewrite Heq_threads.
        reflexivity.
      + exfalso; subst; apply H4.
        unfold latestThread. simpl.
        unfold OrdinalPool.latestThread.
        rewrite Heq_threads.
        reflexivity.
      + subst. erewrite! gssAddCode by eauto.
        simpl; split...
  Qed.

  Lemma erased_remLockSet:
    forall tp tp' addr addr',
      threadPool_erasure tp tp' ->
      threadPool_erasure (remLockSet tp addr)
                        (remLockSet tp' addr').
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.

  End ThreadPoolErasure.

  Hint Resolve erased_updLockSet erased_updThread
       erased_addThread erased_remLockSet: erased.

End ThreadPoolErasure.

(** ** Erasure from FineConc to SC*)
Module SCErasure.

  Import ValErasure MemErasure TraceErasure CoreErasure ThreadPoolErasure.
  Import CoreLanguage HybridMachine HybridMachineSig ThreadPool AsmContext.
  Import Executions event_semantics.
  
  Section SCErasure.
    Context {Sem: Semantics}
            {SemAxioms: SemAxioms}
            {SemD: SemDet}
            {CE: CoreErasure}
            {initU: seq.seq nat}.
    

    Existing Instance OrdinalPool.OrdinalThreadPool.

    Existing Instance DryHybridMachine.dryResources.
    Existing Instance DryHybridMachine.DryHybridMachineSig.
    Existing Instance dryFineMach.
    Existing Instance FineDilMem.
    Existing Instance HybridFineMachine.scheduler.

    Existing Instance BareMachine.resources.
    Existing Instance BareMachine.BareMachineSig.
    Existing Instance BareDilMem.
    Existing Instance bareMach.

    Notation syncStepF := (@syncStep DryHybridMachine.dryResources _ OrdinalPool.OrdinalThreadPool
                                     DryHybridMachine.DryHybridMachineSig).
    Notation syncStepE := (@syncStep BareMachine.resources _ OrdinalPool.OrdinalThreadPool
                                     BareMachine.BareMachineSig).

    Notation start_threadF := (@start_thread DryHybridMachine.dryResources _ OrdinalPool.OrdinalThreadPool
                                             DryHybridMachine.DryHybridMachineSig).
    Notation start_threadE := (@start_thread BareMachine.resources _ OrdinalPool.OrdinalThreadPool
                                             BareMachine.BareMachineSig).

    Notation resume_threadF := (@resume_thread DryHybridMachine.dryResources _ OrdinalPool.OrdinalThreadPool
                                               DryHybridMachine.DryHybridMachineSig).
    Notation resume_threadE := (@resume_thread BareMachine.resources _ OrdinalPool.OrdinalThreadPool
                                               BareMachine.BareMachineSig).
    
    Notation suspend_threadF := (@suspend_thread DryHybridMachine.dryResources _ OrdinalPool.OrdinalThreadPool
                                                 DryHybridMachine.DryHybridMachineSig).
    Notation suspend_threadE := (@suspend_thread BareMachine.resources _ OrdinalPool.OrdinalThreadPool
                                                 BareMachine.BareMachineSig).

    Notation threadStepF := (@threadStep DryHybridMachine.dryResources _ OrdinalPool.OrdinalThreadPool
                                         DryHybridMachine.DryHybridMachineSig).
    Notation threadStepE := (@threadStep BareMachine.resources _ OrdinalPool.OrdinalThreadPool
                                         BareMachine.BareMachineSig).

    
    Notation fstep := (corestep (@fine_semantics _ initU)).
    Notation scstep := (corestep (@bare_semantics _ initU)).
    Notation fsafe := (@HybridFineMachine.fsafe DryHybridMachine.dryResources _ OrdinalPool.OrdinalThreadPool
                                                  DryHybridMachine.DryHybridMachineSig FineDilMem).
    Notation sc_safe := (@HybridFineMachine.fsafe BareMachine.resources _ OrdinalPool.OrdinalThreadPool
                                                  BareMachine.BareMachineSig BareDilMem).
    Notation fexecution := (@fine_execution _ FineDilMem DryHybridMachine.dryResources).
    Notation sc_execution := (@fine_execution _ BareDilMem BareMachine.resources).
    
    (** ** Simulation for syncStep, startStep, resumeStep, suspendStep *)
    Hint Resolve mem_erasure_restr : erased.
    
    Lemma syncStep_erase:
      forall tp1 tp1' m1 m1' tp2 m2 i ev
        (HerasePool: threadPool_erasure tp1 tp1')
        (cnti: containsThread tp1 i)
        (cnti': containsThread tp1' i)
        (Hmem_erasure: mem_erasure m1 m1')
        (Hcomp1: mem_compatible tp1 m1)
        (Hcomp1': mem_compatible tp1' m1')
        (Hstep: syncStepF false cnti Hcomp1 tp2 m2 ev),
      exists tp2' m2',
        syncStepE false cnti' Hcomp1' tp2' m2' (eraseSyncEvent ev) /\
        threadPool_erasure tp2 tp2' /\ mem_erasure m2 m2'.
    Proof with eauto with val_erasure erased.
      intros.
      inversion HerasePool as [Hnum Hthreads].
      specialize (Hthreads _ cnti cnti').
      inversion Hstep; subst;
        match goal with
        | [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
          rewrite H1 in H; destruct Expr2 eqn:?; simpl in H
        end; try (by exfalso);
          try match goal with
              | [H: Mem.load _ _ _ _ = Some _ |- _] =>
                eapply mem_load_erased in H; eauto with val_erasure erased;
                  destruct Hload as [? [Hload ?]]
              end;
          try match goal with
              | [H: Mem.store _ _ _ _ _ = Some _ |- _] =>
                eapply mem_store_erased in H; eauto with val_erasure erased;
                  destruct Hstore as [m2' [Hstore Hmem_erasure']]
              end;
          try match goal with
              | [|- _ <> Vundef] => intro Hcontra; discriminate
              end;
      match goal with
      | [H: at_external _ _ (restrPermMap ?E1) = _, H1: core_erasure _ _   |- _] =>
        pose proof (at_external_erase _ _ H1 (mem_erasure_restr E1 Hmem_erasure) H) as Hat_external';
        destruct Hat_external' as [vs' [Hat_external' Hval_erasure]]
      end;
      repeat match goal with
             | [H: _ /\ _ |- _] => destruct H
             | [H: val_erasure_list _ _ |- _] =>
               inv H
             | [H: val_erasure (Vptr _ _) _ |- _] => inv H
             | [H:val_erasure (Vint _) _ |- _] => inv H
             end; subst.
      - exists (updThreadC cnti' (Kresume s Vundef)), m2'.
        split; [econstructor; eauto | split; eauto].
        constructor. simpl; eauto.
        intros j cntj cntj'.
        rewrite gLockSetCode.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          rewrite gssThreadCode.
          rewrite gssThreadCC.
          simpl;
            now auto.
        + rewrite gsoThreadCode; auto.
          assert (cntj0' := cntUpdateC' _ _ cntj').
          erewrite <- @gsoThreadCC with (cntj := cntj0')
            by eauto.
          inversion HerasePool;
            now eauto.
      - exists (updThreadC cnti' (Kresume s Vundef)), m2'.
        split; [econstructor; eauto | split; eauto].
        constructor. simpl; eauto.
        intros j cntj cntj'.
        rewrite gLockSetCode.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          rewrite gssThreadCode.
          rewrite gssThreadCC.
          simpl;
            now auto.
        + rewrite gsoThreadCode; auto.
          assert (cntj0' := cntUpdateC' _ _ cntj').
          erewrite <- @gsoThreadCC with (cntj := cntj0')
            by eauto.
          inversion HerasePool;
            now eauto.
      - exists (addThread
             (updThreadC cnti' (Kresume s Vundef))
             (Vptr b ofs) v'0 tt), m1'.
        split; [econstructor; eauto | split; eauto].
        eapply erased_addThread; eauto...
        eapply erased_updThread; eauto...
        simpl;
          split;
          now eauto...
      - exists (updThreadC cnti' (Kresume s Vundef)), m2'.
        split; [econstructor; eauto | split; eauto].
        constructor. simpl; eauto.
        intros j cntj cntj'.
        rewrite gLockSetCode.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          rewrite gssThreadCode.
          rewrite gssThreadCC.
          simpl; auto.
        + rewrite gsoThreadCode; auto.
          assert (cntj0' := cntUpdateC' _ _ cntj').
          erewrite <- @gsoThreadCC with (cntj := cntj0')
            by eauto.
          inversion HerasePool; eauto.
      - exists (updThreadC cnti' (Kresume s Vundef)), m1'.
        split; [econstructor; eauto | split; eauto].
        constructor. simpl; eauto.
        intros j cntj cntj'.
        rewrite gRemLockSetCode.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          rewrite gssThreadCode.
          rewrite gssThreadCC.
          simpl; auto.
        + rewrite gsoThreadCode; auto.
          assert (cntj0' := cntUpdateC' _ _ cntj').
          erewrite <- @gsoThreadCC with (cntj := cntj0')
            by eauto.
          inversion HerasePool; eauto.
      - exists tp1', m1'.
        split; [econstructor; eauto | split; eauto].
    Qed.

    Ltac pf_cleanup :=
      repeat match goal with
             | [H1: invariant ?X, H2: invariant ?X |- _] =>
               assert (H1 = H2) by (by eapply proof_irr);
               subst H2
             | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
               assert (H1 = H2) by (by eapply proof_irr);
               subst H2
             | [H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
               assert (H1 = H2) by (by eapply proof_irr); subst H2
             | [H1: containsThread ?TP ?M, H2: containsThread ?TP ?M |- _] =>
               assert (H1 = H2) by (by eapply proof_irr); subst H2
             | [H1: containsThread ?TP ?M,
                    H2: containsThread (@updThreadC _ ?TP _ _) ?M |- _] =>
               apply cntUpdateC' in H2;
               assert (H1 = H2) by (by eapply cnt_irr); subst H2
             | [H1: containsThread ?TP ?M,
                    H2: containsThread (@updThread _ ?TP _ _ _) ?M |- _] =>
               apply cntUpdate' in H2;
               assert (H1 = H2) by (by eapply cnt_irr); subst H2
             end.

    Lemma startStep_erasure:
      forall tp1 tp1' tp2 m1 m1' m2 i
        (HerasePool: threadPool_erasure tp1 tp1')
        (Herase_mem: mem_erasure m1 m1')
        (cnti: containsThread tp1 i)
        (cnti': ThreadPool.containsThread tp1' i)
        (Hcomp1': mem_compatible tp1' m1')
        (Hstep: start_threadF m1 cnti tp2 m2),
      exists tp2' m2',
        start_threadE m1' cnti' tp2' m2' /\
        threadPool_erasure tp2 tp2' /\
        mem_erasure m2 (erasePerm m2').
    Proof.
      intros.
      inversion HerasePool as [Hnum Hthreads].
      specialize (Hthreads _ cnti cnti').
      inversion Hstep; subst.
      pf_cleanup;
        match goal with
          [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
          rewrite H1 in H;
            destruct Expr2 eqn:?;
                     simpl in H
        end; try (by exfalso).
      repeat match goal with
             | [H: _ /\ _ |- _] => destruct H
             | [H: val_erasure_list _ _ |- _] =>
               inv H
             | [H: val_erasure (Vptr _ _) _ |- _] => inv H
             end; subst.
      eapply @erasure_initial_core with (m' := m1') in Hinitial; eauto.
      destruct Hinitial as [c2' [m2' [Hinitial2' [Hcore_erasure2 Hmem_erasure2]]]].
      exists (updThread cnti' (Krun c2') (add_block Hcomp1' cnti' m2')), m2'.
      split; [|split].
      - eapply @StartThread with (Hcmpt := Hcomp1'); eauto.
        unfold install_perm.
        simpl.
        unfold BareMachine.install_perm.
        reflexivity.
      - eapply erased_updThread'; eauto.
      - assumption.
      - inversion Hperm; subst.
        eapply mem_erasure_restr;
          now eauto.
    Qed.

    Lemma resumeStep_erasure:
      forall tp1 m1 tp1' m1' tp2 i
        (HerasePool: threadPool_erasure tp1 tp1')
        (Herase_mem: mem_erasure m1 m1')
        (cnti: containsThread tp1 i)
        (cnti': containsThread tp1' i)
        (Hcomp1': mem_compatible tp1' m1')
        (Hstep: resume_thread m1 cnti tp2),
      exists tp2',
        resume_thread m1' cnti' tp2' /\
        threadPool_erasure tp2 tp2'.
    Proof.
      intros.
      inversion HerasePool as [Hnum Hthreads].
      specialize (Hthreads _ cnti cnti').
      inversion Hstep; subst.
      pf_cleanup;
        match goal with
          [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
          rewrite H1 in H; destruct Expr2 eqn:?; simpl in H
        end; try (by exfalso).
      destruct Hthreads as [HeraseCores Heq]. subst v.
      inversion Hperm; subst.
      destruct X.
      pose proof (at_external_erase _ _ HeraseCores
                                    (mem_erasure_restr (DryHybridMachine.compat_th tp1 m1 Hcmpt cnti)#1 Herase_mem) Hat_external) as Hat_external'.
      destruct Hat_external' as [vs' [Hat_external' Hval_erasure]].
      eapply after_external_erase with (v' := None) in Hafter_external;
        eauto with val_erasure erased.
      destruct Hafter_external as [c2' [Hafter_external' Hcore_erasure']].
      exists (updThreadC cnti' (Krun c2')).
      split.
      - eapply @ResumeThread with (Hcmpt := Hcomp1') (c := s); simpl in *; eauto.
        reflexivity.
      - eapply erased_updThreadC;
          now eauto.
    Qed.

    Lemma suspendStep_erasure:
      forall tp1 m1 tp1' m1' tp2 i
        (HerasePool: threadPool_erasure tp1 tp1')
        (Herase_mem: mem_erasure m1 m1')
        (cnti: containsThread tp1 i)
        (cnti': containsThread tp1' i)
        (Hcomp1': mem_compatible tp1' m1')
        (Hstep: suspend_threadF m1 cnti tp2),
      exists tp2',
        suspend_threadE m1' cnti' tp2' /\
        threadPool_erasure tp2 tp2'.
    Proof.
      intros.
      inversion HerasePool as [Hnum Hthreads].
      specialize (Hthreads _ cnti cnti').
      inversion Hstep; subst.
      pf_cleanup;
        match goal with
          [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
          rewrite H1 in H; 
            destruct Expr2 eqn:?;
                     simpl in H
        end; try (by exfalso).
      inversion Hperm; subst.
      destruct X.
      pose proof (at_external_erase _ _ Hthreads
                                    (mem_erasure_restr (DryHybridMachine.compat_th tp1 m1 Hcmpt cnti)#1 Herase_mem) Hat_external) as Hat_external'.
      destruct Hat_external' as [vs' [Hat_external' Hval_erasure]].
      exists (updThreadC cnti' (Kblocked s)).
      split.
      - eapply @SuspendThread with (c := s) (Hcmpt := Hcomp1'); simpl in *; eauto.
        reflexivity.
      - eapply erased_updThreadC;
          now eauto.
    Qed.
    
    Lemma threadStep_erase:
      forall tp1 tp1' m1 m1' tp2 m2 i ev
        (HerasePool: threadPool_erasure tp1 tp1')
        (cnti: containsThread tp1 i)
        (cnti': containsThread tp1' i)
        (Hmem_erasure: mem_erasure m1 m1')
        (Hcomp1: mem_compatible tp1 m1)
        (Hcomp1': mem_compatible tp1' m1')
        (Hstep: threadStepF cnti Hcomp1 tp2 m2 ev),
      exists tp2' m2' ev',
        threadStepE cnti' Hcomp1' tp2' m2' ev' /\
        threadPool_erasure tp2 tp2' /\ mem_erasure m2 (erasePerm m2') /\
        mem_event_list_erasure ev ev'.
    Proof.
      intros.
      inversion HerasePool as [Hnum Hthreads].
      specialize (Hthreads _ cnti cnti').
      inversion Hstep; subst.
      pf_cleanup;
        match goal with
          [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
          rewrite H1 in H;
            destruct Expr2 eqn:?;
                     simpl in H
        end; try (by exfalso).
      eapply mem_erasure_restr with (Hlt := (DryHybridMachine.compat_th _ _ Hcomp1 cnti).1) in Hmem_erasure.
      eapply evstep_erase in Hcorestep; eauto.
      destruct Hcorestep as (c2' & m2' & ev' & Hevstep' & Hcore_erasure'
                             & Hmem_erasure' & Hev_erasure).
      exists (updThreadC cnti' (Krun c2')), m2', ev'.
      split; eauto.
      econstructor; eauto.
      split; eauto.
      constructor; eauto.
      intros j cntj cntj'.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite gssThreadCC.
        simpl; eauto.
      + assert (cntj0' := cntUpdateC' _ _ cntj').
        assert (cntj0 := cntUpdate' _ _ _ cntj).
        erewrite  @gsoThreadCode with (cntj :=  cntj0) by eauto.
        erewrite <- @gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool;
          now eauto.
    Qed.

    (** A step on the FineConc machine can be matched by a step on the
  SC machine producing an erased event *)
    Lemma sc_sim:
      forall tp1 tp1' i U tr1 tr1' tr2 m1 m1' tp2 m2
        (HerasePool: threadPool_erasure tp1 tp1')
        (Hmem_erasure: mem_erasure m1 m1')
        (Hfstep: fstep (i :: U, tr1, tp1) m1 (U, tr2, tp2) m2),
      exists tp2' m2' tr2',
        scstep (i :: U, tr1', tp1') m1' (U, tr2', tp2') m2' /\
        threadPool_erasure tp2 tp2' /\ mem_erasure m2 m2' /\
        (trace_erasure tr1 tr1' -> trace_erasure tr2 tr2').
    Proof with eauto with trace_erasure mem_erasure.
      intros.
      inversion Hfstep; subst;
        inv HschedN;
        try match goal with
            | [H: containsThread _ ?I |- _ ] =>
              assert (containsThread tp1' I)
                by (eapply erasedPool_contains; simpl in *; subst; eauto)
            end;
        assert (Hcomp1' : mem_compatible tp1' m1')
          by (simpl; unfold BareMachine.mem_compatible; auto).
      - (* start thread case *)
        assert (Hstep' := startStep_erasure HerasePool Hmem_erasure H Hcomp1' Htstep).
        destruct Hstep' as [tp2' [m2' [Hstart' [HerasePool' Herasemem']]]].
        exists tp2', (@diluteMem BareDilMem m2'), tr1'.
        split. econstructor 1; simpl; eauto.
        simpl in *; subst.
        split; eauto...
      - assert (Hstep' := resumeStep_erasure HerasePool Hmem_erasure H Hcomp1' Htstep).
        destruct Hstep' as [tp2' [Hstart' HerasePool']].
        exists tp2', m1', tr1'.
        split. econstructor 2; simpl; eauto.
        simpl in *; subst.
        split; now eauto.
      - assert (Htstep' := threadStep_erase HerasePool H Hmem_erasure Hcomp1' Htstep).
        destruct Htstep' as (tp2' & m2' & ev' & Htstep' & HerasePool'
                             & Hmem_erasure' & Htr_erasure').
        exists tp2', (@diluteMem BareDilMem m2'), (tr1' ++ map [eta Events.internal tid] ev').
        split.
        assert (Hsched: U = @yield HybridFineMachine.scheduler (tid :: U)) by reflexivity.
        rewrite Hsched.
        eapply thread_step; eauto.
        split...
        simpl in *; subst.
        split...
      - assert (Hstep' := suspendStep_erasure HerasePool Hmem_erasure H Hcomp1' Htstep).
        destruct Hstep' as [tp2' [Hstart' HerasePool']].
        exists tp2', m1', tr1'.
        split. econstructor 4; simpl; eauto.
        simpl in *; subst.
        split; now eauto.
      - assert (Hstep' := syncStep_erase HerasePool H Hmem_erasure Hcomp1' Htstep).
        destruct Hstep' as (tp2' & m2' & Hstep' & HerasePool' & Hmem_erasure').
        exists tp2', m2', (tr1' ++ [:: Events.external tid (eraseSyncEvent ev)]).
        split.
        eapply sync_step; eauto.
        simpl in *; subst.
        split...
      - assert (~ containsThread tp1' tid).
        { intros Hcontra.
          destruct HerasePool as [Hnum _].
          unfold containsThread in *.
          simpl in *; subst.
          rewrite <- Hnum in Hcontra.
          auto.
        }
        exists tp1', m1',tr1'.
        split.
        econstructor 6; simpl; eauto.
        simpl in *; subst.
        split; now eauto.
    Qed.

    Lemma fsafe_execution:
      forall tpf mf U tr,
        fsafe tpf mf U (size U).+1 ->
        exists tpf' mf' tr',
          fexecution (U, tr, tpf) mf ([::], tr ++ tr', tpf') mf'.
    Proof.
      intros.
      generalize dependent mf.
      generalize dependent tpf.
      generalize dependent tr.
      induction U; intros.
      - do 2 eexists. exists [::].
        erewrite cats0.
        econstructor 1; eauto.
      - simpl in H.
        inversion H; subst.
        simpl in H0; by exfalso.
        assert (exists ev, fstep ((a :: U), tr, tpf) mf
                            (U, tr ++ ev, tp') m')
          by (eapply step_trace_irr; eauto).
        destruct H0 as [ev Hstep].
        specialize (IHU (tr ++ ev) _ _ H2).
        destruct IHU as (tpf'' & mf'' & tr'' & Hexec).
        rewrite <- catA in Hexec.
        exists tpf'', mf'', (ev ++ tr'').
        econstructor 2; eauto.
        simpl in *.
        now eauto.
    Qed.

    (** The initial state of the SC machine is an erasure of the initial
  state of the FineConc machine*)
    Lemma init_erasure:
      forall f arg U tpsc tpf m m'
        (HinitSC: bare_init initU m (U, [::], tpsc) m' f arg)
        (HinitF: tpf_init initU m (U, [::], tpf) m' f arg),
        threadPool_erasure tpf tpsc.
    Proof.
      intros.
      unfold bare_init, tpf_init in *.
      simpl in *. unfold BareMachine.init_mach, DryHybridMachine.init_mach in *.
      destruct HinitSC as [? [csc [HinitSC Htpsc]]].
      destruct HinitF as [? [csf [HinitF Htpf]]].
      simpl in *. unfold OrdinalPool.mkPool in *.
      simpl in *.
      econstructor; subst; simpl;
        unfold OrdinalPool.containsThread;
        simpl; [tauto|].
      assert (Heq: csf = csc)
        by (eapply initial_core_det; eauto);
      subst.
      intros.
      apply core_erasure_refl;
        now auto.
    Qed.

    (** Any execution of the FineConc machine resulting in some trace
    tr' can be matched by an execution of the SC machine with an
    erased trace *)
    Lemma execution_sim:
      forall U U' tpf tpf' mf mf' tpsc msc tr tr' trsc
        (Hexec: fexecution (U, tr, tpf) mf (U', tr', tpf') mf')
        (HerasedPool: threadPool_erasure tpf tpsc)
        (Hmem_erasure: mem_erasure mf msc),
      exists tpsc' msc' trsc',
        sc_execution (U, trsc, tpsc) msc (U', trsc', tpsc') msc' /\
        threadPool_erasure tpf' tpsc' /\ mem_erasure mf' msc' /\
        (trace_erasure tr trsc -> trace_erasure tr' trsc').
    Proof with eauto.
      intros U.
      induction U.
      - intros.
        inversion Hexec; subst.
        exists tpsc, msc, trsc.
        split.
        econstructor 1. simpl; auto.
        split...
      - intros.
        inversion Hexec; subst.
        + simpl in H5; by exfalso.
        + eapply sc_sim with (tr1' := trsc) in H8; eauto.
          destruct H8 as (tpsc0 & msc0 & tr0 & Hstep0 & HerasedPool0
                          & Hmem_erasure0 & Htrace_erasure0).
          specialize (IHU _ _ _ _ _ _ _ _ _ tr0 H9 HerasedPool0
                          Hmem_erasure0).
          destruct IHU as (tpsc2' & msc2' & trsc2' & Hsexec & HerasedPool'
                           & Hmem_erasure' & Htrace_erasure2').
          exists tpsc2', msc2', trsc2'.
          split...
          pose proof (step_trace_monotone Hstep0) as Htr0.
          destruct Htr0 as [trsc' Htrsc'];
            subst.
          pose proof (fine_execution_schedule Hsexec); subst.
          pose proof (fine_execution_multi_step Hsexec).
          eapply multi_step_trace_monotone in H.
          destruct H as [tr''' ?].
          subst.
          rewrite <- catA.
          rewrite <- catA in Hsexec.
          econstructor; simpl in *;
            now eauto.
    Qed.

    (** Safety of the SC machine*)
    Lemma fsafe_implies_scsafe:
      forall n sched tpsc tpf mf msc
        (Hsafe: fsafe tpf mf sched n)
        (HerasedPool: threadPool_erasure tpf tpsc)
        (Hmem_erasure: mem_erasure mf msc),
        sc_safe tpsc msc sched n.
    Proof.
      intro n.
      induction n; intros.
      - simpl in *.
        inversion Hsafe; subst.
        econstructor.
        eapply @HybridFineMachine.HaltedSafe with (tr := tr);
          simpl; now auto.
      - destruct sched.
        + inv Hsafe.
          eapply @HybridFineMachine.HaltedSafe with (tr := tr);
            simpl; now auto.
          simpl in H0.
          inv H0; simpl in *; discriminate.
        + inv Hsafe.
          simpl in H; by exfalso.
          simpl in *.
          eapply step_trace_irr with (tr'' := [::]) in H0.
          destruct H0 as [ev Hstep]. simpl in Hstep.
          eapply sc_sim with (tr1' := [::]) in Hstep; eauto.
          destruct Hstep as (tpsc2' & msc2' & ? & Hstep & HerasedPool'
                             & Hmem_erasure' & ?).
          econstructor 3; simpl in *; now eauto.
    Qed.

    (** Final erasure theorem from FineConc to SC*)
    Theorem sc_erasure:
      forall f arg tpsc tpf m m'
        (HinitSC: bare_init initU m (initU, [::], tpsc) m' f arg)
        (HinitF: tpf_init initU m (initU, [::], tpf) m' f arg)
        (HsafeF: forall n, fsafe tpf (@diluteMem FineDilMem m') initU n),
        (forall n, sc_safe tpsc (@diluteMem BareDilMem m') initU n) /\
        (forall tpf' mf' tr,
            fexecution (initU, [::], tpf) (@diluteMem FineDilMem m')
                           ([::], tr, tpf') mf' ->
            exists tpsc' msc' tr',
              sc_execution (initU, [::], tpsc) (@diluteMem BareDilMem m')
                           ([::], tr', tpsc') msc' /\
              threadPool_erasure tpf' tpsc' /\ mem_erasure mf' msc' /\
              trace_erasure tr tr').
    Proof with eauto.
      intros.
      assert (HpoolErase := init_erasure HinitSC HinitF).
      assert (HmemErase : mem_erasure (@diluteMem FineDilMem m') (@diluteMem BareDilMem m')).
      { eapply mem_erasure_dilute_1.
        econstructor; eauto.
        intros.
        assert (Hvalid: Mem.valid_block m' b)
          by (unfold Mem.valid_block, diluteMem, erasePerm in *;
              simpl in *; auto).
        assert (Hperm:= erasePerm_V ofs k Hvalid).
        unfold permission_at in Hperm; auto.
        simpl.
        intros.
        eapply memval_erasure_refl.
      }
      split; first by (intros n; eapply fsafe_implies_scsafe; eauto).
      intros.
      eapply execution_sim with (trsc := [::]) in H; eauto.
      destruct H as (? & ? & ? & ?& ?& ? & Htrace_erasure).
      specialize (Htrace_erasure ltac:(by constructor)).
      do 3 eexists; split...
    Qed.

    Corollary init_fsafe_implies_scsafe:
      forall f arg tpsc tpf m m'
        (HinitSC: bare_init initU m (initU, [::], tpsc) m' f arg)
        (HinitF: tpf_init initU m (initU, [::], tpf) m' f arg)
        (HsafeF: forall n, fsafe tpf (@diluteMem FineDilMem m') initU n),
        forall n, sc_safe tpsc (@diluteMem BareDilMem m') initU n.
    Proof.
      intros.
      exploit sc_erasure; eauto.
      intros (? & ?).
      now eauto.
    Qed.

  End SCErasure.
End SCErasure.




