(** ** Erasure from FineConc to a non-angelic SC machine*)

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
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.memory_lemmas.
Require Import concurrency.dry_context.
Require Import concurrency.fineConc_safe.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

(** ** Erasure of Values*)
Module ValErasure.

  Definition val_erasure v1 v2 : Prop :=
    match v1, v2 with
    | Vundef, _ => True
    | v1, v2 => v1 = v2
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

  Lemma val_erasure_list_decode:
    forall vals vals' typs,
      val_erasure_list vals vals' ->
      val_erasure_list (decode_longs typs vals) (decode_longs typs vals').
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
  Qed.

  Lemma memval_erasure_list_refl:
    forall vs, memval_erasure_list vs vs.
  Proof with eauto with val_erasure.
    induction vs; simpl...
  Qed.

  Hint Immediate memval_erasure_list_refl : val_erasure.

  (** ** Lemmas about erased values*)

  Definition isPointer (v : val) :=
    match v with
    | Vptr _ _ => true
    | _ => false
    end.

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
    inv H; inv H0; simpl; auto.
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
    inv H; inv H0; simpl; auto.
    destruct (eq_block b b0); simpl; auto.
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
       val_erasure_divfs val_erasure_negfs val_erasure_absfs : val_erasure.

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
  
  Inductive event_erasure : Events.machine_event -> Events.machine_event -> Prop :=
  | InternalErasure: forall tid mev mev',
      mem_event_erasure mev mev' ->
      event_erasure (Events.internal tid mev) (Events.internal tid mev')
  | ExternalErasure: forall tid ev,
      event_erasure (Events.external tid ev) (Events.external tid ev).

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
    forall m1 m2 b,
      mem_erasure m1 m2 ->
      forall n ofs,
        Mem.range_perm m1 b ofs (ofs + Z_of_nat n) Cur Readable ->
        memval_erasure_list
                     (Mem.getN n ofs (m1.(Mem.mem_contents)#b))
                     (Mem.getN n ofs (m2.(Mem.mem_contents)#b)).
  Proof.
    induction n; intros; simpl.
    constructor.
    rewrite inj_S in H0.
    destruct H.
    constructor.
    eapply erased_contents0; eauto.
    apply IHn. red; intros; apply H0; omega.
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
    destruct (proj_bytes vl1) as [bl1|] eqn:PB1.
    exploit proj_bytes_erasure; eauto. intros PB2. rewrite PB2.
    destruct chunk; simpl; auto.
    assert (A: forall q fn,
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
    destruct chunk; simpl; eauto.
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
    rewrite <- size_chunk_conv.
    exploit Mem.load_valid_access; eauto. 
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
    eapply mem_erasure_valid_pointer_guard in Heqb2; eauto.
    congruence.
    eapply mem_erasure_valid_pointer_guard in Heqb2; eauto.
    congruence.
    subst.
    apply andb_false_iff in Heqb2.
    destruct Heqb2 as [Heqb2 | Heqb2];
      eapply mem_erasure_valid_pointer_guard in Heqb2; eauto;
      congruence.
    apply andb_false_iff in Heqb2.
    eapply mem_erasure_valid_pointer in Heqb1; eauto.
    eapply mem_erasure_valid_pointer in Heqb0; eauto.
    destruct Heqb2 as [Heqb2 | Heqb2];
      congruence.
  Qed.

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
    destruct (zle 0 sz). rewrite nat_of_Z_eq; auto. omega.
    rewrite nat_of_Z_neg. simpl. red; intros; omegaContradiction. omega.
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
  
End MemErasure.

(** Erasure of cores *)
Module Type CoreErasure (SEM: Semantics).
  Import SEM ValErasure MemErasure TraceErasure event_semantics.
  
  Parameter core_erasure : C -> C -> Prop.
  Parameter core_erasure_refl: forall c, core_erasure c c.

  Parameter at_external_erase:
    forall c c' (Herase: core_erasure c c'),
      match at_external Sem c, at_external Sem c' with
      | Some (ef, sig, vs), Some (ef', sig', vs') =>
        ef = ef' /\ sig = sig' /\ val_erasure_list vs vs'
      | None, None => True
      | _, _ => False
      end.

  Parameter after_external_erase:
    forall v v' c c' c2
      (HeraseCores: core_erasure c c')
      (HeraseVal: val_erasure v v')
      (Hafter_external: after_external SEM.Sem (Some v) c = Some c2),
    exists c2',
      after_external SEM.Sem (Some v') c' = Some c2' /\
      core_erasure c2 c2'.
  
  Parameter erasure_initial_core:
    forall ge v arg v' arg' c
      (Hv: val_erasure v v')
      (Harg: val_erasure arg arg')
      (Hinit: initial_core Sem ge v [:: arg] = Some c),
      initial_core Sem ge v' [:: arg'] = Some c.
  
  Parameter halted_erase:
    forall c c'
      (HeraseCores: core_erasure c c')
      (Hhalted: halted SEM.Sem c),
      halted SEM.Sem c'.

  Parameter evstep_erase:
    forall ge c1 c1' c2 ev m1 m1' m2
      (HeraseCores: core_erasure c1 c1')
      (Hmem_erasure: mem_erasure m1 m1')
      (Hstep: ev_step Sem ge c1 m1 ev c2 m2),
    exists c2' m2' ev',
      ev_step Sem ge c1' m1' ev' c2' m2' /\
      core_erasure c2 c2' /\ mem_erasure m2 (erasePerm m2') /\
      mem_event_list_erasure ev ev'.

  Hint Resolve core_erasure_refl : erased.
  
End CoreErasure.

Module ThreadPoolErasure (SEM: Semantics)
       (Machines: MachinesSig with Module SEM := SEM)
       (CE : CoreErasure SEM).
  Import ValErasure CE
         Machines DryMachine ThreadPool.
  
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

  Inductive threadPool_erasure tp (tp' : ErasedMachine.ThreadPool.t) :=
  | ErasedPool :
      num_threads tp = ErasedMachine.ThreadPool.num_threads tp' ->
      (forall i (cnti: containsThread tp i)
         (cnti': ErasedMachine.ThreadPool.containsThread tp' i),
          ctl_erasure (getThreadC cnti)
                    (ErasedMachine.ThreadPool.getThreadC cnti')) ->
      threadPool_erasure tp tp'.

  Lemma erasedPool_contains:
    forall tp1 tp1' 
      (HerasedPool: threadPool_erasure tp1 tp1') i,
      containsThread tp1 i <-> ErasedMachine.ThreadPool.containsThread tp1' i.
  Proof.
    intros.
    inversion HerasedPool.
    unfold containsThread, ErasedMachine.ThreadPool.containsThread.
    rewrite H.
    split; auto.
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
                        (ErasedMachine.ThreadPool.updLockSet tp' addr' rmap').
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.
  
  Lemma erased_updThread:
    forall tp tp' i (cnti: containsThread tp i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp' i) c c' pmap pmap',
      threadPool_erasure tp tp' ->
      ctl_erasure c c' ->
      threadPool_erasure (updThread cnti c pmap)
                        (ErasedMachine.ThreadPool.updThread cnti' c' pmap').
  Proof.
    intros.
    inversion H.
    constructor; auto.
    intros.
    destruct (i0 == i) eqn:Heq; move/eqP:Heq=>Heq.
    subst. rewrite gssThreadCode.
    rewrite ErasedMachine.ThreadPool.gssThreadCode; auto.
    rewrite gsoThreadCode; auto.
    rewrite ErasedMachine.ThreadPool.gsoThreadCode; auto.
  Qed.

  Lemma erased_addThread:
    forall tp tp' i (cnti: containsThread tp i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp' i) v arg v' arg' pmap pmap',
      threadPool_erasure tp tp' ->
      val_erasure v v' ->
      val_erasure arg arg' ->
      threadPool_erasure (addThread tp v arg pmap)
                        (ErasedMachine.ThreadPool.addThread tp' v arg pmap').
  Proof with eauto with val_erasure erased.
    intros.
    inversion H.
    constructor.
    unfold addThread, ErasedMachine.ThreadPool.addThread; simpl. rewrite H2; auto.
    intros.
    assert (cnti00 := cntAdd' _ _ _  cnti0).
    assert (cnti0'0 := ErasedMachine.ThreadPool.cntAdd' _ _ _  cnti'0).
    destruct cnti00 as [[cnti00 ?] | Heq];
      destruct cnti0'0 as [[cnti0'0 ?] | ?].
    - erewrite gsoAddCode with (cntj := cnti00) by eauto.
      erewrite ErasedMachine.ThreadPool.gsoAddCode with (cntj := cnti0'0) by eauto.
      eauto.
    - exfalso; subst; apply H4.
      destruct (num_threads tp), (ErasedMachine.ThreadPool.num_threads tp');
        simpl; inversion H2; auto.
    - exfalso; subst; apply H4.
      destruct (num_threads tp), (ErasedMachine.ThreadPool.num_threads tp');
        simpl; inversion H2; auto.
    - subst. erewrite gssAddCode by eauto.
      erewrite ErasedMachine.ThreadPool.gssAddCode; eauto.
      simpl...
  Qed.
  
  Lemma erased_remLockSet:
    forall tp tp' addr addr',
      threadPool_erasure tp tp' ->
      threadPool_erasure (remLockSet tp addr)
                        (ErasedMachine.ThreadPool.remLockSet tp' addr').
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.

  Hint Resolve erased_updLockSet erased_updThread
       erased_addThread erased_remLockSet: erased.

End ThreadPoolErasure.
  
(** ** Erasure from FineConc to SC*)
Module SCErasure (SEM: Semantics)
       (Machines: MachinesSig with Module SEM := SEM)
       (AsmContext: AsmContext SEM Machines)
       (CE : CoreErasure SEM).
  Module ThreadPoolErasure := ThreadPoolErasure SEM Machines CE.
  Import ValErasure MemErasure TraceErasure CE ThreadPoolErasure.
  Import Machines DryMachine ThreadPool AsmContext.

  Import event_semantics.
  (** ** Simulation for syncStep, startStep, resumeStep, suspendStep,
  and haltedStep *)
  
  Lemma syncStep_erase:
    forall ge tp1 tp1' m1 m1' tp2 m2 i ev
      (HerasePool: threadPool_erasure tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hmem_erasure: mem_erasure m1 m1')
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': ErasedMachine.mem_compatible tp1' m1')
      (Hstep: syncStep ge cnti Hcomp1 tp2 m2 ev),
    exists tp2' m2',
      ErasedMachine.syncStep ge cnti' Hcomp1' tp2' m2' ev /\
      threadPool_erasure tp2 tp2' /\ mem_erasure m2 m2'.
  Proof with eauto with val_erasure erased.
    intros.
    Hint Resolve mem_erasure_restr : erased.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').      
    inversion Hstep; subst;
    match goal with
    | [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
      rewrite H1 in H; simpl in H;
      destruct Expr2 eqn:?
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
    | [H: at_external _ _ = _, H1: core_erasure _ _ |- _] =>
      pose proof (at_external_erase H1);
        match goal with
        | [H2: match at_external _ _ with _ => _ end |- _] =>
          rewrite H in H2;
            match goal with
            | [H3: match at_external ?E1 ?E2 with _ => _ end |- _] =>
              destruct (at_external E1 E2) as [[[? ?] ?]|] eqn:?; try by exfalso
            end
        end
    end;
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [H: val_erasure_list _ _ |- _] =>
             inv H
           | [H: val_erasure (Vptr _ _) _ |- _] => inv H
           | [H:val_erasure (Vint _) _ |- _] => inv H
           end; subst.
    - exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef)), m2'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto.
      intros j cntj cntj'.
      rewrite gLockSetCode.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite ErasedMachine.ThreadPool.gssThreadCC.
        simpl; auto.
      + rewrite gsoThreadCode; auto.
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
        erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool; eauto.
    - exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef)), m2'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto.
      intros j cntj cntj'.
      rewrite gLockSetCode.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite ErasedMachine.ThreadPool.gssThreadCC.
        simpl; auto.
      + rewrite gsoThreadCode; auto.
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
        erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool; eauto.
    - exists (ErasedMachine.ThreadPool.addThread
           (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef))
           (Vptr b ofs) v'0 tt), m1'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto. rewrite Hnum. auto.
      intros j cntj cntj'.
      assert (cntj0 := cntAdd' _ _ _ cntj).
      destruct cntj0 as [[cntj0 ?] | Heq].
      + (* case it's an old thread*)
        erewrite @gsoAddCode with (cntj := cntj0) by eauto.
        assert (cntj00 := cntUpdate' _ _ _ cntj0).
        assert (cntj00': ErasedMachine.ThreadPool.containsThread tp1' j)
          by (unfold containsThread,ErasedMachine.ThreadPool.containsThread;
               rewrite <- Hnum; auto).
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC (Kresume c0 Vundef)
                                                              cnti' cntj00').
        erewrite @ErasedMachine.ThreadPool.gsoAddCode with (cntj := cntj0')
          by eauto.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        * subst.
          rewrite gssThreadCode.
          rewrite ErasedMachine.ThreadPool.gssThreadCC.
          simpl; auto.
        * rewrite gsoThreadCode; auto.
          erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj00')
            by eauto.
          inversion HerasePool; eauto.
      + (*case j is the just added thread *)
        subst.
        erewrite gssAddCode by (unfold latestThread; reflexivity).
        erewrite ErasedMachine.ThreadPool.gssAddCode
          by (unfold ErasedMachine.ThreadPool.latestThread;
               simpl; rewrite Hnum; auto).
        simpl; auto.
    - exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef)), m2'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto.
      intros j cntj cntj'.
      rewrite gLockSetCode.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite ErasedMachine.ThreadPool.gssThreadCC.
        simpl; auto.
      + rewrite gsoThreadCode; auto.
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
        erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool; eauto.
    - exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef)), m1'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto.
      intros j cntj cntj'.
      rewrite gRemLockSetCode.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite ErasedMachine.ThreadPool.gssThreadCC.
        simpl; auto.
      + rewrite gsoThreadCode; auto.
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
        erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool; eauto.
    - exists tp1', m1'.
      split; [econstructor; eauto | split; eauto].
  Qed.

  Global Ltac pf_cleanup :=
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
    forall ge tp1 tp1' tp2 i
      (HerasePool: threadPool_erasure tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hstep: FineConc.start_thread ge cnti tp2),
    exists tp2',
      SC.start_thread ge cnti' tp2' /\
      threadPool_erasure tp2 tp2'.
  Proof.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup;
      match goal with
        [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
        rewrite H1 in H; simpl in H;
        destruct Expr2 eqn:?
      end; try (by exfalso).
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [H: val_erasure_list _ _ |- _] =>
             inv H
           | [H: val_erasure (Vptr _ _) _ |- _] => inv H
           end; subst.
    eapply erasure_initial_core in Hinitial; eauto.
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Krun c_new)).
    split; econstructor; eauto.
    unfold ErasedMachine.invariant; auto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCC.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl. apply core_erasure_refl.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdateC' _ _ cntj).
      erewrite <- @gsoThreadCC with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.

  Lemma resumeStep_erasure:
    forall tp1 tp1' tp2 i
      (HerasePool: threadPool_erasure tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hstep: FineConc.resume_thread cnti tp2),
    exists tp2',
      SC.resume_thread cnti' tp2' /\
      threadPool_erasure tp2 tp2'.
  Proof.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup;
      match goal with
        [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
        rewrite H1 in H; simpl in H;
        destruct Expr2 eqn:?
      end; try (by exfalso).
    destruct Hthreads as [HeraseCores Heq]. subst v.
    pose proof (at_external_erase HeraseCores).
    rewrite Hat_external in H.
    destruct X, p.
    destruct (at_external SEM.Sem c0) eqn:Hat_external'; try by exfalso.
    destruct p as [[? ?] ?].
    destruct H as [? [? ?]]; subst.
    eapply after_external_erase with (v' := Vint Int.zero) in Hafter_external;
      eauto with val_erasure erased.
    destruct Hafter_external as [c2' [Hafter_external' Hcore_erasure']].
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Krun c2')).
    split.
    eapply SC.ResumeThread with (c := c0); simpl in *; eauto.
    unfold ErasedMachine.invariant; auto.
    constructor.
    simpl. auto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCC.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl; eauto.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdateC' _ _ cntj).
      erewrite <- @gsoThreadCC with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.
  
  Lemma suspendStep_erasure:
    forall tp1 tp1' tp2 i
      (HerasePool: threadPool_erasure tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hstep: FineConc.suspend_thread cnti tp2),
    exists tp2',
      SC.suspend_thread cnti' tp2' /\
      threadPool_erasure tp2 tp2'.
  Proof.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup;
      match goal with
        [H: ctl_erasure ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
        rewrite H1 in H; simpl in H;
        destruct Expr2 eqn:?
      end; try (by exfalso).
    pose proof (at_external_erase Hthreads).
    rewrite Hat_external in H.
    destruct X, p.
    destruct (at_external SEM.Sem c0) eqn:Hat_external'; try by exfalso.
    destruct p as [[? ?] ?].
    destruct H as [? [? ?]]; subst.
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kblocked c0)).
    split.
    eapply SC.SuspendThread with (c := c0); simpl in *; eauto.
    unfold ErasedMachine.invariant; auto.
    constructor.
    simpl. auto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCC.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl; eauto.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdateC' _ _ cntj).
      erewrite <- @gsoThreadCC with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.

  Lemma haltStep_erasure:
    forall tp1 tp1' i
      (HerasePool: threadPool_erasure tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hstep: threadHalted cnti),
      ErasedMachine.threadHalted cnti'.
  Proof.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup.
    rewrite Hcode in Hthreads.
    simpl in Hthreads.
    destruct (ErasedMachine.ThreadPool.getThreadC cnti') eqn:?;
             try by exfalso.
    assert (halted SEM.Sem c0)
      by (eapply halted_erase; eauto).
    econstructor; eauto.
  Qed.

  Lemma threadStep_erase:
    forall ge tp1 tp1' m1 m1' tp2 m2 i ev
      (HerasePool: threadPool_erasure tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hmem_erasure: mem_erasure m1 m1')
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': ErasedMachine.mem_compatible tp1' m1')
      (Hstep: threadStep ge cnti Hcomp1 tp2 m2 ev),
    exists tp2' m2' ev',
      ErasedMachine.threadStep ge cnti' Hcomp1' tp2' m2' ev' /\
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
        rewrite H1 in H; simpl in H;
        destruct Expr2 eqn:?
      end; try (by exfalso).
    eapply mem_erasure_restr with (Hlt := Hcomp1 i cnti) in Hmem_erasure.
    eapply evstep_erase in Hcorestep; eauto.
    destruct Hcorestep as (c2' & m2' & ev' & Hevstep' & Hcore_erasure'
                           & Hmem_erasure' & Hev_erasure).
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Krun c2')), m2', ev'.
    split; eauto.
    econstructor; eauto.
    split; eauto.
    constructor; eauto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCode.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl; eauto.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdate' _ _ _ cntj).
      erewrite  @gsoThreadCode with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.

  Notation fstep := (corestep fine_semantics).
  Notation scstep := (corestep sc_semantics).

  (** A step on the FineConc machine can be matched by a step on the
  SC machine producing an erased event *)
  Lemma sc_sim:
    forall ge tp1 tp1' i U tr1 tr1' tr2 m1 m1' tp2 m2
      (HerasePool: threadPool_erasure tp1 tp1')
      (Hmem_erasure: mem_erasure m1 m1')
      (Hfstep: fstep ge (i :: U, tr1, tp1) m1 (U, tr2, tp2) m2),
    exists tp2' m2' tr2',
      scstep ge (i :: U, tr1', tp1') m1' (U, tr2', tp2') m2' /\
      threadPool_erasure tp2 tp2' /\ mem_erasure m2 m2' /\
      (trace_erasure tr1 tr1' -> trace_erasure tr2 tr2').
  Proof with eauto with trace_erasure mem_erasure.
    intros.
    inversion Hfstep; simpl in *; subst;
    inv HschedN;
    try match goal with
        | [H: containsThread _ ?I |- _ ] =>
          assert (ErasedMachine.ThreadPool.containsThread tp1' I)
            by (eapply erasedPool_contains; eauto)
        end;
    assert (Hcomp1' : ErasedMachine.mem_compatible tp1' m1')
      by (unfold ErasedMachine.mem_compatible; auto).
    - assert (Hstep' := startStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1', tr1'.
      split. econstructor 1; simpl; eauto.
      split; eauto.
    - assert (Hstep' := resumeStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1', tr1'.
      split. econstructor 2; simpl; eauto.
      split; eauto.
    - assert (Htstep' := threadStep_erase HerasePool H Hmem_erasure Hcomp1' Htstep).
      destruct Htstep' as (tp2' & m2' & ev' & Htstep' & HerasePool'
                           & Hmem_erasure' & Htr_erasure').
      exists tp2', (erasePerm m2'), (tr1' ++ map [eta Events.internal tid] ev').
      split.
      eapply SC.thread_step; eauto.
      split...
    - assert (Hstep' := suspendStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1', tr1'.
      split. econstructor 4; simpl; eauto.
      split; eauto.
    - assert (Hstep' := syncStep_erase HerasePool H Hmem_erasure Hcomp1' Htstep).
      destruct Hstep' as (tp2' & m2' & Hstep' & HerasePool' & Hmem_erasure').
      exists tp2', m2', (tr1' ++ [:: Events.external tid ev]).
      split.
      eapply SC.sync_step; eauto.
      split...
    - eapply haltStep_erasure with (cnti' := H) in Hhalted; eauto.
      exists tp1', m1', tr1';
        split; eauto.
      econstructor 6; simpl; eauto.
    - assert (~ ErasedMachine.ThreadPool.containsThread tp1' tid).
      { intros Hcontra.
        destruct HerasePool as [Hnum _].
        unfold containsThread, ErasedMachine.ThreadPool.containsThread in *.
        rewrite <- Hnum in Hcontra.
        auto.
      }
      exists tp1', m1',tr1'.
      split.
      econstructor 7; simpl; eauto.
      split; eauto.
  Qed.
  
  Notation sc_safe := (SC.fsafe the_ge).
  Notation fsafe := (FineConc.fsafe the_ge).

  Inductive sc_execution :
    SC.MachState -> mem -> SC.MachState -> mem -> Prop :=
  | refl_sc_exec : forall ms (m : mem),
      SC.halted ms ->
      sc_execution ms m ms m
  | step_sc_trans : forall i U U'
                      (tp tp' tp'': SC.machine_state)
                      (tr tr' tr'': SC.event_trace)
                      (m m' m'' : mem),
      SC.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m' ->
      sc_execution (U, tr', tp') m' (U', tr'', tp'') m'' ->
      sc_execution (i :: U,tr,tp) m (U',tr'',tp'') m''.

  Inductive fine_execution :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | refl_fine_exec : forall ms (m : mem),
      FineConc.halted ms ->
      fine_execution ms m ms m
  | step_fine_trans : forall i U U'
                        (tp tp' tp'': FineConc.machine_state)
                        (tr tr' tr'': FineConc.event_trace)
                        (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      fine_execution (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      fine_execution (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.

  (* TODO: Move this lemma. Maybe definitions above it too*)
  Lemma fstep_trace_irr:
    forall U i tp m tp' m' tr tr'
      (Hstep: FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m'),
    forall tr'', exists ev,
        FineConc.MachStep the_ge (i :: U, tr'', tp) m (U, tr'' ++ ev, tp') m'.
  Proof.
    intros.
    inversion Hstep; subst; simpl in *; subst; inv HschedN; pf_cleanup.
    - exists [::]; erewrite cats0; econstructor; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 2; simpl; eauto.
    - exists (map [eta Events.internal tid] ev); econstructor 3; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 4; simpl; eauto.
    - exists [:: Events.external tid ev]; econstructor 5; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 6; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 7; simpl; eauto.
  Qed.

  Lemma fsafe_execution:
    forall tpf mf U tr,
      fsafe tpf mf U (size U).+1 ->
      exists tpf' mf' tr',
        fine_execution (U, tr, tpf) mf ([::], tr ++ tr', tpf') mf'.
  Proof.
    intros.
    generalize dependent mf.
    generalize dependent tpf.
    generalize dependent tr.
    induction U; intros.
    do 2 eexists. exists [::].
    erewrite cats0.
    econstructor 1; eauto.
    simpl in *.
    inversion H; subst.
    simpl in H0; by exfalso.
    simpl in *.
    assert (exists ev,
               FineConc.MachStep the_ge ((a :: U), tr, tpf) mf
                                 (U, tr ++ ev, tp') m')
      by (eapply fstep_trace_irr; eauto).
    destruct H0 as [ev Hstep].
    specialize (IHU (tr ++ ev) _ _ H2).
    destruct IHU as (tpf'' & mf'' & tr'' & Hexec).
    rewrite <- catA in Hexec.
    exists tpf'', mf'', (ev ++ tr'').
    econstructor 2; eauto.
  Qed.

  (** The initial state of the SC machine is an erasure of the initial
  state of the FineConc machine*)
 Lemma init_erasure:
    forall f arg U tpsc tpf
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf)),
      threadPool_erasure tpf tpsc.
  Proof.
    intros.
    unfold sc_init, tpf_init in *.
    simpl in *. unfold SC.init_machine, FineConc.init_machine in *.
    unfold init_mach, ErasedMachine.init_mach in *.
    simpl in *.
    destruct (initial_core SEM.Sem the_ge f arg); try discriminate.
    destruct init_perm; try discriminate.
    inv HinitSC. inv HinitF.
    unfold initial_machine, ErasedMachine.initial_machine.
    simpl.
    econstructor. simpl; eauto.
    intros. 
    simpl.
    apply core_erasure_refl; auto.
  Qed.

  (** Any execution of the FineConc machine resulting in some trace
    tr' can be matched by an execution of the SC machine with an
    erased trace *)
  Lemma execution_sim:
    forall U U' tpf tpf' mf mf' tpsc msc tr tr' trsc 
      (Hexec: fine_execution (U, tr, tpf) mf (U', tr', tpf') mf')
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
        econstructor...
  Qed.

  (** Safety of the SC machine*)
  Lemma fsafe_implies_scsafe:
    forall sched tpsc tpf mf msc
      (Hsafe: fsafe tpf mf sched (size sched).+1)
      (HerasedPool: threadPool_erasure tpf tpsc)
      (Hmem_erasure: mem_erasure mf msc),
      sc_safe tpsc msc sched (size sched).+1.
  Proof.
    intro sched.
    induction sched as [|i sched]; intros.
    - simpl in *. inversion Hsafe;
        eapply SC.HaltedSafe with (tr := tr);
        simpl; auto.
    - simpl in Hsafe.
      inversion Hsafe; subst.
      simpl in H; by exfalso.
      simpl in *.
      eapply fstep_trace_irr with (tr'' := [::]) in H0.
      destruct H0 as [ev Hstep]. simpl in Hstep.
      eapply sc_sim with (tr1' := [::]) in Hstep; eauto.
      destruct Hstep as (tpsc2' & msc2' & ? & Hstep & HerasedPool'
                         & Hmem_erasure' & ?).
      econstructor 3; eauto.
  Qed.
  
  Theorem sc_erasure:
    forall sched f arg U tpsc tpf m
      (Hmem: init_mem = Some m)
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf))
      (HsafeF: fsafe tpf (DryMachine.diluteMem m) sched (size sched).+1),
      sc_safe tpsc (ErasedMachine.diluteMem m) sched (size sched).+1 /\
      (forall tpf' mf' tr,
          fine_execution (sched, [::], tpf) (DryMachine.diluteMem m)
                         ([::], tr, tpf') mf' ->
          exists tpsc' msc' tr',
            sc_execution (sched, [::], tpsc) (ErasedMachine.diluteMem m)
                         ([::], tr', tpsc') msc' /\
            threadPool_erasure tpf' tpsc' /\ mem_erasure mf' msc' /\
      trace_erasure tr tr').
  Proof with eauto.
    intros.
    assert (HpoolErase := init_erasure _ _ HinitSC HinitF).
    assert (HmemErase : mem_erasure (diluteMem m) (ErasedMachine.diluteMem m)).
    { eapply mem_erasure_dilute_1.
      econstructor; eauto.
      intros.
      assert (Hvalid: Mem.valid_block m b)
        by (unfold Mem.valid_block, ErasedMachine.diluteMem, erasePerm in *;
             simpl in *; auto).
      assert (Hperm:= erasePerm_V ofs k Hvalid).
      unfold permission_at in Hperm; auto.
      simpl.
      intros.
      eapply memval_erasure_refl.
    }
    split; first by (eapply fsafe_implies_scsafe; eauto).
    intros.
    eapply execution_sim with (trsc := [::]) in H; eauto.
    destruct H as (? & ? & ? & ?& ?& ? & Htrace_erasure).
    specialize (Htrace_erasure ltac:(by constructor)).
    do 3 eexists; split... 
  Qed.

End SCErasure.

(*TODO: Move to another file*)
(** ** Spinlock well synchronized*)
(*
(** Competing Events *)

  Definition sameLocation ev1 ev2 :=
    match location ev1, location ev2 with
    | Some (b1, ofs1, size1), Some (b2, ofs2, size2) =>
      b1 = b2 /\ exists ofs, Intv.In ofs (ofs1, (ofs1 + Z.of_nat size1)%Z) /\
                       Intv.In ofs (ofs2, (ofs2 + Z.of_nat size2)%Z)
    | _,_ => False
    end.
  
  Definition competes (ev1 ev2 : machine_event) : Prop :=
    thread_id ev1 <> thread_id ev2 /\
    sameLocation ev1 ev2 /\
    (is_internal ev1 ->
     is_internal ev2 ->
     action ev1 = Some Write \/ action ev2 = Some Write) /\
    (is_external ev1 \/ is_external ev2 ->
     action ev1 = Some Mklock \/ action ev1 = Some Freelock
     \/ action ev2 = Some Mklock \/ action ev2 = Some Freelock).

  (** Spinlock well synchronized*)
  Definition spinlock_synchronized (tr : X86SC.event_trace) :=
    forall i j ev1 ev2,
      i < j ->
      List.nth_error tr i = Some ev1 ->
      List.nth_error tr j = Some ev2 ->
      competes ev1 ev2 ->
      exists u v eu ev,
        i < u < v < j /\
        List.nth_error tr u = Some eu /\
        List.nth_error tr v = Some ev /\
        action eu = Some Release /\ action ev = Some Acquire /\
        location eu = location ev.

  (** Spinlock clean *)
  Definition spinlock_clean (tr : X86SC.event_trace) :=
    forall i j evi evj,
      i < j ->
      List.nth_error tr i = Some evi ->
      List.nth_error tr j = Some evj ->
      action evi = Some Mklock ->
      (~ exists u evu, i < u < j /\ List.nth_error tr u = Some evu /\
                  action evu = Some Freelock /\ location evu = location evi) ->
      sameLocation evj evi ->
      action evj <> Some Write /\ action evj <> Some Read. *)
  



