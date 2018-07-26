Require Import Coq.Lists.ListSet.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Maps.

(** External function specifications and linking *)

Definition PTree_injective {A} (t: PTree.t A) : Prop :=
  forall id1 id2 b, t ! id1 = Some b -> t ! id2 = Some b -> id1 = id2.

Definition injective_PTree A := sig (@PTree_injective A).

Structure external_specification (M E Z : Type) :=
  { ext_spec_type : E -> Type
  ; ext_spec_pre: forall e: E,
    ext_spec_type e -> injective_PTree block -> list typ -> list val -> Z -> M -> Prop
  ; ext_spec_post: forall e: E,
    ext_spec_type e -> injective_PTree block -> option typ -> option val -> Z -> M ->  Prop
  ; ext_spec_exit: option val -> Z -> M ->  Prop }.

Arguments ext_spec_type {M E Z} _ _.
Arguments ext_spec_pre {M E Z} _ _ _ _ _ _ _ _.
Arguments ext_spec_post {M E Z} _ _ _ _ _ _ _ _.
Arguments ext_spec_exit {M E Z} _ _ _ _.

Definition ext_spec := external_specification mem external_function.

Lemma extfunct_eqdec (ef1 ef2 : external_function) : {ef1=ef2} + {~ef1=ef2}.
Proof.
repeat decide equality; try apply Integers.Int.eq_dec.
Defined.

Set Implicit Arguments.

Definition ef_ext_spec (M Z : Type) :=
  external_specification M AST.external_function Z.

Definition spec_of
  (M Z : Type) (ef : AST.external_function) (spec : ef_ext_spec M Z) :=
  (ext_spec_pre spec ef, ext_spec_post spec ef).

Definition oval_inject j (v tv : option val) :=
  match v, tv with
    | None, None => True
    | Some v', Some tv' => Val.inject j v' tv'
    | _, _ => False
  end.

Module ExtSpecProperties.

Definition det (M E Z : Type) (spec : external_specification M E Z) :=
  forall ef (x x' : ext_spec_type spec ef) ge tys z vals m
         oty' ov' z' m' oty'' ov'' z'' m'',
  ext_spec_pre spec ef x ge tys vals z m ->
  ext_spec_post spec ef x ge oty' ov' z' m' ->
  ext_spec_pre spec ef x' ge tys vals z m ->
  ext_spec_post spec ef x' ge oty'' ov'' z'' m'' ->
  oty'=oty'' /\ ov'=ov'' /\ z'=z'' /\ m'=m''.

Record closed (Z : Type) (spec : ext_spec Z) :=
  { P_closed :
      forall ef (x : ext_spec_type spec ef) ge j tys vals z m tvals tm,
      ext_spec_pre spec ef x ge tys vals z m ->
      Val.inject_list j vals tvals ->
      Mem.inject j m tm ->
      ext_spec_pre spec ef x ge tys tvals z tm
  ; Q_closed :
      forall ef (x : ext_spec_type spec ef) ge j oty ov z m otv tm,
      ext_spec_post spec ef x ge oty ov z m ->
      oval_inject j ov otv ->
      Mem.inject j m tm ->
      ext_spec_post spec ef x ge oty otv z tm
  ; exit_closed :
      forall j ov z m otv tm,
      ext_spec_exit spec ov z m ->
      oval_inject j ov otv ->
      Mem.inject j m tm ->
      ext_spec_exit spec otv z tm }.

End ExtSpecProperties.
