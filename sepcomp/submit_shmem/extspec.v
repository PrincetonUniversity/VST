Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.

Require Import ListSet.

(** External function specifications and linking *)

Structure external_specification (M E Z : Type) :=
  { ext_spec_type : E -> Type
  ; ext_spec_pre: forall e: E,
    ext_spec_type e -> list typ -> list val -> Z -> M -> Prop
  ; ext_spec_post: forall e: E,
    ext_spec_type e -> option typ -> option val -> Z -> M ->  Prop
  ; ext_spec_exit: option val -> Z -> M ->  Prop }.

Arguments ext_spec_type {M E Z} _ _.
Arguments ext_spec_pre {M E Z} _ _ _ _ _ _ _.
Arguments ext_spec_post {M E Z} _ _ _ _ _ _ _.
Arguments ext_spec_exit {M E Z} _ _ _ _.

Definition ext_spec := external_specification mem external_function.

Lemma extfunct_eqdec (ef1 ef2 : external_function) : {ef1=ef2} + {~ef1=ef2}.
Proof.
repeat decide equality; try apply Integers.Int.eq_dec.
apply Floats.Float.eq_dec.
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
    | Some v', Some tv' => val_inject j v' tv'
    | _, _ => False
  end.

Module ExtSpecProperties.

Definition det (M E Z : Type) (spec : external_specification M E Z) :=
  forall ef (x x' : ext_spec_type spec ef) tys z vals m
         oty' ov' z' m' oty'' ov'' z'' m'',
  ext_spec_pre spec ef x tys vals z m ->
  ext_spec_post spec ef x oty' ov' z' m' ->
  ext_spec_pre spec ef x' tys vals z m ->
  ext_spec_post spec ef x' oty'' ov'' z'' m'' ->
  oty'=oty'' /\ ov'=ov'' /\ z'=z'' /\ m'=m''.

Record closed (Z : Type) (spec : ext_spec Z) :=
  { P_closed :
      forall ef (x : ext_spec_type spec ef) j tys vals z m tvals tm,
      ext_spec_pre spec ef x tys vals z m ->
      val_list_inject j vals tvals ->
      Mem.inject j m tm ->
      ext_spec_pre spec ef x tys tvals z tm
  ; Q_closed :
      forall ef (x : ext_spec_type spec ef) j oty ov z m otv tm,
      ext_spec_post spec ef x oty ov z m ->
      oval_inject j ov otv ->
      Mem.inject j m tm ->
      ext_spec_post spec ef x oty otv z tm
  ; exit_closed :
      forall j ov z m otv tm,
      ext_spec_exit spec ov z m ->
      oval_inject j ov otv ->
      Mem.inject j m tm ->
      ext_spec_exit spec otv z tm }.

End ExtSpecProperties.


