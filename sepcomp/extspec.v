Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.

Require Import ListSet.

(** External function specifications and linking *)

Structure external_specification {M E Z:Type} := { 
  ext_spec_type: E -> Type;
  ext_spec_pre: forall e: E, 
    ext_spec_type e -> list typ -> list val -> Z -> M -> Prop;
  ext_spec_post: forall e: E, 
    ext_spec_type e -> option typ -> option val -> Z -> M ->  Prop;
  ext_spec_exit: option val -> Z -> M ->  Prop
}.
Implicit Arguments external_specification [].

Definition ext_spec := external_specification mem external_function.

Lemma extfunct_eqdec : forall ef1 ef2: external_function, {ef1=ef2} + {~ef1=ef2}.
Proof. intros ef1 ef2; repeat decide equality; 
  try apply Integers.Int.eq_dec.
apply Floats.Float.eq_dec.
Defined.

Set Implicit Arguments.

Definition ef_ext_spec (M Z: Type) := external_specification M AST.external_function Z.

Definition spec_of (M Z: Type) (ef: AST.external_function) (Sigma: ef_ext_spec M Z) :=
  (ext_spec_pre Sigma ef, ext_spec_post Sigma ef).

Section LinkExtSpec.
Notation IN := (ListSet.set_mem extfunct_eqdec).
Notation NOTIN := (fun ef l => ListSet.set_mem extfunct_eqdec ef l = false).
Notation DIFF := (ListSet.set_diff extfunct_eqdec).

Lemma in_diff (ef: AST.external_function) (l r: list AST.external_function): 
 IN ef l=true -> NOTIN ef r -> IN ef (DIFF l r)=true.
Proof.
simpl; intros H1 H2; apply set_mem_correct2. 
apply set_mem_correct1 in H1.
apply set_mem_complete1 in H2.
apply set_diff_intro; auto.
Qed.

(** Linking external specification [Sigma] with an extension implementing
   functions in [handled] *)

Definition link_ext_spec (M Z: Type) (handled: AST.external_function -> Prop) 
  (Sigma: external_specification M AST.external_function Z) :=
  Build_external_specification M AST.external_function Z
    (ext_spec_type Sigma)
    (fun (ef: AST.external_function) (x: ext_spec_type Sigma ef)
         (tys: list typ) (args: list val) (z: Z) (m: M) => 
             ~handled ef /\ ext_spec_pre Sigma ef x tys args z m)
    (fun (ef: AST.external_function) (x: ext_spec_type Sigma ef)
         (ty: option typ) (ret: option val) (z: Z) (m: M) => 
             handled ef \/ ext_spec_post Sigma ef x ty ret z m)
    (ext_spec_exit Sigma).

(** A client signature is linkable with an extension signature when each
   extension function specification ef:{P}{Q} is a subtype of the
   specification ef:{P'}{Q'} assumed by client. *)

Definition linkable (M Z Zext: Type) (proj_zext: Z -> Zext)
      (handled: AST.external_function -> Prop) 
      (csig: ef_ext_spec M Z) (ext_sig: ef_ext_spec M Zext) := 
  (forall ef P Q P' Q', 
    ~handled ef -> 
    spec_of ef ext_sig = (P, Q) -> 
    spec_of ef csig = (P', Q') -> 
    forall x' tys args m z, P' x' tys args z m -> 
      exists x, P x tys args (proj_zext z) m /\
      forall ty ret m' z', Q x ty ret (proj_zext z') m' -> Q' x' ty ret z' m') /\
  (forall ret z m,
    ext_spec_exit ext_sig ret (proj_zext z) m -> 
    ext_spec_exit csig ret z m).

End LinkExtSpec.

