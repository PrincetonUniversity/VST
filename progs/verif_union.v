Require Import VST.floyd.proofauto.
Require Import VST.progs.union.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Module Single.

Definition fabs_single_spec :=
 DECLARE _fabs_single
 WITH x: float32
 PRE [ _x OF Tfloat F32 noattr]
   PROP() LOCAL(temp _x (Vsingle x)) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() LOCAL (temp ret_temp (Vsingle (Float32.abs x))) SEP().

Definition Gprog : funspecs :=
    ltac:(with_library prog [ fabs_single_spec ]).


Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
start_function.
forward.
forward.
Abort.

End Single.

Module Float.

Definition fabs_single_spec :=
 DECLARE _fabs_single
 WITH x: float
 PRE [ _x OF Tfloat F32 noattr]
   PROP() LOCAL(temp _x (Vfloat x)) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() LOCAL (temp ret_temp (Vfloat (Float.abs x))) SEP().

Definition Gprog : funspecs :=
    ltac:(with_library prog [ fabs_single_spec ]).

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
try (start_function; fail 99).
Abort.

End Float.

(*

Lemma union_conversion:
forall {CS} u sh p (i1 i2: ident) (t1 t2: type),
  match PTree.get u (@cenv_cs CS) with
  | Some {| co_su := Union; 
            co_members := [(i1', t1'); (i2', t2')];
            co_sizeof := 4;
            co_rank := 0;
         |}  => i1'=i1 /\ i2'=i2 /\ t1'=t1 /\ t2'=t2
  | _ => False
  end ->
  i1 <> i2 ->
  forall (x y: val) 
        (v1 v2: reptype (nested_field_type (Tunion u noattr) [])),
  JMeq v1 (@inl val val x) ->
  JMeq v2 (@inr val val y) ->
  (forall bl, 
    Memdata.decode_val (chunk_of_type (typ_of_type t1)) bl = x <->
    Memdata.decode_val (chunk_of_type (typ_of_type t2)) bl = y) ->
  @field_at CS sh (Tunion u noattr) [] v1 p =
  @field_at CS sh (Tunion u noattr) [] v2 p.
Admitted.

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
start_function.
forward.
clear.
pose proof (union_conversion __125 Tsh v_u _f _i tfloat tuint).
simpl in H.
spec H; auto.
spec H. compute; clear; congruence.
evar (y: int).
assert (reptype (Tunion __125 noattr) = (val+val)%type).
reflexivity.

*)
