Require Import VST.floyd.proofauto.
Require Import VST.progs.union.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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
start_function.
forward.
(* in this step there's a soundness bug. *) forward.
forward.
forward.
forward.
Qed.

