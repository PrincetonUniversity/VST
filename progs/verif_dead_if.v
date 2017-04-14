Require Import floyd.proofauto.
Require Import progs.dead_if.
Require Import floyd.deadvars.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.

Definition f_spec :=
 DECLARE _f
  WITH x : Z, y: Z, z: Z
  PRE  [_x OF tint, _y OF tint, _z OF tint]
    PROP ( ) LOCAL (temp _x (Vint (Int.repr x)); 
                    temp _y (Vint (Int.repr y)); temp _z (Vint (Int.repr z)))
    SEP()
  POST [ tint ] PROP() LOCAL() SEP().

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs :=   ltac:(with_library prog [f_spec]).

Lemma body_f:  semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
deadvars.
do 3 forward.
deadvars.
forward.
deadvars.
forward_if (EX i:_, EX j:_, PROP ( )
   LOCAL (temp _c (Vint (Int.repr i)); temp _b (Vint (Int.repr j)))  SEP ()).
Time deadvars.
forward.
rewrite add_repr.
Exists 0 (x+y).
entailer!.
deadvars.
forward.
forward.
Exists z x.
entailer!.
Intros i j.
forward.
Qed.

    
