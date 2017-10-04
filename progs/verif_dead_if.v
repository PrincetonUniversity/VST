Require Import VST.floyd.proofauto.
Require Import VST.progs.dead_if.
Require Import VST.floyd.deadvars.

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

Definition g_spec :=
 DECLARE _g
  WITH x : Z, y: Z, z: Z
  PRE  [_x OF tint, _y OF tint, _z OF tint]
    PROP ( ) LOCAL (temp _x (Vint (Int.repr x)); 
                    temp _y (Vint (Int.repr y)); temp _z (Vint (Int.repr z)))
    SEP()
  POST [ tint ] PROP() LOCAL() SEP().

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs :=   ltac:(with_library prog [g_spec]).

Lemma body_f:  semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
deadvars.  (* nothing dead here *)
do 3 forward.
deadvars.  (* dead *)
forward.
deadvars.  (* nothing dead here *)
forward_if (EX i:_, EX j:_, PROP ( )
   LOCAL (temp _c (Vint (Int.repr i)); temp _b (Vint (Int.repr j)))  SEP ()).
deadvars.   (* dead *)
forward.
rewrite add_repr.
Exists 0 (x+y).
entailer!.
deadvars.  (* dead *)
forward.
forward.
Exists z x.
entailer!.
Intros i j.
forward.
Qed.

Lemma body_g:  semax_body Vprog Gprog f_g g_spec.
Proof.
start_function.
deadvars.  (* dead vars! *)
do 3 forward.
deadvars.  (* dead vars! *)
forward.
normalize.
deadvars.  (* nothing dead here *)
forward_while (EX i:_,
   PROP() LOCAL (temp _a (Vint (Int.repr (x+1))); temp _x (Vint (Int.repr x));
              temp _c (Vint (Int.repr 0)); temp _b (Vint (Int.repr i)))  SEP ()).
* Exists 1. entailer!.
* entailer!.
*
deadvars.   (* dead vars! *)
forward.
Exists x. entailer!.
*
deadvars. (* dead vars! *)
forward.
Qed.

    
