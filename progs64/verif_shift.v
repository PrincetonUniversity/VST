Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs64.shift.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition shift {X} (l : list X) k :=
  sublist k (Zlength l) l ++ sublist 0 k l.

Definition shift_spec :=
 DECLARE _shift
  WITH sh : share, a : val, s : list Z, n : Z, k : Z
  PRE [ _a OF (tptr tint) , _n OF (tint), _k OF (tint)]
     PROP(writable_share sh)
     LOCAL (temp _a a; temp _n (Vint (Int.repr n)); temp _k (Vint (Int.repr k)))
     SEP (data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
  POST [ tvoid ]
     PROP()
     LOCAL()
     SEP ((data_at sh (tarray tint n) (map Vint (map Int.repr (shift s k))) a)).

Definition Gprog : funspecs :=
        ltac:(with_library prog [shift_spec]).

Lemma shift_body : semax_body Vprog Gprog f_shift shift_spec.
Proof.
  start_function.
  forward_call.