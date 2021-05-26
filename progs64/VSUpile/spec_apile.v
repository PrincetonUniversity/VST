Require Import VST.floyd.proofauto.
Require Import apile.
Require Import spec_stdlib.
Require Import PileModel.

(*Apile's predicate bundle is similar to the Onepile's bundle.*)
Record APileAPD := {
  apile: list Z -> globals -> mpred
}.

Local Open Scope assert.

Section ApileASI.
Variable M: MallocFreeAPD.
Variable APILE:APileAPD.

Definition Apile_add_spec :=
 DECLARE _Apile_add
 WITH n: Z, sigma: list Z, gv: globals
 PRE [ tint  ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (Vint (Int.repr n)) GLOBALS (gv)
    SEP(apile APILE sigma gv; mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(apile APILE (n::sigma) gv; mem_mgr M gv).

Definition Apile_count_spec :=
 DECLARE _Apile_count
 WITH sigma: list Z, gv: globals
 PRE [  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS () GLOBALS (gv)
    SEP(apile APILE sigma gv; mem_mgr M gv)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(apile APILE sigma gv; mem_mgr M gv).

Definition ApileASI:funspecs := [ Apile_add_spec; Apile_count_spec].

End ApileASI.