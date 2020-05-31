Require Import VST.floyd.proofauto.
Require Import apile.
Require Import simple_spec_stdlib.
Require Import simple_spec_pile.
Require Import PileModel.

Instance APileCompSpecs : compspecs. make_compspecs prog. Defined.

Definition apile (sigma: list Z) (gv: globals): mpred :=
  !!(headptr (gv _a_pile)) && pilerep sigma (gv _a_pile).

Local Open Scope assert.

Definition Apile_add_spec :=
 DECLARE _Apile_add
 WITH n: Z, sigma: list Z, gv: globals
 PRE [ tint  ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (Vint (Int.repr n)) GLOBALS (gv)
    SEP(apile sigma gv; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(apile (n::sigma) gv; mem_mgr gv).

Definition Apile_count_spec :=
 DECLARE _Apile_count
 WITH sigma: list Z, gv: globals
 PRE [  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS () GLOBALS (gv)
    SEP(apile sigma gv; mem_mgr gv)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(apile sigma gv; mem_mgr gv).

Definition ApileASI:funspecs := [ Apile_add_spec; Apile_count_spec].
