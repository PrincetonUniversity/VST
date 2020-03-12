Require Import VST.floyd.proofauto.
Require Import apile.
Require Import spec_stdlib.
Require Import spec_fastpile.

(*Apile's predicate bundle is similar to the Onepile's bundle.*)
Record APilePredicates := {
  apile: globals -> list Z -> mpred;
  APileCompSpecs: compspecs;
  make_apile: forall gv, headptr (gv apile._a_pile) ->
    @data_at APileCompSpecs Ews tuint (Vint (Int.repr 0))
          (gv _a_pile) |-- apile gv nil
}.

Local Open Scope assert.

Section ApileASI.
Variable M: MemMGRPredicates.
Variable APILE:APilePredicates.

Definition Apile_add_spec :=
 DECLARE _Apile_add
 WITH n: Z, sigma: list Z, gv: globals
 PRE [ tint  ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (Vint (Int.repr n)) GLOBALS (gv)
    SEP(apile APILE gv sigma; mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(apile APILE gv (n::sigma); mem_mgr M gv).

Definition Apile_count_spec :=
 DECLARE _Apile_count
 WITH sigma: list Z, gv: globals
 PRE [  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS () GLOBALS (gv)
    SEP(apile APILE gv sigma; mem_mgr M gv)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(apile APILE gv sigma; mem_mgr M gv).

Definition ApileASI:funspecs := [ Apile_add_spec; Apile_count_spec].

End ApileASI.