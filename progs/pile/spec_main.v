Require Import VST.floyd.proofauto.
Require Import main.
Require Import spec_stdlib.
Require Import spec_onepile.
Require Import spec_apile.
Require Import spec_triang.



Definition linked_prog : Clight.program :=
 ltac: (linking.link_progs_list [
   stdlib.prog; pile.prog; onepile.prog; apile.prog;
   triang.prog; main.prog]).

Instance CompSpecs : compspecs. make_compspecs linked_prog. Defined.

Definition Vprog : varspecs. mk_varspecs linked_prog. Defined.

Local Open Scope assert.


Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre linked_prog tt gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).

Definition specs := [main_spec].

