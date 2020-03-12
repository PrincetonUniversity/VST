Require Import VST.floyd.proofauto.

Require Import spec_stdlib.
Require Import fastpile.
Require Import onepile.
Require Import fastapile.
Require Import triang.
Require Import main.

Definition linked_prog : Clight.program :=
 ltac: (linking.link_progs_list [
   stdlib.prog; fastpile.prog; onepile.prog; fastapile.prog;
   triang.prog; main.prog]).

Local Open Scope assert.

Section MainASI.

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre linked_prog tt gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).
(*Refine postcondition to ...   SEP(spec_stdlib.mem_mgr gv; has_ext tt).?*)

Definition MainASI:funspecs := [main_spec].

End MainASI.

