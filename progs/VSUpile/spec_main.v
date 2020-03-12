Require Import VST.floyd.proofauto.
 
Require Import spec_stdlib.
Require Import pile.
Require Import spec_onepile.
Require Import spec_apile.
Require Import triang.
Require Import main.

Local Open Scope assert.
(*
Section MainbodyASI.

Variable ONEPILE: OnePilePredicates.
Variable APILE: APilePredicates.
(*Variable TriangPred: TriangPredicates - TraingPredicates is empty*)
(*Note that we don't declare a Variable PILE:PilePredicates here*)

(*A spec of the (private) function mainbody.*)
Definition mainbody_spec :=
 DECLARE _mainbody
 WITH gv: globals
 PRE [ ] 
    PROP() PARAMS () GLOBALS (gv) 
    SEP(onepile ONEPILE gv None; apile APILE gv nil; mem_mgr gv)
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).
Locate _mainbody.
Definition MainBodyASI:funspecs := [ mainbody_spec].

End MainbodyASI.
*)
Definition linked_prog : Clight.program :=
 ltac: (linking.link_progs_list [
   stdlib.prog; pile.prog; onepile.prog; apile.prog;
   triang.prog; main.prog]).

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre linked_prog tt gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).
(*Refine postcondition to ...   SEP(spec_stdlib.mem_mgr gv; has_ext tt).?*)


