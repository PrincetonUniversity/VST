Require Import VST.floyd.proofauto.
Require Import main.

Definition main_spec p :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre p tt gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).
(*Refine postcondition to ...   SEP(spec_stdlib.mem_mgr gv; has_ext tt).?*)


