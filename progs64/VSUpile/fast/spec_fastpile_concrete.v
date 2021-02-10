Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.

Record FastpileConcreteAPD:= {
  countrep: Z -> val -> mpred;
  countrep_local_facts: forall s p, countrep s p |-- !! isptr p;
  countrep_valid_pointer: forall s p, countrep s p |-- valid_pointer p;
  count_freeable: val -> mpred
}.
#[export] Hint Resolve countrep_local_facts : saturate_local.
#[export] Hint Resolve countrep_valid_pointer : valid_pointer.

Definition tpile := Tstruct _pile noattr.

Local Open Scope assert.

Section FastpileConcASI.
Variable M: MallocFreeAPD.
Variable FCP: FastpileConcreteAPD.

Definition Pile_new_spec :=
 DECLARE _Pile_new
 WITH gv: globals
 PRE [ ] PROP() PARAMS () GLOBALS (gv) SEP(mem_mgr M gv)
 POST[ tptr tpile ]
   EX p: val,
      PROP() LOCAL(temp ret_temp p)
      SEP(countrep FCP 0 p; count_freeable FCP p; mem_mgr M gv).

Definition Pile_add_spec :=
 DECLARE _Pile_add
 WITH p: val, n: Z, s: Z, gv: globals
 PRE [ tptr tpile, tint ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (p; Vint (Int.repr n)) GLOBALS (gv)
    SEP(countrep FCP s p; mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(countrep FCP (n+s) p; mem_mgr M gv).

Definition Pile_count_spec :=
 DECLARE _Pile_count
 WITH p: val, s: Z
 PRE [ tptr tpile  ]
    PROP()
    PARAMS (p) GLOBALS ()
    SEP(countrep FCP s p)
 POST[ tint ]
   EX s':Z, 
      PROP(s <= Int.max_signed -> s'=s) 
      LOCAL(temp ret_temp (Vint (Int.repr s')))
      SEP(countrep FCP s p).

Definition Pile_free_spec :=
 DECLARE _Pile_free
 WITH p: val, s: Z, gv: globals
 PRE [ tptr tpile  ]
    PROP()
    PARAMS (p) GLOBALS (gv)
    SEP(countrep FCP s p; count_freeable FCP p; mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL() SEP(mem_mgr M gv).

Definition FastpileConcreteASI:funspecs := [ Pile_new_spec; Pile_add_spec; Pile_count_spec; Pile_free_spec].

End FastpileConcASI.

