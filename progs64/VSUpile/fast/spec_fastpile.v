Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.
Require Import PileModel.

Record PileAPD := {
  pilerep: list Z -> val -> mpred;
  pilerep_local_facts: forall sigma p,
    pilerep sigma p |-- !! (isptr p /\ Forall (Z.le 0) sigma);
  pilerep_valid_pointer: forall sigma p,
    pilerep sigma p |-- valid_pointer p;
  pile_freeable (p: val) : mpred (*maybe expose the definition of this as malloc_token? Preferably NOT*)
}.

#[export] Hint Resolve pilerep_local_facts : saturate_local.
#[export] Hint Resolve pilerep_valid_pointer : valid_pointer.

Definition tpile := Tstruct _pile noattr.

Local Open Scope assert.

Section PileASI.
Variable M: MallocFreeAPD.
Variable PILE:PileAPD.

Definition Pile_new_spec :=
 DECLARE _Pile_new
 WITH gv: globals
 PRE [ ] PROP() (PARAMS () GLOBALS (gv) (SEP(mem_mgr M gv)))
 POST[ tptr tpile ]
   EX p: val,
      PROP() LOCAL(temp ret_temp p)
      SEP(pilerep PILE nil p; pile_freeable PILE p; mem_mgr M gv).

Definition Pile_add_spec :=
 DECLARE _Pile_add
 WITH p: val, n: Z, sigma: list Z, gv: globals
 PRE [ tptr tpile, tint  ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (p; Vint (Int.repr n)) GLOBALS (gv)
    SEP(pilerep PILE sigma p; mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(pilerep PILE (n::sigma) p; mem_mgr M gv).

Definition Pile_count_spec :=
 DECLARE _Pile_count
 WITH p: val, sigma: list Z
 PRE [ tptr tpile  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS (p) GLOBALS ()
    SEP (pilerep PILE sigma p)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(pilerep PILE sigma p).

Definition Pile_free_spec :=
 DECLARE _Pile_free
 WITH p: val, sigma: list Z, gv: globals
 PRE [ tptr tpile  ]
    PROP()
    PARAMS (p) (GLOBALS (gv)
    SEP(pilerep PILE sigma p; pile_freeable PILE p; mem_mgr M gv))
 POST[ tvoid ]
     PROP() LOCAL() SEP(mem_mgr M gv).

Definition PileASI:funspecs := [ Pile_new_spec; Pile_add_spec; Pile_count_spec; Pile_free_spec].

End PileASI.
