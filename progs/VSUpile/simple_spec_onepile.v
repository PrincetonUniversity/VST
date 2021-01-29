Require Import VST.floyd.proofauto.
Require Import onepile.
Require Import simple_spec_stdlib.
Require Import simple_spec_pile.
Require Import PileModel.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition onepile (sigma: option (list Z)) (gv: globals): mpred :=
 match sigma with
 | None => data_at_ Ews (tptr tpile) (gv _the_pile)
 | Some il => EX p:val, data_at Ews (tptr tpile) p (gv _the_pile) *
                        pilerep il p * pile_freeable p
 end.

Local Open Scope assert.

Definition Onepile_init_spec :=
 DECLARE _Onepile_init
 WITH gv: globals
 PRE [ ] 
    PROP() PARAMS () GLOBALS (gv) SEP(onepile None gv; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL() SEP(onepile (Some nil) gv; mem_mgr gv).

Definition Onepile_add_spec :=
 DECLARE _Onepile_add
 WITH n: Z, sigma: list Z, gv: globals
 PRE [ tint ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (Vint (Int.repr n)) GLOBALS (gv)
    SEP(onepile (Some sigma) gv; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(onepile (Some (n::sigma)) gv; mem_mgr gv).

Definition Onepile_count_spec :=
 DECLARE _Onepile_count
 WITH sigma: list Z, gv: globals
 PRE [  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS () GLOBALS (gv)
    SEP(onepile (Some sigma) gv)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(onepile (Some sigma) gv).

Definition OnepileASI:funspecs := [ Onepile_init_spec; Onepile_add_spec; Onepile_count_spec].
