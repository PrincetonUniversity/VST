Require Import VST.floyd.proofauto.
Require Import onepile.
Require Import spec_stdlib.
Require Import spec_pile.
Global Open Scope funspec_scope.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Definition onepile (gv: globals) (sigma: option (list Z)) : mpred :=
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
    PROP() PARAMS () GLOBALS (gv) SEP(onepile gv None; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL() SEP(onepile gv (Some nil); mem_mgr gv).

Definition Onepile_add_spec :=
 DECLARE _Onepile_add
 WITH n: Z, sigma: list Z, gv: globals
 PRE [ tint ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (Vint (Int.repr n)) GLOBALS (gv)
    SEP(onepile gv (Some sigma); mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(onepile gv (Some (n::sigma)); mem_mgr gv).

Definition sumlist : list Z -> Z := List.fold_right Z.add 0.

Definition Onepile_count_spec :=
 DECLARE _Onepile_count
 WITH sigma: list Z, gv: globals
 PRE [  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS () GLOBALS (gv)
    SEP(onepile gv (Some sigma))
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(onepile gv (Some sigma)).

Definition specs := [Onepile_init_spec; Onepile_add_spec; Onepile_count_spec].

Lemma make_onepile: forall gv, 
  data_at_ Ews (tptr (Tstruct onepile._pile noattr)) (gv onepile._the_pile)
   |-- onepile gv None.
Proof.
intros.
unfold onepile.
cancel.
Qed.
