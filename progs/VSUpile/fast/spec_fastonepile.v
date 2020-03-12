Require Import VST.floyd.proofauto.
Require Import onepile.
Require Import spec_stdlib.
Require Import spec_fastpile.

Record OnePilePredicates := {
  onepile: globals -> option (list Z) -> mpred;
  OnePileCompSpecs: compspecs;
  make_onepile: forall gv, @data_at_ OnePileCompSpecs Ews (tptr (Tstruct onepile._pile noattr)) (gv onepile._the_pile)
   |-- onepile gv None
}.

Local Open Scope assert.

Section OnepileASI.
Variable M: MemMGRPredicates.
Variable ONEPILE:OnePilePredicates.
 
Definition Onepile_init_spec :=
 DECLARE _Onepile_init
 WITH gv: globals
 PRE [ ] 
    PROP() PARAMS () GLOBALS (gv) SEP(onepile ONEPILE gv None; mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL() SEP(onepile ONEPILE gv (Some nil); mem_mgr M gv).

Definition Onepile_add_spec :=
 DECLARE _Onepile_add
 WITH n: Z, sigma: list Z, gv: globals
 PRE [ tint ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (Vint (Int.repr n)) GLOBALS (gv)
    SEP(onepile ONEPILE gv (Some sigma); mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(onepile ONEPILE gv (Some (n::sigma)); mem_mgr M gv).

(*Reuse definition from the model for pile, in spec_pile 
Definition sumlist : list Z -> Z := List.fold_right Z.add 0.*)

Definition Onepile_count_spec :=
 DECLARE _Onepile_count
 WITH sigma: list Z, gv: globals
 PRE [  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS () GLOBALS (gv)
    SEP(onepile ONEPILE gv (Some sigma))
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(onepile ONEPILE gv (Some sigma)).

Definition OnepileASI:funspecs := [ Onepile_init_spec; Onepile_add_spec; Onepile_count_spec].

End OnepileASI.