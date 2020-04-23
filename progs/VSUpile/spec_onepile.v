Require Import VST.floyd.proofauto.
Require Import onepile.
Require Import spec_stdlib.
Require Import PileModel.

Record OnePileAPD := {
  onepile: option (list Z) -> globals -> mpred(*;
  OnePileCompSpecs: compspecs;
  make_onepile: forall gv, @data_at_ OnePileCompSpecs Ews (tptr (Tstruct onepile._pile noattr)) (gv onepile._the_pile)
   |-- onepile None gv*)
}.

Local Open Scope assert.

Section OnepileASI.
Variable M: MallocFreeAPD.
Variable ONEPILE:OnePileAPD.
 
Definition Onepile_init_spec :=
 DECLARE _Onepile_init
 WITH gv: globals
 PRE [ ] 
    PROP() PARAMS () GLOBALS (gv) SEP(onepile ONEPILE None gv; mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL() SEP(onepile ONEPILE (Some nil) gv; mem_mgr M gv).

Definition Onepile_add_spec :=
 DECLARE _Onepile_add
 WITH n: Z, sigma: list Z, gv: globals
 PRE [ tint ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (Vint (Int.repr n)) GLOBALS (gv)
    SEP(onepile ONEPILE (Some sigma) gv; mem_mgr M gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(onepile ONEPILE (Some (n::sigma)) gv; mem_mgr M gv).

(*Reuse definition from the model for pile, in spec_pile 
Definition sumlist : list Z -> Z := List.fold_right Z.add 0.*)

Definition Onepile_count_spec :=
 DECLARE _Onepile_count
 WITH sigma: list Z, gv: globals
 PRE [  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS () GLOBALS (gv)
    SEP(onepile ONEPILE (Some sigma) gv)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(onepile ONEPILE (Some sigma) gv).

Definition OnepileASI:funspecs := [ Onepile_init_spec; Onepile_add_spec; Onepile_count_spec].

End OnepileASI.