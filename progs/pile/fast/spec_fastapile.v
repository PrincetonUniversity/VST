Require Import VST.floyd.proofauto.
Require Import fastapile.
Require Import spec_stdlib.
Require Import spec_fastpile.
Global Open Scope funspec_scope.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition apile (gv: globals) (sigma: list Z) : mpred :=
  pilerep sigma (gv _a_pile).

Local Open Scope assert.

Definition Apile_add_spec :=
 DECLARE _Apile_add
 WITH n: Z, sigma: list Z, gv: globals
 PRE [ tint  ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (Vint (Int.repr n)) GLOBALS (gv)
    SEP(apile gv sigma; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(apile gv (n::sigma); mem_mgr gv).

Definition sumlist : list Z -> Z := List.fold_right Z.add 0.

Definition Apile_count_spec :=
 DECLARE _Apile_count
 WITH sigma: list Z, gv: globals
 PRE [  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS () GLOBALS (gv)
    SEP(apile gv sigma; mem_mgr gv)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(apile gv sigma; mem_mgr gv).

Definition specs := [Apile_add_spec; Apile_count_spec].

Lemma make_apile: forall gv, 
  headptr (gv fastapile._a_pile) ->
  data_at Ews tuint (Vint (Int.repr 0))
          (gv fastapile._a_pile) |-- apile gv nil.
Proof.
intros. unfold apile, pilerep. 
 Exists 0.
 entailer!.
 unfold_data_at (data_at _ tpile _ _).
 rewrite field_at_data_at. simpl.
 rewrite field_compatible_field_address
   by auto with field_compatible.
 simpl. normalize. rewrite data_at_tuint_tint.
 apply derives_refl.
Qed.
