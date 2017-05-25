Require Import floyd.proofauto.
Require Import floyd.library.
Require Import progs.object.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope Z.
Local Open Scope logic.

Definition object_invariant := list Z -> val -> mpred.

Definition tobject := tptr (Tstruct _object noattr).

Definition reset_spec (instance: object_invariant) :=
  WITH self: val, history: list Z
  PRE [ _self OF tobject]
          PROP ()
          LOCAL (temp _self self)
          SEP (instance history self)
  POST [ tvoid ]
          PROP() LOCAL () SEP(instance nil self).

Definition twiddle_spec (instance: object_invariant) :=
  WITH self: val, i: Z, history: list Z
  PRE [ _self OF tobject, _i OF tint]
          PROP (0 < i)
          LOCAL (temp _self self; temp _i (Vint (Int.repr i)))
          SEP (instance history self)
  POST [ tint ]
      EX v: Z, 
          PROP(2* fold_right Z.add 0 history < v <= 2* fold_right Z.add 0 (i::history))
          LOCAL (temp ret_temp (Vint (Int.repr v))) 
          SEP(instance (i::history) self).

Definition object_methods (instance: object_invariant) (mtable: val) : mpred :=
  EX sh: share, EX reset: val, EX twiddle: val,
  !! readable_share sh && 
  func_ptr' (reset_spec instance) reset *
  func_ptr' (twiddle_spec instance) twiddle *
  data_at sh (Tstruct _methods noattr) (reset,twiddle) mtable.

Lemma object_methods_local_facts: forall instance p,
  object_methods instance p |-- !! isptr p.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle.
entailer!.
Qed.
Hint Resolve object_methods_local_facts : saturate_local.

Definition object_mpred (history: list Z) (self: val) : mpred :=
  EX instance: object_invariant, EX mtable: val, 
       (object_methods instance mtable *
     field_at Tsh (Tstruct _object noattr) [StructField _mtable] mtable self*
     instance history self).

Definition foo_invariant : object_invariant :=
  (fun (history: list Z) p => field_at Tsh (Tstruct _foo_object noattr) 
            [StructField _data] (Vint (Int.repr (2*fold_right Z.add 0 history))) p
      *  malloc_token Tsh (sizeof (Tstruct _foo_object noattr)) p).

Definition foo_reset_spec :=
 DECLARE _foo_reset (reset_spec foo_invariant).

Definition foo_twiddle_spec :=
 DECLARE _foo_twiddle  (twiddle_spec foo_invariant).

Definition make_foo_spec :=
 DECLARE _make_foo
 WITH mtable: val
 PRE [ ]
    PROP () LOCAL (gvar _foo_methods mtable) 
    SEP (object_methods foo_invariant mtable)
 POST [ tobject ]
    EX p: val, PROP () LOCAL (temp ret_temp p) 
     SEP (object_mpred nil p; object_methods foo_invariant mtable).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs :=   ltac:(with_library prog [
    foo_reset_spec; foo_twiddle_spec; make_foo_spec; main_spec]).

Lemma body_foo_reset: semax_body Vprog Gprog f_foo_reset foo_reset_spec.
Proof.
unfold foo_reset_spec, foo_invariant, reset_spec.
start_function.
simpl.
Intros.
forward.
forward.
Qed.

Lemma body_foo_twiddle: semax_body Vprog Gprog f_foo_twiddle foo_twiddle_spec.
Proof.
unfold foo_twiddle_spec, foo_invariant, twiddle_spec.
start_function.
simpl.
Intros.
forward.
forward.
forward.
Exists (2 * fold_right Z.add 0 history + i).
entailer!.
replace (2 * (i + fold_right Z.add 0 history))%Z with (2* fold_right Z.add 0 history + 2 * i).
entailer!.
omega.
Qed.


Lemma split_func_ptr': 
 forall fs p, func_ptr' fs p = func_ptr' fs p * func_ptr' fs p.
Proof.
intros.
unfold func_ptr'.
pose proof (corable_func_ptr fs p).
rewrite  corable_andp_sepcon1 by auto.
rewrite emp_sepcon.
rewrite <- andp_assoc.
f_equal.
apply pred_ext. apply andp_right; auto. apply andp_left2; auto.
Qed.

Lemma split_object_methods:
  forall instance m, 
    object_methods instance m |-- object_methods instance m * object_methods instance m.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle.
Exists (fst (Share.split sh)) reset twiddle.
Exists (snd (Share.split sh)) reset twiddle.
rewrite (split_func_ptr' (reset_spec instance) reset) at 1.
rewrite (split_func_ptr' (twiddle_spec instance) twiddle) at 1.
entailer!.
split.
apply slice.split_YES_ok1; auto.
apply slice.split_YES_ok2; auto.
rewrite (data_at_share_join (fst (Share.split sh)) (snd (Share.split sh)) sh).
auto.
apply split_join.
destruct (Share.split sh) as [a b]; reflexivity.
Qed.

Lemma body_make_foo: semax_body Vprog Gprog f_make_foo make_foo_spec.
Proof.
unfold make_foo_spec.
start_function.
forward_call (sizeof (Tstruct _foo_object noattr)).
(* TODO:  If the user omits "Import floyd.library", then the error message
    at forward call gives a hard-to-understand error message 
    about witness types. *)
simpl. computable.
Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p; gvar _foo_methods mtable)
   SEP (malloc_token Tsh (sizeof (Tstruct _foo_object noattr)) p;
          memory_block Tsh (sizeof (Tstruct _foo_object noattr)) p;
          object_methods foo_invariant mtable)).
change (Memory.EqDec_val p nullval) with (eq_dec p nullval).
*
if_tac; entailer.
*
forward_call tt.
contradiction.
*
rewrite if_false by (intro; subst; inv H).
Intros.
forward.
entailer!.
*
assert_PROP (field_compatible (Tstruct _foo_object noattr) [] p).
entailer!.
rewrite memory_block_data_at_; auto.
unfold data_at_.
unfold field_at_.
simpl.
unfold default_val; simpl.
forward.
forward.
forward.
Exists p.
unfold object_mpred.
Exists foo_invariant mtable.
sep_apply (split_object_methods foo_invariant mtable).
unfold foo_invariant.
entailer!.
simpl.
unfold_field_at 1%nat.
cancel.
rewrite !field_at_data_at.
simpl.
apply derives_refl'.
f_equal.
rewrite !field_compatible_field_address; auto with field_compatible.
destruct H as [? [? [? [? [? [? [? ?]]]]]]].
repeat split; auto.
hnf in H7|-*. destruct p; auto; simpl in H7|-*; omega.
hnf in H8|-*. destruct p; auto; simpl in H8|-*; omega.
Qed.

Lemma prove_foo_mtable: 
  forall Delta twiddle reset mtable, 
  Delta = func_tycontext f_main Vprog Gprog ->
ENTAIL Delta,
PROP ( )
LOCAL (gvar _foo_twiddle twiddle; gvar _foo_reset reset;
gvar _foo_methods mtable)
SEP (func_ptr' (reset_spec foo_invariant) reset;
      func_ptr' (twiddle_spec foo_invariant) twiddle;
     mapsto Ews
       (Tpointer
          (Tfunction
             (Tcons (Tpointer (Tstruct 1%positive noattr) noattr)
                (Tcons (Tint I32 Signed noattr) Tnil))
             (Tint I32 Signed noattr) cc_default) noattr)
       (offset_val 4 mtable) (offset_val 0 twiddle);
mapsto Ews
  (Tpointer
     (Tfunction (Tcons (Tpointer (Tstruct 1%positive noattr) noattr) Tnil)
        Tvoid cc_default) noattr) (offset_val 0 mtable) (offset_val 0 reset))
|-- PROP ( )
    LOCAL (gvar _foo_methods mtable)  SEP (object_methods foo_invariant mtable).
Proof.
intros.
unfold object_methods.
Exists Ews reset twiddle.
unfold_data_at 1%nat.
subst.

simplify_func_tycontext.
assert_PROP (field_compatible (Tstruct _methods noattr) [StructField _reset] mtable). {
  entailer!.
  split3; auto.
  split3; auto.
  split3; auto.
  simpl; computable.
  repeat split; auto.
  left; auto.
}
assert_PROP (field_compatible (Tstruct _methods noattr) [StructField _twiddle] mtable). {
  entailer!.
  split3; auto.
  split3; auto.
  split3; auto.
  simpl; computable.
  repeat split; auto.
  right; left; auto.
}
entailer!.
rewrite sepcon_comm.
apply sepcon_derives.
rewrite <- mapsto_field_at with (v:=reset); auto.
rewrite field_compatible_field_address by auto.
simpl.
rewrite isptr_offset_val_zero; auto.
rewrite <- mapsto_field_at with (v:=twiddle); auto.
rewrite field_compatible_field_address by auto.
simpl.
apply derives_refl.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
rename gvar2 into twiddle; rename gvar1 into reset; rename gvar0 into mtable.
fold noattr. fold cc_default.
make_func_ptr _foo_twiddle.
make_func_ptr _foo_reset.
eapply semax_pre; [apply prove_foo_mtable; reflexivity | ].
(* TODO:  If the funspec does not have a (LOCAL (temp ret_temp x)) in the postcondition,
     then forward_call just freezes. *)
fwd_call mtable.
Intros p.
(* drop_LOCALs [_foo_methods].  This is permitted if we don't intend to create any more foo objects *)

(* first method-call *)
unfold object_mpred.
Intros instance mtable0.
forward.
unfold object_methods at 1.
Intros sh r0 t0.
forward.
forward_call (p, @nil Z).
gather_SEP 1 2 3.
replace_SEP 0 (object_methods instance mtable0).
unfold object_methods.
entailer!. Exists sh r0 t0. entailer!.
gather_SEP 0 1 2.
replace_SEP 0 (object_mpred nil p).
unfold object_mpred; entailer!. Exists instance mtable0; entailer!.
drop_LOCALs [_p_reset; _mtable]. clear sh H r0 t0 mtable0 instance.

(* second method-call *)
unfold object_mpred.
Intros instance mtable0.
forward.
unfold object_methods at 1.
Intros sh r0 t0.
forward.
forward_call (p, 3, @nil Z).
computable.
Intros i.
gather_SEP 1 2 3.
replace_SEP 0 (object_methods instance mtable0).
unfold object_methods.
entailer!. Exists sh r0 t0. entailer!.
gather_SEP 0 1 2.
replace_SEP 0 (object_mpred [3] p).
unfold object_mpred; entailer!. Exists instance mtable0; entailer!.
drop_LOCALs [_p_twiddle; _mtable]. clear sh H r0 t0 mtable0 instance.

(* return *)
forward.
Qed.






