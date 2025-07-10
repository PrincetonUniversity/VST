From VST.typing Require Import programs own array function adequacy.
Require Import VST.floyd.proofauto.

Section mixed.

Context `{!VSTGS OK_ty Σ} {cs : compspecs}.

Program Definition fn_params_pre' {A} fn params fp : @dtfr Σ A -n> (genviron * list val) -d> mpred := λne x,
  PROP () (PARAMSx (params x) (GLOBALSx [] (SEPx [([∗ list] v;'(cty, t) ∈ params x;zip (map snd (fn_params fn)) (fp_atys (fp x)), v ◁ᵥₐₗ| cty | t) ∗ fp_Pa (fp x)]))).
Next Obligation.
Admitted.

Program Definition fn_params_post' {A} fn fp : @dtfr Σ A -n> option val -d> mpred := λne x,
  ∃ v, PROP () (RETURNx v (SEPx [∃ y, opt_ty_own_val (fn_return fn) ((fp x).(fp_fr) y).(fr_rty) v ∗ ((fp x).(fp_fr) y).(fr_R)])).
Next Obligation.
Admitted.

Program Definition fn_params_post_void {A} (fn : function) fp : @dtfr Σ A -n> option val -d> mpred := λne x,
  PROP () RETURN () (SEPx [∃ y, emp ∗ ((fp x).(fp_fr) y).(fr_R)]).
Next Obligation.
Admitted.

Definition funtype_to_funspec A fn params (fp : @dtfr Σ A → function.fn_params) : funspec :=
  mk_funspec (fn_typesig fn) (fn_callconv fn) A (λne _, ⊤) (fn_params_pre' fn params fp) (fn_params_post' fn fp).

Definition funtype_to_funspec_void A fn params (fp : @dtfr Σ A → function.fn_params) : funspec :=
  mk_funspec (fn_typesig fn) (fn_callconv fn) A (λne _, ⊤) (fn_params_pre' fn params fp) (fn_params_post_void fn fp).

End mixed.

Require Import VST.progs64.permute.
Require Import VST.progs64.permute2.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* import this from the example file *)
Lemma permute_defined : exists b, Genv.find_symbol (globalenv prog) _permute = Some b /\
  Genv.find_funct_ptr (globalenv prog) b = Some (External (EF_external "permute" [Xptr; Xint; Xint ---> Xvoid]%asttyp)
      [tptr tint; tint; tint] tvoid cc_default).
Proof.
  setoid_rewrite Genv.find_funct_ptr_iff.
  by apply Genv.find_def_symbol.
Qed.

Definition permute_address : address := (proj1_sig (find_symbol_funct_ptr_ex_sig _ _ _ _ permute_defined), 0).

Section permute2.

Context `{!VSTGS OK_ty Σ}.

Lemma convert_array : forall n lv lv' b o,
  lv = map (λ i, Vint (Int.repr i)) lv' →
  data_at Tsh (tarray tint n) lv (Vptr b o) ⊣⊢ (b, Ptrofs.unsigned o) ◁ₗ array tint (lv' `at_type` int.int tint).
Proof.
Admitted.

Definition permute_type : @dtfr Σ (ConstType (address * list Z * nat * nat * Z * Z)) → function.fn_params := λ '(p, elts, x, y, v1, v2),
  {| fp_atys := [p @ &own (array tint (elts `at_type` int.int tint));  x @ int.int tint; y @ int.int tint];
     fp_Pa := ⌜elts !! x = Some v1 /\ elts !! y = Some v2 /\ x ≠ y⌝%stdpp ∧ emp;
     fp_rtype := unit;
     fp_fr := λ _, {| fr_rty := tytrue; fr_R := p ◁ₗ (array tint ((<[y:=v1]>(<[x:=v2]> elts)) `at_type` int.int tint)) |} |}.

Axiom permute_correct : forall Espec ge, ⊢ permute_address ◁ᵥₐₗ|type_of_function f_permute| function_ptr Espec ge permute_type.

Definition permute_spec := (_permute, funtype_to_funspec_void (ConstType (address * list Z * nat * nat * Z * Z)) f_permute
  (λ '(p, elts, x, y, v1, v2), [adr2val p; Vint (Int.repr x); Vint (Int.repr y)]) permute_type).

Definition reverse3_using_permute_spec := DECLARE _reverse3_using_permute
  WITH u : unit
  PRE [ ]
    PROP ()
    PARAMS ()
    SEP ()
  POST [ tvoid ]
    ∃ p : val,
    PROP ()
    RETURN ()
    SEP ().

Definition Gprog : funspecs := [permute_spec; reverse3_using_permute_spec].

Lemma body_reverse3_using_permute : semax_body Vprog Gprog f_reverse3_using_permute reverse3_using_permute_spec.
Proof.
  start_function.
  do 3 forward.
  replace (upd_Znth _ _ _) with [Vint (Int.repr 1); Vint (Int.repr 2); Vint (Int.repr 3)] by list_solve.
  assert_PROP (isptr v_a) by entailer!.
  destruct v_a; try done.
  rewrite (convert_array _ _ [1; 2; 3]) //.
  forward_call ((b, Ptrofs.unsigned i), [1; 2; 3], 0%nat, 2%nat, 1, 3).
  { rewrite /adr2val Ptrofs.repr_unsigned; entailer!. }
  { simpl; entailer!.
    rewrite /ty_own_val_at /ty_own_val /=.
    rewrite /Frame; instantiate (1 := []); simpl; cancel.
    iIntros "_"; iPureIntro; repeat (split; auto). }
  Intros y; simpl.
  rewrite -(convert_array 3 _ [3; 2; 1]) //.
  Opaque data_at.
  Exists (Vptr b i); entailer!.
Qed.

End permute2.
