Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Import programs own array function adequacy.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.proofauto.

Section mixed.

Context `{!VSTGS OK_ty Σ} {cs : compspecs}.

(* for now, fix to const type *)
Program Definition fn_params_pre' {A} fn params fp : @dtfr Σ (ConstType A) -n> (genviron * list val) -d> mpred := λne x,
  PROP () (PARAMSx (params x) (GLOBALSx [] (SEPx [([∗ list] v;'(cty, t) ∈ params x;zip (map snd (fn_params fn)) (fp_atys (fp x)), v ◁ᵥₐₗ| cty | t) ∗ fp_Pa (fp x)]))).

Program Definition fn_params_post' {A} fn fp : @dtfr Σ (ConstType A) -n> option val -d> mpred := λne x,
  ∃ v, PROP () (RETURNx v (SEPx [∃ y, opt_ty_own_val (fn_return fn) ((fp x).(fp_fr) y).(fr_rty) v ∗ ((fp x).(fp_fr) y).(fr_R)])).

Program Definition fn_params_post_void {A} (fn : function) fp : @dtfr Σ (ConstType A) -n> option val -d> mpred := λne x,
  PROP () RETURN () (SEPx [∃ y, emp ∗ ((fp x).(fp_fr) y).(fr_R)]).

Definition funtype_to_funspec A fn params (fp : @dtfr Σ (ConstType A) → function.fn_params) : funspec :=
  mk_funspec (fn_typesig fn) (fn_callconv fn) (ConstType A) (λne _, ⊤) (fn_params_pre' fn params fp) (fn_params_post' fn fp).

Definition funtype_to_funspec_void A fn params (fp : @dtfr Σ (ConstType A) → function.fn_params) : funspec :=
  mk_funspec (fn_typesig fn) (fn_callconv fn) (ConstType A) (λne _, ⊤) (fn_params_pre' fn params fp) (fn_params_post_void fn fp).

End mixed.

Require Import VST.progs64.permute.
Require Import VST.progs64.permute2.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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

Opaque Z.of_nat.

Lemma convert_array : forall (n : nat) lv lv' b o,
  lv = map (λ i, Vint (Int.repr i)) lv' →
  n = length lv' →
  Forall repable_signed lv' →
  data_at Tsh (tarray tint n) lv (Vptr b o) ⊣⊢ (b, o) ◁ₗ array tint (lv' `at_type` int.int tint).
Proof.
  intros ?????? Hlen Hrep.
  rewrite /data_at /field_at /at_offset data_at_rec_eq /=.
  rewrite /ty_own /= -bi.persistent_and_affinely_sep_l.
  rewrite /has_layout_loc /adr2val /= length_fmap -Hlen.
  destruct (field_compatible_dec (tarray tint (Z.of_nat n)) [] (Vptr b o));
    [rewrite !bi.pure_True // !bi.True_and | rewrite !bi.pure_False // !bi.False_and //].
  rewrite Z.max_r; last lia.
  rewrite /array_pred /aggregate_pred.array_pred Z.sub_0_r.
  rewrite bi.pure_True.
  2: { subst; rewrite /unfold_reptype /= Zlength_map Zlength_correct //. }
  rewrite bi.True_and ptrofs_add_repr_0_r Nat2Z.id.
  generalize dependent lv'; revert lv; generalize dependent o; induction n; simpl; intros.
  - destruct lv'; done.
  - destruct lv'; first done; simpl in *; inv Hlen; inv Hrep.
    f_equiv.
    + rewrite /at_offset /ty_own /= /heap_mapsto_own_state /type.mapsto /adr2val Znth_0_cons /=.
      rewrite data_at_rec_eq /= mapsto_eq //.
      iSplit.
      * iIntros "$"; iPureIntro.
        split3; simpl; try done.
        { rewrite Int.signed_repr //. }
        split; last done; rewrite /offset_def /has_layout_loc /adr2val /= Z.add_0_r.
        pose proof f as Hcompat.
        apply (field_compatible_app_inv' [ArraySubsc 0]) in f; last done.
        rewrite app_nil_r in f.
        apply (field_compatible_app []) in f; simpl in f.
        rewrite field_address_offset // in f.
        rewrite field_compatible_cons /=; split; auto; lia.
      * iIntros "(% & %Hv & %Heq & % & H)".
        destruct Hv as (Hv & _); rewrite value_fits_eq /= in Hv.
        destruct v; inv Heq.
        rewrite Int.repr_signed //.
    + erewrite aggregate_pred.rangespec_shift; first setoid_rewrite IHn; try done.
      3: { intros ??? Hi; rewrite /at_offset /unfold_reptype /= -Hi; f_equal.
           * list_solve.
           * f_equal.
             instantiate (1 := (Ptrofs.add o (Ptrofs.repr 4))).
             rewrite Ptrofs.add_assoc ptrofs_add_repr; do 2 f_equal; lia. }
      2: { pose proof f as Hcompat.
           rewrite (field_compatible_Tarray_split _ 1) in f; last lia.
           destruct f as (_ & f).
           replace (Z.of_nat (S (base.length lv')) - 1) with (Z.of_nat (base.length lv')) in f by lia.
           rewrite field_address0_offset // in f.
           rewrite field_compatible0_cons /=.
           split; [lia | done]. }
      f_equiv; last done.
      intros ??; rewrite /offset_def /=.
      f_equiv; f_equiv.
      rewrite Ptrofs.add_assoc ptrofs_add_repr; do 2 f_equiv.
      hnf; lia.
Qed.

Transparent Z.of_nat.

(* to be imported from the example file *)
Definition permute_type : @dtfr Σ (ConstType (lifting_expr.address * list Z * nat * nat * Z * Z)) → function.fn_params := λ '(p, elts, x, y, v1, v2),
  {| fp_atys := [p @ &own (array tint (elts `at_type` int.int tint));  x @ int.int tint; y @ int.int tint];
     fp_Pa := ⌜elts !! x = Some v1 /\ elts !! y = Some v2 /\ x ≠ y⌝%stdpp ∧ emp;
     fp_rtype := unit;
     fp_fr := λ _, {| fr_rty := tytrue; fr_R := p ◁ₗ (array tint ((<[y:=v1]>(<[x:=v2]> elts)) `at_type` int.int tint)) |} |}.

Definition permute_spec := (_permute, funtype_to_funspec_void (lifting_expr.address * list Z * nat * nat * Z * Z) f_permute
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
  rewrite (convert_array 3 _ [1; 2; 3]) //; last by repeat constructor.
  forward_call ((b, i), [1; 2; 3], 0%nat, 2%nat, 1, 3).
  { simpl; entailer!.
    rewrite /ty_own_val_at /ty_own_val /=.
    rewrite /Frame; instantiate (1 := []); simpl; cancel.
    iIntros "_"; iPureIntro; repeat (split; auto). }
  Intros y; simpl.
  rewrite -(convert_array 3 _ [3; 2; 1]) //; last by repeat constructor.
  Opaque data_at.
  Exists (Vptr b i); entailer!.
Qed.

End permute2.
