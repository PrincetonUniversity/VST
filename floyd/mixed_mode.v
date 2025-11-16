Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Import programs singleton own array function adequacy.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.proofauto.

Definition to_address (v : val) := option.default (1%positive, Ptrofs.zero) (type.val2adr v).

Lemma to_address_eq v : isptr v → adr2val (to_address v) = v.
Proof. by destruct v. Qed.

Arguments nested_field_offset {_} _ _ /.
Arguments cenv_cs : simpl never.

Section mixed.

Context `{!VSTGS OK_ty Σ} {cs : compspecs}.

Lemma unfold_own_type cty v l t : ty_has_op_type t cty MCNone → v ◁ᵥ|tptr cty| l @ &own t ⊣⊢ ⌜l = to_address v⌝ ∧ ∃ a, data_at Tsh cty a v ∗ a ◁ᵥ|cty| t.
Proof.
  intros.
  rewrite /frac_ptr; simpl_type.
  rewrite /repinject /= -bi.persistent_and_affinely_sep_l.
  eapply pure_equiv; first apply bi.and_elim_l.
  { iIntros "(-> & % & H & _)"; rewrite data_at_isptr.
    iDestruct "H" as "(% & _)"; rewrite to_address_eq //. }
  intros ->; rewrite !bi.pure_True //; last by destruct l.
  rewrite !bi.True_and /data_at /field_at /at_offset /=.
  setoid_rewrite Ptrofs.add_zero.
  iSplit.
  - iIntros "H".
    iDestruct (ty_aligned with "H") as %?; first done.
    iDestruct (ty_deref with "H") as (?) "($ & $)"; done.
  - iIntros "(% & (% & H) & ?)".
    iApply (ty_ref with "[//] H"); done.
Qed.

Lemma unfold_own_type0 cty v t : ty_has_op_type t cty MCNone → v ◁ᵥ|tptr cty| &own t ⊣⊢ ∃ a, data_at Tsh cty a v ∗ a ◁ᵥ|cty| t.
Proof.
  intros.
  rewrite /ty_of_rty; simpl_type.
  setoid_rewrite unfold_own_type; last done.
  iSplit.
  - iIntros "(% & -> & $)".
  - iIntros "(% & H & $)".
    rewrite {1}data_at_isptr; iDestruct "H" as (?) "$"; eauto.
Qed.

Lemma fold_own_type cty l t : l ◁ₗ t ⊣⊢ l ◁ᵥ|tptr cty| l @ &own t.
Proof.
  rewrite /frac_ptr; simpl_type.
  rewrite bi.pure_True // bi.affinely_True_emp emp_sep //.
Qed.

Lemma unfold_own_own_type cty l t : l ◁ₗ &own t ⊣⊢ ∃ l' : lifting_expr.address, data_at Tsh (tptr cty) l' l ∗ l' ◁ₗ t.
Proof.
  intros.
  rewrite /ty_of_rty; simpl_type.
  do 2 f_equiv.
  rewrite /frac_ptr; simpl_type.
  rewrite /data_at /field_at /at_offset /= Ptrofs.add_zero.
  rewrite /heap_mapsto_own_state (mapsto_tptr _ _ _ cty) (field_compatible_tptr _ cty).
  iSplit.
  - iIntros "(% & $ & $)"; auto.
  - iIntros"((% & $) & $)"; auto.
Qed.

Lemma unfold_bool_type a b : a ◁ᵥ|tint| b @ boolean.generic_boolean boolean.StrictBool tint ⊣⊢ <affine> ⌜a = Val.of_bool b⌝.
Proof.
  intros; rewrite /boolean.generic_boolean; simpl_type.
  rewrite val_of_bool_eq.
  iSplit.
  - iIntros "(_ & % & _ & %Hk & ->)".
    destruct a; inv Hk.
    rewrite Int.repr_signed //.
  - iIntros (->); iPureIntro.
    split; first done; eexists; split3; try done.
    rewrite Int.signed_repr //; by destruct b.
Qed.

Lemma unfold_int_type a k : repable_signed k → a ◁ᵥ|tint| k @ int.int tint ⊣⊢ <affine> ⌜a = Vint (Int.repr k)⌝.
Proof.
  intros; rewrite /int.int; simpl_type.
  iSplit.
  - iIntros "(_ & _ & %Hk)".
    destruct a; inv Hk.
    rewrite Int.repr_signed //.
  - iIntros (->); iPureIntro.
    rewrite /= Int.signed_repr //.
Qed.

Lemma unfold_value_type cty a v : type_is_volatile cty = false → value_fits cty (valinject cty v) →
  a ◁ᵥ|cty| value cty v ⊣⊢ <affine> ⌜a = valinject cty v⌝.
Proof.
  intros; rewrite /value; simpl_type.
  iPureIntro; split; try tauto.
  intros ->; done.
Qed.

Lemma unfold_value_ptr_type cty a v : is_pointer_or_null v →
  a ◁ᵥ|tptr cty| value (tptr cty) v ⊣⊢ <affine> ⌜a = v⌝.
Proof.
  intros; apply (unfold_value_type (tptr cty)); try done.
  rewrite value_fits_eq /=.
  intros _; simpl.
  rewrite andb_false_r //.
Qed.

(* for now, fix to const type *)
Program Definition fn_params_pre' {A} fn params fp : @dtfr Σ (ConstType A) -n> (genviron * list val) -d> mpred := λne x,
  PROP () (PARAMSx (params x) (GLOBALSx [] (SEPx [([∗ list] v;'(cty, t) ∈ params x;zip (map snd (fn_params fn)) (fp_atys (fp x)), v ◁ᵥₐₗ| cty | t) ∗ fp_Pa (fp x)]))).

Program Definition fn_params_post' {A} fn fp : @dtfr Σ (ConstType A) -n> option val -d> mpred := λne x,
  ∃ v, PROP () (RETURN (v) (SEPx [∃ y, v ◁ᵥₐₗ|fn_return fn| ((fp x).(fp_fr) y).(fr_rty) ∗ ((fp x).(fp_fr) y).(fr_R)])).

Program Definition fn_params_post_void {A} (fn : function) fp : @dtfr Σ (ConstType A) -n> option val -d> mpred := λne x,
  PROP () RETURN () (SEPx [∃ y, emp ∗ ((fp x).(fp_fr) y).(fr_R)]).

Definition funtype_to_funspec A fn params (fp : @dtfr Σ (ConstType A) → function.fn_params) : funspec :=
  mk_funspec (fn_typesig fn) (fn_callconv fn) (ConstType A) (λne _, ⊤) (fn_params_pre' fn params fp) (fn_params_post' fn fp).

Definition funtype_to_funspec_void A fn params (fp : @dtfr Σ (ConstType A) → function.fn_params) : funspec :=
  mk_funspec (fn_typesig fn) (fn_callconv fn) (ConstType A) (λne _, ⊤) (fn_params_pre' fn params fp) (fn_params_post_void fn fp).

End mixed.
