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
  ∃ v, PROP () (RETURN (v) (SEPx [∃ y, v ◁ᵥₐₗ|fn_return fn| ((fp x).(fp_fr) y).(fr_rty) ∗ ((fp x).(fp_fr) y).(fr_R)])).

Program Definition fn_params_post_void {A} (fn : function) fp : @dtfr Σ (ConstType A) -n> option val -d> mpred := λne x,
  PROP () RETURN () (SEPx [∃ y, emp ∗ ((fp x).(fp_fr) y).(fr_R)]).

Definition funtype_to_funspec A fn params (fp : @dtfr Σ (ConstType A) → function.fn_params) : funspec :=
  mk_funspec (fn_typesig fn) (fn_callconv fn) (ConstType A) (λne _, ⊤) (fn_params_pre' fn params fp) (fn_params_post' fn fp).

Definition funtype_to_funspec_void A fn params (fp : @dtfr Σ (ConstType A) → function.fn_params) : funspec :=
  mk_funspec (fn_typesig fn) (fn_callconv fn) (ConstType A) (λne _, ⊤) (fn_params_pre' fn params fp) (fn_params_post_void fn fp).

End mixed.
