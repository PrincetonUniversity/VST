Require Import VST.floyd.proofauto.
Require Import VST.progs64.permute_norm. (* without normalize, start_function fails *)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section permute.

Context `{!VSTGS OK_ty Σ}.

Definition permute_spec :=
 DECLARE _permute
  WITH ar: val, elts : list val, i : nat, j : nat, vi : int, vj : int
  PRE [ (tptr tint), tint, tint ]
          PROP  (Znth i elts = Vint vi; Znth j elts = Vint vj; i ≠ j; repable_signed i; repable_signed j)
          PARAMS (ar; Vint (Int.repr i); Vint (Int.repr j))
          SEP   (data_at Ews (tarray tint (Zlength elts)) elts ar)
  POST [ tvoid ]
        PROP () RETURN ()
           SEP (data_at Ews (tarray tint (Zlength elts)) (upd_Znth j (upd_Znth i elts (Vint vj)) (Vint vi)) ar).

Definition Gprog : funspecs := ltac:(with_library prog [permute_spec]).

Lemma body_permute: semax_body Vprog Gprog f_permute permute_spec.
Proof.
  start_function.
  assert (0 <= i < Zlength elts).
  { apply Znth_inbounds; rewrite H //. }
  assert (0 <= j < Zlength elts).
  { apply Znth_inbounds; rewrite H0 //. }
  forward.
  { rewrite H; entailer!. }
  forward.
  { rewrite H0; entailer!. }
  forward.
  forward.
  rewrite H H0; entailer!.
Qed.

End permute.
