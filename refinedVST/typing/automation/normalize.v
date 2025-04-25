From lithium Require Export normalize.
From refinedc.typing Require Import type.

#[export] Hint Rewrite ly_align_ly_with_align ly_align_ly_offset ly_align_ly_set_size : lithium_rewrite.
#[export] Hint Rewrite ly_size_ly_set_size ly_size_ly_with_align : lithium_rewrite.

(* The following lemma is a problem with Keyed Unification as it
unfolds e.g. layout_of *)
(* Lemma ly_size_of_mk_layout n : ly_size (mk_layout n) = n. *)
(* Proof. done. Qed. *)
(* Hint Rewrite ly_size_of_mk_layout : lithium_rewrite. *)
