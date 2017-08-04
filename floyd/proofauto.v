Require Export floyd.base2.
Require Export floyd.sublist.
Require Export floyd.client_lemmas.
Require Export floyd.go_lower.
Require Export floyd.closed_lemmas.
Require Export floyd.compare_lemmas.
Require Export floyd.semax_tactics.
Require Export floyd.forward.
Require Export floyd.call_lemmas.
Require Export floyd.forward_lemmas.
Require Export floyd.for_lemmas.
Require Export floyd.nested_pred_lemmas.
Require Export floyd.nested_field_lemmas.
Require Export floyd.efield_lemmas.
Require Export floyd.mapsto_memory_block.
Require Export floyd.aggregate_type.
Require floyd.aggregate_pred. Export floyd.aggregate_pred.aggregate_pred.
Require Export floyd.reptype_lemmas.
Require Export floyd.simpl_reptype.
Require Export floyd.data_at_rec_lemmas.
Require Export floyd.field_at.
Require Export floyd.field_compat.
Require Export floyd.stronger.
Require Export floyd.loadstore_mapsto.
Require Export floyd.loadstore_field_at.
Require Export floyd.nested_loadstore.
Require Export floyd.local2ptree_denote.
Require Export floyd.local2ptree_eval.
Require Export floyd.proj_reptype_lemmas.
Require Export floyd.replace_refill_reptype_lemmas.
Require Export floyd.sc_set_load_store.
(*Require Export floyd.unfold_data_at.*)
Require Export floyd.entailer.
Require Export floyd.globals_lemmas.
Require Export floyd.diagnosis.
Require Export floyd.freezer.
Require Export floyd.deadvars.
Export ListNotations.

Hint Rewrite add_repr mul_repr sub_repr : entailer_rewrite.
Arguments deref_noload ty v / .
Arguments nested_field_array_type {cs} t gfs lo hi / .
Arguments nested_field_type {cs} t gfs / .  (* redundant? *)
Arguments nested_field_offset {cs} t gfs / .  (* redundant? *)
Arguments Z.mul !x !y.
Arguments Z.sub !m !n.
Arguments Z.add !x !y.
Global Transparent peq.
