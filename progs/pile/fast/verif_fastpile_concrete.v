Require Import VST.floyd.proofauto.
Require Import linking.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile_concrete.

Definition Gprog : funspecs :=   
   spec_stdlib.specs ++ spec_fastpile_concrete.ispecs ++ spec_fastpile_concrete.specs.

Lemma body_Pile_new: semax_body Vprog Gprog f_Pile_new Pile_new_spec.
Proof.
start_function.
forward_call (tpile, gv).
split3; simpl; auto; computable.
Intros p.
forward.
forward.
unfold countrep, count_freeable.
Exists p 0.
entailer!.
Qed.

Lemma body_Pile_add: semax_body Vprog Gprog f_Pile_add Pile_add_spec.
Proof.
start_function.
unfold countrep.
Intros s'.
forward.
forward_if (temp _t'1 (if zle 0 n then if zle n (Int.max_signed-s') then Vtrue else Vfalse else Vfalse)).
-
forward.
entailer!.
destruct (zle 0 n); [ | omega].
destruct (zle _ _).
unfold Int.lt. rewrite zlt_false.
reflexivity.
normalize. rep_omega.
unfold Int.lt. rewrite zlt_true.
reflexivity.
normalize.
rep_omega.
-
forward.
entailer!.
-
destruct (zle 0 n); try omega.
forward_if (PROP()LOCAL (temp _p p)
   SEP(countrep (n+s) p; mem_mgr gv)).
+
if_tac in H3; inv H3.
forward.
unfold countrep. Exists (s'+n).
entailer!.
+
forward.
unfold countrep.
if_tac in H3; inv H3.
Exists s'. entailer!.
+
forward.
Qed.

Lemma body_Pile_count: semax_body Vprog Gprog f_Pile_count Pile_count_spec.
Proof.
start_function.
unfold countrep.
Intros s'.
forward.
forward.
unfold countrep.
Exists s' s'.
entailer!.
Qed.

Lemma body_Pile_free: semax_body Vprog Gprog f_Pile_free Pile_free_spec.
Proof.
start_function.
unfold countrep, count_freeable. Intros s'.
assert_PROP (p<>nullval) by entailer!. 
forward_call (free_spec_sub (Tstruct _pile noattr))  (p, gv).
rewrite if_false by auto.
cancel.
forward.
Qed.

(*Same statement and proof as verif_pile. Indeed, the C files have the same code duplication...*)
(*Statement and proof also shared with verif_fastpile.v*)
Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
start_function.
forward_call (malloc_spec_sub t) gv.
Intros p.
if_tac.
forward_if False.
forward_call tt.
contradiction.
forward.
contradiction.
forward_if True.
forward_call tt.
contradiction.
forward.
entailer!.
forward.
Exists p.
entailer!.
Qed.

Definition module := 
  [mk_body body_surely_malloc; 
   mk_body body_Pile_new; 
   mk_body body_Pile_add;
   mk_body body_Pile_count; 
   mk_body body_Pile_free ].