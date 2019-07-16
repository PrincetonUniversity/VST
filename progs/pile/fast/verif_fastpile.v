Require Import VST.floyd.proofauto.
Require Import linking.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile.

Definition Gprog : funspecs :=   
   spec_stdlib.specs ++ spec_fastpile.ispecs ++ spec_fastpile.specs.

Lemma body_Pile_new: semax_body Vprog Gprog f_Pile_new Pile_new_spec.
Proof.
start_function.
forward_call (tpile, gv).
split3; simpl; auto; computable.
Intros p.
forward.
forward.
unfold pilerep, pile_freeable.
Exists p 0.
entailer!.
Qed.

Lemma sumlist_nonneg: forall sigma, 
  Forall (Z.le 0) sigma -> 0 <= sumlist sigma.
Proof.
intros.
induction sigma; simpl. omega. inv H.
apply IHsigma in H3; omega.
Qed.

Lemma body_Pile_add: semax_body Vprog Gprog f_Pile_add Pile_add_spec.
Proof.
start_function.
unfold pilerep.
Intros s.
forward.
forward_if (temp _t'1 (if zle 0 n then if zle n (Int.max_signed-s) then Vtrue else Vfalse else Vfalse)).
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
forward.
entailer!.
unfold MORE_COMMANDS, abbreviate.
destruct (zle 0 n); try omega. clear l.
destruct (zle n (Int.max_signed - s)).
-
forward_if (PROP()LOCAL (temp _p p)
   SEP(data_at Ews tpile (Vint (Int.repr (s+n))) p;
         mem_mgr gv)).
forward.
entailer!.
inversion H3.
forward.
unfold pilerep.
Exists (s+n).
entailer!.
split.
constructor; auto. omega.
simpl. intros.
rewrite H2.
omega.
apply sumlist_nonneg in H1; omega.
-
forward_if (PROP()LOCAL (temp _p p)
   SEP(data_at Ews tpile (Vint (Int.repr s)) p;
         mem_mgr gv)).
contradiction H3'; auto.
forward.
entailer!.
forward.
unfold pilerep.
Exists s.
entailer!.
split.
constructor; auto.
omega.
simpl.
apply sumlist_nonneg in H1; omega.
Qed.

Lemma body_Pile_count: semax_body Vprog Gprog f_Pile_count Pile_count_spec.
Proof.
start_function.
unfold pilerep. Intros s.
forward.
forward.
entailer!.
rewrite H2; auto.
unfold pilerep.
Exists s.
entailer!.
Qed.

Lemma body_Pile_free: semax_body Vprog Gprog f_Pile_free Pile_free_spec.
Proof.
start_function.
unfold pilerep, pile_freeable. Intros s.
assert_PROP (p<>nullval) by entailer!. 
forward_call (free_spec_sub (Tstruct _pile noattr))  (p, gv).
rewrite if_false by auto.
cancel.
forward.
Qed.

(*Same pstatement and proof as verif_pile. Indeed, the C files have the same code duplication...*)
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
