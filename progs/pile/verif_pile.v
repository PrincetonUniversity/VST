Require Import VST.floyd.proofauto.
Require Import linking.
Require Import pile.
Require Import spec_stdlib.
Require Import spec_pile.

Definition Gprog : funspecs :=   
   spec_stdlib.specs ++ spec_pile.ispecs ++ spec_pile.specs.

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

Lemma body_Pile_new: semax_body Vprog Gprog f_Pile_new Pile_new_spec.
Proof.
start_function.
forward_call (tpile, gv).
split3; simpl; auto; computable.
Intros p.
repeat step!.
unfold pilerep, listrep, pile_freeable.
repeat step!.
Qed.

Lemma body_Pile_add: semax_body Vprog Gprog f_Pile_add Pile_add_spec.
Proof.
start_function.
forward_call (tlist, gv).
split3; simpl; auto; computable.
Intros q.
unfold pilerep.
Intros head.
forward.
simpl.
forward.
forward.
forward.
forward.
unfold pilerep.
Exists q.
unfold listrep at 2; fold listrep.
Exists head.
entailer!.
Qed.

Lemma body_Pile_count: semax_body Vprog Gprog f_Pile_count Pile_count_spec.
Proof.
start_function.
unfold pilerep. Intros head.
forward.
unfold Sfor.
forward.
forward_loop (EX r:val, EX s2: list Z,
   PROP(0 <= sumlist s2 <= sumlist sigma)
   LOCAL(temp _c (Vint (Int.repr (sumlist sigma - sumlist s2)));
              temp _p p; temp _q r)
   SEP (data_at Ews tpile head p; 
          listrep s2 r -* listrep sigma head;
          listrep s2 r))%assert
   break: 
  (PROP()
   LOCAL(temp _c (Vint (Int.repr (sumlist sigma))); temp _p p)
   SEP (data_at Ews tpile head p; 
          listrep sigma head))%assert.
-
Exists head sigma.
entailer!. rewrite Z.sub_diag. auto.
apply wand_sepcon_adjoint. cancel.
-
Intros r s2.
forward_if (r<>nullval).
forward.
entailer!.
subst r.
forward.
entailer!.
assert (s2=nil) by intuition; subst s2.
simpl. rewrite Z.sub_0_r; auto.
sep_apply (modus_ponens_wand (listrep s2 nullval)).
cancel.
Intros.
destruct s2.
assert_PROP False; [ | contradiction]. {
 entailer!. assert (r=nullval) by intuition; subst r. congruence.
}
unfold listrep at 3; fold listrep.
Intros r'.
forward.
forward. {
 entailer!.
 simpl in H0.
 clear - H0 H H2 H9.
 rewrite (Int.signed_repr z) by rep_omega.
 rewrite (Int.signed_repr) by rep_omega.
 assert (0 <= sumlist s2). {
 clear - H9. induction s2; simpl; auto. omega.
 inv H9. apply IHs2 in H2. omega.
 }
 rep_omega.
}
forward.
Exists r' s2.
entailer!.
simpl. split.
simpl in H0.
 assert (0 <= sumlist s2). {
 clear - H9. induction s2; simpl; auto. omega.
 inv H9. apply IHs2 in H2. omega.
 }
 rep_omega.
 f_equal; f_equal; omega.
apply -> wand_sepcon_adjoint.
match goal with |- _ * ?A * ?B * ?C |-- _ => 
 assert (A * B * C |-- listrep(z::s2) r) end.
unfold listrep at 2; fold listrep. Exists r'. entailer!.
sep_apply H10.
sep_apply modus_ponens_wand.
auto.
 -
forward.
unfold pilerep.
Exists head.
cancel.
Qed.

Lemma body_Pile_free: semax_body Vprog Gprog f_Pile_free Pile_free_spec.
Proof.
start_function.
unfold pilerep, pile_freeable. Intros head.
forward.
forward_while (EX q:val, EX s2: list Z,
   PROP ( )
   LOCAL (temp _q q; temp _p p; gvars gv)
   SEP (data_at Ews tpile head p; 
       listrep s2 q; malloc_token Ews tpile p;
   mem_mgr gv))%assert.
Exists head sigma; entailer!.
entailer!.
destruct s2.
   assert_PROP False; [|contradiction]. unfold listrep. entailer!.
unfold listrep; fold listrep.
Intros y.
forward.
forward_call (free_spec_sub (Tstruct _list noattr)) (q, gv).
rewrite if_false by (intro; subst; contradiction).
cancel.
forward.
Exists (y, s2).
entailer!.
cancel.
subst.
assert_PROP (p<>nullval). entailer!.
forward_call (free_spec_sub (Tstruct _pile noattr))  (p, gv).
rewrite if_false by auto.
cancel.
forward.
rewrite (proj1 H0) by auto.
unfold listrep.
entailer!.
Qed.

Definition module := 
  [mk_body body_surely_malloc;
   mk_body body_Pile_new;
   mk_body body_Pile_add;
   mk_body body_Pile_count;
   mk_body body_Pile_free].
