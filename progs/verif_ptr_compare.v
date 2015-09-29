Require Import floyd.proofauto.
Require Import progs.ptr_compare.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

Local Open Scope logic.

Definition f_spec :=
 DECLARE _f
  WITH p: val, q:val, sh: share
  PRE  [_p OF tptr tint, _q OF tptr tint] 
        PROP ()
        LOCAL(temp _p p; temp _q q)
        SEP(`(data_at sh tint (Vint Int.zero) p);`(data_at sh tint (Vint Int.zero) q))
  POST [ tint ]
         PROP() 
         LOCAL (temp 1%positive (if eq_dec p q then Vtrue else Vfalse))
         SEP (`(data_at sh tint (Vint Int.zero) p);`(data_at sh tint (Vint Int.zero) q)).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := nil.

Lemma data_at__valid_pointer:
  forall sh t a, sizeof cenv_cs t > 0 ->
    data_at_ sh t a * TT |-- valid_pointer a.
Proof.
intros.
Admitted.

Lemma valid_pointer_weak:
 forall a, valid_pointer a |-- weak_valid_pointer a.
Proof.
intros.
unfold valid_pointer, weak_valid_pointer.
change predicates_hered.orp with orp. (* delete me *)
apply orp_right1.
auto.
Qed.

Lemma prove_comparable_ptrs1:
  forall P sh t1 t2 a b,
    sizeof cenv_cs t1 > 0 ->
    sizeof cenv_cs t2 > 0 ->
    P |-- data_at_ sh t1 a * TT ->
    P |-- data_at_ sh t2 b * TT ->
    P |-- comparable_ptrs a b.
Proof.
intros.
unfold comparable_ptrs.
destruct (sameblock a b).
apply andp_right; 
 (eapply derives_trans; [ | apply valid_pointer_weak]).
eapply derives_trans; [ | apply data_at__valid_pointer; auto]; eassumption.
eapply derives_trans; [ | apply data_at__valid_pointer; auto]; eassumption.
apply andp_right; 
(eapply derives_trans; [ | apply data_at__valid_pointer; auto]; eassumption).
Qed.

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
name p' _p.
name q' _q.
forward.
apply field_compatible_isptr in H; destruct p'; try contradiction.
apply field_compatible_isptr in H1; destruct q'; try contradiction.
entailer!.
split.
unfold sem_cmp_pp; simpl.
if_tac; try reflexivity.
destruct (Int.eq i i0); reflexivity.
unfold sem_cmp_pp.
if_tac; simpl.
inv H4. rewrite if_true by auto.
rewrite Int.eq_true. reflexivity.
if_tac. rewrite Int.eq_false by congruence.
reflexivity.
reflexivity.
apply andp_right; auto.
simpl.
eapply prove_comparable_ptrs1; try cancel;
  simpl; computable.
Qed.
