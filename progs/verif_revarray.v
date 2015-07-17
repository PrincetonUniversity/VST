Require Import floyd.proofauto.
Require Import progs.revarray.

Local Open Scope logic.

Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Definition reverse_spec :=
 DECLARE _reverse
  WITH a0: val, sh : share, contents : list val, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed;
                writable_share sh;
                size = Zlength contents;
                forall i, 0 <= i < size -> is_int I32 Signed (Znth i contents Vundef))
          LOCAL (temp _a a0; temp _n (Vint (Int.repr size)))
          SEP (`(data_at sh (tarray tint size) (zl_constr tint 0 size contents) a0))
  POST [ tvoid ]
     PROP() LOCAL()
     SEP(`(data_at sh (tarray tint size) (zl_constr tint 0 size (rev contents)) a0)).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_four, Tarray tint 4 noattr)::nil.

Definition Gprog : funspecs := 
    reverse_spec :: main_spec::nil.

Definition flip_between t lo hi size (contents: list (reptype t)) :=
  zl_concat (zl_sublist 0 lo (zl_constr t 0 size (rev contents)))
    (zl_concat (zl_sublist lo hi (zl_constr t 0 size contents))
                  (zl_sublist hi size (zl_constr t 0 size (rev contents)))).

Definition reverse_Inv a0 sh contents size := 
 EX j:Z,
  (PROP  (0 <= j; j <= size-j; isptr a0;
          size = Zlength contents;
          forall i, 0 <= i < size -> is_int I32 Signed (Znth i contents Vundef))
   LOCAL  (temp _a a0; temp _lo (Vint (Int.repr j)); temp _hi (Vint (Int.repr (size-j))))
   SEP (`(data_at sh (tarray tint size) (flip_between tint j (size-j) size contents) a0))).

Lemma flip_fact_0: forall t size (contents: list (reptype t)),
  zl_constr t 0 size contents = flip_between t 0 (size - 0) size contents.
Proof.
  admit.
(*
  intros.
  unfold flip_between.
  rewrite Z.sub_0_r.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite skipn_exact_length.
  change (Z.to_nat 0) with 0%nat.
  simpl.
  rewrite app_nil_r.
  rewrite firstn_exact_length.
  reflexivity.
*)
Qed.

Lemma flip_fact_1: forall t size (contents: list (reptype t)) j,
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  flip_between t j (size - j) size contents =
   zl_constr t 0 size (rev contents).
Proof.
  admit.
(*
  intros.
  assert (Zlength contents - j - 1 = j \/ Zlength contents - j = j)
    by (destruct (zle (Zlength contents - j) j); omega).
  assert (skipn (Z.to_nat j) (firstn (Z.to_nat (Zlength contents - j)) contents) = 
    rev (skipn (Z.to_nat j) (firstn (Z.to_nat (Zlength contents - j)) contents))).
  Focus 1. {
    apply len_le_1_rev.
    rewrite skipn_length.
    rewrite firstn_length.
    rewrite min_l.
    + rewrite <- Z2Nat.inj_sub by omega.
      change 1%nat with (Z.to_nat 1).
      apply Z2Nat.inj_le; omega.
    + rewrite Z2Nat.inj_sub by omega.
      rewrite Zlength_correct.
      rewrite Nat2Z.id.
      omega.
  } Unfocus.
  unfold flip_between.
  rewrite H2.
  rewrite <- !rev_app_distr.
  f_equal.
  rewrite <- firstn_firstn with (n := Z.to_nat j) (m := Z.to_nat (Zlength contents - j))
    by (apply Z2Nat.inj_le; omega).
  rewrite !firstn_skipn.
  reflexivity.
*)
Qed.

Lemma zl_nth_rev:
  forall {cs: compspecs} {csl: compspecs_legal cs}{t: type}
           i lo hi (al: list (reptype t)),
      lo <= i < hi ->
      hi-lo = Zlength al ->
      zl_nth i (zl_constr t lo hi al) = zl_nth (hi-i-1+lo) (zl_constr t lo hi (rev al)).
Proof.
intros.
 rewrite !zl_constr_correct by omega.
 unfold Znth. rewrite !if_false by omega.
       replace (hi-i-1+lo-lo) with (Zlength al -  (1+(i-lo))) by omega.
       rewrite rev_nth.
       f_equal.
  apply Nat2Z.inj. rewrite Z2Nat.id by omega.
  rewrite Nat2Z.inj_sub.
 rewrite <- Zlength_correct. rewrite <- H0. 
 rewrite inj_S. rewrite Z2Nat.id by omega.
 omega.
  apply Nat2Z.inj_le. rewrite <- Zlength_correct.
  rewrite inj_S. rewrite Z2Nat.id by omega. omega.
  apply Nat2Z.inj_lt. rewrite <- Zlength_correct. rewrite Z2Nat.id by omega. 
 omega.
Qed.
 
Lemma flip_fact_3: 
 forall (contents : list val)
    (n j : Z),
   j < n - j - 1 ->  0 <= j -> n = Zlength contents ->
 zl_equiv
  (zl_concat
     (zl_concat
        (zl_sublist 0 j
           (zl_concat
              (zl_concat
                 (zl_sublist 0 (n - j - 1)
                    (flip_between tint j (n - j) n contents))
                 (zl_singleton (n - j - 1)
                    (zl_nth j (zl_constr tint 0 n contents))))
              (zl_sublist (n - j-1+1) n 
               (flip_between tint j (n - j) n contents))))
        (zl_singleton j (zl_nth (n - j - 1) (zl_constr tint 0 n contents))))
     (zl_sublist (j + 1) n
        (zl_concat
           (zl_concat
              (zl_sublist 0 (n - j - 1)
                 (flip_between tint j (n - j) n contents))
              (zl_singleton (n - j - 1)
                 (zl_nth j (zl_constr tint 0 n contents))))
           (zl_sublist (n - j-1+1) n 
             (flip_between tint j (n - j) n contents)))))
  (flip_between tint (j + 1) (n - j - 1) n contents).
Proof.
intros.
change val with (@reptype CompSpecs tint) in H1.
   rewrite zl_sub_concat_l by omega.
   rewrite zl_sub_concat_l by omega.
   rewrite zl_sub_sub by omega.
   rewrite zl_sub_concat_mid by omega.
   rewrite zl_sub_sub by omega.
   rewrite zl_sub_concat_mid by omega.
   rewrite zl_sub_sub by omega.
   rewrite (zl_nth_rev (n-j-1)) by omega.
   rewrite zl_sub_singleton' by omega.
   unfold flip_between at 1.
   rewrite zl_sub_concat_l by omega.
   rewrite zl_sub_sub by omega.
  rewrite zl_concat_sub by omega.
 unfold flip_between at 1.
  rewrite zl_sub_concat_r by omega.
  rewrite zl_sub_concat_l by omega.
   rewrite zl_sub_sub by omega.
 unfold flip_between at 1.
  rewrite zl_sub_singleton'' by omega.
  rewrite zl_sub_concat_r by omega.
  rewrite zl_sub_concat_r by omega.
   rewrite zl_sub_sub by omega.
 unfold flip_between at 1.
 apply Proper_concat; auto with typeclass_instances.
 reflexivity.
 rewrite <- zl_concat_assoc by omega.
 apply Proper_concat; auto with typeclass_instances.
 reflexivity.
 rewrite zl_nth_rev by omega.
 rewrite Z.add_0_r.
 rewrite <- zl_sub_singleton by omega.
 rewrite zl_concat_sub by omega.
 reflexivity.
Qed.

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function.
name a _a.
name n _n.
name lo' _lo.
name hi' _hi.
name s _s.
name t _t.

assert_PROP (isptr a0). entailer!.

rename H1 into TCa0.

forward.  (* lo = 0; *)
forward _. (* hi = n; *)

forward_while (reverse_Inv a0 sh contents size)
    (PROP  () LOCAL  (temp _a a0)
   SEP (`(data_at sh (tarray tint size) (zl_constr tint 0 size (rev contents)) a0)))
   j.
(* Prove that current precondition implies loop invariant *)
apply exp_right with 0.
entailer!; try omega.
f_equal; omega.
apply derives_refl'.
f_equal.
apply flip_fact_0; auto.
(* Prove that loop invariant implies typechecking condition *)
entailer!.
(* Prove that invariant && not loop-cond implies postcondition *)
entailer!.
apply derives_refl'.
f_equal.
apply flip_fact_1; omega.
(* Prove that loop body preserves invariant *)
forward. (* t = a[lo]; *)
{
  entailer!.
  unfold flip_between.
  unfold unfold_reptype; simpl.
  autorewrite with zl_nth_db.
  apply H6; omega.
}
unfold unfold_reptype; simpl.
change  {| attr_volatile := false; attr_alignas := @None N |} with noattr.
change  (Tint I32 Signed noattr) with tint.
match goal with |- context [temp _t ?A] =>
 replace A with (zl_nth j (zl_constr tint 0 size contents))
  by (unfold flip_between;
      rewrite zl_concat_correct_r by omega;
      rewrite zl_concat_correct_l by omega;
      rewrite zl_sublist_correct by omega; auto)
end.
forward.  (* s = a[hi-1]; *)
{
  entailer!.
  unfold flip_between.
  unfold unfold_reptype; simpl.
  autorewrite with zl_nth_db.
  apply H6; omega.
}
unfold unfold_reptype; simpl.
match goal with |- context [temp _s ?A] =>
 replace A with (zl_nth (size-j-1) (zl_constr tint 0 size contents))
  by (unfold flip_between;
      rewrite zl_concat_correct_r by omega;
      rewrite zl_concat_correct_l by omega;
      rewrite zl_sublist_correct by omega; auto)
end.
forward. (*  a[hi-1] = t; *)
forward. (* a[lo] = s; *)
unfold unfold_reptype; simpl.
forward lo'0. (* lo++; *)
forward hi'0. (* hi--; *)
(* Prove postcondition of loop body implies loop invariant *)
{
  apply exp_right with (Zsucc j).
  erewrite field_at_data_equal. (* This should be more convenient.  - Qinxiang *)
  Focus 2. {
    apply data_equal_zl_equiv.
  rewrite !sem_cast_neutral_int
  by (exists I32, Signed; unfold flip_between; simpl;
       autorewrite with zl_nth_db; apply H6; omega).
  simpl force_val.
  rewrite !(unfold_reptype_JMeq (tarray tint size)).
  apply flip_fact_3; omega.
  } Unfocus.
  unfold data_at.
  replace (size - Z.succ j) with (size - j - 1) by omega.
  replace (Z.succ j) with (j + 1) by omega.
  entailer.
}
forward. (* return; *)
Qed.

Definition four_contents := [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4].

Lemma forall_Forall: forall A (P: A -> Prop) xs d,
  (forall x, In x xs -> P x) ->
  forall i, 0 <= i < Zlength xs -> P (Znth i xs d).
Proof.
  intros.
  unfold Znth.
  if_tac; [omega |].
  assert (Z.to_nat i < length xs)%nat.
  Focus 1. {
    rewrite Zlength_correct in H0.
    destruct H0 as [_ ?].
    apply Z2Nat.inj_lt in H0; [| omega | omega].
    rewrite Nat2Z.id in H0.
    exact H0.
  } Unfocus.
  forget (Z.to_nat i) as n.
  clear i H0 H1.
  revert n H2; induction xs; intros.
  + destruct n; simpl in H2; omega.
  + destruct n.
    - specialize (H a (or_introl eq_refl)).
      simpl.
      tauto.
    - simpl in *.
      apply IHxs; [| omega].
      intros.
      apply H.
      tauto.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
normalize; intro a; normalize.

forward_call'  (*  revarray(four,4); *)
  (a, Ews, map Vint four_contents, 4).
   repeat split; try computable; auto.
   intros. unfold four_contents.
   apply forall_Forall; [| auto].
   intros.
   repeat (destruct H0; [subst; simpl; auto|]); inversion H0.

forward_call'  (*  revarray(four,4); *)
    (a,Ews, rev (map Vint four_contents),4).
   repeat split; try computable; auto.
   intros. unfold four_contents.
   apply forall_Forall; [| auto].
   intros.
   repeat (destruct H0; [subst; simpl; auto|]); inversion H0.
rewrite rev_involutive.
forward. (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_reverse.
semax_func_cons body_main.
apply semax_func_nil.
Qed.

