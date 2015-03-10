Require Import floyd.proofauto.
Require Import progs.revarray.

Local Open Scope logic.

Definition reverse_spec :=
 DECLARE _reverse
  WITH a0: val, sh : share, contents : list val, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed;
                writable_share sh;
                size = Zlength contents;
                forall i, 0 <= i < size -> is_int I32 Signed (Znth i contents Vundef))
          LOCAL (temp _a a0; temp _n (Vint (Int.repr size)))
          SEP (`(data_at sh (tarray tint size) contents a0))
  POST [ tvoid ]
     PROP() LOCAL()
     SEP(`(data_at sh (tarray tint size) (rev contents) a0)).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_four, Tarray tint 4 noattr)::nil.

Definition Gprog : funspecs := 
    reverse_spec :: main_spec::nil.

Definition flip_between {A} lo hi (contents: list A) :=
  rev (skipn (Z.to_nat hi) contents) ++
  skipn (Z.to_nat lo) (firstn (Z.to_nat hi) contents) ++
  rev (firstn (Z.to_nat lo) contents).

Definition reverse_Inv a0 sh contents size := 
 EX j:Z,
  (PROP  (0 <= j; j <= size-j; isptr a0;
                size = Zlength contents;
           forall i, 0 <= i < size -> is_int I32 Signed (Znth i contents Vundef))
   LOCAL  (temp _a a0; temp _lo (Vint (Int.repr j)); temp _hi (Vint (Int.repr (size-j))))
   SEP (`(data_at sh (tarray tint size) (flip_between j (size-j) contents) a0))).

Lemma flip_fact_0: forall {A} (contents: list A),
  contents = flip_between 0 (Zlength contents - 0) contents.
Proof.
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
Qed.

Lemma flip_fact_1: forall {A} (contents: list A) j,
  0 <= j ->
  Zlength contents - j - 1 <= j <= Zlength contents - j ->
  flip_between j (Zlength contents - j) contents = rev contents.
Proof.
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
Qed.

Lemma flip_fact_2: forall {A} (contents: list A) j k d,
  0 <= j <= Zlength contents - j - 1 ->
  j <= k < Zlength contents - j ->
  Znth k (flip_between j (Zlength contents - j) contents) d = Znth k contents d.
Proof.
  intros.
  assert (Z.to_nat (Zlength contents) = length contents)
    by (rewrite Zlength_correct, Nat2Z.id; reflexivity).
  assert (Z.to_nat j <= length contents)%nat
    by (rewrite <- H1; apply Z2Nat.inj_le; omega).
  assert (Z.to_nat j <= Z.to_nat k)%nat by (apply Z2Nat.inj_le; omega).
  unfold flip_between.
  unfold Znth.
  if_tac; [omega |].
  rewrite app_nth2; rewrite rev_length, skipn_length; rewrite Z2Nat.inj_sub by omega; [| omega].
  replace (Z.to_nat k - (length contents - (Z.to_nat (Zlength contents) - Z.to_nat j)))%nat
    with (Z.to_nat k - Z.to_nat j)%nat by omega.
  rewrite app_nth1.
  Focus 2. {
    rewrite skipn_length, firstn_length.
    rewrite min_l by omega.
    rewrite <- !Z2Nat.inj_sub by omega.
    apply Z2Nat.inj_lt; omega.
  } Unfocus.
  rewrite nth_skipn.
  simpl.
  rewrite nth_firstn.
  Focus 2. {
    rewrite <- !Z2Nat.inj_sub by omega.
    rewrite <- Z2Nat.inj_add by omega.
    apply Z2Nat.inj_lt; omega.
  } Unfocus.
  f_equal.
  omega.
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
forward.  (* lo = 0; *) 
forward.  (* hi = n; *)
rename H2 into POP.
assert_PROP (isptr a0). entailer!. rename H2 into TCa0.
forward_while (reverse_Inv a0 sh contents size)
    (PROP  () LOCAL  (temp _a a0)
   SEP (`(data_at sh (tarray tint size) (rev contents) a0))).
(* Prove that current precondition implies loop invariant *)
unfold reverse_Inv.
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
rewrite Int.sub_signed in H4.
normalize in H4.
simpl_compare.
apply derives_refl'.
f_equal.
apply flip_fact_1; omega.
(* Prove that loop body preserves invariant *)
forward.  (* t = a[lo]; *)
{
  entailer.
  rewrite Int.sub_signed in H4.
  rewrite Int.signed_repr in H4 by repable_signed.
  rewrite Int.signed_repr in H4 by repable_signed.
  simpl_compare.
  entailer!.
  rewrite flip_fact_2 by omega.
  apply POP.
  omega.
}
{
  entailer!.
  rewrite Int.sub_signed in H4.
  rewrite Int.signed_repr in H4 by repable_signed.
  rewrite Int.signed_repr in H4 by repable_signed.
  simpl_compare.
  omega.
}
forward.  (* s = a[hi-1]; *)
{
  entailer.
  rewrite Int.sub_signed in H5.
  rewrite Int.signed_repr in H5 by repable_signed.
  rewrite Int.signed_repr in H5 by repable_signed.
  simpl_compare.
  entailer!.
  rewrite flip_fact_2 by omega.
  apply POP.
  omega.
}
{
  entailer!.
  rewrite Int.sub_signed in H5.
  rewrite Int.signed_repr in H5 by repable_signed.
  rewrite Int.signed_repr in H5 by repable_signed.
  simpl_compare.
  omega.
}
normalize.
forward. (*  a[hi-1] = t ; *)
{
  entailer!.
  rewrite Int.sub_signed in H6.
  rewrite Int.signed_repr in H6 by repable_signed.
  rewrite Int.signed_repr in H6 by repable_signed.
  simpl_compare.
  omega.
}
normalize.
forward. (*  a[lo] = s; *) 
{
  entailer!.
  rewrite Int.sub_signed in H6.
  rewrite Int.signed_repr in H6 by repable_signed.
  rewrite Int.signed_repr in H6 by repable_signed.
  simpl_compare.
  omega.
}
normalize.
forward. (* lo++; *)
forward. (* hi--; *)
(* Prove postcondition of loop body implies loop invariant *)
{
  unfold reverse_Inv.
  apply exp_right with (Zsucc j).
  entailer.
  rewrite Int.sub_signed in H6.
  rewrite Int.signed_repr in H6 by repable_signed.
  rewrite Int.signed_repr in H6 by repable_signed.
  simpl_compare.
  rewrite !flip_fact_2 by omega.
  rewrite !sem_cast_neutral_int by (exists I32, Signed; apply POP; omega).
  simpl force_val.
  apply andp_right.
  + apply prop_right.
    split; [omega |].
    f_equal; omega.
  + admit.
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
unfold main_post. entailer.
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

