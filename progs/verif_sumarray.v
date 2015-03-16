Require Import floyd.proofauto.
Require Import progs.sumarray.

Local Open Scope logic.

Definition force_option {A} (x:A) (i: option A) := 
  match i with Some y => y | None => x end.

Definition sum_int := fold_right Int.add Int.zero.

Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a0: val, sh : share, contents : list int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP  (0 <= size <= Int.max_signed;
                 Zlength contents = size;
                 forall i, 0 <= i < size -> is_int I32 Signed (Znth i (map Vint contents) Vundef))
          LOCAL (temp _a a0; temp _n (Vint (Int.repr size)))
          SEP   (`(data_at sh (tarray tint size) (map Vint contents) a0))
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (sum_int contents)))
           SEP (`(data_at sh (tarray tint size) (map Vint contents) a0)).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_four, Tarray tint 4 noattr)::nil.

Definition Gprog : funspecs := 
    sumarray_spec :: main_spec::nil.

Definition sumarray_Inv a0 sh contents size := 
 EX i: Z,
   PROP  (0 <= i <= size;
          forall j, 0 <= j < size -> is_int I32 Signed (Znth j (map Vint contents) Vundef))
   LOCAL (temp _a a0; 
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (sum_int (firstn (Z.to_nat i) contents))))
   SEP   (`(data_at sh (tarray tint size) (map Vint contents) a0)).

(*
Lemma fold_range_split:
  forall A f (z: A) lo hi delta,
   lo <= hi -> delta >= 0 ->
   fold_range f z lo (hi+delta) =
   fold_range f (fold_range f z hi (hi+delta)) lo hi.
Proof.
unfold fold_range; intros.
replace (hi+delta-hi) with delta by omega.
replace (hi+delta-lo) with ((hi-lo)+ delta) by omega.
rewrite nat_of_Z_plus by omega.
forget (nat_of_Z delta) as d.
clear delta H0.
pattern hi at 2.
replace hi with (hi-lo+lo) by omega.
remember (hi-lo) as r. 
replace r with (Z.of_nat (Z.to_nat r))
 by (rewrite Z2Nat.id; omega).
forget (Z.to_nat r) as n; clear r hi H Heqr.
rewrite nat_of_Z_of_nat.
revert z lo d; induction n; intros.
reflexivity.
change (S n + d)%nat with (S (n + d)).
unfold fold_range' at 1 2; fold @fold_range'.
f_equal.
rewrite IHn; clear IHn.
f_equal. f_equal.
rewrite Nat2Z.inj_succ.
omega.
Qed.

Lemma fold_range_fact1:
 forall lo hi contents,
  lo <= hi ->
  fold_range (add_elem contents) Int.zero lo (Z.succ hi) =
  Int.add (fold_range (add_elem contents) Int.zero lo hi) 
                 (force_int (contents hi)).
Proof.
intros.
unfold Z.succ.
rewrite fold_range_split by omega.
unfold fold_range at 2.
replace (hi+1-hi) with 1 by omega.
change (nat_of_Z 1) with 1%nat.
unfold fold_range'.
*
unfold fold_range.
forget (nat_of_Z (hi-lo)) as n.
unfold add_elem at 2.
forget (contents hi) as a.
rewrite Int.add_zero.
clear.
revert lo; induction n; intros.
simpl. rewrite Int.add_zero_l. auto.
simpl.
rewrite (IHn (Z.succ lo)).
clear IHn.
forget (fold_range' (add_elem contents) Int.zero (Z.succ lo) n) as B.
unfold add_elem.
rewrite Int.add_assoc.
auto.
Qed.
*)

Lemma derives_extract_PROP:
  forall (PP : Prop) (P : list Prop) Q R Post,
  (PP -> (PROPx P (LOCALx Q (SEPx R))) |-- Post) -> (PROPx (PP :: P) (LOCALx Q (SEPx R))) |-- Post.
Proof.
  intros.
  rewrite <- move_prop_from_LOCAL, <- insert_local.
  unfold local, lift1, lift0.
  intro rho.
  simpl.
  apply derives_extract_prop.
  intro.
  apply (H H0).
Qed.

Lemma add_one_more_to_sum: forall contents i x,
  Znth i (map Vint contents) Vundef = Vint x ->
  0 <= i ->
  sum_int (firstn (Z.to_nat (Z.succ i)) contents) =
   Int.add (sum_int (firstn (Z.to_nat i) contents)) x.
Proof.
  intros.
  rewrite Int.add_commut.
  rewrite Z2Nat.inj_succ by eauto.
  unfold Znth in H.
  if_tac in H; [omega |].
  forget (Z.to_nat i) as ii.
  clear i H0 H1.
  revert contents H.
  induction ii; intros.
  + simpl in *.
    destruct contents.
    - inversion H.
    - simpl in H; inversion H.
      reflexivity.
  + destruct contents; [inversion H |].
    remember (S ii).
    rewrite Heqn at 2.
    simpl firstn.
    simpl sum_int.
    subst n.
    rewrite IHii by exact H.
    rewrite <- !Int.add_assoc.
    f_equal.
    apply Int.add_commut.
Qed.

Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
start_function.
name a _a.
name n _n.
name i _i.
name s _s.
name x _x.
forward.  (* i = 0; *) 
forward.  (* s = 0; *)
unfold MORE_COMMANDS, abbreviate.
forward_while (sumarray_Inv a0 sh contents size)
    (PROP  () 
     LOCAL (temp _a a0;
            temp _s (Vint (sum_int contents)))
     SEP   (`(data_at sh (tarray tint size) (map Vint contents) a0))).
(* Prove that current precondition implies loop invariant *)
unfold sumarray_Inv.
apply exp_right with 0.
entailer!.
(* Prove that loop invariant implies typechecking condition *)
entailer!.
(* Prove that invariant && not loop-cond implies postcondition *)
entailer!.
assert (a1 = Zlength contents) by omega; subst.
rewrite Zlength_correct, Nat2Z.id, firstn_exact_length.
reflexivity.
(* Prove postcondition of loop body implies loop invariant *)
normalize.
forward. (* x = a[i] *)
  entailer!. apply H1. omega.
forward. (* s += x; *)
forward. (* i++; *)
  apply exp_right with (Zsucc a1).
  entailer!.
 rewrite H5 in H4. inv H4. 
  erewrite add_one_more_to_sum; eauto. omega.
(* After the loop *)
forward.  (* return s; *)
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
name s _s.
start_function.
normalize. intro four. normalize.
forward_call' (*  r = sumarray(four,4); *)
  (four,Ews,four_contents,4).
 split3. computable. reflexivity.
 intros. unfold four_contents.
   apply forall_Forall; [| auto].
   intros.
   repeat (destruct H0; [subst; simpl; auto|]); inversion H0.
 forward. (* return s; *)
 unfold main_post. entailer!.
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_sumarray.
semax_func_cons body_main.
apply semax_func_nil.
Qed.

