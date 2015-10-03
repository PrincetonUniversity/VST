Require Import floyd.proofauto.
Require Import progs.revarray.
Require Import floyd.sublist.

Local Open Scope logic.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

Definition reverse_spec :=
 DECLARE _reverse
  WITH a0: val, sh : share, contents : list int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed; writable_share sh)
          LOCAL (temp _a a0; temp _n (Vint (Int.repr size)))
          SEP (`(data_at sh (tarray tint size) (map Vint contents) a0))
  POST [ tvoid ]
     PROP() LOCAL()
     SEP(`(data_at sh (tarray tint size) (map Vint (rev contents)) a0)).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_four, Tarray tint 4 noattr)::nil.

Definition Gprog : funspecs := 
    reverse_spec :: main_spec::nil.

Definition flip_between {A} lo hi (contents: list A) :=
  sublist 0 lo (rev contents)
  ++ sublist lo hi contents
  ++ sublist hi (Zlength contents) (rev contents).

Definition reverse_Inv a0 sh contents size := 
 EX j:Z,
  (PROP  (0 <= j; j <= size-j)
   LOCAL  (temp _a a0; temp _lo (Vint (Int.repr j)); temp _hi (Vint (Int.repr (size-j))))
   SEP (`(data_at sh (tarray tint size) (flip_between j (size-j) contents) a0))).

Lemma flip_fact_0: forall A size (contents: list A),
  Zlength contents = size ->
  contents = flip_between 0 (size - 0) contents.
Proof.
  intros.
  unfold flip_between.
  replace (size-0) with (Zlength contents) by omega.
  rewrite !sublist_nil.
  simpl. rewrite <- app_nil_end.
  rewrite sublist_same by auto.
  auto.
Qed.

Lemma flip_fact_1: forall A size (contents: list A) j,
  Zlength contents = size ->
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  flip_between j (size - j) contents = rev contents.
Proof.
  intros.
  unfold flip_between.
  symmetry.
  replace (sublist j (size-j) contents) with
    (sublist j (size-j) (rev contents)).
  rewrite !sublist_rejoin by (rewrite ?Zlength_rev; omega).
  rewrite sublist_same by (rewrite ?Zlength_rev; omega).
  auto.
  rewrite sublist_rev by omega.
  rewrite len_le_1_rev.
  f_equal. f_equal. omega. omega.
  apply Nat2Z.inj_le. change (Z.of_nat 1) with 1.
  rewrite <- Zlength_correct.
  rewrite Zlength_sublist; omega.
Qed.

Lemma Zlength_flip_between:
 forall A i j (al: list A),
 0 <= i  -> i<=j -> j <= Zlength al ->
 Zlength (flip_between i j al) = Zlength al.
Proof.
intros.
unfold flip_between.
rewrite !Zlength_app, !Zlength_sublist by  (rewrite ?Zlength_rev; omega).
omega.
Qed.


Ltac list_simpl :=
try omega;
repeat 
  (first [ rewrite Zlength_sublist
       | rewrite Zlength_flip_between
       | rewrite Zlength_rev
       | rewrite Zlength_app
       | rewrite Z.min_l by omega
       | rewrite Z.min_r by omega
       | rewrite Z.max_l by omega
       | rewrite Z.max_r by omega
       | rewrite sublist_nil
       | rewrite <- app_nil_end
       | rewrite app_nil_l
       | rewrite Z.add_0_r
       | rewrite Z.sub_0_r 
       | rewrite Z.add_0_l
       | rewrite Z.sub_diag
       | rewrite Z.sub_add];
    try omega).


Lemma flip_fact_3:
 forall A (al: list A) j size,
  size = Zlength al ->
  0 <= j < size - j - 1 ->
sublist 0 j
  (sublist 0 (size - j - 1) (flip_between j (size - j) al) ++
   sublist j (j + 1) (flip_between j (size - j) al) ++
   sublist (size - j - 1 + 1) (Zlength al) (flip_between j (size - j) al)) ++
sublist (size - j - 1) (size - j - 1 + 1) al ++
sublist (j + 1)
  (size - j - 1 - 0 + (j + 1 - j + (Zlength al - (size - j - 1 + 1))))
  (sublist 0 (size - j - 1) (flip_between j (size - j) al) ++
   sublist j (j + 1) (flip_between j (size - j) al) ++
   sublist (size - j - 1 + 1) (Zlength al) (flip_between j (size - j) al)) =
flip_between (Z.succ j) (size - Z.succ j) al.
Proof.
intros.
rewrite <- H.
list_simpl.
replace (size - j - 1 + (j + 1 - j + (size - (size - j ))))
  with size by omega.
unfold Z.succ.
unfold flip_between.
rewrite <- H.
repeat (rewrite sublist_app, ?sublist_sublist; list_simpl).
replace (size - (size - j - 1) - (j + 1 - j) + (size - j) - j - (size - j - j) +
   (size - j))
 with size by omega.
replace (size-(j+1)) with (size-j-1) by omega.
rewrite (sublist_split 0 j (j+1)); list_simpl.
rewrite <- app_assoc.
f_equal.
f_equal.
rewrite sublist_rev; list_simpl.
rewrite Zlen_le_1_rev; list_simpl.
f_equal; omega.
f_equal.
rewrite (sublist_split (size-j-1) (size-j) size); list_simpl.
f_equal.
rewrite sublist_rev; list_simpl.
rewrite Zlen_le_1_rev; list_simpl.
f_equal; list_simpl.
Qed.

Lemma flip_between_map:
  forall A B (F: A -> B) lo hi (al: list A),
   0 <= lo -> lo <= hi -> hi <= Zlength al ->
  flip_between lo hi (map F al) = map F (flip_between lo hi al).
Proof.
intros.
unfold flip_between.
rewrite !map_app.
rewrite !map_sublist, !map_rev, Zlength_map.
auto.
Qed.

Lemma flip_fact_2:
  forall {A} (al: list A) size j d,
 Zlength al = size ->
  j < size - j - 1 ->
   0 <= j ->
  Znth (size - j - 1) al d =
  Znth (size - j - 1) (flip_between j (size - j) al) d.
Proof.
intros.
unfold flip_between.
rewrite app_Znth2
 by (rewrite Zlength_sublist; rewrite ?Zlength_rev; omega).
rewrite Zlength_sublist; rewrite ?Zlength_rev; try omega.
rewrite app_Znth1
 by (rewrite Zlength_sublist; rewrite ?Zlength_rev; omega).
rewrite Znth_sublist by omega.
f_equal; omega.
Qed.

Lemma skipn2sublist:
 forall {A} n (al: list A),
 0 <= n <= Zlength al ->
 skipn (Z.to_nat n) al = sublist n (Zlength al) al.
Proof.
intros.
unfold sublist.
symmetry.
etransitivity; [ | apply (firstn_exact_length (skipn (Z.to_nat n) al))].
f_equal.
apply Nat2Z.inj.
rewrite  <- Zlength_correct.
rewrite Zlength_skipn.
rewrite (Z.max_r 0 n) by omega.
rewrite Z.max_r by omega.
rewrite Z2Nat.id by omega.
auto.
Qed.

Lemma firstn2sublist:
 forall {A} n (al: list A),
 0 <= n <= Zlength al ->
 firstn (Z.to_nat n) al = sublist 0 n al.
Proof.
intros.
unfold sublist.
f_equal.
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
forward. (* hi = n; *)

assert_PROP (Zlength (map Vint contents) = size).
 entailer.
rename H0 into ZL.
forward_while (reverse_Inv a0 sh (map Vint contents) size)
   j.
(* Prove that current precondition implies loop invariant *)
apply exp_right with 0.
entailer!; try omega.
f_equal; f_equal; omega.
apply derives_refl'.
f_equal.
apply flip_fact_0; auto.
(* Prove that loop invariant implies typechecking condition *)
entailer!.
(* Prove that loop body preserves invariant *)
forward. (* t = a[lo]; *)
{
  entailer!.
  clear - H0 H HRE H1.
  rewrite Zlength_map in *.
  rewrite flip_between_map by omega.
  rewrite Znth_map with (d':=Int.zero).
  apply I.
  rewrite Zlength_flip_between by omega.
  omega.
}
forward.  (* s = a[hi-1]; *)
{
  entailer!.
  clear - H0 HRE H1.
  rewrite Zlength_map in *.
  rewrite flip_between_map by omega.
  rewrite Znth_map with (d':=Int.zero).
  apply I.
  rewrite Zlength_flip_between by omega.
  omega.
}
rewrite <- flip_fact_2 by (rewrite ?Zlength_flip_between; omega).
forward. (*  a[hi-1] = t; *)
forward. (* a[lo] = s; *)
forward. (* lo++; *)
forward. (* hi--; *)

(* Prove postcondition of loop body implies loop invariant *)
{
  apply exp_right with (Zsucc j).
 entailer. rewrite prop_true_andp by (f_equal; f_equal; omega).
 apply derives_refl'. clear H5 H4.
 rewrite H3,H2; simpl. rewrite <- H3, <- H2. clear H2 H3 TC.
 unfold data_at.    f_equal.
 clear - H0 H HRE H1.
 remember (Zlength (map Vint contents)) as size.
 forget (map Vint contents) as al.
 repeat match goal with |- context [reptype ?t] => change (reptype t) with val end.
 unfold upd_Znth_in_list.
 rewrite !Znth_cons_sublist by (repeat rewrite Zlength_flip_between; try omega).
 rewrite ?Zlength_app, ?Zlength_firstn, ?Z.max_r by omega.
 rewrite ?Zlength_flip_between by omega.
 rewrite ?Zlength_sublist by (rewrite ?Zlength_flip_between ; omega).
 apply flip_fact_3; auto.
}
(* after the loop *)
forward. (* return; *)
rewrite map_rev. rewrite flip_fact_1 by omega.
auto.
Qed.

Definition four_contents := [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4].

(*
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
*)

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
normalize; intro a; normalize.

forward_call  (*  revarray(four,4); *)
  (a, Ews, four_contents, 4).
   repeat split; try computable; auto.
forward_call  (*  revarray(four,4); *)
    (a,Ews, rev four_contents,4).
   split. computable. auto.
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

