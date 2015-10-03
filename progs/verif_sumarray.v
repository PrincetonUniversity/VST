Require Import floyd.proofauto.
Require Import progs.sumarray.
Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.

Definition force_option {A} (x:A) (i: option A) := 
  match i with Some y => y | None => x end.

Definition sum_int := fold_right Int.add Int.zero.
  

Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a0: val, sh : share, contents : list int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed)
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
   PROP  (0 <= i <= size)
   LOCAL (temp _a a0; 
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (sum_int (sublist 0 i contents))))
   SEP   (`(data_at sh (tarray tint size) (map Vint contents) a0)).

Lemma Znth_overflow: (*  move to floyd/sublist.v *)
  forall {A} i (al: list A) d, i >= Zlength al -> Znth i al d = d.
Proof.
intros.
  pose proof (Zlength_nonneg al).
   unfold Znth. rewrite if_false by omega.
  apply nth_overflow.
  apply Nat2Z.inj_le. rewrite <- Zlength_correct.
  rewrite Z2Nat.id by omega. omega.
Qed.

Lemma sublist_one: (*  move to floyd/sublist.v *)
  forall {A} lo hi (al: list A) d, 
    0 <= lo -> hi <= Zlength al ->
    lo+1=hi -> sublist lo hi al = Znth lo al d :: nil.
Proof.
intros.
subst.
rewrite Znth_cons_sublist by omega. rewrite <- app_nil_end.
auto.
Qed.

Lemma add_one_more_to_sum: forall contents i x,
  Znth i (map Vint contents) Vundef = Vint x ->
  0 <= i ->
  sum_int (sublist 0 (Z.succ i) contents) =
   Int.add (sum_int (sublist 0 i contents)) x.
Proof.
  intros.
  destruct (zlt i (Zlength contents));
   [ | rewrite Znth_overflow in H by (rewrite Zlength_map; omega); inv H].
  rewrite Int.add_commut.
  rewrite (sublist_split 0 i (Z.succ i)) by omega.
  rewrite (sublist_one i (Z.succ i) contents) with (d:=Int.zero) by omega. 
  rewrite Znth_map with (d':=Int.zero) in H by omega.
  injection H; intro. rewrite H1. clear.
  induction (sublist 0 i contents); simpl; auto.
  rewrite IHl.
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
forward_while (sumarray_Inv a0 sh contents size)
     a1.
(* Prove that current precondition implies loop invariant *)
apply exp_right with 0.
entailer!.
(* Prove that loop invariant implies typechecking condition *)
entailer!.
(* Prove postcondition of loop body implies loop invariant *)
forward. (* x = a[i] *)
entailer!.
  (* there should be an easier way than this: *)
   rewrite Znth_map with (d':=Int.zero). apply I.
  rewrite Zlength_map in *; omega.
forward. (* s += x; *)
forward. (* i++; *)
  apply exp_right with (Zsucc a1).
 entailer!. rewrite H2 in H1; inv H1.
 f_equal; apply add_one_more_to_sum; try omega; auto.
(* After the loop *)
forward.  (* return s; *)
entailer!.
rewrite Zlength_map in *.
rewrite sublist_same by omega.
reflexivity.
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
forward_intro four. normalize.
forward_call (*  r = sumarray(four,4); *)
  (four,Ews,four_contents,4) vret.
 split; auto. computable. 
 forward. (* return s; *)
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

