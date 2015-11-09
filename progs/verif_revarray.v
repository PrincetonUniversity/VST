Require Import floyd.proofauto.
Require Import progs.revarray.
Require Import floyd.sublist.

Local Open Scope logic.

Definition CompSpecs' : compspecs.
Proof. make_compspecs1 prog. Defined.
Instance CompSpecs : compspecs.
Proof. make_compspecs2 CompSpecs'. Defined.

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

Definition flip_ends {A} lo hi (contents: list A) :=
  sublist 0 lo (rev contents)
  ++ sublist lo hi contents
  ++ sublist hi (Zlength contents) (rev contents).

Definition reverse_Inv a0 sh contents size := 
 EX j:Z,
  (PROP  (0 <= j; j <= size-j)
   LOCAL  (temp _a a0; temp _lo (Vint (Int.repr j)); temp _hi (Vint (Int.repr (size-j))))
   SEP (`(data_at sh (tarray tint size) (flip_ends j (size-j) contents) a0))).


Lemma Zlength_flip_ends:
 forall A i j (al: list A),
 0 <= i  -> i<=j -> j <= Zlength al ->
 Zlength (flip_ends i j al) = Zlength al.
Proof.
intros.
unfold flip_ends.
autorewrite with sublist. omega.
Qed.
Hint Rewrite @Zlength_flip_ends using (autorewrite with sublist; omega) : sublist.

Lemma flip_fact_1: forall A size (contents: list A) j,
  Zlength contents = size ->
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  flip_ends j (size - j) contents = rev contents.
Proof.
  intros.
  unfold flip_ends.
  rewrite <- (Zlen_le_1_rev (sublist j (size-j) contents))
      by (autorewrite with sublist; omega).
  rewrite !sublist_rev by (autorewrite with sublist; omega).
 rewrite <- !rev_app_distr, ?H.
 autorewrite with sublist; auto. 
Qed.

Lemma flip_fact_3:
 forall A (al: list A) j size,
  size = Zlength al ->
  0 <= j < size - j - 1 ->
sublist 0 j (flip_ends j (size - j) al) ++
sublist (size - j - 1) (size - j) al ++
sublist (j + 1) size
  (sublist 0 (size - j - 1) (flip_ends j (size - j) al) ++
   sublist j (j + 1) (flip_ends j (size - j) al) ++
   sublist (size - j) size (flip_ends j (size - j) al)) =
flip_ends (j + 1) (size - (j + 1)) al.
Proof.
intros.
unfold flip_ends.
rewrite <- H.
autorewrite with sublist.
rewrite (sublist_split 0 j (j+1)) by (autorewrite with sublist; omega).
rewrite !app_ass.
f_equal. f_equal.
rewrite !sublist_rev, <- ?H by omega.
rewrite Zlen_le_1_rev by (autorewrite with sublist; omega).
f_equal; omega.
rewrite (sublist_app2 (size-j) size)
 by (autorewrite with sublist; omega).
autorewrite with sublist.
rewrite sublist_app'
 by (autorewrite with sublist; omega).
autorewrite with sublist.
f_equal.
f_equal; omega.
autorewrite with sublist.
  rewrite <- (Zlen_le_1_rev (sublist j (1+j) al))
      by (autorewrite with sublist; omega).
rewrite !sublist_rev, <- ?H by omega.
 rewrite <- !rev_app_distr, <- ?H.
 autorewrite with sublist.
 f_equal; f_equal; omega.
Qed.

Lemma flip_ends_map:
  forall A B (F: A -> B) lo hi (al: list A),
  flip_ends lo hi (map F al) = map F (flip_ends lo hi al).
Proof.
intros.
unfold flip_ends.
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
  Znth (size - j - 1) (flip_ends j (size - j) al) d.
Proof.
intros.
unfold flip_ends.
autorewrite with sublist. auto.
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

assert_PROP (Zlength (map Vint contents) = size)
    as ZL by entailer!.
forward_while (reverse_Inv a0 sh (map Vint contents) size)
   j.
* (* Prove that current precondition implies loop invariant *)
Exists 0.
entailer!.
+ f_equal; f_equal; omega.
+ unfold flip_ends; autorewrite with sublist; auto.
* (* Prove that loop invariant implies typechecking condition *)
entailer!.
* (* Prove that loop body preserves invariant *)
forward. (* t = a[lo]; *)
{
  entailer!.
  clear - H0 HRE.
  autorewrite with sublist in *|-*.
  rewrite flip_ends_map.
  rewrite Znth_map with (d':=Int.zero)
   by (autorewrite with sublist; omega).
  apply I.
}
forward.  (* s = a[hi-1]; *)
{
  entailer!.
  clear - H0 HRE.
  autorewrite with sublist in *|-*.
  rewrite flip_ends_map.
  rewrite Znth_map with (d':=Int.zero)
   by (autorewrite with sublist; omega).
  apply I.
}
rewrite <- flip_fact_2 by (rewrite ?Zlength_flip_ends; omega).
forward. (*  a[hi-1] = t; *)
forward. (* a[lo] = s; *)
forward. (* lo++; *)
forward. (* hi--; *)

(* Prove postcondition of loop body implies loop invariant *)
 Exists (Zsucc j).
 entailer!.
 f_equal; f_equal; omega.
 apply derives_refl'.
 unfold data_at.    f_equal.
 rewrite H3,H2; simpl. rewrite <- H3, <- H2.
 clear - H0 HRE H1.
 forget (map Vint contents) as al.
 remember (Zlength al) as size.
 repeat match goal with |- context [reptype ?t] => change (reptype t) with val end.
 unfold upd_Znth_in_list.
 rewrite !Znth_cons_sublist by (repeat rewrite Zlength_flip_ends; try omega).
 rewrite ?Zlength_app, ?Zlength_firstn, ?Z.max_r by omega.
 rewrite ?Zlength_flip_ends by omega.
 rewrite ?Zlength_sublist by (rewrite ?Zlength_flip_ends ; omega).
 unfold Z.succ. rewrite <- Heqsize. autorewrite with sublist.
 replace (size - j - 1 + (1 + j)) with size by (clear; omega).
 apply flip_fact_3; auto.

* (* after the loop *)
forward. (* return; *)
rewrite map_rev. rewrite flip_fact_1 by omega.
auto.
Qed.

Definition four_contents := [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name four _four.
start_function.

forward_call  (*  revarray(four,4); *)
  (four, Ews, four_contents, 4).
   split; [computable | auto].
forward_call  (*  revarray(four,4); *)
    (four,Ews, rev four_contents,4).
   split; [computable | auto].
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

