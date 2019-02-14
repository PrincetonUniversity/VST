Require Import VST.floyd.proofauto.
Require Import VST.progs.revarray.
Require Import VST.floyd.sublist.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition reverse_spec :=
 DECLARE _reverse
  WITH a0: val, sh : share, contents : list int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed; writable_share sh)
          LOCAL (temp _a a0; temp _n (Vint (Int.repr size)))
          SEP (data_at sh (tarray tint size) (map Vint contents) a0)
  POST [ tvoid ]
     PROP() LOCAL()
     SEP(data_at sh (tarray tint size) (map Vint (rev contents)) a0).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [reverse_spec; main_spec]).

Definition flip_ends {A} lo hi (contents: list A) :=
  sublist 0 lo (rev contents)
  ++ sublist lo hi contents
  ++ sublist hi (Zlength contents) (rev contents).

Definition reverse_Inv a0 sh contents size :=
 (EX j:Z,
  (PROP  (0 <= j; j <= size-j)
   LOCAL  (temp _a a0; temp _lo (Vint (Int.repr j)); temp _hi (Vint (Int.repr (size-j))))
   SEP (data_at sh (tarray tint size) (flip_ends j (size-j) contents) a0)))%assert.

Hint Rewrite @Znth_rev using Zlength_solve : Znth_solve.
Hint Rewrite Zlength_rev using Zlength_solve : Zlength.

Ltac dup :=
    match goal with
    | |- ?Goal => assert Goal
    end;
    only 2:
    match goal with
    | H : ?Goal |- ?Goal => clear H
    end.

Goal 
  forall j contents,
    (1 + BIG = BIG1)%nat /\Zlength (sublist 0 j (rev (map Vint contents))) +
Zlength
  (sublist j (Zlength (map Vint contents) - j) (map Vint contents) ++
   sublist (Zlength (map Vint contents) - j) (Zlength (map Vint contents)) (rev (map Vint contents))) =
Zlength (map Vint (rev contents)).
Proof.
  intros.
  split.
  auto.
  Set Ltac Profiling.
  do 6 dup;
  rewrite Zlength_app.
  Show Ltac Profile.

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function.
repeat step.

assert_PROP (Zlength (map Vint contents) = size)
    as ZL by entailer!.
forward_while (reverse_Inv a0 sh (map Vint contents) size).
* (* Prove that current precondition implies loop invariant *)
admit.
* (* Prove that loop invariant implies typechecking condition *)
admit.
* (* Prove that loop body preserves invariant *)
(* unfold flip_ends. *) (* seems good to do this, but it makes step VERY slow *)
admit.
* (* after the loop *)
forward. (* return; *)
apply data_at_data_at_cancel. unfold flip_ends.
autorewrite with Zlength in * |-.
apply (Znth_eq_ext _ Inhabitant_val).
Require Import Coq.Program.Tactics.
Ltac Zlength_solve ::= show_goal; autorewrite with Zlength; pose_Zlength_nonneg; omega.
clear.

  Set Ltac Profiling.
  do 6 dup;
  rewrite Zlength_app.
  Show Ltac Profile.
Set Ltac Profiling.
rewrite Zlength_app.
rewrite Zlength_app.
rewrite Zlength_sublist by Zlength_solve.
Show Ltac Profile.
 by Zlength_solve.
  Zlength_solve.
Time Zlength_solve. (* example of slow rewrite *)
autorewrite with Zlength in *.
intros.
Znth_solve.
- do 2 f_equal. omega.
- do 2 f_equal. omega.
- do 2 f_equal. omega.
Time Qed.
(* Finished transaction in 53.902 secs (53.859u,0.s) (successful) *)

Definition four_contents := [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name four _four.
start_function.

forward_call  (*  revarray(four,4); *)
  (gv _four, Ews, four_contents, 4).
   split; [computable | auto].
forward_call  (*  revarray(four,4); *)
    (gv _four,Ews, rev four_contents,4).
   split; [computable | auto].
rewrite rev_involutive.
forward. (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_reverse.
semax_func_cons body_main.
Qed.
