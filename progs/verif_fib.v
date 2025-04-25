Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.progs.fib.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Fixpoint fib_of_nat (n: nat): Z :=
  match n with
  | O => 0
  | S n' =>
    match n' with
    | O => 1
    | S n'' => fib_of_nat n'' + fib_of_nat n'
    end
  end.

Definition fib_of_Z (n: Z): Z := fib_of_nat (Z.to_nat n).

Theorem fib_0: fib_of_Z 0 = 0.
Proof. reflexivity. Qed.

Theorem fib_1: fib_of_Z 1 = 1.
Proof. reflexivity. Qed.

Theorem fib_rec: forall n, n >= 0 -> fib_of_Z (n + 2) = fib_of_Z n + fib_of_Z (n + 1).
Proof.
  intros.
  unfold fib_of_Z. 
  rewrite !Z2Nat.inj_add, !(Nat.add_comm (Z.to_nat n)) by lia.
  reflexivity.
Qed.

Lemma fib_nonneg: forall n, 0 <= fib_of_Z n.
Proof.
  intros.
  unfold fib_of_Z.
  forget (Z.to_nat n) as m; clear.
  assert (0 <= fib_of_nat m /\ 0 <= fib_of_nat (S m)); [| tauto].
  induction m; [simpl; try lia |].
  
  destruct IHm.
  split; [auto |].
  change (fib_of_nat (S (S m))) with (fib_of_nat m + fib_of_nat (S m)).
  lia.
Qed.

Lemma fib_ordered: forall n, 0 <= n -> fib_of_Z n <= fib_of_Z (n + 1).
Proof.
  intros.
  destruct (zeq n 0); [subst; simpl; rewrite fib_0, fib_1; lia |].
  replace (n + 1) with (n - 1 + 2) by lia.
  rewrite fib_rec by lia.
  replace (n - 1 + 1) with n by lia.
  pose proof fib_nonneg (n -1).
  lia.
Qed.

Lemma fib_bound: forall n, 0 <= n < 46 -> 0 <= fib_of_Z n < Int.max_signed.
Proof.
  assert (fib_of_Z 0 = 0 -> fib_of_Z (0 + 1) = 1 -> forall n, 0 <= n < 46 -> 0 <= fib_of_Z n < Int.max_signed);
    [| intros; apply H; auto].
  do 46
  match goal with
  | |- fib_of_Z ?z = ?f0  -> fib_of_Z (?z + 1) = ?f1 -> forall n, ?z <= n < 46 -> _ =>
         let f2 := eval compute in (f0 + f1) in
         assert (fib_of_Z (z + 1) = f1 -> fib_of_Z (z + 2) = f2 -> forall n, z + 1 <= n < 46 ->0 <= fib_of_Z n < Int.max_signed); [
           replace (z + 2) with (z + 1 + 1) by lia |
           intros HH0 HH1; specialize (H HH1 ltac:(rewrite fib_rec by (simpl; lia); rewrite HH0, HH1; reflexivity));
           intros; destruct (zeq z n); [subst n; rewrite HH0; rep_lia | apply H; lia] (*;
           split; [apply fib_nonneg | specialize (H (n + 1) ltac:(lia)); pose proof fib_ordered n; lia]*)
           ]
  end.
  intros; simpl in *. lia.
Qed.

Definition fib_spec fun_id :=
 DECLARE fun_id
  WITH n : Z
  PRE  [ tint ]
     PROP (0 <= n < 45) (* 50th term is too large to be a 32bit int *)
     PARAMS (Vint (Int.repr n))
     SEP ()
  POST [ tint ]
     PROP () RETURN (Vint (Int.repr (fib_of_Z n)))
     SEP ().

Definition Gprog : funspecs :=
         ltac:(with_library prog [ fib_spec _fib_loop; fib_spec _fib_loop_save_var; fib_spec _fib_rec ]).

Lemma body_fib_loop: semax_body Vprog Gprog f_fib_loop (fib_spec _fib_loop).
Proof.
  start_function.
  forward.  (* a0 = 0; *)
  forward.  (* a1 = 1; *)
  forward_for_simple_bound n
    (EX i: Z,
    (PROP ()
     LOCAL (temp _a1 (Vint (Int.repr (fib_of_Z (i + 1)))); temp _a0 (Vint (Int.repr (fib_of_Z i))); temp _n (Vint (Int.repr n)))
     SEP ())).
  { (* Prove that loop invariant implies typechecking of loop condition *)
    entailer!!.
  }
  { (* Prove that loop body preserves invariant *)
    assert (0 <= fib_of_Z i < Int.max_signed /\
            0 <= fib_of_Z (i + 1) < Int.max_signed /\
            0 <= fib_of_Z i + fib_of_Z (i + 1) < Int.max_signed) as [R0 [R1 R2]].
    {
      rewrite <- fib_rec by lia.
      split; [| split]; apply fib_bound; lia.
    }
    forward. (* a2 = a0 + a1; *)
    forward. (* a0 = a1; *)
    forward. (* a1 = a2; *)
    entailer!!.
    rewrite <- fib_rec by lia.
    do 3 f_equal; lia.
  }
  forward. (* return a0; *)
Qed.

Lemma body_fib_rec: semax_body Vprog Gprog f_fib_rec (fib_spec _fib_rec).
Proof.
  start_function.
  forward_if.
  { forward. }
  forward_if.
  { forward. }
  forward_call (n - 2).
  forward_call (n - 1).
  assert (0 <= fib_of_Z (n - 2) < Int.max_signed /\
          0 <= fib_of_Z (n - 1) < Int.max_signed /\
          0 <= fib_of_Z (n - 2) + fib_of_Z (n - 1) < Int.max_signed) as [R0 [R1 R2]].
  {
    replace (n - 1) with (n - 2 + 1) at 3 4 by lia.
    rewrite <- fib_rec by lia.
    split; [| split]; apply fib_bound; lia.
  }
  forward.
  entailer!!.
  replace (n - 1) with (n - 2 + 1) by lia.
  rewrite <- fib_rec by lia.
  do 3 f_equal; lia.
Qed.

Lemma body_fib_loop_save_var: semax_body Vprog Gprog f_fib_loop_save_var (fib_spec _fib_loop_save_var).
Proof.
  start_function.
  forward.  (* a0 = 0; *)
  forward.  (* a1 = 1; *)
  forward_loop
    (EX i: Z,
    (PROP (0 <= i <= n)
     LOCAL (temp _a1 (Vint (Int.repr (fib_of_Z (i + 1))));
            temp _a0 (Vint (Int.repr (fib_of_Z i)));
            temp _n (Vint (Int.repr (n - i))))
     SEP ()))
  break:
    (PROP ()
     LOCAL (temp _a0 (Vint (Int.repr (fib_of_Z n))))
     SEP ()).
  { (* Prove that the precon implies the loop invariant *)
    Exists 0.
    entailer!.
  }
  { (* Prove that loop body preserves invariant *)
    Intros i.
    forward_if.
    2:{ (* Else branch *)
      forward. (* break; *)
      assert (i = n) by lia.
      entailer!!.
    }
    (* Then branch and other loop body *)
    assert (0 <= fib_of_Z i < Int.max_signed /\
            0 <= fib_of_Z (i + 1) < Int.max_signed /\
            0 <= fib_of_Z i + fib_of_Z (i + 1) < Int.max_signed) as [R0 [R1 R2]].
    {
      rewrite <- fib_rec by lia.
      split; [| split]; apply fib_bound; lia.
    }
    forward. (* a1 = a0 + a1; *)
    forward. (* a0 = a1 - a0; *)
    forward. (* -- n *)
    Exists (i + 1).
    entailer!!.
    split3.
    + rewrite <- fib_rec by lia.
      do 3 f_equal; lia.
    + do 2 f_equal; lia.
    + do 2 f_equal; lia.
  }
  forward. (* return a0; *)
Qed.
