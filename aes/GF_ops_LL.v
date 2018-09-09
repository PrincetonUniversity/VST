Require Import ZArith.
Local Open Scope Z_scope.
Require Import compcert.lib.Integers.

Fixpoint repeat_op_nat{T: Type}(n: nat)(start: T)(op: T -> T): T := match n with
| O => start
| S m => op (repeat_op_nat m start op)
end.

Definition repeat_op{T: Type}(n: Z)(start: T)(op: T -> T): T := repeat_op_nat (Z.to_nat n) start op.

Lemma repeat_op_step: forall {T: Type} (i: Z) (start: T) (op: T -> T),
  0 <= i ->
  repeat_op (i + 1) start op = op (repeat_op i start op).
Proof.
  intros. unfold repeat_op. rewrite Z2Nat.inj_add by omega.
  rewrite Nat.add_1_r. simpl. reflexivity.
Qed.

Definition times2(x: int): int := 
  Int.and
    (Int.xor (Int.shl x (Int.repr 1))
             (if Int.eq (Int.and x (Int.repr 128)) Int.zero then Int.zero else Int.repr 27))
    (Int.repr 255).

Definition pow2(e: Z): int := repeat_op e (Int.repr 1) times2.

Definition times3(x: int): int := 
  Int.and
    (Int.xor x (Int.xor (Int.shl x (Int.repr 1))
                        (if Int.eq (Int.and x (Int.repr 128)) Int.zero then Int.zero else Int.repr 27)))
    (Int.repr 255).

Definition pow3(e: Z): int := repeat_op e (Int.repr 1) times3.

Fixpoint log3_nat(p: int)(n: nat): Z :=
  if Int.eq p (pow3 (Z.of_nat n)) then Z.of_nat n
  else match n with
  | O => -1 (* illegal argument *)
  | S m => log3_nat p m
  end.

(* Note: For (log3 1), we have two possible return values: 0 and 255.
   We choose 255, because then both the domain and the codomain of log3 are 1..255. *)
Definition log3(p: int): Z := log3_nat p 255.

Definition mul(x y: int): int :=
  if Int.eq x Int.zero then Int.zero else
  if Int.eq y Int.zero then Int.zero else
  pow3 (Int.unsigned (Int.mods (Int.repr (log3 x + log3 y)) (Int.repr 255))).

Lemma pow3_not0: forall i, pow3 i <> Int.zero.
Admitted.

Lemma pow3log3: forall j,
  1 <= j < 256 ->
  Int.unsigned (pow3 (log3 (Int.repr j))) = j.
Admitted.

Lemma log3range: forall j,
  1 <= j < 256 ->
  1 <= log3 (Int.repr j) < 256.
Admitted.

Lemma mod_range: forall i m,
  0 <= i ->
  0 < m ->
  0 <= Int.unsigned (Int.mods (Int.repr i) (Int.repr m)) < m.
Admitted.

Lemma pow2_range: forall e,
  0 <= e ->
  0 <= Int.unsigned (pow2 e) < 256.
Admitted.

Lemma pow3_range: forall e,
  0 <= e ->
  0 <= Int.unsigned (pow3 e) < 256.
Admitted.

Lemma pow3_inj: forall (i j : Z),
  pow3 i = pow3 j -> Int.eqmod 255 i j.
Admitted.

Lemma invert_pow3: forall i,
  1 <= i < 256 ->
  exists j, 1 <= j < 256 /\ i = (Int.unsigned (pow3 j)).
Admitted.
