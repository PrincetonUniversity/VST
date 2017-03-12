Load loadpath.
Require Import veristar.LibTactics.

(** LibTactics1:
a couple extra tactics for writing Ssreflect-style proofs *)

Ltac terminator := auto.

(**
Ssreflect-style apply; note that use of LibTactics rapply here *)

Tactic Notation "app" :=
  let H := fresh "H" in
    introv H; rapply H; clear H; terminator.

(** tapp:
apply a term T to the top goal *)

Tactic Notation "tapp" constr(T) :=
  let H := fresh "H" in
    introv H; apply T in H; gen H; terminator.

(** tinv:
invert the top goal as intro pattern I1 *)

Tactic Notation "tinv" simple_intropattern(I1) :=
  let H := fresh "H" in
    introv H; inverts H as I1; terminator.

Tactic Notation "tinv0" :=
  let H := fresh "H" in
    introv H; inverts H; terminator.

(** tcase:
case eliminate the top goal as intro pattern I1 *)

Tactic Notation "tcase" simple_intropattern(I1) :=
  let H := fresh "H" in
    intro H; destruct H as I1; terminator.

Tactic Notation "tcase0" :=
  let H := fresh "H" in
    intro H; destruct H; terminator.

(** telim:
eliminate an inductive on the top of the goal stack as intro pattern I1 *)

Tactic Notation "telim" simple_intropattern(I1) :=
  let H := fresh "H" in
    intro H; induction H as I1; terminator.

Tactic Notation "telim0" :=
  let H := fresh "H" in
    intro H; induction H; terminator.

(** done0:
solve the goal immediately, or fail; modeled after Ssreflect "done" *)

Tactic Notation "done0" :=
  trivial; hnf; intros; solve
    [ do 25 (idtac; [solve [trivial | apply sym_equal; trivial]
                    | discriminate | contradiction | split])
    | assumption
    | false
    | terminator
    | constructor ].

(** done:
solve the goal immediately using tactic T, or fail; modeled after
Ssreflect "by" *)

Tactic Notation "done" tactic(T) :=
  T; done0.




