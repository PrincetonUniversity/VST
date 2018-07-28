From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Set Implicit Arguments.

(* tactics to support Omega for ssrnats*)
Ltac arith_hypo_ssrnat2coqnat :=
  match goal with
    | H : context [andb _ _] |- _ => let H0 := fresh in case/andP: H => H H0
    | H : context [orb _ _] |- _ => case/orP: H => H
    | H : context [?L <= ?R] |- _ => move/leP: H => H
    | H : context [?L < ?R] |- _ => move/ltP : H => H
    | H : context [?L == ?R] |- _ => move/eqP : H => H
    | H : context [addn ?L ?R] |- _ => rewrite -plusE in H
    | H : context [muln ?L ?R] |- _ => rewrite -multE in H
    | H : context [subn ?L ?R] |- _ => rewrite -minusE in H
  end.

Ltac arith_goal_ssrnat2coqnat :=
  rewrite ?NatTrec.trecE -?plusE -?minusE -?multE -?leqNgt -?ltnNge;
  repeat match goal with
           | |- is_true (andb _ _) => apply/andP; split
           | |- is_true (orb _ _) => try apply/orP
           | |- is_true (_ <= _) => try apply/leP
           | |- is_true (_ < _) => try apply/ltP
         end.

Ltac ssromega :=
  repeat arith_hypo_ssrnat2coqnat;
  arith_goal_ssrnat2coqnat; simpl;
  omega.
