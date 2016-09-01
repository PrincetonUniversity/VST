From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.
      
Require Import Coq.ZArith.ZArith.

Require Import compcert.common.Memory.

Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.

Require Import concurrency.konig.


Definition closed (P:ST -> SCH -> Prop):=
  forall st U1 U2, P st U1 -> valid st U2 -> P st U2.

   
Inductive R' (P P': ST -> SCH -> Prop): Prop:=
|blah' :
    (forall st U, P st U -> exists st' U', STEP st U st' U' /\ P' st' U') ->
    (forall st' U', P' st' U' -> exists U st, P st U /\ STEP st U st' U') ->
    closed P' ->
          R' P P'.