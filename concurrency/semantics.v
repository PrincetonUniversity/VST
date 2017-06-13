From mathcomp.ssreflect Require Import ssreflect seq ssrbool.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.
Require Import sepcomp.semantics.
Require Import sepcomp.event_semantics.

Require Import concurrency.machine_semantics.
Require Import concurrency.permissions.
Require Import concurrency.addressFiniteMap.

Require Import concurrency.scheduler.
Require Import Coq.Program.Program.

Module Type Semantics.
  (*Parameter F V : Type. *)
  Parameter G: Type.
  Parameter C: Type.
  Parameter Sem: @EvSem G C.
  (* Parameter getEnv : G -> Genv.t F V. *)
End Semantics.

Module Type Resources.
  Parameter res : Type.
  Parameter lock_info : Type.
End Resources.

(** *The record version*)
Record Semantics_rec:=
  {
  (* semF: Type ;
  semV: Type; *)
  semG: Type;
  semC: Type;
  semSem: @EvSem semG semC;
   (* getEnv : semG -> Genv.t semF semV *)
  }.

Record Resources_rec:=
  {
    recres: Type;
    reclock_info : Type
    }.