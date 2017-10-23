From mathcomp.ssreflect Require Import ssreflect seq ssrbool.
Require Import sepcomp.semantics.
Require Import sepcomp.event_semantics.

Require Import concurrency.machine_semantics.

(** *The record version*)
Class Semantics:=
  {
    (* semF: Type ;
  semV: Type; *)
    semG: Type;
    semC: Type;
    semSem: @EvSem semG semC;
    (* getEnv : semG -> Genv.t semF semV *)
  }.

Class Resources:=
  {
    res: Type;
    lock_info : Type
  }.