From mathcomp.ssreflect Require Import ssreflect seq ssrbool.
Require Import VST.concurrency.common.core_semantics.
Require Import VST.sepcomp.event_semantics.

Require Import VST.concurrency.common.machine_semantics.

(** *The typeclass version*)
Class Semantics:=
  {
    (* semF: Type ;
  semV: Type; *)
    semG: Type;
    semC: Type;
    semSem: @EvSem semC;
    (* getEnv : semG -> Genv.t semF semV *)
    the_ge: semG
  }.

Class Resources:=
  {
    res: Type;
    lock_info : Type
  }.

(** The Module version *)

Module Type SEMANTICS.
  Parameter G : Type.
  Parameter C : Type.
  Parameter SEM : @EvSem C.
End SEMANTICS.
