Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import juicy_mem.
Require Import juicy_extspec.

Require Import pos.
Require Import linking. 

Section safety.

Variable N : pos.

Variable plt : ident -> option 'I_N.

Variable sems : 'I_N -> Modsem.t juicy_mem.

Notation linked := (LinkerSem.coresem N sems plt).

Variable Z : Type.

Variable spec : external_specification juicy_mem external_function Z.

Variable ge : ge_ty.

Variable all_safe : 
  forall (entry_point : ident) idx,
  plt entry_point = Some idx -> 

End safety.  