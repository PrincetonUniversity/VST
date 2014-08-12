Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import compcert. Import CompcertCommon.
Require Import core_semantics.

(* This file demonstrates one method for building "Gallina" core          *)
(* semantics.  That is, core semantics for which the step relation is     *)
(* just a Gallina relation.                                               *)
(*                                                                        *)
(* Below, I specialize to the "assertion" case, in which we inspect the   *)
(* external function name, external function arguments and memory at the  *)
(* point of an external call but leave the memory unchanged (m=m') and    *)
(* always return the same value (Vzero) to the caller. The more general   *)
(* case (in which the Gallina relation determines the input/output        *)
(* relation on m/m') is just as easy to build.                            *)

Definition gallinaObs := forall (v : val) (args : list val) (m : mem), Prop.

Definition gallinaGenv := Genv.t unit unit.

Definition gallinaState := option (gallinaObs*val*list val)%type.

Section gallinaSem.

Variable history_oblivious_obs : gallinaObs.

Definition gallina_init (ge : gallinaGenv) (v : val) (vs : list val) 
  : option gallinaState := Some (Some (history_oblivious_obs,v,vs)).

Definition gallina_at_external (c : gallinaState) 
  : option (external_function * signature * seq val)
  := None.

Definition gallina_after_external (ov : option val) (c : gallinaState) 
  : option gallinaState
  := None.

Definition gallina_halted (c : gallinaState) : option val 
  := match c with
       | None => Some Vzero
       | Some _ => None
     end.

Definition gallina_corestep (ge : gallinaGenv) 
    (c : gallinaState) m (c' : gallinaState) m' :=
  [/\ c'=None, m'=m
    & exists obs v vs, [/\ c = Some (obs,v,vs) & obs v vs m]].

Program Definition gallinaSem : CoreSemantics gallinaGenv gallinaState mem :=
  Build_CoreSemantics _ _ _
    gallina_init gallina_at_external gallina_after_external
    gallina_halted gallina_corestep
    _ _ _.
Next Obligation. by case: H=> eq eq' []obs []v []vs []->. Qed.

End gallinaSem.