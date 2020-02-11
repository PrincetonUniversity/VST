Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.

Require Export VST.sepcomp.semantics.

Definition is_a_sync (name:string):=
  match name with
  | "create"%string | "free"%string |
  "mklock"%string | "release"%string | "acquire"%string => true
      | _ => false
end.

Definition at_sync
  (sem : Smallstep.part_semantics) (st : Smallstep.state sem):
    option (prod AST.external_function (list val)):=
  match Smallstep.at_external sem st with
  | Some ( EF_external name sig, args) =>
    if is_a_sync name then  Some ( EF_external name sig, args) else None
  | _ => None  
  end.
Lemma at_sync_None:
  forall sem st,
    Smallstep.at_external sem st = None ->
    at_sync sem st = None.
Proof. intros. unfold at_sync. rewrite H; auto. Qed.
Lemma at_sync_Some:
  forall sem st X,
    at_sync sem st = Some X ->
    Smallstep.at_external sem st = Some X.
Proof. intros. unfold at_sync in H. repeat match_case in H. Qed.

(* Extract a CoreSemantics from a part_semantics*)
Inductive step2corestep (sem:part_semantics):(state sem) -> mem -> (state sem) -> mem -> Prop :=
  coreify: forall s1 m1 t s2,
    step sem (set_mem s1 m1) t s2 ->
    Smallstep.at_external sem (set_mem s1 m1) = None ->
    step2corestep sem s1 m1 s2 (get_mem s2).
    
Program Definition sem2coresem (sem:part_semantics) corestep_not_halted : CoreSemantics _ _:=
  {|
    initial_core := fun _ m c m' f args => entry_point sem m c f args /\ get_mem c = m'
    ; at_external := fun s m => Smallstep.at_external sem (set_mem s m) 
    ; after_external := Smallstep.after_external sem
    ; halted:= final_state sem
    ; corestep := step2corestep sem
    ; corestep_not_halted:=corestep_not_halted
|}.
Next Obligation.
  inv H; auto.
Qed.
