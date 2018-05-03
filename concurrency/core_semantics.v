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


(** * Core Semantics *)

Record CoreSemantics {C M : Type} : Type :=
  { initial_core : nat -> M -> C -> val -> list val -> Prop
  ; at_external : C -> M -> option (external_function * signature * list val)
  ; after_external : option val -> C -> M -> option C
  ; halted : C -> int -> Prop
  ; corestep : C -> M -> C -> M -> Prop

  
  ; corestep_not_halted:
      forall m q m' q' i, corestep q m q' m' -> ~ halted q i
  ; corestep_not_at_external:
      forall m q m' q', corestep q m q' m' -> at_external q m = None }.

(* Extract a CoreSemantics from a part_semantics*)
Inductive step2corestep (sem:part_semantics):(state sem) -> mem -> (state sem) -> mem -> Prop :=
  coreify: forall s1 m1 t s2 m2,
    step sem (set_mem s1 m1) t (set_mem s2 m2) ->
    Smallstep.at_external sem (set_mem s1 m1) = None ->
    step2corestep sem s1 m1 s2 m2.
    
Program Definition sem2coresem (sem:part_semantics) corestep_not_halted : CoreSemantics:=
  {|
    initial_core := fun _:nat => entry_point sem
    ; at_external := fun s m => Smallstep.at_external sem (set_mem s m) 
    ; after_external := Smallstep.after_external sem
    ; halted:= final_state sem
    ; corestep := step2corestep sem
    ; corestep_not_halted:=corestep_not_halted
|}.
Next Obligation.
  inv H; auto.
Qed.


Arguments CoreSemantics : clear implicits.

Inductive mem_step m m' : Prop :=
    mem_step_storebytes: forall b ofs bytes,
       Mem.storebytes m b ofs bytes = Some m' -> mem_step m m'
  | mem_step_alloc: forall lo hi b',
       Mem.alloc m lo hi = (m',b') -> mem_step m m'
  | mem_step_freelist: forall l,
       Mem.free_list m l = Some m' -> mem_step m m'
  (*Some non-observable external calls are not a single alloc/free/store-step*)
  | mem_step_trans: forall m'',
       mem_step m m'' -> mem_step m'' m' -> mem_step m m'.

Local Notation "a # b" := (PMap.get b a) (at level 1).
Record perm_lesseq (m m': mem):= {
  perm_le_Cur:
    forall b ofs, Mem.perm_order'' ((Mem.mem_access m')#b ofs Cur) ((Mem.mem_access m)#b ofs Cur)
; perm_le_Max:
    forall b ofs, Mem.perm_order'' ((Mem.mem_access m')#b ofs Max) ((Mem.mem_access m)#b ofs Max)
; perm_le_cont:
    forall b ofs, Mem.perm m b ofs Cur Readable ->
     ZMap.get ofs (Mem.mem_contents m') !! b= ZMap.get ofs (Mem.mem_contents m) !! b
; perm_le_nb: Mem.nextblock m = Mem.nextblock m'
}.


(* Memory semantics are CoreSemantics that are specialized to CompCert memories
   and evolve memory according to mem_step. Previous notion CoopCoreSem is deprecated,
   but for now retained in file CoopCoreSem.v *)
Record MemSem {C} :=
  { csem :> @CoreSemantics C mem

  ; corestep_mem : forall c m c' m' (CS: corestep csem c m c' m'), mem_step m m'
  (*later, we'll want to add the following constraint
  ; corestep_incr_perm: forall g c m c' m' (CS: corestep csem g c m c' m')  m1 (PLE: perm_lesseq m m1),
         exists m1', corestep csem g c m1 c' m1' /\ perm_lesseq m' m1'*)
  }.

Arguments MemSem : clear implicits.
