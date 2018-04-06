Require Import VST.sepcomp.semantics.

Require Import VST.compcert.lib.Coqlib.
Require Import VST.compcert.lib.Maps.
Require Import VST.compcert.lib.Integers.
Require Import VST.compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.sepcomp.mem_lemmas.


(** *I'm overloading the definition of coresemantics. **)
(* Bellow, I produce a way of lifting the old coresemantics to the new one. *)
(* This is bad design and should be changed. *)
Record ThreadSemantics {G C M : Type} : Type :=
  { (*nat is thread id. It should not be seen by the code.*)
    initial_core : nat -> G -> val -> list val -> option C 
  ; at_external : C -> option (external_function * list val)
  ; after_external : option val -> C -> option C
  ; halted : C -> option val
  ; corestep : G -> C -> M -> C -> M -> Prop

  ; corestep_not_at_external:
      forall ge m q m' q', corestep ge q m q' m' -> at_external q = None
  ; corestep_not_halted:
      forall ge m q m' q', corestep ge q m q' m' -> halted q = None
  ; at_external_halted_excl:
      forall q, at_external q = None \/ halted q = None }.

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
Record MemSem {G C} :=
  { csem :> @CoreSemantics G C mem

  ; corestep_mem : forall g c m c' m' (CS: corestep csem g c m c' m'), mem_step m m'
  (*later, we'll want to add the following constraint
  ; corestep_incr_perm: forall g c m c' m' (CS: corestep csem g c m c' m')  m1 (PLE: perm_lesseq m m1),
         exists m1', corestep csem g c m1 c' m1' /\ perm_lesseq m' m1'*)
  }.

Arguments MemSem : clear implicits.
