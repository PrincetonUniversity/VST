Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.sepcomp.mem_lemmas.

(** * Interaction Semantics *)

(** NOTE: In the code, we call interaction semantics [CoreSemantics]. *)

(** The [G] type parameter is the type of global environments, the type
   [C] is the type of core states, and the type [E] is the type of
   extension requests. *)

(** [at_external] gives a way to determine when the sequential
   execution is blocked on an extension call, and to extract the
   data necessary to execute the call. *)

(** [after_external] give a way to inject the extension call results
   back into the sequential state so execution can continue. *)

(** [initial_core] produces the core state corresponding to an entry
   point of a module.  The arguments are the genv, a pointer to the
   function to run, and the arguments for that function. *)

(** [halted] indicates when a program state has reached a halted state,
   and what it's exit code/return value is when it has reached such
   a state. *)

(** [corestep] is the fundamental small-step relation for the
   sequential semantics. *)

(** The remaining properties give basic sanity properties which constrain
   the behavior of programs. *)
(** -1 a state cannot be both blocked on an extension call and also step, *)
(** -2 a state cannot both step and be halted, and *)
(** -3 a state cannot both be halted and blocked on an external call. *)
Record CoreSemantics {C M : Type} : Type :=
  { initial_core : nat -> M -> C -> M -> val -> list val -> Prop
  ; at_external : C -> M -> option (external_function * list val)
  ; after_external : option val -> C -> M -> option C
  ; halted : C -> int -> Prop
  ; corestep : C -> M -> C -> M -> Prop
  ; corestep_not_halted:
      forall m q m' q' i, corestep q m q' m' -> ~ halted q i
  ; corestep_not_at_external:
      forall m q m' q', corestep q m q' m' -> at_external q m = None }.

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
