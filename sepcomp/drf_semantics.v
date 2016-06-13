Require Import compcert.lib.Coqlib. 
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers. 
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import msl.Extensionality. 
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.

Inductive drf_step m m' : Prop :=
    drf_step_storebytes: forall b ofs bytes,
       Mem.storebytes m b ofs bytes = Some m' -> drf_step m m'
  | drf_step_loadbytes: forall b ofs n bytes,
       Mem.loadbytes m b ofs n = Some bytes ->
       (forall mm, (exists n, 0 <= n < Zlength bytes /\
                   Mem.perm_order'' (Some Nonempty) ((Mem.mem_access mm) !! b (ofs+n) Cur)) ->
                   Mem.loadbytes mm b ofs n = None) -> m'=m ->
       drf_step m m'
  | drf_step_alloc: forall lo hi b',
       Mem.alloc m lo hi = (m',b') -> drf_step m m'
  | drf_step_freelist: forall l,
       Mem.free_list m l = Some m' -> drf_step m m'
  (*add cases for lock/unlock, by inspecting atExternal? Or leave this to the "DRF machine"
    which also add thread indices etc?*)
  (*Some non-observable external calls are alloc+store-steps*)
  | drf_step_trans: forall m'',
       drf_step m m'' -> drf_step m'' m' -> drf_step m m'.

(* DRF semantics are CoreSemantics that are specialized to CompCert memories
   and evolve memory according to drf_step.*)
Record DrfSem {G C} :=
  { csem :> @CoreSemantics G C mem

  ; corestep_drf : forall g c m c' m' (CS: corestep csem g c m c' m'), drf_step m m'
  }.

Implicit Arguments DrfSem [].

(********************* Lemmas********)

Lemma drf_step_refl m: drf_step m m.
  apply (drf_step_freelist _ _ nil); trivial.
Qed. 
 
Lemma drf_step_free: 
      forall m b lo hi m', Mem.free m b lo hi = Some m' -> drf_step m m'.
Proof.
 intros. eapply (drf_step_freelist _ _ ((b,lo,hi)::nil)). 
 simpl. rewrite H; reflexivity.
Qed.

Lemma drf_step_store: 
      forall m ch b a v m', Mem.store ch m b a v = Some m' -> drf_step m m'.
Proof.
 intros. eapply drf_step_storebytes. eapply Mem.store_storebytes; eassumption. 
Qed.

Lemma drf_step_mem_step: 
      forall m m', drf_step m m' -> mem_step m m'.
Proof.
 intros. induction H.
 eapply mem_step_storebytes; eassumption.
 subst. eapply mem_step_refl.
 eapply mem_step_alloc; eassumption.
 eapply mem_step_freelist; eassumption.
 eapply mem_step_trans; eassumption. 
Qed.

(** * Semantics annotated with Owens-style trace*)
Inductive drf_event :=
  Write : forall (b : block) (ofs : Z) (bytes : list memval), drf_event
| Read : forall (b:block) (ofs n:Z), drf_event
| Arith: drf_event
| Alloc: forall (lo hi:Z) (b:block), drf_event
| Lock: drf_event
| Unlock: drf_event
(*| Seq : drf_event -> drf_event -> drf_event*).

(** Similar to effect semantics, DRF semantics augment memory semantics with suitable effects, in the form 
    of a set of memory access traces associated with each internal 
    step of the semantics. *)

Record DRFSem {G C} :=
  { (** [sem] is a memory semantics. *)
    msem :> MemSem G C

    (** The step relation of the new semantics. *)
  ; drfstep: G -> drf_event -> C -> mem -> C -> mem -> Prop

    (** The next three fields axiomatize [drfstep] and its relation to the
        underlying step relation of [msem]. *)
  ; drfax1: forall T g c m c' m',
       drfstep g T c m c' m' ->
            corestep msem g c m c' m' 
  ; drfax2: forall g c m c' m',
       corestep msem g c m c' m' ->
       exists M, drfstep g M c m c' m'
  ; drf_fun: forall T' T'' g c m c' m' c'' m'',
       drfstep g T' c m c' m' -> drfstep g T'' c m c'' m'' -> T'=T''
  ; drfstep_wr: forall g c m c' m' b ofs bytes,
       drfstep g (Write b ofs bytes) c m c' m' ->
       Mem.storebytes m b ofs bytes = Some m' /\
       forall mm, (exists n, 0 <= n < Zlength bytes /\
                   Mem.perm_order'' (Some Readable) ((Mem.mem_access mm) !! b (ofs+n) Cur)) ->
                   Mem.storebytes mm b ofs bytes = None 
  ; drfstep_rd: forall g c m c' m' b ofs n,
       drfstep g (Read b ofs n) c m c' m' ->
       exists bytes, Mem.loadbytes m b ofs n = Some bytes /\
       (forall mm, (exists n, 0 <= n < Zlength bytes /\
                   Mem.perm_order'' (Some Nonempty) ((Mem.mem_access mm) !! b (ofs+n) Cur)) ->
                   Mem.loadbytes mm b ofs n = None) 
  ; drfstep_alloc: forall g c m c' m' lo hi b,
       drfstep g (Alloc lo hi b) c m c' m' ->
       Mem.alloc m lo hi = (m',b)
  ; drfstep_arith: forall g c m c' m',
       drfstep g Arith c m c' m' -> 
       (m=m' /\ forall mm, corestep msem g c mm c' mm)
  }.

Implicit Arguments DRFSem [].
