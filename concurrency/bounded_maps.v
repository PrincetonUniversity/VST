Require Import compcert.lib.Axioms.
Require Import compcert.lib.Maps.

Require Import concurrency.sepcomp. Import SepComp.

Require Import concurrency.pos.
Require Import concurrency.scheduler.
Require Import concurrency.TheSchedule.
Require Import concurrency.konig.
Require Import concurrency.addressFiniteMap. (*The finite maps*)
Require Import concurrency.pos.
Require Import concurrency.lksize.
Require Import concurrency.permjoin_def.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.


Require Import Coq.ZArith.ZArith.

Require Import concurrency.permissions.
Require Import concurrency.threadPool.
 
Require Import compcert.common.Memory. (*for Mem.perm_order'' *)

Definition map_leq {A B} (m1: PTree.t A)(m2: PTree.t B): Prop :=
  forall p, m1 ! p -> m2 ! p.

Lemma treemap_sub_map: forall {A B} (f: positive -> B -> A) m2,
    map_leq (PTree.map f m2) m2.
Proof.
  move => A B f m2 p.
  rewrite PTree.gmap.
  destruct (m2 ! p) eqn:m2p; auto; intros HH; inversion HH.
Qed.

Definition map_empty_def {A} (m1: PMap.t (Z -> option A)):=
  m1.1 = fun _ => None.

Definition fun_leq {A B} (f1: Z -> option A) (f2: Z -> option B): Prop :=
  forall p, f1 p -> f2 p.

Definition bounded_func {A} (f: Z -> option A): Prop :=
  exists hi lo,
  (forall p, (p > hi )%Z -> f p = None) /\
  (forall p, (p < lo)%Z -> f p = None).

Definition bounded_map {A} (m: PTree.t (Z -> option A)):=
  forall p f, m ! p = Some f -> bounded_func f.

Definition sub_map {A B} (m1: PTree.t (Z -> option A))(m2: PTree.t (Z -> option B)):=
  forall p f1, m1 ! p = Some f1 ->
       exists f2, m2 ! p = Some f2 /\ fun_leq f1 f2.


Lemma finite_sub_maps:
  forall A B m2,
    @bounded_map B m2 ->
    konig.finite
      (fun m1 => @sub_map A B m1 m2).
Proof.
  intros.
Admitted.



(*Lemma leq_sub_map:
  forall m1 m2,
    @map_leq A B m1 m2 ->
   (forall p f1, m1 ! p = f1  -> exists f2, m2 ! p = f2 /\ ). 
  *)  
    
    