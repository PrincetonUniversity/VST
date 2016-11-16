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

Lemma map_leq_apply:
  forall {A B} (m1: PTree.t A)(m2: PTree.t B) p f1,
    map_leq m1 m2 ->
    m1 ! p = Some f1 -> exists f2, m2 ! p = Some f2. 
Proof.
  move => A B m1 m2 p f1.
  rewrite /map_leq => /(_ p) Mle AA.
  rewrite AA in Mle. specialize (Mle ltac:(auto)).
  destruct (m2 ! p) as [f2|]; try solve[inversion Mle].
  exists f2; auto.
Qed.
  
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

Definition bounded_nat_func' {A} (f: nat -> option A) hi: Prop :=
  (forall p, (p >= hi )%nat -> f p = None).

Definition bounded_func' {A} (f: Z -> option A) hi lo: Prop :=
  (forall p, (p > hi )%Z -> f p = None) /\
  (forall p, (p < lo)%Z -> f p = None).

Definition bounded_func {A} (f: Z -> option A): Prop :=
  exists hi lo,
  (forall p, (p > hi )%Z -> f p = None) /\
  (forall p, (p < lo)%Z -> f p = None).

Definition bounded_map {A} (m: PTree.t (Z -> option A)):=
  forall p f, m ! p = Some f -> bounded_func f.

Definition sub_map {A B} (m1: PTree.t (Z -> option A))(m2: PTree.t (Z -> option B)):=
  forall p f1, m1 ! p = Some f1 ->
       exists f2, m2 ! p = Some f2 /\ fun_leq f1 f2.


Definition nat_to_perm (i:nat) :=
  match i with
  | 0 => None
  | 1 => Some Nonempty
  | 2 => Some Readable
  | 3 => Some Writable
  | 4 => Some Freeable
  | _ => None
  end.

Definition perm_to_nat (p: option permission) :=
  match p with
  | None => 0
  | Some Nonempty => 1
  | Some Readable => 2
  | Some Writable => 3
  | Some Freeable => 4
  end.

 Lemma finite_bounded_nat_func:
          forall hi ,
            konig.finite
              ( fun f:nat -> option permission => bounded_nat_func' f hi).
 Proof.
   intros hi.
   pose (K:= perm_to_nat).
   induction hi.
   - exists 1.
     exists (fun _ _ => None).
     intros.
     exists 0%nat.
     split; auto.
     unfold bounded_nat_func' in H.
     extensionality i.
     symmetry.
     apply H.
     apply leq0n.
   - destruct IHhi as [N [FN H]].
     exists (5*N).
     exists (fun x i => if (Nat.eq_dec i hi) then
                       nat_to_perm (Nat.modulo x 5)
                else FN (Nat.div x 5) i).
     intros f HH.
     specialize (H (fun n => if (Nat.eq_dec n hi) then
                            None
                          else f n) ).
     destruct H as [i [ineq f_spec]].
     + intros pp pphi.
       destruct (Nat.eq_dec pp hi).
       * auto.
       * simpl; eapply HH.
         admit.

         idtac.
     + exists ((5 * i) + (perm_to_nat (f hi))).
       split.
       * (* 5*i <= 5 * (N-1) *)
         (* perm_to_nat x < 5 *)
         admit.

       * { extensionality n.
           destruct (Nat.eq_dec n hi).
           - replace  ((5 * i + perm_to_nat (f hi)) mod 5)
             with (perm_to_nat (f hi) mod 5).
             replace  (( perm_to_nat (f hi)) mod 5)
             with (perm_to_nat (f hi)).
             replace (nat_to_perm (perm_to_nat (f hi)))
             with (f hi).
             subst; reflexivity.
             admit.
             admit.
             admit.
           - replace ((5 * i + perm_to_nat (f hi)) / 5)
             with (i).
             simpl. rewrite f_spec.
             simpl.
             destruct (Nat.eq_dec n hi);
               try solve[exfalso; apply n0; auto].
             reflexivity.
             admit.
 Admitted.
    
Lemma finite_sub_maps:
  forall m2,
    @bounded_map permission m2 ->
    konig.finite
      (fun m1 => @sub_map (option permission) permission m1 m2).
Proof.
  intros.
Admitted.

    
    