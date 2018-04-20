Require Import VST.msl.Axioms.
Require Import compcert.common.Memory.
Require Import VST.concurrency.core_semantics.

Module FSem.
Record t M TM := mk {
    F : forall G C, @CoreSemantics G C M -> @CoreSemantics G C TM
  ; E : TM -> M
  ; P : TM -> TM -> Prop
  ; step  : forall G C sem ge c m c' m',
            @corestep _ _ _ (F G C sem) ge c m c' m' =
           (@corestep _ _ _ sem ge c (E m) c' (E m') /\ P m m')
  ; init : forall G C sem n m v vl q,
     initial_core (F G C sem) n m q v vl <->
     initial_core sem n (E m) q v vl
  ; atext  : forall G C sem c m,
      at_external (F G C sem) c m = at_external sem c (E m)
  ; aftext : forall G C sem ret c m,
      after_external (F G C sem) ret c m = after_external sem ret c (E m)
  ; halted : forall G C sem, halted (F G C sem) = halted sem
  }.
End FSem.

Module IdFSem.
Program Definition t M : FSem.t M M :=
  FSem.mk M M (fun G C sem => sem) id (fun _ _ => True) _ _ _ _ _.
Next Obligation.
apply prop_ext.
split; intros H.
split; auto.
destruct H; auto.
Qed.
Next Obligation.
intuition.
Qed.
End IdFSem.

Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.own.

(*
Definition special_init {G C} (csem: @CoreSemantics G C mem) : Prop :=
  forall n ge m v args q m', 
    semantics.initial_core csem n ge m v args = Some (q, m') -> m=m'.
*)

Module JuicyFSem.
Program Definition t : FSem.t mem juicy_mem :=
  FSem.mk mem juicy_mem (@juicy_core_sem) m_dry
    (fun jm jm' => resource_decay (Mem.nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
       ageable.level jm = S (ageable.level jm') /\
       ghost_of (m_phi jm') = ghost_approx jm' (ghost_of (m_phi jm)))
    _ _ _ _ _.
Next Obligation.
reflexivity.
Qed.
End JuicyFSem.

