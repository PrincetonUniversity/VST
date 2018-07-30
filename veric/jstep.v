Require Import VST.msl.Axioms.
Require Import compcert.common.Memory.
Require Import VST.sepcomp.semantics.

Module FSem.
Record t M TM := mk {
    F : forall C, @CoreSemantics C M -> @CoreSemantics C TM
  ; E : TM -> M
  ; P : TM -> TM -> Prop
  ; step  : forall C sem c m c' m',
            @corestep _ _ (F C sem) c m c' m' =
           (@corestep _ _ sem c (E m) c' (E m') /\ P m m')
(*  ; init : forall C sem n m m' v vl q,
     initial_core (F C sem) n m q m' v vl <->
     initial_core sem n (E m) q (E m') v vl*) (* Should this really be true? *)
  ; atext  : forall C sem c m,
      at_external (F C sem) c m = at_external sem c (E m)
  ; aftext : forall C sem ret c m,
      after_external (F C sem) ret c m = after_external sem ret c (E m)
  ; halted : forall C sem, halted (F C sem) = halted sem
  }.
End FSem.

Module IdFSem.
Program Definition t M : FSem.t M M :=
  FSem.mk M M (fun C sem => sem) id (fun _ _ => True) _ _ _ _.
Next Obligation.
apply prop_ext.
split; intros H.
split; auto.
destruct H; auto.
Qed.
(*Next Obligation.
intuition.
Qed.*)
End IdFSem.

Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.own.

Module JuicyFSem.
Program Definition t : FSem.t mem juicy_mem :=
  FSem.mk mem juicy_mem (@juicy_core_sem) m_dry
    (fun jm jm' => resource_decay (Mem.nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
       ageable.level jm = S (ageable.level jm') /\
       ghost_of (m_phi jm') = ghost_approx jm' (ghost_of (m_phi jm)))
    _ _ _ _.
End JuicyFSem.

