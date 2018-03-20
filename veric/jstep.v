Require Import VST.msl.Axioms.
Require Import compcert.common.Memory.
Require Import VST.sepcomp.semantics.

Module FSem.
Record t M TM := mk {
    F : forall G C, @CoreSemantics G C M -> @CoreSemantics G C TM
  ; E : TM -> M
  ; P : TM -> TM -> Prop
  ; step  : forall G C sem ge c m c' m',
            @corestep _ _ _ (F G C sem) ge c m c' m' =
           (@corestep _ _ _ sem ge c (E m) c' (E m') /\ P m m')
  ; init : forall G C sem n ge m v vl q, 
     initial_core (F G C sem) n ge m v vl = Some (q,None) <->
     initial_core sem n ge (E m) v vl = Some (q, None)
  ; atext  : forall G C sem g c m , 
      at_external (F G C sem) g c m = at_external sem g c (E m)
  ; aftext : forall G C sem, after_external (F G C sem) = after_external sem
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
unfold j_initial_core.
destruct (initial_core sem n ge (m_dry m) v vl) as [[? ?] | ] eqn:?;
  [ | intuition congruence].
destruct o. intuition congruence.
split; intro.
inversion H; clear H; subst.
split; auto.
congruence.
Qed.
End JuicyFSem.

