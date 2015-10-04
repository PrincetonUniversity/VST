Require Import msl.Axioms.

Require Import Memory.

Require Import core_semantics.

Module FSem.
Record t M TM := mk { 
    F : forall G C, CoreSemantics G C M -> CoreSemantics G C TM
  ; E : TM -> M
  ; P : TM -> TM -> Prop
  ; step  : forall G C sem ge c m c' m',
            @corestep _ _ _ (F G C sem) ge c m c' m' =
           (@corestep _ _ _ sem ge c (E m) c' (E m') /\ P m m')
  ; init : forall G C sem, initial_core (F G C sem) = initial_core sem
  ; atext  : forall G C sem, at_external (F G C sem) = at_external sem
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
End IdFSem.

Require Import juicy_mem.
Require Import juicy_extspec.

Module JuicyFSem.
Program Definition t : FSem.t mem juicy_mem :=
  FSem.mk mem juicy_mem (@juicy_core_sem) m_dry 
    (fun jm jm' => 
       resource_decay (Mem.nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
       ageable.level jm = S (ageable.level jm'))
    _ _ _ _ _.
End JuicyFSem.

