Require Import Memory.

Require Import semantics.

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

