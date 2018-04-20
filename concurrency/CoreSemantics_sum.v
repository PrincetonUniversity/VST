Require Import VST.concurrency.core_semantics.
Require Import VST.concurrency.semantics.
Require Import VST.sepcomp.event_semantics.

(*

{ initial_core : nat -> M -> C -> Values.val -> list Values.val -> Prop;
    at_external : C -> M -> option (AST.external_function * AST.signature * list Values.val);
    after_external : option Values.val -> C -> M -> option C;
    halted : C -> Integers.Int.int -> Prop;
    corestep : G -> C -> M -> C -> M -> Prop;
    corestep_not_at_external : forall (ge : G) (m : M) (q : C) (m' : M) (q' : C),
                               corestep ge q m q' m' -> at_external q m = None }

 *)

Inductive state_sum (Cs Ct:Type): Type :=
| SState (c:Cs)
| TState (c:Ct).

Definition state_sum_options {Cs Ct:Type} (cso: option Cs): option (state_sum Cs Ct) :=
  match cso with
  | Some cs => Some (SState _ _ cs)
  | _ => None
  end.
Definition state_sum_optiont {Cs Ct:Type} (cto: option Ct): option (state_sum Cs Ct) :=
  match cto with
  | Some ct => Some (TState _ _ ct)
  | _ => None
  end.

Definition state_sum_optionms {Cs Ct M:Type} (cso: option (Cs * option M)): option (state_sum Cs Ct * option M) :=
  match cso with
  | Some (cs, m) => Some (SState _ _ cs, m)
  | _ => None
  end.
Definition state_sum_optionmt {Cs Ct M:Type} (cto: option (Ct * option M)): option (state_sum Cs Ct * option M) :=
  match cto with
  | Some (ct, m) => Some (TState _ _ ct, m)
  | _ => None
  end.

Definition lt_op (n: nat) (no:option nat): bool :=
  match no with
    | None => true
    | Some n' => Nat.ltb n n' 
  end.

Definition initial_core_sum (no:option nat) (Cs Ct:Type) (M: Type)
           (sinitial_core : nat -> M -> Cs -> Values.val -> list Values.val -> Prop)
           (tinitial_core : nat -> M -> Ct -> Values.val -> list Values.val -> Prop):
  nat -> M -> state_sum Cs Ct -> Values.val -> list Values.val -> Prop :=
  fun (n:nat) m c val vals =>
    match c with
    | SState c => sinitial_core n m c val vals
    | TState c => tinitial_core n m c val vals
    end.

Definition sum_func {Cs Ct X:Type} (fs:Cs -> X) (ft:Ct-> X) s:=
  match s with
  | SState c => (fs c)
  | TState c => (ft c)
  end.

Definition sum_func_option {Cs Ct Cs' Ct':Type} 
           (fs: Cs -> option Cs') (ft: Ct-> option Ct') s:=
  match s with
  | SState c => state_sum_options (fs c) 
  | TState c => state_sum_optiont (ft c) 
  end.

Definition at_external_sum (Cs Ct M: Type)
           (sat_external: Cs -> M -> option (AST.external_function * AST.signature * list Values.val))
           (tat_external: Ct -> M -> option (AST.external_function * AST.signature * list Values.val))
           :=
  sum_func sat_external tat_external.

Definition after_external_sum (Cs Ct M: Type)
           (safter_external: option Values.val -> Cs -> M -> option Cs)
           (tafter_external: option Values.val -> Ct -> M -> option Ct)
           :=
  fun vals c m => sum_func_option (fun c => safter_external vals c m)
                                  (fun c => tafter_external vals c m) c.

Definition halted_sum Cs Ct
           (shalted: Cs -> Integers.Int.int -> Prop)
           (thalted: Ct -> Integers.Int.int -> Prop) :=
  sum_func shalted thalted.

Inductive corestep_sum {Gs Gt M Cs Ct}
          (scorestep: Gs -> Cs -> M -> Cs -> M -> Prop)
          (tcorestep: Gt -> Ct -> M -> Ct -> M -> Prop):
  (Gs * Gt) -> state_sum Cs Ct -> M -> state_sum Cs Ct -> M -> Prop:=
| SCorestep: forall g s m s' m',
    scorestep (fst g) s m s' m' ->
    corestep_sum scorestep tcorestep g (SState _ _ s) m (SState _ _ s') m'
| TCorestep: forall g s m s' m',
    tcorestep (snd g) s m s' m' ->
    corestep_sum scorestep tcorestep g (TState _ _ s) m (TState _ _ s') m'.

Lemma corestep_not_at_external_sum:
  forall Gs Gt M Cs Ct
    (scorestep: Gs -> Cs -> M -> Cs -> M -> Prop) 
    (sat_external: Cs -> M -> option (AST.external_function * AST.signature * list Values.val))
    (scorestep_not_at_external: forall (ge : Gs) (m : M) (q : Cs) (m' : M) (q' : Cs),
        scorestep ge q m q' m' -> sat_external q m = None)
    (tcorestep: Gt -> Ct -> M -> Ct -> M -> Prop)
    (tat_external: Ct -> M -> option (AST.external_function * AST.signature * list Values.val))
    (tcorestep_not_at_external: forall (ge : Gt) (m : M) (q : Ct) (m' : M) (q' : Ct),
        tcorestep ge q m q' m' -> tat_external q m = None),
  forall (ge : Gs * Gt) (m : M) (q : state_sum Cs Ct) (m' : M) (q' : state_sum Cs Ct),
    corestep_sum scorestep tcorestep ge q m q' m' ->
    at_external_sum _ _ _ sat_external tat_external q m = None.
Proof.
  intros.
  inversion H; subst; simpl; eauto.
Qed.

(*Lemma corestep_not_halted_sum:
  forall Gs Gt  M Cs Ct
    (scorestep: Gs -> Cs -> M -> Cs -> M -> Prop) 
    (shalted : Cs -> Integers.Int.int -> Prop)
    (scorestep_not_halted: forall (ge : Gs) (m : M) (q : Cs) (m' : M) (q' : Cs),
        scorestep ge q m q' m' -> shalted q = None)
    (tcorestep: Gt -> Ct -> M -> Ct -> M -> Prop)
    (thalted : Ct -> Integers.Int.int -> Prop)
    (tcorestep_not_halted: forall (ge : Gt) (m : M) (q : Ct) (m' : M) (q' : Ct),
        tcorestep ge q m q' m' -> thalted q = None),
  forall (ge : Gs * Gt) (m : M) (q : state_sum Cs Ct) (m' : M) (q' : state_sum Cs Ct),
    corestep_sum scorestep tcorestep ge q m q' m' ->
    halted_sum _ _ shalted thalted q = None.
Proof.
  intros.
  inversion H; subst; simpl; eauto.
Qed.

Lemma at_external_halted_excl_sum:
  forall Gs Gt M Cs Ct
    (scorestep: Gs -> Cs -> M -> Cs -> M -> Prop) 
    (shalted : Cs -> option Values.val)
    (sat_external: Gs -> Cs -> M -> option (AST.external_function * list Values.val))
    (sat_external_halted_excl : forall ge (q : Cs) m, sat_external ge q m = None \/ shalted q = None)
    (tcorestep: Gt -> Ct -> M -> Ct -> M -> Prop)
    (thalted : Ct -> option Values.val)
    (tat_external: Gt -> Ct -> M -> option (AST.external_function * list Values.val))
    (tat_external_halted_excl : forall ge (q : Ct) m, tat_external ge q m = None \/ thalted q = None),
  forall  (ge : Gs * Gt) (m : M) (q : state_sum Cs Ct),
    at_external_sum _ _ _ _ _ sat_external tat_external ge q m = None \/
    halted_sum _ _ shalted thalted q = None.
Proof.
  intros.
  destruct q; simpl; auto.
Qed.*)

Program Definition CoreSemanticsSum hb Gs Gt M Cs Ct
        (CSs: CoreSemantics Gs Cs M )
        (CSt: CoreSemantics Gt Ct M ): CoreSemantics (Gs * Gt) (state_sum Cs Ct) M :=
  Build_CoreSemantics (Gs * Gt) _ _
    (initial_core_sum hb _ _ _ (initial_core CSs) (initial_core CSt))
    (at_external_sum _ _ _ (at_external CSs) (at_external CSt))
    (after_external_sum _ _ _ (after_external CSs) (after_external CSt))
    (halted_sum _ _  (halted CSs) (halted CSt))
    (corestep_sum (corestep CSs) (corestep CSt)) 
    _
.
Next Obligation.
  intros; eapply corestep_not_at_external_sum; eauto; first [apply CSs|apply CSt].
Qed.
(*Next Obligation.
  intros; eapply corestep_not_halted_sum; eauto; first [apply CSs|apply CSt].
Qed.
Next Obligation.
  intros; eapply (at_external_halted_excl_sum Gs Gt); eauto; first [apply CSs|apply CSt].
Qed.*)

Program Definition MemSemanticsSum (hb:option nat) Gs Gt Cs Ct
        (CSs: MemSem Gs Cs )
        (CSt: MemSem Gt Ct ): MemSem (Gs * Gt) (state_sum Cs Ct):=
  Build_MemSem _ _ (CoreSemanticsSum hb Gs Gt Memory.Mem.mem Cs Ct CSs CSt) _.
Next Obligation.
  intros.
  inversion CS; subst.
  - eapply CSs; eassumption.
  - eapply CSt; eassumption.
Defined.

Inductive ev_step_sum {Gs Gt Cs Ct:Type}
          (ESs: Gs -> Cs -> Memory.Mem.mem -> list mem_event -> Cs -> Memory.Mem.mem -> Prop)
          (ESt: Gt -> Ct -> Memory.Mem.mem -> list mem_event -> Ct -> Memory.Mem.mem -> Prop):
  (Gs * Gt) -> (state_sum Cs Ct) -> Memory.Mem.mem -> list mem_event -> (state_sum Cs Ct) -> Memory.Mem.mem -> Prop
  :=
| SEvstep: forall g s m t s' m',
    ESs (fst g) s m t s' m' ->
    ev_step_sum ESs ESt g (SState _ _ s) m t (SState _ _ s') m'
| TEvstep: forall g s m t s' m',
    ESt (snd g) s m t s' m' ->
    ev_step_sum ESs ESt g (TState _ _ s) m t (TState _ _ s') m'.
  

Program Definition EvSemanticsSum (hb:option nat) Gs Gt Cs Ct
        (CSs: @EvSem Gs Cs )
        (CSt: @EvSem Gt Ct ): @EvSem (Gs * Gt) (state_sum Cs Ct):=
  Build_EvSem _ _ (MemSemanticsSum hb Gs Gt Cs Ct CSs CSt) (ev_step_sum (ev_step CSs) (ev_step CSt)) _ _ _ _.
Next Obligation.
  intros.
  inversion H; subst.
  - constructor; eapply CSs; eauto.
  - constructor; eapply CSt; eauto.
Defined.
Next Obligation.
  intros.
  inversion H; subst.
  - eapply CSs in H0; destruct H0 as [T ?]. 
    exists T; constructor; eauto.
  - eapply CSt in H0; destruct H0 as [T ?]. 
    exists T; constructor; eauto.
Defined.
Next Obligation.
  intros.
  inversion H; subst;
  inversion H0; subst.
  - eapply CSs; eauto.
  - eapply CSt; eauto.
Defined.
Next Obligation.
  intros.
  inversion STEP; subst.
  -  eapply (ev_step_elim CSs) in H; destruct H as [HH1 HH2];
       split; eauto; intros.
     apply HH2 in H.
     destruct H as [cc' HH].
     eexists; constructor; eauto.
  -  eapply (ev_step_elim CSt) in H; destruct H as [HH1 HH2];
       split; eauto; intros.
     apply HH2 in H.
     destruct H as [cc' HH].
     eexists; constructor; eauto.
Defined.


Definition CoreSem_Sum (hb:option nat) (Sems Semt: Semantics): Semantics:=
  Build_Semantics  _ _
                   (EvSemanticsSum hb _ _ _ _ (@semSem Sems) (@semSem Semt)).

