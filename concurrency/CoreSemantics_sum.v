Require Import sepcomp.semantics.

(*

  { initial_core : G -> Values.val -> list Values.val -> option C;
    at_external : C -> option (AST.external_function * list Values.val);
    after_external : option Values.val -> C -> option C;
    halted : C -> option Values.val;
    corestep : G -> C -> M -> C -> M -> Prop;
    corestep_not_at_external : forall (ge : G) (m : M) (q : C) (m' : M) (q' : C),
                               corestep ge q m q' m' -> at_external q = None;
    corestep_not_halted : forall (ge : G) (m : M) (q : C) (m' : M) (q' : C),
                          corestep ge q m q' m' -> halted q = None;
    at_external_halted_excl : forall q : C, at_external q = None \/ halted q = None }

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

Definition lt_op (n: nat) (no:option nat): bool :=
  match no with
    | None => true
    | Some n' => Nat.ltb n n' 
  end.

Definition initial_core_sum (no:option nat) G (Cs Ct:Type)
           (sinitial_core : nat -> G -> Values.val -> list Values.val -> option Cs)
           (tinitial_core : nat -> G -> Values.val -> list Values.val -> option Ct):
  nat -> G -> Values.val -> list Values.val -> option (state_sum Cs Ct):=
  fun (n:nat) g val vals =>
    if lt_op n no
    then state_sum_options (sinitial_core n g val vals)
    else state_sum_optiont (tinitial_core n g val vals).


Definition sum_func {Cs Ct X:Type} (fs:Cs -> X) (ft:Ct-> X) s:=
  match s with
  | SState c => (fs c)
  | TState c => (ft c)
  end.

Definition sum_func_option {Cs Ct Cs' Ct':Type} (fs:Cs -> option Cs') (ft:Ct-> option Ct') s:=
  match s with
  | SState c => state_sum_options (fs c) 
  | TState c => state_sum_optiont (ft c) 
  end.

Definition at_external_sum Cs Ct
           (sat_external: Cs -> option (AST.external_function * list Values.val))
           (tat_external: Ct -> option (AST.external_function * list Values.val)):=
  sum_func sat_external tat_external.

Definition after_external_sum Cs Ct
           (safter_external: option Values.val -> Cs -> option Cs)
           (tafter_external: option Values.val -> Ct -> option Ct):=
  fun vals => sum_func_option (safter_external vals) (tafter_external vals).

Definition halted_sum Cs Ct
           (shalted: Cs -> option Values.val)
           (thalted: Ct -> option Values.val):=
  sum_func shalted thalted.

Inductive corestep_sum {G M Cs Ct}
          (scorestep: G -> Cs -> M -> Cs -> M -> Prop)
          (tcorestep: G -> Ct -> M -> Ct -> M -> Prop):
  G -> state_sum Cs Ct -> M -> state_sum Cs Ct -> M -> Prop:=
| SCorestep: forall g s m s' m',
    scorestep g s m s' m' ->
    corestep_sum scorestep tcorestep g (SState _ _ s) m (SState _ _ s') m'
| TCorestep: forall g s m s' m',
    tcorestep g s m s' m' ->
    corestep_sum scorestep tcorestep g (TState _ _ s) m (TState _ _ s') m'.

Lemma corestep_not_at_external_sum:
  forall G M Cs Ct
    (scorestep: G -> Cs -> M -> Cs -> M -> Prop) 
    (sat_external: Cs -> option (AST.external_function * list Values.val))
    (scorestep_not_at_external: forall (ge : G) (m : M) (q : Cs) (m' : M) (q' : Cs),
        scorestep ge q m q' m' -> sat_external q = None)
    (tcorestep: G -> Ct -> M -> Ct -> M -> Prop)
    (tat_external: Ct -> option (AST.external_function * list Values.val))
    (tcorestep_not_at_external: forall (ge : G) (m : M) (q : Ct) (m' : M) (q' : Ct),
        tcorestep ge q m q' m' -> tat_external q = None),
  forall (ge : G) (m : M) (q : state_sum Cs Ct) (m' : M) (q' : state_sum Cs Ct),
    corestep_sum scorestep tcorestep ge q m q' m' ->
    at_external_sum _ _ sat_external tat_external q = None.
Proof.
  intros.
  inversion H; subst; simpl; eauto.
Qed.

Lemma corestep_not_halted_sum:
  forall G M Cs Ct
    (scorestep: G -> Cs -> M -> Cs -> M -> Prop) 
    (shalted : Cs -> option Values.val)
    (scorestep_not_halted: forall (ge : G) (m : M) (q : Cs) (m' : M) (q' : Cs),
        scorestep ge q m q' m' -> shalted q = None)
    (tcorestep: G -> Ct -> M -> Ct -> M -> Prop)
    (thalted : Ct -> option Values.val)
    (tcorestep_not_halted: forall (ge : G) (m : M) (q : Ct) (m' : M) (q' : Ct),
        tcorestep ge q m q' m' -> thalted q = None),
  forall (ge : G) (m : M) (q : state_sum Cs Ct) (m' : M) (q' : state_sum Cs Ct),
    corestep_sum scorestep tcorestep ge q m q' m' ->
    halted_sum _ _ shalted thalted q = None.
Proof.
  intros.
  inversion H; subst; simpl; eauto.
Qed.

Lemma at_external_halted_excl_sum:
  forall G M Cs Ct
    (scorestep: G -> Cs -> M -> Cs -> M -> Prop) 
    (shalted : Cs -> option Values.val)
    (sat_external: Cs -> option (AST.external_function * list Values.val))
    (sat_external_halted_excl : forall q : Cs, sat_external q = None \/ shalted q = None)
    (tcorestep: G -> Ct -> M -> Ct -> M -> Prop)
    (thalted : Ct -> option Values.val)
    (tat_external: Ct -> option (AST.external_function * list Values.val))
    (tat_external_halted_excl : forall q : Ct, tat_external q = None \/ thalted q = None),
  forall (q : state_sum Cs Ct),
    at_external_sum _ _ sat_external tat_external q = None \/
    halted_sum _ _ shalted thalted q = None.
Proof.
  intros.
  destruct q; simpl; auto.
Qed.

Program Definition CoreSemanticsSum n G M Cs Ct
        (CSs: CoreSemantics G Cs M )
        (CSt: CoreSemantics G Ct M ): CoreSemantics G (state_sum Cs Ct) M :=
  Build_CoreSemantics _ _ _
    (initial_core_sum n _ _ _ (initial_core CSs) (initial_core CSt))
    (at_external_sum _ _ (at_external CSs) (at_external CSt))
    (after_external_sum _ _  (after_external CSs) (after_external CSt))
    (halted_sum _ _  (halted CSs) (halted CSt))
    (corestep_sum (corestep CSs) (corestep CSt)) 
    _ _ _     
.
Next Obligation.
  eapply corestep_not_at_external_sum; eauto; first [apply CSs|apply CSt].
Qed.
Next Obligation.
  eapply corestep_not_halted_sum; eauto; first [apply CSs|apply CSt].
Qed.
Next Obligation.
  eapply at_external_halted_excl_sum; eauto; first [apply CSs|apply CSt].
Qed.