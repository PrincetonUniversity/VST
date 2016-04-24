Require Import Omega.

Class RandomOracle: Type := {
  ro_question: Type;
  ro_answer: ro_question -> Type
}.

Definition RandomQA {ora: RandomOracle}: Type := {q: ro_question & ro_answer q}.

Definition RandomHistory {ora: RandomOracle}: Type := {h: nat -> option RandomQA | forall x y, x < y -> h x = None -> h y = None}.

Definition history_get {ora: RandomOracle} (h: RandomHistory) (n: nat) := proj1_sig h n.

Coercion history_get: RandomHistory >-> Funclass.

Lemma history_sound1: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x < y -> h x = None -> h y = None.
Proof. intros ? [? ?]; auto. Qed.

Lemma history_sound2: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x < y -> (exists a, h y = Some a) -> (exists a, h x = Some a).
Proof.
  intros.
  pose proof history_sound1 h x y H.
  destruct (h x), (h y), H0; eauto.
  specialize (H1 eq_refl).
  congruence.
Qed.

Definition history_coincide {ora: RandomOracle} (n: nat) (h1 h2: RandomHistory): Prop :=
  forall m, m < n -> h1 m = h2 m.

(*
Definition history_cons {ora: RandomOracle} (h1: RandomHistory) (a: RandomQA) (h2: RandomHistory): Prop :=
  exists n,
    history_coincide n h1 h2 /\
    h1 n = None /\
    h2 n = Some a /\
    h2 (S n) = None.
*)

Definition history_app {ora: RandomOracle} (h1 h2 h: RandomHistory): Prop :=
  exists n,
    h1 n = None /\
    history_coincide n h1 h /\
    (forall m, h (m + n) = h2 m).

Definition finite_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  exists n, h n = None.

Definition infinite_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  forall n, h n <> None.

Definition prefix_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  forall n, h1 n = None \/ h1 n = h2 n.

Definition n_bounded_prefix_history {ora: RandomOracle} (m: nat) (h1 h2: RandomHistory): Prop :=
  forall n, (h1 n = None /\ h2 (n + m) = None) \/ h1 n = h2 n.

Record RandomVariable {ora: RandomOracle} (A: Type): Type := {
  raw_var: RandomHistory -> option A;
  rand_consi1:
    forall h1 h2 n a,
      history_coincide n h1 h2 ->
      h1 n = None ->
      h2 n = Some a ->
      raw_var h1 = None \/ raw_var h2 = None;
  rand_consi2:
    forall h1 h2 n a1 a2,
      history_coincide n h1 h2 ->
      h1 n = Some a1 ->
      h2 n = Some a2 ->
      projT1 a1 <> projT1 a2 ->
      raw_var h1 = None \/ raw_var h2 = None
}.

Definition rand_var_get {ora: RandomOracle} {A: Type} (v: RandomVariable A) (h: RandomHistory): option A := raw_var A v h.

Coercion rand_var_get: RandomVariable >-> Funclass.

Definition join {ora: RandomOracle} {A: Type} (v1 v2 v: RandomVariable A): Prop :=
  forall h, (v1 h = None /\ v2 h = v h) \/ (v2 h = None /\ v1 h = v h).

Definition Forall_RandomHistory {ora: RandomOracle} {A: Type} (P: A -> Prop) (v: RandomVariable A): Prop :=
  forall h,
    match v h with
    | None => True
    | Some a => P a
    end.

Definition unit_space_var {ora: RandomOracle} {A: Type} (v: A): RandomVariable A.
  refine (Build_RandomVariable _ _ (fun h => match h 0 with None => Some v | Some _ => None end) _ _).
  + intros.
    destruct n.
    - rewrite H0, H1.
      auto.
    - pose proof history_sound2 h2 0 (S n).
      specialize (H2 (le_n_S _ _ (le_0_n _))).
      specialize (H2 (ex_intro _ a H1)).
      destruct H2.
      rewrite H2; auto.
  + intros.
    destruct n.
    - rewrite H0, H1.
      auto.
    - pose proof history_sound2 h2 0 (S n).
      specialize (H3 (le_n_S _ _ (le_0_n _))).
      specialize (H3 (ex_intro _ a2 H1)).
      destruct H3.
      rewrite H3; auto.
Defined.

Definition RandomVarMap {ora: RandomOracle} {A B: Type} (f: A -> B) (v: RandomVariable A): RandomVariable B.
  refine (Build_RandomVariable _ _ (fun h => match v h with Some a => Some (f a) | None => None end) _ _).
  + destruct v as [v ?H ?H]; simpl.
    intros.
    specialize (H h1 h2 n a H1 H2 H3).
    clear - H.
    destruct (v h1), (v h2); destruct H; inversion H; auto.
  + destruct v as [v ?H ?H]; simpl.
    intros.
    specialize (H0 h1 h2 n a1 a2 H1 H2 H3 H4).
    clear - H0.
    destruct (v h1), (v h2); destruct H0; inversion H; auto.
Defined.

Lemma RandomVarMap_sound: forall {ora: RandomOracle} {A B: Type} (f: A -> B) (v: RandomVariable A) h,
  RandomVarMap f v h =
  match v h with
  | Some a => Some (f a)
  | None => None
  end.
Proof. intros. reflexivity. Qed.

Definition RandomVarDomain {ora: RandomOracle}: Type := RandomVariable unit.

Definition DomainOfVar {ora: RandomOracle} {A: Type} (v: RandomVariable A): RandomVarDomain :=
  RandomVarMap (fun _ => tt) v.

Definition in_domain {ora: RandomOracle} (v: RandomVarDomain) (h: RandomHistory): Prop :=
  v h = Some tt.

Coercion in_domain: RandomVarDomain >-> Funclass.

Lemma DomainOfVar_sound: forall {ora: RandomOracle} {A: Type} (v: RandomVariable A),
  forall h, match v h with Some _ => True | None => False end <-> DomainOfVar v h.
Proof.
  intros.
  unfold DomainOfVar.
  pose proof RandomVarMap_sound (fun _ => tt) v h.
  unfold in_domain.
  rewrite H; clear H.
  destruct (v h); split; intros; try tauto; congruence.
Qed.

Definition future_domain {ora: RandomOracle} (present future: RandomVarDomain): Prop :=
  forall h, future h ->
  exists h', prefix_history h' h -> present h'.

Definition n_bounded_future_domain {ora: RandomOracle} (n: nat) (present future: RandomVarDomain): Prop :=
  forall h, future h ->
  exists h', n_bounded_prefix_history n h' h -> present h'.

Definition bounded_future_domain {ora: RandomOracle} (present future: RandomVarDomain): Prop :=
  exists n, n_bounded_future_domain n present future.

(*
(* TODO: seems no use *)
Definition single_update {ora: RandomOracle} {A: Type} (h0: RandomHistory) (a1 a2: A) (v1 v2: RandomVariable A): Prop :=
  v1 h0 = Some a1 /\
  v2 h0 = Some a2 /\
  forall h, h0 <> h -> v1 h = v2 h.

Definition single_expand {ora: RandomOracle} {A: Type} (h0: RandomHistory) (a1: A) (a2: {q: ro_question & ro_answer q -> A}) (v1 v2: RandomVariable A): Prop :=
  v1 h0 = Some a1 /\
  v2 h0 = None /\
  (forall (a: ro_answer (projT1 a2)) h,
     history_cons h0 (existT ro_answer (projT1 a2) a) h ->
     v1 h = None /\ v2 h = Some (projT2 a2 a)) /\
  (forall h,
     h0 <> h ->
     (forall (a: ro_answer (projT1 a2)), ~ history_cons h0 (existT ro_answer (projT1 a2) a) h) ->
     v2 h = v1 h).
*)