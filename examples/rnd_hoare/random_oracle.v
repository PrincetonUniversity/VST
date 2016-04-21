Class RandomOracle: Type := {
  ro_question: Type;
  ro_answer: ro_question -> Type
}.

Definition RandomQA {ora: RandomOracle}: Type := {q: ro_question & ro_answer q}.

Definition RandomHistory {ora: RandomOracle}: Type := {h: nat -> option RandomQA | forall x y, x < y -> h x = None -> h y = None}.

Definition history_get {ora: RandomOracle} (h: RandomHistory) (n: nat) := proj1_sig h n.

Coercion history_get: RandomHistory >-> Funclass.

Lemma history_sound: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x < y -> h x = None -> h y = None.
Proof. intros ? [? ?]; auto. Qed.

Definition history_coincide {ora: RandomOracle} (n: nat) (h1 h2: RandomHistory): Prop :=
  forall m, m < n -> h1 m = h2 m.

Definition history_cons {ora: RandomOracle} (h1: RandomHistory) (a: RandomQA) (h2: RandomHistory): Prop :=
  exists n,
    history_coincide n h1 h2 /\
    h1 n = None /\
    h2 n = Some a /\
    h2 (S n) = None.

Definition finite_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  exists n, h n = None.

Definition infinite_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  forall n, h n <> None.

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