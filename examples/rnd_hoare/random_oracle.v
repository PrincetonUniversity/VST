Class RandomOracle: Type := {
  ro_question: Type;
  ro_answer: ro_question -> Type
}.

Definition RandomQA {ora: RandomOracle}: Type := {q: ro_question & ro_answer q}.

Definition RandomHistory {ora: RandomOracle}: Type := {h: nat -> option RandomQA | forall x y, x < y -> h x = None -> h y = None}.

Definition history_get {ora: RandomOracle} (h: RandomHistory) (n: nat) := projT1 h n.

Coercion history_get: RandomHistory >-> Funclass.

Lemma history_sound: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x < y -> h x = None -> h y = None.
Proof. intros ? [? ?]; auto. Qed.

Definition history_prefix {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  forall n a, h1 n = Some a -> h2 n = Some a.

Definition RandomEvent {ora: RandomOracle} (A: Type): Type :=
  {f: RandomHistory -> option A | forall h1 h2, history_prefix h1 h2 -> f h1 = None \/ f h2 = None}.