Require Import VST.floyd.list_solver.
Require Import ZArith.
Import eq_dec.
Require Import Lia.
Require Import Coq.Lists.List.
Open Scope Z_scope.

Example Forall_app : forall A {d : Inhabitant A} (a b : list A) P,
  Forall P a ->
  Forall P b ->
  Forall P (a ++ b).
Proof.
  list_solve.
Qed.

Example not_In_app : forall A {d : Inhabitant A} (a b : list A) x,
  ~(In x a) ->
  ~(In x b) ->
  ~(In x (a ++ b)).
Proof.
  intros.
  rewrite not_In_forall_range_iff.
  list_solve.
Qed.

Example In_app_1 : forall A {d : Inhabitant A} (a b : list A) x,
  In x a ->
  In x (a ++ b).
Proof.
  (* This is provable by construction in Coq. *)
  intros.
  rewrite !In_Znth_iff in H |- *.
  destruct H as [i [H1 H2]].
  exists i.
  list_solve.
Abort.

Example In_app_1 : forall A {d : Inhabitant A} (a b : list A) x,
  In x a ->
  In x (a ++ b).
Proof.
  (* But full automation needs non-constructive logic. *)
  intros.
  apply Classical_Prop.NNPP. intro.
  list_solve.
Qed.

(* Association list *)

Section AssocList.

Context {A B} {da : Inhabitant A} {db : Inhabitant B} {Heq_dec : EqDec A}.

Definition set (l : list (A * B)) a b :=
  (a, b) :: l.

Fixpoint get (l : list (A * B)) key :=
  match l with
  | nil => default
  | (a, b) :: l' =>
      if Heq_dec key a then b else get l' key
  end.

Fixpoint get_index (l : list (A * B)) key : Z :=
  match l with
  | nil => 0
  | (a, b) :: l' =>
      if Heq_dec key a then 0 else 1 + (get_index l' key)
  end.

Ltac if_tac :=
  match goal with
  | |- context [if ?x then _ else _] =>
    destruct x
  end.

Ltac if_tac_in H :=
  match type of H with
  | context [if ?x then _ else _] =>
    destruct x in H
  end.

Lemma get_index_nonneg : forall (l : list (A * B)) key,
  get_index l key >= 0.
Proof.
  intros; induction l; unfold get_index; fold get_index;
    only 2 : (destruct a as [a b]; destruct (Heq_dec key a)); lia.
Qed.

Lemma get_by_get_index : forall l key,  
  let i := get_index l key in
  (if Z_lt_le_dec i (Zlength l) then snd (Znth i l) else default)
    = get l key.
Proof.
  intros.
  induction l; auto.
  destruct a as [a b]; simpl.
  subst i. unfold get_index; fold get_index.
  destruct (Heq_dec key a).
  - (* key = a*)
    if_tac; list_solve.
  - (* key <> a*)
    simpl in IHl.
    pose proof (get_index_nonneg l key).
    if_tac; if_tac_in IHl; list_solve.
Qed.

(* Starting from here, we prove an awesome lemma get_index_spec. It can
  hardly be proved without the list solver. The current proof takes about
  30 lines. The proof is separated into intermediate goals that can be 
  solved by the list solver's algorithm if the base solver is complete.
  The implemented list solver is limited by the completeness of the base
  solver.
  
  Not only the lemma itself is good, but also its implications.
  With this lemma, and combining with the last lemma, we can express
  the get function using In and other list operations. In can be
  expressed by a quantified formula, which has only one quantified variable
  and one list access. So such quantified formula only creates an edge
  to an leaf node in the IPG, and does not incur any loops. So
  association list becomes fully decidable in our theory.
  
  This is not just for association list. When querying an association list,
  we can also pass a test function to the query, and expect the first entry
  that hits satisfies the test function. This generalization also fits in
  this expression of association list. *)

(* Tell list solver to interpret "not In" as a quantified formula. *)
Hint Rewrite @not_In_forall_range_iff : list_solve_rewrite.

Lemma get_index_only_if1 : forall key i,
  0 = i ->
  0 <= i < Zlength (@nil (A*B)) /\
  fst (Znth i (@nil (A*B))) = key /\ ~ In key (map fst (sublist 0 i (@nil (A*B)))) \/
  i = Zlength (@nil (A*B)) /\ ~ In key (map fst (sublist 0 i (@nil (A*B)))).
Proof.
  (* ideal list_solve should solve here. *)
  intros. right. list_solve.
Qed.

Lemma get_index_only_if2 : forall (a : A) (b : B) l key i,
  key = a ->
  0 = i ->
  (0 <= i < Zlength ((a, b) :: l) /\
  fst (Znth i ((a, b) :: l)) = key /\
  ~ In key (map fst (sublist 0 i ((a, b) :: l))) \/
  i = Zlength ((a, b) :: l) /\ ~ In key (map fst (sublist 0 i ((a, b) :: l)))).
Proof.
  (* ideal list_solve should solve here. *)
  intros. left. list_solve.
Qed.

Lemma get_index_only_if3 : forall (a : A) (b : B) l key i,
  forall (IHl: 0 <= i - 1 < Zlength l /\
      fst (Znth (i - 1) l) = key /\ ~ In key (map fst (sublist 0 (i - 1) l)) \/
      i - 1 = Zlength l /\ ~ In key (map fst (sublist 0 (i - 1) l))),
  key <> a ->
  1 + get_index l key = i ->
  get_index l key >= 0 ->
  (0 <= i < Zlength ((a, b) :: l) /\
  fst (Znth i ((a, b) :: l)) = key /\
  ~ In key (map fst (sublist 0 i ((a, b) :: l))) \/
  i = Zlength ((a, b) :: l) /\ ~ In key (map fst (sublist 0 i ((a, b) :: l)))).
Proof.
  (* ideal list_solve should solve here. *)
  intros.
  destruct IHl as [[? []] | []].
  + left. list_solve.
    (* Some problems about that Inhabitant for type B cannot be filled by autorewrite
      when dealing with map. *)
    (* Now solved. *)
  + right. list_solve.
Qed.

Lemma get_index_only_if : forall l key i,
  get_index l key = i
    ->
  (0 <= i < Zlength l /\ fst (Znth i l) = key /\ ~In key (map fst (sublist 0 i l)))
    \/ (i = Zlength l /\ ~In key (map fst (sublist 0 i l))).
Proof.
  intros.
  generalize dependent i; induction l; intros.
  { apply get_index_only_if1; auto. }
  unfold get_index in H; fold get_index in H.
  destruct a as [a b].
  destruct (Heq_dec key a).
  (* We might need to transform into Prenex normal form to solve such goals. *)
  - { apply get_index_only_if2; auto. }
  - specialize (IHl (i-1) ltac:(lia)).
    pose proof (get_index_nonneg l key).
    { apply get_index_only_if3; auto. }
Qed.

Lemma get_index_if1 : forall key i,
  (0 <= i < Zlength (@nil (A*B)) /\
    fst (Znth i (@nil (A*B))) = key /\ ~ In key (map fst (sublist 0 i (@nil (A*B)))) \/
    i = Zlength (@nil (A*B)) /\ ~ In key (map fst (sublist 0 i (@nil (A*B))))) ->
  0 = i.
Proof.
  intros. destruct H; list_solve.
Qed.

Lemma get_index_if2 : forall (a : A) (b : B) l key i,
  (0 <= i < Zlength ((a, b) :: l) /\
    fst (Znth i ((a, b) :: l)) = key /\
    ~ In key (map fst (sublist 0 i ((a, b) :: l))) \/
    i = Zlength ((a, b) :: l) /\
    ~ In key (map fst (sublist 0 i ((a, b) :: l)))) ->
  key = a ->
  0 = i.
Proof.
  (* ideal list_solve should solve here. *)
  intros.
  destruct H as [[? []] | []].
  (* Some problems about (1) the map problem the same as above,
      (2) the solver does not instantiate for the bound set (only the index set),
      traded completeness for better efficiecy,
      (3) incompleteness of the base solver. *)
  - list_simplify.
    specialize (H9 0 ltac:(list_solve)). simpl in H9.
    congruence.
  - list_simplify.
    specialize (H8 0 ltac:(lia)). simpl in H8.
    congruence.
Qed.

Lemma get_index_if3 : forall (a : A) (b : B) l key i,
  forall (IHl : 0 <= i - 1 < Zlength l /\
    fst (Znth (i - 1) l) = key /\ ~ In key (map fst (sublist 0 (i - 1) l)) \/
    i - 1 = Zlength l /\ ~ In key (map fst (sublist 0 (i - 1) l)) ->
    get_index l key = i - 1),
  (0 <= i < Zlength ((a, b) :: l) /\
    fst (Znth i ((a, b) :: l)) = key /\
    ~ In key (map fst (sublist 0 i ((a, b) :: l))) \/
    i = Zlength ((a, b) :: l) /\
    ~ In key (map fst (sublist 0 i ((a, b) :: l)))) ->
  key <> a ->
  1 + get_index l key = i.
Proof.
  (* ideal list_solve should solve here. *)
  intros.
  assert (0 <= i - 1 < Zlength l /\
    fst (Znth (i - 1) l) = key /\ ~ In key (map fst (sublist 0 (i - 1) l)) \/
    i - 1 = Zlength l /\ ~ In key (map fst (sublist 0 (i - 1) l))).
  {
    destruct H as [[? []] | []].
    - left.
      list_simplify; try (simpl in H1; congruence).
    - right. list_solve.
  }
  rewrite (IHl H1). lia.
Qed.

Lemma get_index_if : forall l key i,
  (0 <= i < Zlength l /\ fst (Znth i l) = key /\ ~In key (map fst (sublist 0 i l)))
  \/ (i = Zlength l /\ ~In key (map fst (sublist 0 i l)))
    ->
  get_index l key = i.
Proof.
  intros.
  generalize dependent i; induction l; intros.
  { eapply get_index_if1; eauto. }
  unfold get_index; fold get_index.
  destruct a as [a b].
  destruct (Heq_dec key a).
  { eapply get_index_if2; eauto. }
  specialize (IHl (i-1)).
  { eapply get_index_if3; eauto. }
Qed.

Lemma get_index_spec : forall l key i,
  get_index l key = i
    <->
  (0 <= i < Zlength l /\ fst (Znth i l) = key /\ ~In key (map fst (sublist 0 i l)))
    \/ (i = Zlength l /\ ~In key (map fst (sublist 0 i l))).
Proof.
  intros. split; [
    apply get_index_only_if
  | apply get_index_if
  ].
Qed.

End AssocList.

Example entangled_example (l : list nat) n :
  0 < n <= Zlength l ->
  sublist 0 (n-1) l = sublist 1 n l -> False.
Proof.
  Fail list_solve.
Abort.
