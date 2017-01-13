(*+ Resource maps *)

(** In this file:
- common results about lists
- definition of resource maps, ignoring problems related to step
  indexing *)

Require Import List Arith Omega Setoid String.
Require Import Coq.Logic.FunctionalExtensionality.

(*+ List functions *)

Fixpoint nth {A} (l : list A) i :=
  match l with
  | nil => None
  | x :: l =>
    match i with
    | O => Some x
    | S i => nth l i
    end
  end.

Fixpoint nth_upd {A} (l : list A) i x :=
  match l with
  | nil => nil
  | y :: l =>
    match i with
    | O => x :: l
    | S i => y :: nth_upd l i x
    end
  end.

Lemma eq_nat_dec (a b : nat) : {a=b}+{a<>b}. decide equality. Defined.

Ltac ifeq :=
    match goal with
      [ H : context [ eq_nat_dec ?x ?x ] |- _ ] => destruct (eq_nat_dec x x) as [_|]; [|congruence]
    | [ |- context [ eq_nat_dec ?x ?x ] ] => destruct (eq_nat_dec x x) as [_|]; [|congruence]
    | [ H : context [ eq_nat_dec ?x ?y ] |- _ ] => destruct (eq_nat_dec x y)
    | [ |- context [ eq_nat_dec ?x ?y ] ] => destruct (eq_nat_dec x y)
    end.

Lemma nth_nth_upd {A} (l : list A) i x y j :
  nth l i = Some x ->
  nth (nth_upd l i y) j = if eq_nat_dec i j then Some y else nth l j.
Proof.
  revert i j x y; induction l; intros [|i] [|j] x y E; simpl in E; try solve [auto|inversion E].
  unfold nth_upd; fold (@nth_upd A).
  unfold nth; fold (@nth A).
  rewrite (IHl i j x y E).
  ifeq; ifeq; congruence || omega.
Qed.

Lemma nth_upd_app_1 {A} (l1 l2 : list A) i x y :
  nth l1 i = Some x ->
  nth_upd l1 i y ++ l2 = nth_upd (l1 ++ l2) i y.
Proof.
  revert i; induction l1; intros [|i] E; inversion E; auto.
  simpl; f_equal.
  eauto.
Qed.

Lemma nth_app_1 {A} (l1 l2 : list A) i x :
  nth l1 i = Some x ->
  nth (l1 ++ l2) i = Some x.
Proof.
  revert l1; induction i; intros [|y l1] E; simpl; inversion E; auto.
  rewrite IHi; auto.
Qed.

Lemma nth_snoc {A} i (l : list A) x :
  i <> List.length l ->
  nth (l ++ x :: nil) i = nth l i.
Proof.
  revert i; induction l; simpl; intros [|i] D; try congruence.
  apply IHl; auto.
Qed.

Lemma nth_snoc_len {A} (l : list A) x :
  nth (l ++ x :: nil) (List.length l) = Some x.
Proof.
  induction l; simpl; try congruence.
Qed.

Lemma nth_len {A} (l : list A) :
  nth l (List.length l) = None.
Proof.
  induction l; simpl; try congruence.
Qed.

Lemma length_nth_upd {A} (l : list A) i x : List.length (nth_upd l i x) = List.length l.
Proof.
  revert i; induction l; intros [|i]; simpl; auto.
Qed.

Lemma nth_nth_upd' {A} i j l (x : A) :
  j <> i ->
  nth (nth_upd l i x) j = nth l j.
Proof.
  revert i j; induction l; simpl; intros [|] [|] ?; simpl; auto; congruence.
Qed.

(*+ Resource maps *)

(** Here, we avoid solving the indirection equation by abstracting
over the desired properties, not worrying about step indexing to add
predicates in the "memory" (i.e. the resource maps).  Note that it is
also possible to instantiate the variable [lock] with a deep embedding
of the desired resource invariants without cheating. *)

Variable lock : Set.
Definition val := (nat + lock)%type.
Definition map := nat -> option val.
Variable interp_lock : lock -> (map -> Prop).

Definition emptymap : map := fun _ => None.

Definition eqmap (m m' : map) := forall x, m x = m' x.

Lemma eqmap_eq m m' : eqmap m m' -> m = m'.
Proof.
  intros H; extensionality x. apply H.
Qed.

Instance eqmap_equiv : Equivalence eqmap.
Proof.
  split; compute; firstorder; congruence.
Qed.

Definition upd {A} (m : nat -> A) x e :=
  fun y => if eq_nat_dec x y then e else m y.

Definition updatemap (m : map) (x e : nat) : option map :=
  match m x with Some _ => Some (upd m x (Some (inl e))) | None => None end.

Definition assertmap (m : map) (x : nat) : Prop :=
  match m x with Some (inl (S _)) => True | _ => False end.

(*+ Join relation on resources and resource maps *)

Definition joincell (a b : option val) : option (option val) :=
  match a, b with
    | None, None => Some None
    | Some a, None | None, Some a => Some (Some a)
    | Some _, Some _ => None
  end.

Definition join (m n o : map) : Prop := forall x, joincell (m x) (n x) = Some (o x).
Definition joins (m n : map) : Prop := exists o, join m n o.

Add Parametric Morphism : join with signature eqmap ==> eqmap ==> eqmap ==> iff as join_morphism.
Proof.
  unfold eqmap, join, joincell.
  intros a b E c d F e f G; split; intros H x;
  specialize (H x);
  rewrite E, F, G in *;
  destruct (d x), (e x), (f x); congruence.
Qed.

Lemma join_eqmap_compat_l {m m' n o}  : eqmap m m' -> join m n o -> join m' n o.
Proof.
  intros E J x; specialize (J x); specialize (E x).
  destruct (m x), (n x); congruence.
Qed.

Lemma join_eqmap_compat_r {m n n' o}  : eqmap n n' -> join m n o -> join m n' o.
Proof.
  intros E J x; specialize (J x); specialize (E x).
  destruct (m x), (n x); congruence.
Qed.

Lemma join_eqmap {m n o o'}  : join m n o -> join m n o' -> eqmap o o'.
Proof.
  intros J J' x; specialize (J x); specialize (J' x).
  destruct (m x), (n x); congruence.
Qed.

Lemma join_eqmap_r {m n n' o}  : join m n o -> join m n' o -> eqmap n n'.
Proof.
  intros J J' x; specialize (J x); specialize (J' x).
  destruct (m x), (n x), (n' x), (o x); inversion J; inversion J'; congruence.
Qed.

Lemma join_eqmap_l {m m' n o}  : join m n o -> join m' n o -> eqmap m m'.
Proof.
  intros J J' x; specialize (J x); specialize (J' x).
  destruct (m x), (n x), (m' x), (o x); inversion J; inversion J'; congruence.
Qed.

Definition joincell_split {a b ab c abc} :
  joincell a b = Some ab -> joincell ab c = Some abc ->
  { bc | joincell b c = Some bc /\ joincell a bc = Some abc }.
Proof.
  destruct a, b, ab, c, abc; simpl; intros E F; try discriminate;
    eexists; intuition; try congruence.
Defined.

Lemma join_split a b ab c abc : join a b ab -> join ab c abc ->
  exists bc, join b c bc /\ join a bc abc.
Proof.
  intros H I.
  exists (fun x => proj1_sig (joincell_split (H x) (I x))); split; intros x; simpl;
    apply (proj2_sig (joincell_split (H x) (I x))).
Qed.

Lemma join_emptymap_l a : join emptymap a a.
Proof.
  intros x; destruct (a x); auto.
Qed.

Lemma join_emptymap_r a : join a emptymap a.
Proof.
  intros x; destruct (a x); auto.
Qed.

Lemma joins_emptymap_l a : joins emptymap a.
Proof.
  exists a; intros x; destruct (a x); auto.
Qed.

Lemma joins_emptymap_r a : joins a emptymap.
Proof.
  exists a; intros x; destruct (a x); auto.
Qed.

Lemma join_comm a b c : join a b c -> join b a c.
Proof.
  intros J x; rewrite <-J.
  destruct (a x), (b x); auto.
Qed.

Lemma joins_sym a b : joins a b -> joins b a.
Proof.
  intros [c J]; exists c; apply join_comm; auto.
Qed.

Hint Resolve
     join_emptymap_l
     join_emptymap_r
     joins_emptymap_l
     joins_emptymap_r
     join_comm
     joins_sym.

Lemma joins_pointwise m n : joins m n <-> (forall x, joincell (m x) (n x) <> None).
Proof.
  split.
  - intros [o H] x; rewrite (H x). congruence.
  - intros H.
    exists (fun x => match joincell (m x) (n x) with Some n => n | None => None end).
    intros x; destruct (joincell (m x) (n x)) eqn:E; auto.
    apply (H x) in E; tauto.
Qed.

Lemma join_joins_distrib a b ab : join a b ab -> forall c, joins ab c -> joins a c /\ joins b c.
Proof.
  intros H c [d J]; split; apply joins_pointwise; intros x;
    specialize (H x); specialize (J x);
      destruct (a x), (b x), (c x); simpl in *; try congruence;
        injection H; intros E; rewrite <-E in *; inversion J.
Qed.

Lemma join_joins_distrib' a b ab : join a b ab -> forall c, joins a c -> joins b c -> joins ab c.
Proof.
  intros H c [d J] [e I]; apply joins_pointwise; intros x;
    specialize (H x); specialize (J x); specialize (I x);
      destruct (a x), (b x), (c x); simpl in *; try congruence;
        injection H; intros E F; rewrite <-E in *; simpl; discriminate.
Qed.

Definition empty (m : map) : Prop := forall x, m x = None.

Lemma join_empty m n : empty n -> join m n m.
Proof.
  intros E x; rewrite E; destruct (m x); auto.
Qed.

Definition nonempty (m : map) : Prop := exists x, m x <> None.

Lemma eqmap_joins m1 m2 : joins m1 m2 -> eqmap m1 m2 -> empty m1 /\ empty m2.
Proof.
  intros [o J] EQ.
  cut (empty m1); [ intros E; split; intros x; auto; rewrite <- EQ; auto | ].
  intros x; specialize (J x); rewrite <-EQ in J.
  destruct (m1 x); auto; inversion J.
Qed.

(*+ Predicates over resource maps *)

Definition pred := map -> Prop.

Definition sat (m : map) (P : pred) : Prop := P m.
(* Definition sat (m : map) (P : pred) : Prop := forall n, eqmap m n -> P n. *)

Infix " |= " := sat (at level 40).

Definition emp : pred := fun m => forall n, m n = None.

Definition TT : pred := fun m => True.

Definition FF : pred := fun m => False.

Definition imp (P Q : pred) : Prop := forall m, m |= P -> m |= Q.

Definition sepcon (P Q : pred) : pred :=
  fun m => exists m1 m2, join m1 m2 m /\ P m1 /\ Q m2.

Infix "**" := sepcon (at level 30).

Lemma imp_sepcon P Q F : imp P Q -> imp (P ** F) (Q ** F).
Proof.
  intros i m (m1 & m2 & J & H1 & H2).
  apply i in H1.
  compute; eauto.
Qed.

Definition pequiv (P Q : pred) := forall m, P m <-> Q m.

Infix " == " := pequiv (at level 50, no associativity).

Lemma pequiv_sym P Q : P == Q -> Q == P.
Proof.
  compute; firstorder.
Qed.

Lemma pequiv_imp P Q : P == Q -> imp P Q.
Proof.
  compute; firstorder.
Qed.

Lemma sepcon_comm P Q : P ** Q == Q ** P.
Proof.
  intros m; split; intros (p & q & J & Pp & Qq); exists q, p; intuition; eauto.
Qed.

Lemma sepcon_assoc P Q R : P ** (Q ** R) == (P ** Q) ** R.
Proof.
  intros m; split.
  - intros (p & qr & J & Pp & q & r & J' & Qq & Rr).
    apply join_comm in J.
    apply join_comm in J'.
    destruct (join_split _ _ _ _ _ J' J) as (pq & J'' & J''').
    exists pq, r; split; intuition.
    exists p, q; split; eauto.
  - intros (pq & r & J & (p & q & J' & Pp & Qq) & Rr).
    destruct (join_split _ _ _ _ _ J' J) as (qr & J'' & J''').
    exists p, qr; split; intuition.
    exists q, r; split; eauto.
Qed.

Lemma sepcon_emp P : emp ** P == P.
Proof.
  intros m; split.
  - intros (p & q & J & Pp & Qq).
    (* hmm we need P to be stable under pointwise equality *)
    replace m with q; auto.
    apply functional_extensionality.
    intros x.
    specialize (J x).
    rewrite (Pp x) in *.
    destruct (q x); inversion J; auto.
  - intros Pm.
    exists emptymap, m; split; intuition eauto.
    intro; reflexivity.
Qed.

Definition subheap m o := exists n, join m n o.

Definition precise (R : pred) : Prop := forall o m1 m2,
    m1 |= R -> m2 |= R ->
    subheap m1 o -> subheap m2 o -> eqmap m1 m2.

Lemma precise_FF : precise FF.
Proof.
  intros o m1 m2 [].
Qed.

Definition mapsto x v : pred := fun m => forall n, m n = if eq_nat_dec x n then Some v else None.

Definition mapsto_ x : pred := fun m => forall n, if eq_nat_dec x n then m n <> None else m n = None.

Lemma mapsto_mapsto_ x n m : mapsto x n m -> mapsto_ x m.
Proof.
  unfold mapsto, mapsto_.
  intros H y; rewrite (H y).
  destruct (eq_nat_dec x y); congruence.
Qed.

Lemma precise_mapsto x n : precise (mapsto x n).
Proof.
  intros o m1 m2 s1 s2 [n1 J1] [n2 J2] y.
  rewrite (s1 y), (s2 y); auto.
Qed.

Lemma precise_mapsto_ x : precise (mapsto_ x).
Proof.
  intros o m1 m2 s1 s2 [n1 J1] [n2 J2] y.
  specialize (s1 y).
  specialize (s2 y).
  ifeq; try congruence.
  specialize (J1 y).
  specialize (J2 y).
  destruct (m1 y); try congruence.
  destruct (m2 y); try congruence.
  destruct (n1 y); try congruence; try inversion J1.
  destruct (n2 y); try congruence; try inversion J2.
  congruence.
Qed.

Lemma precise_join R m1 m2 : precise R -> m1 |= R -> m2 |= R -> joins m1 m2 -> empty m1 /\ empty m2.
Proof.
  intros PR s1 s2 [o J].
  assert (S1:subheap m1 o) by (unfold subheap; eauto).
  assert (S2:subheap m2 o) by (unfold subheap; eauto).
  specialize (PR o _ _ s1 s2 S1 S2).
  apply eqmap_joins; unfold joins; eauto.
Qed.

(*+ Collection of disjoint maps *)

(** For the proof of composition of safety, we need to maintain the
    invariants "all the maps are disjoint*" which is why we need this
    section.

  * pairwise-disjointness is equivalent to arbitrary disjointness
    because the permissions are "set-theoretical" *)

Definition selfjoins {A} (maps : A -> map) :=
  forall i j, i <> j -> joins (maps i) (maps j).

Definition sameperms (m n : map) := forall x, m x = None <-> n x = None.

Lemma sameperms_refl m : sameperms m m.
Proof.
  compute; tauto.
Qed.

Lemma sameperms_sym m n : sameperms m n -> sameperms n m.
Proof.
  compute; intros S x; specialize (S x); intuition.
Qed.

Lemma sameperms_trans m n o : sameperms m n -> sameperms n o -> sameperms m o.
Proof.
  compute; intros S T x; specialize (S x); specialize (T x); intuition.
Qed.

Hint Resolve sameperms_refl sameperms_sym sameperms_trans.

Lemma sameperms_updatemap m x e m' : updatemap m x e = Some m' -> sameperms m m'.
Proof.
  unfold updatemap, upd; destruct (m x) eqn:E; intros U i; inversion U; subst; clear U.
  ifeq; intuition; congruence.
Qed.

Lemma sameperms_joins m m' n : sameperms m m' -> joins m n -> joins m' n.
Proof.
  intros S [o J].
  exists (fun x => match m' x, n x with
           | None, None => None
           | None, Some n | Some n, None => Some n
           | Some _, Some _ => None end).
  intros x.
  specialize (J x); specialize (S x).
  destruct (m x) eqn:D, (m' x) eqn:E, (n x) eqn:F; auto.
  - inversion J.
  - intuition.
    discriminate.
Qed.

Hint Resolve sameperms_updatemap.

Lemma selfjoins_sameperms_compat {A} maps1 maps2 : (forall i:A, sameperms (maps1 i) (maps2 i)) -> selfjoins maps1 -> selfjoins maps2.
Proof.
  intros S J i j ij.
  specialize (J i j ij).
  pose proof (S i); pose proof (S j).
  eapply sameperms_joins; eauto.
  apply joins_sym.
  eapply sameperms_joins; eauto.
Qed.

Definition swapped {A} (m1 m2 : A -> map) i j a b c d :=
  m1 i = a /\
  m1 j = b /\
  m2 i = c /\
  m2 j = d /\
  forall k, k <> i -> k <> j -> m1 k = m2 k.

Lemma selfjoins_swapped {A} {m1 m2 : A -> map} (Adec:forall x y:A,{x=y}+{x<>y})
      i j (J:selfjoins m1) e a b c d :
  swapped m1 m2 i j a b c d ->
  join a b e ->
  join c d e ->
  selfjoins m2.
Proof.
  intros (<- & <- & <- & <- & diff) ab cd x y xy.
  pose proof join_joins_distrib' _ _ _ ab.
  destruct (Adec x i) as [xi|xi];
  destruct (Adec x j) as [xj|xj];
  destruct (Adec y i) as [yi|yi];
  destruct (Adec y j) as [yj|yj]; try congruence; try subst x; try subst y;
    try (assert (y': m1 y = m2 y) by (apply diff; auto));
    try (assert (x': m1 x = m2 x) by (apply diff; auto));
    repeat match goal with
             [ H : ?p <> ?q |- _ ] => pose proof (J _ _ H); clear H
           end; try rewrite <-x' in *; try rewrite <-y' in *;
      solve
        [ auto
        | eexists; eauto
        | apply (join_joins_distrib _ _ _ cd); auto
        | apply joins_sym, (join_joins_distrib _ _ _ cd); auto ].
Qed.

Lemma natnateqdec (x y : nat + nat) : {x=y}+{x<>y}. repeat decide equality. Defined.

(*+ Rewriting tactics *)

Tactic Notation "rewr" :=
  match goal with
  | H : ?f = _ |- context [?f] => rewrite H
  | H : ?f _ = ?f _ |- _ => try (injection H; repeat intros ->)
  end.

Tactic Notation "rewr" constr(e) :=
  match goal with E : e = _ |- _ => rewrite E | E : _ = e |- _ => rewrite <-E end.

Tactic Notation "rewr" constr(e) "in" "*" :=
  match goal with E : e = _ |- _ => rewrite E in * | E : _ = e |- _ => rewrite <-E in * end.

Tactic Notation "rewr" constr(e) "in" hyp(H) :=
  match goal with E : e = _ |- _ => rewrite E in H | E : _ = e |- _ => rewrite <-E in H end.
