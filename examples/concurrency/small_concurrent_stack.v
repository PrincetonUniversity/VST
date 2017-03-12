(*+ Small concurrent stack *)

(** In this file:
- a single-theaded semantics (with oracle and invariants)
- a multi-thread concurrent machine (with schedule and invariants)
- proof that the safety of all threads implies the safety of the machine
- a hoare logic implying safety in the oracle semantics
- a small example yielding safety of the corresponding machine
*)

Require Import List Arith Omega Setoid String.
Require Import Coq.Logic.FunctionalExtensionality.

(* we can remove the need for functional extensionality, at the
   expense of heavier definitions and proofs, with [m |= P] defined as
   [forall m', eqmap m m' -> P m'] instead of [P m] *)

(*+ Syntax *)


Inductive instruction :=
  | set (x e:nat)      (* mem[x] := e *)
  | assert (x:nat)     (* assert mem[x]<>0 *)
  | release (l:nat)    (* unlocking a lock *)
  | acquire (l:nat)    (* locking a lock *)
  | spawn (f:string) (* spawning function f *).

(** spawning could be replaced with

  | spawn (p : list instruction)

and then when reaching it in the oracular semantics, the oracle says
how the current map is split [NO! the oracle would say which map
you're given when you do JOIN, but the safety of the thread has to
provide which map to give away], and then the oracle itself is
(interleaving)-split into two.  We could also write

  | par (p1 p2 : list instruction)

and do the same.  We adopt the spawning with an ID instead because
it's closer to the architecture of VST *)


(*+ General results about safety *)

Definition Rel X := X -> X -> Prop.

Inductive star {X} (R : Rel X) : Rel X :=
  | star_refl x : star R x x
  | star_cons x y z : R x y -> star R y z -> star R x z.

Definition safe {X} (R : Rel X) x := forall y, star R x y -> exists z, R y z.

Lemma safe_R {X} (R : Rel X) x y : safe R x -> R x y -> safe R y.
Proof.
  intros Sx xy z yz.
  destruct (Sx z); eauto.
  econstructor; eauto.
Qed.

Lemma safe_det {X} (R : Rel X) x y : safe R y -> R x y -> (forall y', R x y' -> y = y') -> safe R x.
Proof.
  intros Sy xy D z xz; inversion xz; subst; eauto.
  rewrite <-(D _ H) in *; eauto.
Qed.

Lemma safe_selfloop {X} (R : Rel X) x : R x x -> (forall y, R x y -> y = x) -> safe R x.
Proof.
  intros self loop z xz; induction xz; eauto.
  rewrite (loop _ H) in *; eauto.
Qed.

Lemma safe_one {X} (R : Rel X) x y : R x y -> (forall y, R x y -> safe R y) -> safe R x.
Proof.
  intros xy H z xz.
  inversion xz; subst; compute in *; eauto.
Qed.

(*! Indexed version of safety (not needed here) *)

Inductive iter {X} (R : Rel X) : nat -> Rel X :=
  | iter_O x : iter R O x x
  | iter_S n x y z : R x y -> iter R n y z -> iter R (S n) x z.

Definition safe_ n {X} (R : Rel X) x := forall y m, m < n -> iter R m x y -> exists z, R y z.

Lemma safe_safe_ {X} (R : Rel X) x : safe R x <-> forall n, safe_ n R x.
Proof.
  split.
  - intros Sx n y k kn it; apply Sx.
    clear -it; induction it. constructor.
    econstructor; eauto.
  - intros Sx y st.
    cut (exists n, iter R n x y).
    { intros (n, it). refine (Sx (S n) _ n _ it). auto. }
    clear -st; induction st.
    + exists 0; constructor.
    + destruct IHst as (n, IH); exists (S n); econstructor; eauto.
Qed.

Lemma safe__det {X} (R : Rel X) n x y : safe_ n R y -> R x y -> (forall y', R x y' -> y = y') -> safe_ (S n) R x.
Proof.
  intros Sy xy D z m mn xz; inversion xz; subst; eauto.
  assert (n0 < n) by auto with *.
  rewrite <-(D _ H) in *; eauto.
Qed.

Lemma safe__R {X} (R : Rel X) n x y : safe_ (S n) R x -> R x y -> safe_ n R y.
Proof.
  intros Sx xy z m mn it.
  edestruct (Sx z (S m)); eauto. auto with *.
  econstructor; eauto.
Qed.

Lemma safe_S {X} (R : Rel X) n x : safe_ (S n) R x -> safe_ n R x.
Proof.
  intros S y m mn; apply S; auto.
Qed.

(*+ Stdlib: some list functions *)

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

(*+ Memory maps *)

Definition map := nat -> option nat.

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
  match m x with Some _ => Some (upd m x (Some e)) | None => None end.

Definition assertmap (m : map) (x : nat) : Prop :=
  match m x with Some (S _) => True | _ => False end.

Definition joincell (a b : option nat) : option (option nat) :=
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

(*+ Predicates *)

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

(*+ Oracular semantics *)

(** Single-thread oracular semantics: each thread assumes that the
    oracle provides maps satisfying the invariants, but the thread
    also have to give back maps that satisfy those invariants. *)

Record globals := mkglobals
  { resinvs : nat -> pred (* resource invariant for each lock *) ;
    funspecs : string -> option pred (* precondition of each function *)
  }.

Reserved Notation " c1 ---> c2 " (at level 50).

Definition oracle := list map.

Inductive step : Rel (globals * oracle * map * list instruction) :=
  | step_halted G oracle m :
      (G, oracle, m, nil) --->
      (G, oracle, m, nil)
  | step_set G oracle m m' x e p :
      updatemap m x e = Some m' ->
      (G, oracle, m, set x e :: p) --->
      (G, oracle, m', p)
  | step_assert G oracle m x p :
      assertmap m x ->
      (G, oracle, m, assert x :: p) --->
      (G, oracle, m, p)
  | step_release G oracle m mlock m' l p :
      mlock |= resinvs G l ->
      join m' mlock m ->
      (G, oracle, m, release l :: p) --->
      (G, oracle, m', p)
  | step_acquire G oracle m mlock m' l p :
      mlock |= resinvs G l ->
      join m mlock m' ->
      (G, mlock :: oracle, m, acquire l :: p) --->
      (G, oracle, m', p)
  | step_acquire_wrong_oracle G oracle m mlock l p :
      ~(mlock |= resinvs G l /\ joins m mlock) ->
      (G, mlock :: oracle, m, acquire l :: p) --->
      (G, mlock :: oracle, m, acquire l :: p)
  | step_acquire_empty_oracle G m l p :
      (G, nil, m, acquire l :: p) --->
      (G, nil, m, acquire l :: p)
  | step_spawn G PRE oracle m mspawned m' f p :
      funspecs G f = Some PRE ->
      mspawned |= PRE ->
      join m' mspawned m ->
      (G, oracle, m, spawn f :: p) --->
      (G, oracle, m', p)
where
" c1 ---> c2 " := (step  c1 c2).

Hint Constructors step.

(*+ Concurrent machine *)

(** Semantics of the collection of all threads. Thread and locked
    locks each have their own map. *)

Definition schedule := list nat.

Definition threads := list (map * list instruction).

Definition lockpool := nat -> option map.

Definition functions := string -> option (list instruction).

Definition config := (schedule * functions * globals * threads * lockpool)%type.

Reserved Notation " c1 ===> c2 " (at level 50).

(** reasons for having a list of threads rather than a function nat ->
option thread ? 1) It's a bit more deterministic and hence slighlty
easier to prove sound.  2) We can always allocate new threads. 3)
people prefer that, apparently *)

Inductive machine : Rel config :=
  | machine_outofschedule F G thd pool :
      (nil, F, G, thd, pool) ===>
      (nil, F, G, thd, pool)
  | machine_scheduleoutofbound i sch F G thd pool :
      nth thd i = None ->
      (i :: sch, F, G, thd, pool) ===>
      (sch, F, G, thd, pool)
  | machine_set i sch F G thd m m' x e p pool :
      nth thd i = Some (m, set x e :: p) ->
      updatemap m x e = Some m' ->
      (i :: sch, F, G, thd, pool) ===>
      (i :: sch, F, G, nth_upd thd i (m', p), pool)
  | machine_assert i sch F G thd m x p pool :
      nth thd i = Some (m, assert x :: p) ->
      assertmap m x ->
      (i :: sch, F, G, thd, pool) ===>
      (i :: sch, F, G, nth_upd thd i (m, p), pool)
  | machine_release i sch F G thd m mlock m' l p pool :
      nth thd i = Some (m, release l :: p) ->
      mlock |= resinvs G l ->
      join m' mlock m ->
      (i :: sch, F, G, thd, pool) ===>
      (sch, F, G, nth_upd thd i (m', p), upd pool l (Some mlock))
  | machine_acquire_failure i sch F G thd m l p pool :
      nth thd i = Some (m, acquire l :: p) ->
      pool l = None (* locked *) ->
      (i :: sch, F, G, thd, pool) ===>
      (sch, F, G, thd, pool)
  | machine_acquire_success i sch F G thd m mlock m' l p pool :
      nth thd i = Some (m, acquire l :: p) ->
      pool l = Some mlock (* unlocked *) ->
      join m mlock m' ->
      (i :: sch, F, G, thd, pool) ===>
      (i :: sch, F, G, nth_upd thd i (m', p), upd pool l None)
  | machine_halted i sch F G thd m pool :
      nth thd i = Some (m, nil) ->
      (i :: sch, F, G, thd, pool) ===>
      (sch, F, G, thd, pool)
  | machine_spawn i sch F G PRE thd m mspawned prog m' f p pool :
      nth thd i = Some (m, spawn f :: p) ->
      funspecs G f = Some PRE ->
      mspawned |= PRE ->
      F f = Some prog ->
      join m' mspawned m ->
      (i :: sch, F, G, thd, pool) ===>
      (sch, F, G, nth_upd thd i (m', p) ++ (mspawned, prog) :: nil, pool)
where
" c1 ===> c2 " := (machine c1 c2).

(** Note that we do not consume the schedule in machine_set,
    machine_assert and machine_aquire_success.  We could, which would
    make the semantics more fine-grained (the proofs below are not
    affected at all by this change) *)

Hint Constructors machine.


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

Definition reindex (thd:threads) pool : _ -> map :=
  fun x : nat + nat =>
           match x with
           | inl n =>
             match nth thd n with
             | Some (m, _) => m
             | None => emptymap
             end
           | inr n =>
             match pool n with
             | Some m => m
             | None => emptymap
             end
           end.

Lemma natnateqdec (x y : nat + nat) : {x=y}+{x<>y}. repeat decide equality. Defined.

(*+ Composing safety of several threads *)

(** If each thread behaves well (assuming a good oracle) then running
    those threads in a concurrent machine is safe, too.  The proof
    builds a good oracle for each thread so that each thread follows
    the steps of the machine. *)

Definition lockpool_matches (pool : lockpool) RI :=
  forall l, match pool l with Some m => m |= RI l | None => True end.

Definition functions_safe G F :=
  forall f, match funspecs G f, F f with
       | Some P, Some p =>
         forall m oracle, P m -> safe step (G, oracle, m, p)
       | None, None => True
       | _, _ => False
       end.

Ltac funspecs_inv :=
  match goal with
  | FF : functions_safe ?G ?F |- _ =>
    match goal with
    | FSf : funspecs G ?f = Some _ |- _ =>
      let H := fresh "Hsafe" in
      let p := fresh "p" in
      let E := fresh "E" in
      pose proof FF f as H;
      destruct (F f) as [p|] eqn:E;
      rewrite FSf in H; [|tauto]
    | Ff : F ?f = Some _ |- _ =>
      let H := fresh "Hsafe" in
      let P := fresh "PRE" in
      let E := fresh "E" in
      pose proof FF f as H;
      destruct (funspecs G f) as [P|] eqn:E;
      rewrite Ff in H; [|tauto]
    end
  end.

(* Our invariant:
 - resource invariants are precise (no need for them to be positive)
 - all the functions are safe (given a precondition)
 - lock pool maps and threads maps are disjoint
 - lock pool maps match the resource invariants
 - all threads are safe for n steps
*)

Definition P (x : config) :=
  match x with (_, F, G, thd, pool) =>
    (forall l, precise (resinvs G l)) /\
    functions_safe G F /\
    selfjoins (reindex thd pool) /\
    lockpool_matches pool (resinvs G) /\
    (forall i oracle m p,
        nth thd i = Some (m, p) ->
        safe step (G, oracle, m, p))
  end.

(* Progress : the invariant implies we can take a machine step *)

Theorem progress x : P x -> exists y, x ===> y.
Proof.
  destruct x as (((([|i sch], F), G), thd), pool). eexists; constructor.
  intros (_ & FF & J & _ & S).
  + destruct (nth thd i) as [[m p]|] eqn:E; [ | eauto].
    destruct (S i nil m p E _ (star_refl _ _)) as [z Hz].
    inversion Hz; subst.
    - eauto.
    - eexists. eapply machine_set; reflexivity || eauto.
    - eexists. eapply machine_assert; reflexivity || eauto.
    - eexists. eapply machine_release; reflexivity || eauto.
    - clear Hz (* the oracle is actually used here, z/Hz is useless. *).
      destruct (J (inl i) (inr l)) as [o Jl]; [congruence|]; simpl in Jl; rewrite E in *.
      destruct (pool l) eqn:El (* is the pool lock unlocked or locked? *).
      * eexists. eapply machine_acquire_success; simpl; eauto.
      * eexists. eapply machine_acquire_failure; simpl; eauto.
    - funspecs_inv.
      eexists. eapply machine_spawn; reflexivity || eauto.
Qed.

Tactic Notation "rewr" :=
  match goal with
  | H : ?f = _ |- context [?f] => rewrite H
  | H : ?f _ = ?f _ |- _ => try (injection H; repeat intros ->)
  end.

Tactic Notation "rewr" constr(e) := match goal with E : e = _ |- _ => rewrite E | E : _ = e |- _ => rewrite <-E end.
Tactic Notation "rewr" constr(e) "in" "*" := match goal with E : e = _ |- _ => rewrite E in * | E : _ = e |- _ => rewrite <-E in * end.
Tactic Notation "rewr" constr(e) "in" hyp(H) := match goal with E : e = _ |- _ => rewrite E in H | E : _ = e |- _ => rewrite <-E in H end.

(* Subject reduction : taking a step let us stay in the invariant *)

Theorem subject_reduction x y : x ===> y -> P x -> P y.
Proof.
  destruct x as (((([|i sch], F), G), thd), pool);
    intros xy; inversion xy; subst; intros (PR & FF & J & M & S);
      simpl fst in *; simpl snd in *.

  - (* out of schedule *)
    hnf; intuition; eauto.

  - (* schedule out of bound *)
    hnf; intuition; eauto.

  - (* set *)
    repeat split; auto.
    + eapply selfjoins_sameperms_compat; [..|apply J]; intros [k|]; simpl; eauto.
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      rewr; eauto.
    + intros j oracle; specialize (S j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      intros. rewr.
      eapply safe_R; eauto.

  - (* assert *)
    repeat split; auto.
    + eapply selfjoins_sameperms_compat; [..|apply J]; intros [k|]; simpl; eauto.
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      rewr; eauto.
    + intros j oracle; specialize (S j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      intros. rewr.
      eapply safe_R; eauto.

  - (* release *)
    simpl; repeat split; auto.
    + assert (Empl : match pool l with None => True | Some ml => empty ml end). {
        destruct (pool l) as [ml|] eqn:E; auto.
        cut (empty ml /\ empty mlock);[intuition|].
        apply precise_join with (resinvs G l); eauto.
        - specialize (M l); rewrite E in M; auto.
        - assert (D:inl i <> inr l) by congruence.
          specialize (J _ _ D); simpl in J.
          rewr (nth thd i) in J.
          rewr (pool l) in J.
          pose proof (join_joins_distrib m' mlock m H8 ml); intuition eauto.
      }
      eapply (selfjoins_swapped natnateqdec (inl i) (inr l) J).
      * unfold swapped, reindex, upd; repeat split.
        intros [|] a b; [ | ifeq; congruence].
        erewrite nth_nth_upd;[|eassumption].
        ifeq; congruence.
      * apply join_empty; simpl.
        destruct (pool l) as [ml|]; unfold empty; auto.
      * erewrite nth_nth_upd;[|eassumption].
        ifeq; ifeq.
        rewr; eauto.
    + intros k; unfold upd; ifeq; subst; auto. apply M.
    + intros j oracle; specialize (S j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      intros. rewr.
      eapply safe_R; eauto.

  - (* acquire (locked) *)
    repeat split; eauto.

  - (* acquire (unlocked) *)
    repeat split; auto.
    + eapply (selfjoins_swapped natnateqdec (inl i) (inr l) J).
      * unfold swapped, reindex, upd; repeat split.
        intros [|] a b; try (ifeq; congruence).
        erewrite nth_nth_upd;[|eassumption].
        ifeq; congruence.
      * rewr. rewr. eauto.
      * rewr. ifeq.
        erewrite nth_nth_upd;[|eassumption].
        ifeq. auto.
    + intros k; unfold upd; ifeq; subst; auto. apply M.
    + intros j oracle.
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; eauto.
      specialize (S j (mlock :: oracle)).
      intros; rewr.
      specialize (M l); rewr (pool l) in *.
      eapply safe_R; eauto.

  - (* halted *)
    repeat split; eauto.

  - (* spawn *)
    repeat split; auto.
    + eapply (selfjoins_swapped natnateqdec (inl i) (inl (List.length thd)) J).
      * unfold swapped, reindex, upd; repeat split.
        intros [k|l] a b; try (ifeq; congruence); auto.
        rewrite nth_snoc. 2:rewrite length_nth_upd; auto.
        rewrite nth_nth_upd'. 2:auto.
        auto.
      * rewr. rewrite nth_len. eauto.
      * auto.
        erewrite <-length_nth_upd.
        rewrite nth_snoc_len.
        rewrite nth_snoc. 2:rewrite length_nth_upd; intros ->. 2:rewrite nth_len in H6; discriminate.
        erewrite nth_nth_upd;[|eassumption].
        ifeq; eauto.
    + intros j oracle.
      destruct (eq_nat_dec j (List.length thd)).
      * (* safety of new thread *)
        subst j.
        intros m'' p''.
        erewrite <-length_nth_upd.
        rewrite nth_snoc_len.
        intros E; rewr.
        funspecs_inv.
        replace p0 with p'' in * by congruence.
        auto.
      * (* safety of spawner thread *)
        rewrite nth_snoc. 2:rewrite length_nth_upd; congruence.
        specialize (S j oracle).
        erewrite nth_nth_upd; [|eassumption].
        ifeq; subst; auto.
        intros. rewr.
        eapply safe_R; eauto.
Qed.

Lemma P_safe x : P x -> safe machine x.
Proof.
  intros Px y it.
  apply progress.
  induction it; simpl; auto.
  apply IHit.
  eapply subject_reduction; eauto.
Qed.

Theorem soundness sch F G thd pool :
  (forall l, precise (resinvs G l)) ->
  selfjoins (reindex thd pool) ->
  lockpool_matches pool (resinvs G) ->
  functions_safe G F ->
  (forall i oracle m p,
      nth thd i = Some (m, p) ->
      safe step (G, oracle, m, p)) ->
  safe machine (sch, F, G, thd, pool).
Proof.
  intros PR J M FF SS.
  apply P_safe; unfold P; intuition.
Qed.

(*+ Hoare logic (single thread) *)

(** We now build a Hoare logic for a single thread based on the
    oracular semantics (it can assume that acquire will give back a
    good map, but has to provide back good maps at release.) *)

Definition safe_onethread G P c :=
  forall m, m |= P -> forall oracle, safe step (G, oracle, m, c).

Definition semax G P c Q := forall F k,
    safe_onethread G (Q ** F) k ->
    safe_onethread G (P ** F) (c ++ k).

Lemma semax_app G P Q R c1 c2 : semax G P c1 Q -> semax G Q c2 R -> semax G P (c1++c2) R.
Proof.
  intros H1 H2 k Sk.
  rewrite app_ass; auto.
Qed.

Lemma semax_nil G P : semax G P nil P.
Proof.
  compute; auto.
Qed.

Lemma semax_cons G P Q R i c : semax G P (i :: nil) Q -> semax G Q c R -> semax G P (i :: c) R.
Proof.
  intros; eapply (semax_app _ _ _ _ (i :: nil) c); eauto.
Qed.

Lemma updatemap_mapsto_ x n' n m :
  (mapsto_ x m \/ mapsto x n' m) ->
  exists m', updatemap m x n = Some m' /\ mapsto x n m'.
Proof.
  intros H.
  assert (M : mapsto_ x m) by (intuition; eapply mapsto_mapsto_; eauto); clear H.
  destruct (updatemap m x n) as [m'|] eqn:E; [exists m'; split;auto|].
  - intros y; pose proof (M x) as Mx;  pose proof (M y) as My.
    ifeq.
    unfold updatemap in *.
    destruct (m x); [|congruence].
    injection E; clear E; intro; subst.
    unfold upd.
    ifeq; auto.
  - exfalso.
    specialize (M x); ifeq.
    unfold updatemap in *.
    destruct (m x); congruence.
Qed.

Lemma updatemap_mapsto_frame F x n m :
  m |= mapsto_ x ** F ->
  exists m', updatemap m x n = Some m' /\ m' |= mapsto x n ** F.
Proof.
  intros (m1 & m2 & J & s1 & s2).
  destruct (updatemap_mapsto_ x 0 n _ (or_introl s1)) as (m1' & E & s1').
  unfold updatemap in *.
  destruct (m x) eqn:Ex.
  - eexists; repeat split.
    exists m1', m2; repeat split; auto.
    intros y; specialize (J y).
    destruct (m1 x) eqn:E1; [injection E; intro; subst; clear E|discriminate].
    unfold upd; ifeq; auto.
    subst.
    rewrite E1 in J.
    destruct (m2 y). inversion J. auto.
  - specialize (J x); rewrite Ex in J.
    destruct (m1 x) eqn:E1; [injection E; intro; subst; clear E|discriminate].
    destruct (m2 x); inversion J.
Qed.

Lemma semax_set G x e : semax G (mapsto_ x) (set x e :: nil) (mapsto x e).
Proof.
  intros F k Sk m sat oracle; simpl.
  destruct (updatemap_mapsto_frame _ _ e _ sat) as (m', (E, Hm')).
  specialize (Sk m' Hm' oracle).
  apply (safe_det _ _ _ Sk).
  - constructor; auto.
  - intros Y SY; inversion SY; subst.
    repeat f_equal; congruence.
Qed.

Lemma semax_assert G x n : n <> 0 -> semax G (mapsto x n) (assert x :: nil) (mapsto x n).
Proof.
  intros P F k Sk m sat oracle.
  specialize (Sk m sat oracle).
  apply (safe_det _ _ _ Sk).
  - constructor.
    unfold assertmap.
    destruct sat as (m1 & m2 & J & s1 & s2).
    specialize (J x).
    specialize (s1 x); ifeq.
    destruct n, (m1 x), (m2 x), (m x); try congruence; inversion J; subst.
    destruct n1; auto; congruence.
  - intros Y SY; inversion SY; subst.
    repeat f_equal; congruence.
Qed.

Lemma safe_onethread_implies G (P P' : pred) c :
  imp P' P ->
  safe_onethread G P c -> safe_onethread G P' c.
Proof.
  unfold imp, safe_onethread; auto.
Qed.

Lemma semax_frame G P c Q F : semax G P c Q -> semax G (P ** F) c (Q ** F).
Proof.
  intros S F' k Sk m sat oracle.
  refine (S (F ** F') k _ m _ oracle).
  - eapply safe_onethread_implies; eauto.
    apply pequiv_imp, sepcon_assoc.
  - revert sat; apply pequiv_imp, pequiv_sym, sepcon_assoc.
Qed.

Lemma semax_acquire' G l : (forall P, P \/ ~P) -> semax G emp (acquire l :: nil) (resinvs G l).
Proof.
  intros EM F k Sk m sat oracle; simpl.
  destruct oracle as [|mlock oracle].
  - apply safe_selfloop. constructor.
    intros y step; inversion step; auto.
  - destruct (EM (mlock |= resinvs G l /\ joins m mlock)) as [[s [m' J]]|nok].
    + assert (s' : m' |= resinvs G l ** F).
      { exists mlock, m; intuition.
        eapply pequiv_imp in sat; [ | apply sepcon_emp ]; auto.
      }
      specialize (Sk m' s' oracle).
      eapply safe_det; eauto.
      intros y' step; inversion step; subst; auto.
      * repeat f_equal.
        apply eqmap_eq.
        eapply join_eqmap; eauto.
      * assert (joins m mlock) by (eexists; eauto).
        tauto.
    + apply safe_selfloop. constructor. tauto.
      intros y step; inversion step; auto; subst.
      assert (joins m mlock) by (eexists; eauto).
      tauto.
Qed.

Lemma semax_pre G (P P' : pred) c Q :
  imp P' P ->
  semax G P c Q -> semax G P' c Q.
Proof.
  intros I Se F k Sa.
  eapply safe_onethread_implies with (P ** F); eauto.
  apply imp_sepcon, I.
Qed.

Lemma semax_post G P c (Q Q' : pred) :
  imp Q Q' ->
  semax G P c Q -> semax G P c Q'.
Proof.
  intros I Se F k Sa.
  apply Se.
  eapply safe_onethread_implies with (Q' ** F); auto.
  apply imp_sepcon, I.
Qed.

Lemma semax_acquire G l F :  (forall P, P \/ ~P) -> semax G F (acquire l :: nil) (resinvs G l ** F).
Proof.
  intros EM.
  apply semax_pre with (emp ** F).
  - apply pequiv_imp, pequiv_sym, sepcon_emp.
  - apply semax_frame, semax_acquire'; auto.
Qed.

Lemma semax_release' G l : precise (resinvs G l) -> semax G (resinvs G l) (release l :: nil) emp.
Proof.
  intros PR F k Sk m sat oracle; simpl.
  destruct sat as (mlock & m' & J & sl & s').
  assert (s'' : m' |= emp ** F). {
    refine (pequiv_imp _ _ _ _ s').
    apply pequiv_sym, sepcon_emp. }
  specialize (Sk m' s'' oracle).
  apply (safe_det _ _ _ Sk).
  - apply step_release with mlock; auto.
  - intros Y SY; inversion SY; subst.
    repeat f_equal.
    apply join_comm in J.
    cut (eqmap mlock mlock0).
    { intros E; apply (join_eqmap_compat_r E) in J.
      eapply eqmap_eq, (join_eqmap_l J); eauto. }
    refine (PR m _ _ sl _ _ _); unfold subheap; eauto.
Qed.

Lemma semax_release G l F : precise (resinvs G l) -> semax G (resinvs G l ** F) (release l :: nil) F.
Proof.
  intros PR.
  apply semax_post with (emp ** F).
  { apply pequiv_imp, sepcon_emp. }
  apply semax_frame, semax_release'; auto.
Qed.

Lemma safe_nil G P : safe_onethread G P nil.
Proof.
  intros m sat oracle.
  remember (G, oracle, m, nil) as x.
  intros z Sz; exists x.
  cut (x = z).
  { intros <-; subst; constructor. }
  induction Sz; auto; subst.
  inversion H; subst; auto.
Qed.

Lemma semax_safe G P c : semax G P c TT -> safe_onethread G P c.
Proof.
  intros S; specialize (S emp nil (safe_nil _ _)).
  rewrite app_nil_r in S.
  refine (safe_onethread_implies _ _ _ _ _ S); clear.
  intros m; exists m, (fun _ => None); compute; intuition.
  destruct (m x); auto.
Qed.

(*+ Example *)

Ltac forward :=
  first [
      apply semax_nil
    | eapply semax_cons; [ eapply semax_set | ]
    | eapply semax_cons; [ eapply semax_assert | ]
    | eapply semax_cons; [ eapply semax_acquire' | ]
    | eapply semax_cons; [ eapply semax_acquire | ]
    | eapply semax_cons; [ eapply semax_release' | ]
    | eapply semax_cons; [ eapply semax_release | ]
    | eapply semax_cons
    ]; auto.

(* The following example show that running two (or more) copies of the
following program is safe:

  acquire;
  x := 1;
  release;
  acquire;
  assert x != 0
*)

Example even (sch : schedule) :
  (forall P, P \/ ~P) ->
  let odd n := exists m, n = 1 + 2 * m in
  let mpool : map := fun x => if eq_nat_dec x 5 then Some 1 else None in
  let pool : lockpool := fun l => if eq_nat_dec l 0 then Some mpool else None in
  let c := acquire 0 :: set 5 1 :: release 0 :: acquire 0 :: assert 5 :: nil in
  let RI := fun l => if eq_nat_dec l 0 then mapsto 5 1 else FF in
  let F : functions := fun _ => None in
  let FS := fun _ => None in
  let G := mkglobals RI FS in
  safe machine (sch, F, G, (emptymap, c) :: (emptymap, c) :: nil, pool).
Proof.
  intros EM odd mpool pool c RI F FS G.
  assert (emptymap |= emp) by (compute; auto).
  assert (PR : forall l, precise (RI l)). {
    intros l; unfold RI; ifeq.
    apply precise_mapsto.
    apply precise_FF.
  }
  cut (safe_onethread G emp c).
  { intros Sc.
    apply soundness; auto.
    - intros [[|[|n]]|[|[|n]]] [[|[|m]]|[|[|m]]] E;
      apply joins_emptymap_l || apply joins_emptymap_r || congruence.
    - unfold pool, RI, mpool; intros l; ifeq; subst; auto.
      intro x; ifeq; ifeq; congruence.
    - compute; auto.
    - intros [|[|i]] or m p E; inversion E; subst; eauto.
  }
  apply semax_safe.
  assert (r: resinvs G 0 = mapsto 5 1) by reflexivity.

  forward.
  rewrite r.
  apply semax_pre with (mapsto_ 5); [ intros x; apply mapsto_mapsto_ | ].
  forward.
  rewrite <-r.
  forward.
  forward.
  rewrite r.
  forward.
  apply semax_pre with TT. compute; auto.
  forward.
Qed.
