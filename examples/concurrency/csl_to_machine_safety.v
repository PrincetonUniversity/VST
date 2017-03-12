(*+ CSL to progress and preservation *)

(* In this file, we use the same notion of thread safety as in the
rest of VST, which is defined using specifications for external
functions. In the rest of VST, we derive safety of the concurrent
(juicy) machine from [progress] and [preservation] of an invariant.

We give a toy version of those definitions and proofs here,
simplifying greatly problems related to step indexing, external calls
and spawning. *)

(* standard files distributed with Coq *)
Require Import List Arith Omega Setoid String.
Require Import Coq.Logic.FunctionalExtensionality.

(* local file *)
Require Import resourcemaps.

Definition interp_lock := resourcemaps.interp_lock.

Definition islock (l : nat) (R : map -> Prop) (m : map) :=
  exists lock, m l = Some (inr lock) /\ interp_lock lock = R.

Lemma islock_inj : forall v R1 R2 m, islock v R1 m -> islock v R2 m -> R1 = R2.
  intros v R1 R2 m [lock1 [E1 H1]] [lock2 [E2 H2]].
  congruence.
Qed.

(*+ Core steps *)

Variable C' : Set.

Variable corestep : C' -> map -> C' -> map -> Prop.

Variable corestep_fun : forall c m c1 m1 c2 m2,
    corestep c m c1 m1 ->
    corestep c m c2 m2 ->
    c1 = c2 /\ m1 = m2.

Variable corestep_sameperms : forall c m c' m', corestep c m c' m' -> sameperms m m'.

Variable corestep_samelocks : forall c m c' m' l lock,
    corestep c m c' m' -> (m l = Some (inr lock) <-> m' l = Some (inr lock)).

Variable cancellative : forall m1 m1' m2 m3, join m1 m2 m3 -> join m1' m2 m3 -> m1 = m1'.

(** Concurrent instructions are built on top of those [C'] *)

Inductive C : Set :=
  | acquire : nat -> C -> C
  | release : nat -> C -> C
  | normal : C' -> C.

(*+ Joinability hypotheses *)

(* Those lemmas can be proved if the support set of maps is finite.
We omit those for conveninence, here. *)

Variable jointo : forall {A} (maps : A -> map) (m : map), Prop.

Axiom selfjoins_jointo : forall {A} (maps : A -> map),
    selfjoins maps -> exists m, jointo maps m.

Axiom jointo_selfjoins : forall {A} (maps : A -> map) m,
    jointo maps m -> selfjoins maps.

Axiom jointo_det : forall {A} (maps : A -> map) m1 m2,
    jointo maps m1 -> jointo maps m2 -> m1 = m2.

Axiom jointo_Some : forall {A} (maps : A -> map) m a addr v,
    jointo maps m -> maps a addr = Some v -> m addr = Some v.

Axiom jointo_Some_inv : forall {A} (maps : A -> map) m addr v,
    jointo maps m -> m addr = Some v -> exists a, maps a addr = Some v.

Lemma join_Some m1 m2 m addr v :
  join m1 m2 m ->
  m1 addr = Some v ->
  m addr = Some v.
Proof.
  intros J E; specialize (J addr).
  rewrite E in J.
  destruct (m2 addr); simpl in *; auto; congruence.
Qed.

Axiom jointo_swapped :
  forall {A} {m1 m2 : A -> map} (Adec:forall x y:A,{x=y}+{x<>y})
    i j Phi e a b a' b',
    swapped m1 m2 i j a b a' b' ->
    join a b e ->
    join a' b' e ->
    jointo m1 Phi ->
    jointo m2 Phi.

(*+ Definition of safety *)

(* We define safety based on specification of externals (acquire and
release) *)

(* no need for an oracle, so it is unit *)
Definition Z := unit.

Record ext : Type := mkext {
    ext_type : Type;
    Pre : ext_type -> Z -> map -> Prop;
    Post : ext_type -> Z -> map -> Prop
  }.

Definition after_external : C -> option C :=
  fun c =>
    match c with
    | acquire _ k => Some k
    | release _ k => Some k
    | _ => None
    end.

(* [Hrel] is related to step indexing levels, and specify that the
PURE of the maps coincide, which is always implied by joinability *)
Variable Hrel : nat -> map -> map -> Prop.
Axiom join_Hrel1 : forall m1 m2 m3 n, join m1 m2 m3 -> Hrel n m3 m1.
Axiom join_Hrel2 : forall m1 m2 m3 n, join m1 m2 m3 -> Hrel n m1 m3.

Inductive safeN_ (at_ext : C -> option ext) : nat -> Z -> C -> map -> Prop :=
    safeN_0 : forall (z : Z) (c : C) (m : map), safeN_ at_ext 0 z c m
  | safeN_step : forall (n : nat) (z : Z) (c c' : C') (m m' : map),
      corestep c m c' m' ->
      safeN_ at_ext n z (normal c') m' ->
      safeN_ at_ext (S n) z (normal c) m
  | safeN_external : forall (n : nat) (z : Z) (c : C) (m : map) (e : ext) (x : ext_type e),
      at_ext c = Some e ->
      Pre e x z m ->
      (forall (m' : map) (z' : Z) (n' : nat),
          n' <= n ->
          Hrel n' m m' ->
          Post e x z' m' ->
          exists c' : C,
            after_external c = Some c' /\
            safeN_ at_ext n' z' c' m') ->
      safeN_ at_ext (S n) z c m.

Lemma safeN_S at_ext n z c m : safeN_ at_ext (S n) z c m -> safeN_ at_ext n z c m.
Proof.
  revert z c m; induction n; intros z c m.
  - intros _. constructor.
  - intros H; inversion H; subst.
    + econstructor; eauto.
    + econstructor; eauto.
Qed.

Lemma strong_nat_ind (P : nat -> Prop) (IH : forall n, (forall i, i < n -> P i) -> P n) n : P n.
Proof.
  apply IH; induction n; intros i li; inversion li; eauto.
Qed.


(*+ Specifications *)

Definition acquire_spec l : ext :=
  mkext
    (nat * (map -> Prop))
    (fun x Ω m =>
       match x with
       | (lx, Rx) =>
         lx = l /\
         islock l Rx m
       end)
    (fun x Ω m =>
       exists m1 m2,
         join m1 m2 m /\
         match x with
         | (lx, Rx) =>
           islock lx Rx m1 /\
           Rx m2
         end).

Definition release_spec l : ext :=
  mkext
    (nat * (map -> Prop))
    (fun x Ω m =>
       exists m1 m2,
         join m1 m2 m /\
         match x with
         | (lx, Rx) =>
           lx = l /\
           islock l Rx m1 /\
           precise Rx /\
           Rx m2
         end)
    (fun x Ω m =>
       match x with
       | (lock, Rx) =>
         islock lock Rx m
       end).

Definition at_ext : C -> option ext :=
  fun c =>
    match c with
    | acquire l _ => Some (acquire_spec l)
    | release l _ => Some (release_spec l)
    | _ => None
    end.

(*+ Concurrent machine *)

(** Semantics of the collection of all threads. Thread and locked
    locks each have their own map. *)

Definition schedule := list nat.

Definition threads := list (map * C).

Definition lockpool := nat -> option (option map).

Definition config := (schedule * threads * lockpool)%type.

Reserved Notation " c1 ===> c2 " (at level 50).

Definition there_is_a_lock_at (m : map) (l : nat) :=
  exists lock,
    m l = Some (inr lock).

Definition map_matches_lock_at (m : map) (l : nat) (mlock : map) :=
  exists lock,
    m l = Some (inr lock) /\
    interp_lock lock mlock.

Inductive machine : config -> config -> Prop :=
  | machine_outofschedule thd pool :
      (nil, thd, pool) ===>
      (nil, thd, pool)
  | machine_scheduleoutofbound i sch thd pool :
      nth thd i = None ->
      (i :: sch, thd, pool) ===>
      (sch, thd, pool)
  | machine_core i sch thd c c' m m' pool :
      corestep c m c' m' ->
      nth thd i = Some (m, normal c) ->
      (i :: sch, thd, pool) ===>
      (i :: sch, nth_upd thd i (m', normal c'), pool)
  | machine_release i sch thd m mlock m' l p pool :
      pool l <> None ->
      nth thd i = Some (m, release l p) ->
      (* mlock |= resinvs l -> *)
      map_matches_lock_at m l mlock ->
      join m' mlock m ->
      (i :: sch, thd, pool) ===>
      (sch, nth_upd thd i (m', p), upd pool l (Some (Some mlock)))
  | machine_acquire_failure i sch thd m l p pool :
      nth thd i = Some (m, acquire l p) ->
      pool l = Some (None) (* locked *) ->
      (i :: sch, thd, pool) ===>
      (sch, thd, pool)
  | machine_acquire_success i sch thd m mlock m' l p pool :
      nth thd i = Some (m, acquire l p) ->
      pool l = Some (Some mlock) (* unlocked *) ->
      join m mlock m' ->
      (i :: sch, thd, pool) ===>
      (i :: sch, nth_upd thd i (m', p), upd pool l (Some None))
where
" c1 ===> c2 " := (machine c1 c2).

Hint Constructors machine.

(*+ Proving machine safety from the invariant *)

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
             | Some (Some m) => m
             | Some None => emptymap
             | None => emptymap
             end
           end.

Definition lockpool_matches_map (pool : lockpool) (Phi : map) :=
  forall l,
    match pool l with
    | Some (Some mlock) => map_matches_lock_at Phi l mlock
    | Some None => there_is_a_lock_at Phi l
    | None => True
    end.

Definition map_matches_lockpool (pool : lockpool) (Phi : map) :=
  forall l lock,
    Phi l = Some (inr lock) ->
    pool l <> None.

Definition invariant n (x : config) :=
  match x with (_, thd, pool) =>
    exists Phi,
      jointo (reindex thd pool) Phi /\
      lockpool_matches_map pool Phi /\
      map_matches_lockpool pool Phi /\
      (forall i oracle m p,
          nth thd i = Some (m, p) ->
          safeN_ at_ext n oracle p m)
  end.

Theorem progress n x : invariant (S n) x -> exists y, x ===> y.
Proof.
  destruct x as (([|i sch], thd), pool). eexists; constructor.
  intros (Phi & J & PM & MP & Safe).
  destruct (nth thd i) as [[m p]|] eqn:E; [ | eauto].
  destruct p as [v c | v c | c].

  - (* Case for acquire *)

    (* The precondition for acquire tells us there is a lock in the
    global map, which means by our invariant that the lock pool has a
    lock there. *)
    pose proof (Safe i tt _ _ E) as Sa.
    inversion Sa as [ | | n0 z c0 m0 ex x atex PRE POST]; subst.
    inversion atex; subst.
    destruct x as [vx Rx].
    simpl in PRE.
    destruct PRE as (-> & isl).
    specialize (MP v).
    destruct isl as [lock [Ev At]].
    assert (EPhiv : Phi v = Some (inr lock)). {
      eapply jointo_Some with (a := inl i); eauto.
      simpl. rewrite E; auto.
    }
    specialize (MP lock EPhiv).
    destruct (pool v) as [ [ mlock | ] | ] eqn:Epoolv; [ | | congruence ].

    + (* In the case the lock is unlocked, [acquire] succeeds *)
      apply jointo_selfjoins in J.
      destruct (J (inl i) (inr v)) as [m' J']. congruence.
      simpl in J'. rewrite E in J'. rewr (pool v) in J'.
      eexists.
      eapply machine_acquire_success.
      now apply E.
      now apply Epoolv.
      now apply J'.

    + (* In the case the lock is locked, [acquire] fails *)
      eexists.
      eapply machine_acquire_failure. now apply E.
      assumption.

  - (* Case for release *)

    (* To determine the next state, we need to use [release]'s
    precondition which provides one possible subheap [m2] of the
    thread's heap.  (By [release]'s precondition, we also know that
    this subheap is unique, which will be useful in the preservation
    theorem.) *)
    pose proof (Safe i tt _ _ E) as Sa.
    inversion Sa as [ | | n0 z c0 m0 ex x atex PRE POST]; subst.
    inversion atex; subst.
    destruct x as [vx Rx].
    simpl in PRE.
    destruct PRE as (m1 & m2 & J12 & -> & isl & Rm2).

    (* Using this [m2] we prove that the global map, we prove that the
    lock pool indeed has a lock there. *)
    specialize (MP v).
    destruct isl as [lock [Ev At]].
    pose proof (J12 v) as J12v.
    rewr (m1 v) in J12v. destruct (m2 v); inversion J12v.
    assert (EPhiv : Phi v = Some (inr lock)). {
      eapply jointo_Some with (a := inl i); eauto.
      simpl. rewrite E. auto.
    }
    simpl.
    specialize (MP lock EPhiv).

    (* We now can apply the release machine step *)
    eexists.
    match goal with |- _ ===> ?y => pose y end.
    eapply machine_release; [ apply MP | apply E | .. ].
    + unfold map_matches_lock_at.
      exists lock. split; auto.
      subst Rx.
      apply Rm2.
    + apply J12.

  - (* Case for corestep *)
    pose proof (Safe i tt _ _ E) as Sa.
    inversion Sa; subst.
    + eexists; eapply machine_core; eassumption.
    + discriminate.

Qed.

Theorem preservation n x y : x ===> y -> invariant (S n) x -> invariant n y.
Proof.
  destruct x as (([|i sch], thd), pool);
    intros xy; inversion xy; subst; intros (Phi & J & PM & MP & Sa); simpl fst in *; simpl snd in *.
  - (* out of schedule *)
    hnf; intuition; eauto.
    exists Phi; intuition.
    eapply safeN_S.
    eapply Sa; eauto.

  - (* schedule out of bound *)
    hnf; intuition; eauto.
    exists Phi; intuition.
    eapply safeN_S.
    eapply Sa; eauto.

  - (* Case of a corestep *)
    assert (SJ : selfjoins (reindex (nth_upd thd i (m', normal c')) pool)). {
      apply jointo_selfjoins in J.
      eapply selfjoins_sameperms_compat; [..|apply J]; intros [k|]; simpl; eauto.
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      rewr (nth thd k).
      eapply corestep_sameperms; eassumption.
    }
    apply selfjoins_jointo in SJ.
    destruct SJ as [Phi' J'].
    exists Phi'.
    repeat split; auto.
    + intros l. specialize (PM l).
      destruct (pool l) as [[mlock|]|].
      * destruct PM as [lock [E asd]].
        exists lock; intuition.
        {
          destruct (jointo_Some_inv _ _ _ _ J E) as [ [x | x] Ex ]; simpl in Ex.
          - destruct (nth thd x) as [[m0 c0] | ] eqn:Emx.
            + destruct (eq_nat_dec i x).
              * subst x. assert (m0 = m) by congruence; subst m0.
                eapply (jointo_Some _ _ (inl i)). eassumption.
                simpl; erewrite nth_nth_upd; eauto.
                ifeq; eauto.
                rewrite <-corestep_samelocks; eauto.
              * eapply (jointo_Some _ _ (inl x)). eassumption. simpl.
                erewrite nth_nth_upd. ifeq. tauto. rewrite Emx. auto. eauto.
            + inversion Ex.
          - eapply (jointo_Some _ _ (inr x)). eassumption. simpl. auto.
        }
      * destruct PM as [lock E].
        exists lock; intuition.
        {
          destruct (jointo_Some_inv _ _ _ _ J E) as [ [x | x] Ex ]; simpl in Ex.
          - destruct (nth thd x) as [[m0 c0] | ] eqn:Emx.
            + destruct (eq_nat_dec i x).
              * subst x. assert (m0 = m) by congruence; subst m0.
                eapply (jointo_Some _ _ (inl i)). eassumption.
                simpl; erewrite nth_nth_upd; eauto.
                ifeq; eauto.
                rewrite <-corestep_samelocks; eauto.
              * eapply (jointo_Some _ _ (inl x)). eassumption. simpl.
                erewrite nth_nth_upd. ifeq. tauto. rewrite Emx. auto. eauto.
            + inversion Ex.
          - eapply (jointo_Some _ _ (inr x)). eassumption. simpl. auto.
        }
      * auto.
    + intros l lock AT. apply (MP _ lock).
      destruct (jointo_Some_inv _ _ _ _ J' AT) as [ [ x | x ] Ex ]; simpl in Ex.
      * erewrite nth_nth_upd in Ex; [ | eassumption ].
        {
          destruct (nth thd x) as [[m0 c0] | ] eqn:Emx.
          - destruct (eq_nat_dec i x).
            + subst x. assert (m0 = m) by congruence; subst m0.
              eapply (jointo_Some _ _ (inl i)). eassumption.
              simpl. rewr (nth thd i).
              revert Ex.
              match goal with |- ?P -> ?Q => cut (Q <-> P); [ intuition | ] end.
              eapply corestep_samelocks. eauto.
            + eapply (jointo_Some _ _ (inl x)). eassumption. simpl.
              rewr (nth thd x) in *. auto.
          - destruct (eq_nat_dec i x).
            + congruence.
            + inversion Ex.
        }
      * eapply (jointo_Some _ _ (inr x)). eassumption. simpl. auto.
    + intros j oracle; specialize (Sa j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      * specialize (Sa _ _ H5).
        intros. rewr.
        intros <- <- .
        inversion Sa; subst. 2:inversion H1.
        destruct (corestep_fun _ _ _ _ _ _ H4 H2) as [<- <-].
        assumption.
      * intros; apply safeN_S; eauto.

  - (* Case of release *)
    exists Phi. intuition.
    + (* First, we prove joinability *)
      assert (Empl : match pool l with None => False | Some None => True | Some (Some ml) => empty ml end). {
        destruct (pool l) as [[ml|]|] eqn:E; auto.
        cut (empty ml /\ empty mlock);[intuition|].
        destruct H6 as [lock [Eml SAT]].

        (* We need preciseness, which we get it thanks to the precondition *)
        assert (PR : precise (interp_lock lock)). {
          specialize (Sa i tt _ _ H5).
          inversion Sa as [ | | n0 z c m0 ex x ae PRE POST]; subst.
          assert (A:Hrel n m m') by (eapply join_Hrel1; eauto).
          inversion ae; subst.
          destruct x as [vx Rx].
          destruct PRE as (m1 & m2 & J12 & -> & isl & PreciseRx & Rm2).
          destruct isl as [lock' [Em1l <-]].
          assert (m l = Some (inr lock')). {
            specialize (J12 l).
            rewrite Em1l in *.
            simpl in J12.
            destruct (m2 l); congruence.
          }
          replace lock' with lock in * by congruence.
          assumption.
        }

        apply precise_join with (interp_lock lock); eauto.
        - specialize (PM l); rewrite E in PM; auto.
          hnf in PM.
          destruct PM as [lock' [El SAT']].
          assert (lock = lock'). {
            assert (Phi l = Some (inr lock)). {
              eapply jointo_Some with (a := inl i); eauto; simpl.
              rewr (nth thd i). auto.
            }
            congruence.
          }
          subst lock'.
          apply SAT'.
        - assert (D:inl i <> inr l) by congruence.
          apply jointo_selfjoins in J.
          specialize (J _ _ D); simpl in J.
          rewr (nth thd i) in J.
          rewr (pool l) in J.
          pose proof (join_joins_distrib m' mlock m H7 ml); intuition eauto.
      }
      eapply (jointo_swapped natnateqdec (inl i) (inr l) Phi); [ .. | eapply J].
      * unfold swapped, reindex, upd; repeat split.
        {
          intros [|] a b; [ | ifeq ].
          - erewrite nth_nth_upd;[|eassumption].
            ifeq; congruence.
          - subst. tauto.
          - destruct (pool n); reflexivity.
        }
      * apply join_empty; simpl.
        destruct (pool l) as [[ml|]|]; unfold empty; auto.
      * erewrite nth_nth_upd;[|eassumption].
        ifeq; ifeq.
        rewr; eauto.
    + intros k; unfold upd; ifeq; subst; auto.
      * hnf.
        destruct H6 as [lock [El SAT]].
        exists lock; intuition.
        eapply jointo_Some with (a := inl i); eauto; simpl.
        rewr (nth thd i). auto.
      * specialize (PM k); auto.
    + intros k lock Ek. unfold upd; ifeq.
      * congruence.
      * apply (MP k lock Ek).
    + erewrite nth_nth_upd in H. 2:eassumption.
      ifeq; [ | apply safeN_S; eapply Sa; eauto ].
      subst i0.
      specialize (Sa i tt _ _ H5). injection H as <- <-.
      inversion Sa as [ | | n0 z c m0 ex x ae PRE POST]; subst.
      assert (A:Hrel n m m') by (eapply join_Hrel1; eauto).
      specialize (POST m' oracle n (le_n _) A).
      destruct POST as [c' [E Sa']].
      * inversion ae; subst.
        destruct x as [vx Rx].
        simpl in PRE |- *.
        destruct PRE as (m1 & m2 & J12 & E & isl & PreciseRx & Rm2).
        intuition.
        subst.
        (* Here, we need preciseness in the specification of release *)
        assert (m2 = mlock). {
          apply eqmap_eq.
          eapply PreciseRx; auto.
          - destruct H6 as [lock [Eml SAT]].
            destruct isl as [lock' [Em1l' <-]].
            assert (m l = Some (inr lock')). {
              eapply join_Some; eauto.
            }
            replace lock' with lock in * by congruence.
            auto.
          - exists m1. apply join_comm. apply J12.
          - exists m'. apply join_comm. assumption.
        }
        subst m2.
        assert (m' = m1) by (eapply cancellative; eauto).
        congruence.
      * inversion ae; subst.
        inversion E; subst.
        apply Sa'.

  - (* acquire (locked) *)
    exists Phi; intuition.
    apply safeN_S.
    eapply Sa; eauto.

  - (* acquire (unlocked) *)
    exists Phi; intuition.
    + eapply (jointo_swapped natnateqdec (inl i) (inr l) Phi); [ .. | apply J].
      * unfold swapped, reindex, upd; repeat split.
        intros [|] a b; try (ifeq; (congruence || subst; tauto)).
        erewrite nth_nth_upd;[|eassumption].
        ifeq; congruence.
      * rewr. rewr. eauto.
      * rewr. ifeq.
        erewrite nth_nth_upd;[|eassumption].
        ifeq. auto.
    + intros k; unfold upd; ifeq; subst; auto.
      * specialize (PM k). rewr (pool k) in PM. destruct PM as [lock []]; exists lock. assumption.
      * apply (PM k).
    + intros k lock Ek. unfold upd; ifeq.
      * subst k. specialize (PM l). congruence.
      * apply (MP k lock Ek).
    + erewrite nth_nth_upd in H. 2:eassumption.
      ifeq; [ | now apply safeN_S; eapply Sa; eauto ].
      subst i0.
      injection H as <- <-.
      specialize (Sa _ tt _ _ H4).
      inversion Sa as [ | | n0 z c m0 ex x ae PRE POST]; subst.
      assert (A:Hrel n m m') by (eapply join_Hrel2; eauto).
      specialize (POST m' oracle n (le_n _) A).
      destruct POST as [c' [E Sa']].
      * inversion ae; subst.
        destruct x as [vx Rx].
        simpl in PRE |- *.
        destruct PRE as [-> isl].
        exists m, mlock; intuition.
        destruct isl as [lock [Eml <-]].
        specialize (PM l). rewr (pool l) in PM.
        destruct PM as [lock' [E' SAT]].
        assert (Phi l = Some (inr lock)). {
          eapply jointo_Some with (a := inl i); eauto; simpl.
          rewr (nth thd i). auto.
        }
        congruence.
      * inversion ae; subst.
        inversion E; subst.
        apply Sa'.
Qed.

Inductive csafe : nat -> config -> Prop :=
| csafe_0 sch thd pool : csafe 0 (sch, thd, pool)
| csafe_halted n thd pool : csafe n (nil, thd, pool)
| csafe_core n sch thd pool thd' pool' :
    machine (sch, thd, pool) (sch, thd', pool') ->
    csafe n (sch, thd', pool') ->
    csafe (S n) (sch, thd, pool)
| csafe_sch n i sch thd pool thd' pool' :
    machine (i :: sch, thd, pool) (sch, thd', pool') ->
    (forall sch', csafe n (sch', thd', pool')) ->
    csafe (S n) (i :: sch, thd, pool).

Lemma safety_invariant n state :
  invariant n state -> csafe n state.
Proof.
  assert (forall n s s' t p, invariant n (s, t, p) -> invariant n (s', t, p))
    by (clear; intros n s s' t p (Phi & J & PM & MP & Safe); exists Phi; intuition).
  revert state; induction n; intros ((sch, thd), pool) Inv.
  now constructor.
  destruct (progress _ _ Inv) as (x, step).
  assert (pre : forall y, (sch, thd, pool) ===> y -> invariant n y)
    by (intros; eapply preservation; eauto).
  inversion Inv as (Phi & J & PM & MP & Safe).
  inversion step; subst.
  - constructor.
  - eapply csafe_sch; [ now eapply step | ]; eauto.
  - eapply csafe_core; eauto.
  - eapply csafe_sch; [ now eapply step | ]; eauto.
  - eapply csafe_sch; [ now eapply step | ]; eauto.
  - eapply csafe_core; eauto.
Qed.
