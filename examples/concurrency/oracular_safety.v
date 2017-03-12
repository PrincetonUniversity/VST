(*+ Reasoning about oracular safety *)

(* In this file, we use the same notion as safety as in the rest of
VST and we define oracular specifications (specifications that can
reason about the oracle) to simulate, in term of safety, the bad/good
oracle rules, through the WITH variable (x, below).

Because those are too complicated to reason about in the program
logic, we also define "clean" specifications (that require nothing
about the oracle).  Because the "dirty" specifications are only using
the oracle in a "optimist" way, oracular safety is actually easier to
prove, which can be stated through the theorem "clean safety => dirty
safety". (which one should read as "safety for oracular-aware
specifications" is less strong than regular safety) *)

Definition val := nat.

Variable C' : Set.
Inductive C : Set :=
  | acquire : val -> C -> C
  | release : val -> C -> C
  | normal : C' -> C.

Definition M := val -> option nat.
Variable corestep : C' -> M -> C' -> M -> Prop.

Variable islock : val -> (M -> Prop) -> M -> Prop.
Variable islock_inj : forall v R1 R2 m, islock v R1 m -> islock v R2 m -> R1 = R2.

Definition Z := list M.

Record ext : Type := mkext {
    ext_type : Type;
    Pre : ext_type -> Z -> M -> Prop;
    Post : ext_type -> Z -> M -> Prop
  }.

Definition good_oracle (Ω : list M) (R : M -> Prop) := exists m Ω', Ω = cons m Ω' /\ R m.

Definition good_oracle_old (Ω : list M) (m : M) (v : val) :=
  exists R, islock v R m /\ exists mlock Ω', Ω = cons mlock Ω' /\ R mlock.

Definition tail {A} (l : list A) := match l with nil => None | cons _ l => Some l end.

(*+ "Oracular" specifications of acquire/release *)

Definition acquire_spec_old l : ext :=
  mkext
    (Prop * val * list M * (M -> Prop))
    (fun x Ω m =>
       match x with
       | (okx, lx, Ωx, Rx) =>
         lx = l /\
         islock l Rx m /\
         (match Ω with
          | nil => ~okx
          | cons mlock Ω' => Ω' = Ωx /\ (Rx mlock <-> okx)
          end)
       end)
    (fun x Ω m =>
       match x with
       | (okx, lx, Ωx, Rx) =>
         Ω = Ωx /\
         okx /\
         islock lx Rx m
       end).

Definition acquire_spec l : ext :=
  mkext
    (val * list M * (M -> Prop))
    (fun x Ω m =>
       match x with
       | (lx, Ωx, Rx) =>
         lx = l /\
         islock l Rx m /\
         Ω = Ωx
       end)
    (fun x Ω m =>
       match x with
       | (lx, Ωx, Rx) =>
         (match Ωx with
          | nil => False
          | cons phi Ωx' => Ω = Ωx' /\ Rx phi
          end) /\
         islock lx Rx m
       end).

Definition release_spec l : ext :=
  mkext
    (val * list M * (M -> Prop))
    (fun x Ω m =>
       match x with
       | (lx, Ωx, Rx) =>
         lx = l /\
         islock l Rx m /\
         Ω = Ωx
       end)
    (fun x Ω m =>
       match x with
       | (lock, Ωx, Rx) =>
         Ω = Ωx /\
         islock lock Rx m
       end).

(*+ Definition of safety *)

Definition oracle_at_ext_old : C -> option ext :=
  fun c =>
    match c with
    | acquire l _ => Some (acquire_spec_old l)
    | release l _ => Some (release_spec l)
    | _ => None
    end.

Definition oracle_at_ext : C -> option ext :=
  fun c =>
    match c with
    | acquire l _ => Some (acquire_spec l)
    | release l _ => Some (release_spec l)
    | _ => None
    end.

Definition after_external : C -> option C :=
  fun c =>
    match c with
    | acquire _ k => Some k
    | release _ k => Some k
    | _ => None
    end.

Variable Hrel : nat -> M -> M -> Prop.
Variable Hrel_islock : forall n m m' R v, Hrel n m m' -> islock v R m -> islock v R m'.

Inductive safeN_ (at_ext : C -> option ext) : nat -> Z -> C -> M -> Prop :=
    safeN_0 : forall (z : Z) (c : C) (m : M), safeN_ at_ext 0 z c m
  | safeN_step : forall (n : nat) (z : Z) (c c' : C') (m m' : M),
      corestep c m c' m' ->
      safeN_ at_ext n z (normal c') m' ->
      safeN_ at_ext (S n) z (normal c) m
  | safeN_external : forall (n : nat) (z : Z) (c : C) (m : M) (e : ext) (x : ext_type e),
      at_ext c = Some e ->
      Pre e x z m ->
      (forall (m' : M) (z' : Z) (n' : nat),
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

(*+ New way of writing specs *)

Lemma strong_nat_ind (P : nat -> Prop) (IH : forall n, (forall i, i < n -> P i) -> P n) n : P n.
Proof.
  apply IH; induction n; intros i li; inversion li; eauto.
Qed.

Require Import List.

Theorem old_new n Ω c m :
  safeN_ oracle_at_ext_old  n Ω c m ->
  safeN_ oracle_at_ext n Ω c m.
Proof.
  revert n Ω c m; induction n as [n SIH] using strong_nat_ind; intros Ω c m Safe.

  (* we reason by induction on clean safety *)
  induction Safe as [ | | n Ω c m e x E PRE SPOST ];
    try solve [econstructor; eauto].
  destruct c as [ lock k | lock k | c ].

  - (* acquire *)
    injection E as <-; simpl in *.
    destruct x as (((okx, vx), orax), R), PRE as [-> [isl PRE]].
    destruct Ω as [ | mlock Ω ].
    + simpl.
      apply safeN_external with
      (e := acquire_spec lock)
        (x := (lock, nil, R));
        simpl; intuition.
    + simpl.
      apply safeN_external with
      (e := acquire_spec lock)
        (x := (lock, mlock :: Ω, R));
        simpl; try solve [intuition].
      intros m' z' n' nn' HREL [[-> SAT] isl'].
      specialize (SPOST m' Ω n' nn' HREL).
      destruct SPOST as (c', (Eq, Safe)).
      * intuition.
      * exists c'; intuition.

  - (* release *)
    eapply safeN_external; eauto.
    intros m' z' n' H H0 H1.
    destruct (SPOST m' z' n' H H0 H1) as [c' Sa].
    exists c'; intuition.

  - (* corestep *)
    inversion E.
Qed.

Theorem new_old n Ω c m :
  safeN_ oracle_at_ext  n Ω c m ->
  safeN_ oracle_at_ext_old n Ω c m.
Proof.
  revert n Ω c m; induction n as [n SIH] using strong_nat_ind; intros Ω c m Safe.

  (* we reason by induction on clean safety *)
  induction Safe as [ | | n Ω c m e x E PRE SPOST ];
    try solve [econstructor; eauto].
  destruct c as [ lock k | lock k | c ].

  - (* acquire *)
    injection E as <-; simpl in *.
    destruct x as ((vx, orax), R), PRE as [-> [isl PRE]].
    destruct Ω as [ | mlock Ω ].
    + simpl.
      apply safeN_external with
      (e := acquire_spec_old lock)
        (x := (False, lock, nil, R));
        simpl; intuition.
    + simpl.
      apply safeN_external with
      (e := acquire_spec_old lock)
        (x := (R mlock, lock, Ω, R));
        simpl; try solve [intuition].
      intros m' z' n' nn' HREL [-> [SAT isl']].
      subst orax.
      specialize (SPOST m' Ω n' nn' HREL).
      destruct SPOST as (c', (Eq, Safe)).
      * intuition.
      * exists c'; intuition.

  - (* release *)
    eapply safeN_external; eauto.
    intros m' z' n' H H0 H1.
    destruct (SPOST m' z' n' H H0 H1) as [c' Sa].
    exists c'; intuition.

  - (* corestep *)
    inversion E.
Qed.


(*+ Intuition of "good oracle" rule *)

Lemma safeN_oracle_step_ n m l k R mlock :
  islock l R m ->
  R mlock ->
  (forall Ω, safeN_ oracle_at_ext_old (S n) Ω (acquire l k) m) ->
  forall m', Hrel n m m' ->
    (forall Ω, safeN_  oracle_at_ext_old n Ω k m').
Proof.
  intros Isl Sat Safe.

  (* first, with dummy oracle *)
  pose proof (Safe (cons mlock nil)) as Safe'.
  inversion Safe' as [ | | A B C D e x atex PRE POST K L M ]; subst A B C D.
  injection atex as <- .
  destruct x as (((okx, lx), Ωx), Rx).
  simpl in PRE, POST; unfold good_oracle in PRE.
  destruct PRE as (-> & isl & <- & PRE).

  intros m' Hm' Ω.

  (* now with real oracle *)
  pose proof (Safe (cons mlock Ω)) as Safe''.

  inversion Safe'' as [ | | A B C D e'' x'' atex'' PRE'' POST'' K L M ]; subst A B C D.
  injection atex'' as <- .
  destruct x'' as (((okx'', lx''), Ωx''), Rx'').
  simpl in PRE'', POST''; unfold good_oracle in PRE''.
  destruct PRE'' as (-> & isl'' & E'' & PRE'').

  assert (POST''' :
            forall (m' : M) (z' : Z) (n' : nat),
              n' <= n -> Hrel n' m m' -> z' = Ωx'' /\ okx'' /\ islock l Rx'' m' -> safeN_   oracle_at_ext_old n' z' k m').
  {
    clear -POST''.
    intros m' z' n' Hn HH Ha.
    specialize (POST'' m' z' n' Hn HH Ha).
    destruct POST'' as [c' [Ec' S]].
    injection Ec' as <- .
    auto.
  }

  apply POST'''; auto. split; auto. split; auto.
  Require Import Setoid.
  rewrite <-PRE''.
  replace R with Rx'' in * by (eapply islock_inj; eauto).
  now subst; auto.
  now eapply Hrel_islock; eauto.
Qed.

(*+ Intuition of "bad oracle" rule *)

Lemma safeN_oracle_step_rev_false_ n m l k R mlock :
  islock l R m ->
  ~ R mlock ->
  (forall Ω, safeN_ oracle_at_ext_old (S n) (cons mlock Ω) (acquire l k) m).
Proof.
  intros isl nSat Ω.
  apply safeN_external with (acquire_spec_old l) (False, l, Ω, R); simpl; intuition; subst.
Qed.

Lemma safeN_oracle_step_rev_nil_ n m l k R :
  islock l R m ->
  safeN_ oracle_at_ext_old (S n) nil(acquire l k) m.
Proof.
  intros isl.
  apply safeN_external with (acquire_spec_old l) (False, l, nil, R); simpl; intuition; subst.
Qed.


(*+ "Clean" specifications not mentioning oracle *)

Definition clean_acquire_spec l : ext :=
  mkext
    (val * (M -> Prop))
    (fun x Ω m =>
       match x with
       | (lx, Rx) =>
         lx = l /\
         islock l Rx m
       end)
    (fun x Ω m =>
       match x with
       | (lx, Rx) =>
         islock lx Rx m
       end).

Definition clean_release_spec l : ext :=
  mkext
    (val * (M -> Prop))
    (fun x Ω m =>
       match x with
       | (lx, Rx) =>
         lx = l /\
         islock l Rx m
       end)
    (fun x Ω m =>
       match x with
       | (lock, Rx) =>
         islock lock Rx m
       end).

Definition clean_at_ext : C -> option ext :=
  fun c =>
    match c with
    | acquire l _ => Some (clean_acquire_spec l)
    | release l _ => Some (clean_release_spec l)
    | _ => None
    end.

(*+ Proof that clean safety => dirty safety *)

Require Import Arith.

Open Scope list_scope.

(* no need for excluded middle thanks to the trick in the spec (ok <->
R mlock instead of doing the case analysis (e.g. ok = true <-> R
mlock) *)

Theorem clean_safeN_implies_safeN_ n Ω c m :
  safeN_ clean_at_ext  n Ω c m ->
  safeN_ oracle_at_ext n Ω c m.
Proof.
  intros H; apply old_new.
  revert n Ω c m H; induction n as [n SIH] using strong_nat_ind; intros Ω c m Safe.

  (* we reason by induction on clean safety *)
  induction Safe as [ | | n Ω c m e x E PRE SPOST ];
    try solve [econstructor; eauto].
  destruct c as [ lock k | lock k | c ].
  - (* acquire *)
    injection E as <-; simpl in *.
    destruct x as (lx, R), PRE as [-> PRE].
    destruct Ω as [ | mlock Ω ].
    + simpl.
      apply safeN_external with
      (e := acquire_spec_old lock)
        (x := (False, lock, nil, R));
        simpl; intuition.
    + simpl.
      apply safeN_external with
      (e := acquire_spec_old lock)
        (x := (R mlock, lock, Ω, R));
        simpl; try solve [intuition].
      intros m' z' n' nn' HREL [-> [Rm isl]].
      specialize (SPOST m' Ω n' nn' HREL isl).
      destruct SPOST as (c', (Eq, Safe)). injection Eq as <-.
      exists k; split; auto.
      apply SIH; auto with *.
  - (* release *)
    injection E as <-; simpl in *.
    destruct x as (lx, R), PRE as [-> PRE].
    apply safeN_external with
    (e := release_spec lock)
      (x := (lock, Ω, R));
      simpl; try solve [intuition].
    intros m' z' n' nn' HREL [-> isl].
    specialize (SPOST m' Ω n' nn' HREL isl).
    destruct SPOST as (c', (Eq, Safe)). injection Eq as <-.
      exists k; split; auto.
      apply SIH; auto with *.
  - (* corestep *)
    inversion E.
Qed.


(*+ Parallel composition of safety *)

(*+ BELOW, THE OTHER FILE *)

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

Definition instruction := C.

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

Definition map := M.

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

Inductive step : Rel (globals * oracle * map * C) :=
(*
  | step_halted G oracle m :
      (G, oracle, m, nil) --->
      (G, oracle, m, nil)
*)
  | step_core G oracle c c' m m' :
      corestep c m c' m' ->
      (G, oracle, m, normal c) --->
      (G, oracle, m', normal c')
  | step_release G oracle m mlock m' l p :
      mlock |= resinvs G l ->
      join m' mlock m ->
      (G, oracle, m, release l p) --->
      (G, oracle, m', p)
  | step_acquire G oracle m mlock m' l p :
      mlock |= resinvs G l ->
      join m mlock m' ->
      (G, mlock :: oracle, m, acquire l p) --->
      (G, oracle, m', p)
  | step_acquire_wrong_oracle G oracle m mlock l p :
      ~(mlock |= resinvs G l /\ joins m mlock) ->
      (G, mlock :: oracle, m, acquire l p) --->
      (G, mlock :: oracle, m, acquire l p)
  | step_acquire_empty_oracle G m l p :
      (G, nil, m, acquire l p) --->
      (G, nil, m, acquire l p)
(*
  | step_spawn G PRE oracle m mspawned m' f p :
      funspecs G f = Some PRE ->
      mspawned |= PRE ->
      join m' mspawned m ->
      (G, oracle, m, spawn f :: p) --->
      (G, oracle, m', p)
*)
where
" c1 ---> c2 " := (step  c1 c2).

(* oh wait that was supposed to be defined in terms of safety

MAYBE prove jsafeN => safety wrt these steps
AND THEN => safety of the machine

*)

Hint Constructors step.

(*+ Concurrent machine *)

(** Semantics of the collection of all threads. Thread and locked
    locks each have their own map. *)

Definition schedule := list nat.

Definition threads := list (map * C).

Definition lockpool := val -> option map.

Definition functions := string -> option C.

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
  | machine_core i sch F G thd c c' m m' pool :
      corestep c m c' m' ->
      nth thd i = Some (m, normal c) ->
      (i :: sch, F, G, thd, pool) ===>
      (i :: sch, F, G, nth_upd thd i (m', normal c'), pool)
  | machine_release i sch F G thd m mlock m' l p pool :
      nth thd i = Some (m, release l p) ->
      mlock |= resinvs G l ->
      join m' mlock m ->
      (i :: sch, F, G, thd, pool) ===>
      (sch, F, G, nth_upd thd i (m', p), upd pool l (Some mlock))
  | machine_acquire_failure i sch F G thd m l p pool :
      nth thd i = Some (m, acquire l p) ->
      pool l = None (* locked *) ->
      (i :: sch, F, G, thd, pool) ===>
      (sch, F, G, thd, pool)
  | machine_acquire_success i sch F G thd m mlock m' l p pool :
      nth thd i = Some (m, acquire l p) ->
      pool l = Some mlock (* unlocked *) ->
      join m mlock m' ->
      (i :: sch, F, G, thd, pool) ===>
      (i :: sch, F, G, nth_upd thd i (m', p), upd pool l None)
(*
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
*)
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
  - destruct (nth thd i) as [[m p]|] eqn:E; [ | eauto].
    destruct (S i nil m p E _ (star_refl _ _)) as [z Hz].
    inversion Hz; subst.
    + eexists. eapply machine_core; reflexivity || eauto.
    + eexists. eapply machine_release; reflexivity || eauto.
    + clear Hz (* the oracle is actually used here, z/Hz is useless. *).
      destruct (J (inl i) (inr l)) as [o Jl]; [congruence|]; simpl in Jl; rewrite E in *.
      destruct (pool l) eqn:El (* is the pool lock unlocked or locked? *).
      * eexists. eapply machine_acquire_success; simpl; eauto.
      * eexists. eapply machine_acquire_failure; simpl; eauto.
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

Variable sameperms_corestep : forall c m c' m', corestep c m c' m' -> sameperms m m'.

Theorem subject_reduction x y : x ===> y -> P x -> P y.
Proof.
  destruct x as (((([|i sch], F), G), thd), pool);
    intros xy; inversion xy; subst; intros (PR & FF & J & M & S);
      simpl fst in *; simpl snd in *.

  - (* out of schedule *)
    hnf; intuition; eauto.

  - (* schedule out of bound *)
    hnf; intuition; eauto.

  - (* corestep *)
    repeat split; auto.
    + eapply selfjoins_sameperms_compat; [..|apply J]; intros [k|]; simpl; eauto.
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      unfold map.
      rewrite H7.
      eapply sameperms_corestep; eassumption.
    + intros j oracle; specialize (S j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      intros. rewr.
      intros <- <- .
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
        intros [|] a b; [ | ifeq ].
        -- erewrite nth_nth_upd;[|eassumption].
           ifeq; congruence.
        -- subst. tauto.
        -- destruct (pool n); reflexivity.
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
        intros [|] a b; try (ifeq; (congruence || subst; tauto)).
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


(*+ (removed Hoare logic part) *)

(*+ Trying to relate spec safety to "oracle steps" safety *)
(** It turns out that the joinability condition of the oracle step
can't be ensure (see last admit below) *)

Variable corestep_fun : forall c m c1 m1 c2 m2,
    corestep c m c1 m1 ->
    corestep c m c2 m2 ->
    c1 = c2 /\ m1 = m2.

Variable excluded_middle : forall P : Prop, P \/ ~P.

Theorem jsafeN_versus_step_safeN_ n z c m G :
  safeN_ oracle_at_ext_old n z c m -> safe_ n step (G, z, m, c).
Proof.
  revert n z c m; induction n as [n SIH] using strong_nat_ind; intros z c m Safe.

  inversion Safe as
      [ | n_ z1 c_ c' m1 m' Step safe H5 H6 H7 H8
        | n_ z1 c1 m1 ex x atex Pre Post H6 H7 H8 H9]; subst.
  - intros state n l0. omega.
  - apply safe__det with (G, z, m', normal c').
    + eapply SIH. omega. assumption.
    + constructor; auto.
    + intros state step.
      inversion step; subst.
      repeat f_equal; eapply corestep_fun; eauto.
  - destruct c as [v c | v c | c]; inversion atex as [E]; subst ex.
    + destruct x as [[[okx vx] orax] Rx].
      simpl in Pre0.
      (* rename Post0 into Post. report? this makes the next line fail?? *)
      destruct Pre0 as [-> [isl Pre_ora]].
      rename Post0 into Post.
      destruct z as [ | mlock z ].
      * apply safe_safe_.
        apply safe_selfloop.
        -- eapply step_acquire_empty_oracle.
        -- intros y sy; inversion sy; subst. reflexivity.
      * destruct Pre_ora as [-> COR].
        destruct (excluded_middle (Rx mlock)) as [sat|nsat]; swap 1 2.
        -- apply safe_safe_.
           apply safe_selfloop.
           ++ apply step_acquire_wrong_oracle.
              intros [sat' J].
              apply nsat.
              admit (* relate this Rx to resinvs G somehow *).
           ++ intros y sy; inversion sy; subst.
              ** exfalso; apply nsat.
                 admit (* same as above *).
              ** reflexivity.
        -- rename n_ into n.
           assert (A: Hrel n m m) by admit.
           destruct (Post m orax n (le_n _) A) as [c' [afex Safe']].
           ++ simpl. intuition.
           ++ eapply safe__det.
              ** eapply SIH. omega. apply Safe'.
              ** injection afex as <-.
                 apply step_acquire.
                 --- admit (* same as above *).
                 --- admit (* PROBLEM HERE: NOT A HYPOTHESIS *).
Abort.


(*+ Trying to relate spec safety to "oracle steps" safety *)

Definition Q n (x : config) :=
  match x with (_, F, G, thd, pool) =>
    (forall l, precise (resinvs G l)) /\
    functions_safe G F /\
    selfjoins (reindex thd pool) /\
    lockpool_matches pool (resinvs G) /\
    (forall i oracle m p,
        nth thd i = Some (m, p) ->
        safeN_ oracle_at_ext n oracle p m)
  end.

Theorem progress_Q n x : Q (S n) x -> exists y, x ===> y.
Proof.
  destruct x as (((([|i sch], F), G), thd), pool). eexists; constructor.
  intros (PR & FF & J & M & Safe).
  destruct (nth thd i) as [[m p]|] eqn:E; [ | eauto].
  destruct p as [v c | v c | c]; swap 1 3.
  - pose proof (Safe i nil _ _ E) as Sa.
    inversion Sa; subst.
    + eexists; eapply machine_core; eassumption.
    + discriminate.
  - pose proof (Safe i nil _ _ E) as Sa.
    inversion Sa as [ | | n0 z c0 m0 ex x atex PRE POST]; subst.
    inversion atex; subst.
    destruct x as [[vx orax] Rx].
    simpl in PRE.
    destruct PRE as [-> [isl <-]].
    (* now one should get the map *)
    eexists.
    eapply machine_release; [ apply E | .. ].
    + (* should add the SEP clause to the spec. I anticipate no
      problem here. *)
      admit.
    + (* here again the PRE should have given information that
      splitting is possible. (with precisely this join) *)
      admit.
  - specialize (M v).
    destruct (pool v) eqn:p.
    + eexists; eapply machine_acquire_success; [ apply E | .. ]. eassumption.
      admit (* implied by J, whatever *).
    + eexists; eapply machine_acquire_failure; [ apply E | .. ]. eassumption.
Abort.

Theorem Q_subject_reduction n x y : x ===> y -> Q (S n) x -> Q n y.
Proof.
  destruct x as (((([|i sch], F), G), thd), pool);
    intros xy; inversion xy; subst; intros (PR & FF & J & M & Sa);
      simpl fst in *; simpl snd in *.
  - (* out of schedule *)
    hnf; intuition; eauto.
    eapply safeN_S.
    eapply Sa; eauto.

  - (* schedule out of bound *)
    hnf; intuition; eauto.
    eapply safeN_S.
    eapply Sa; eauto.

  - (* corestep *)
    repeat split; auto.
    + eapply selfjoins_sameperms_compat; [..|apply J]; intros [k|]; simpl; eauto.
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      unfold map.
      rewrite H7.
      eapply sameperms_corestep; eassumption.
    + intros j oracle; specialize (Sa j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      * specialize (Sa _ _ H7).
        intros. rewr.
        intros <- <- .
        inversion Sa; subst.
        -- destruct (corestep_fun _ _ _ _ _ _ H6 H2) as [<- <-].
           assumption.
        -- inversion H1.
      * intros; apply safeN_S; eauto.

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
        intros [|] a b; [ | ifeq ].
        -- erewrite nth_nth_upd;[|eassumption].
           ifeq; congruence.
        -- subst. tauto.
        -- destruct (pool n); reflexivity.
      * apply join_empty; simpl.
        destruct (pool l) as [ml|]; unfold empty; auto.
      * erewrite nth_nth_upd;[|eassumption].
        ifeq; ifeq.
        rewr; eauto.
    + intros k; unfold upd; ifeq; subst; auto. apply M.
    + intros j oracle; specialize (Sa j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      * specialize (Sa _ _ H6).
        intros. injection H as <- <-.
        inversion Sa as [ | | n0 z c m0 ex x ae PRE POST]; subst.
        assert (A:Hrel n m m') by admit.
        specialize (POST m' oracle n (le_n _) A).
        destruct POST as [c' [E Sa']].
        -- inversion ae; subst.
           destruct x as [[vx orax] Rx].
           simpl in PRE |- *.
           intuition.
           subst.
           assert (Hrel n m m' -> islock l Rx m -> islock l Rx m') by admit.
           auto.
        -- inversion ae; subst.
           inversion E; subst.
           apply Sa'.
      * intros m0 p0 H.
        apply safeN_S.
        eapply Sa; auto.

  - (* acquire (locked) *)
    repeat split; eauto.
    intros i0 oracle0 m0 p0 H.
    apply safeN_S.
    eapply Sa; eauto.

  - (* acquire (unlocked) *)
    repeat split; auto.
    + eapply (selfjoins_swapped natnateqdec (inl i) (inr l) J).
      * unfold swapped, reindex, upd; repeat split.
        intros [|] a b; try (ifeq; (congruence || subst; tauto)).
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
      * intros m0 p0 H. injection H as <- <-.
        specialize (Sa _ (mlock :: oracle) _ _ H6).
        inversion Sa as [ | | n0 z c m0 ex x ae PRE POST]; subst.
        assert (A:Hrel n m m') by admit.
        specialize (POST m' oracle n (le_n _) A).
        destruct POST as [c' [E Sa']].
        -- inversion ae; subst.
           destruct x as [[vx orax] Rx].
           simpl in PRE |- *.
           intuition; subst.
           ++ intuition.
              pose proof M l.
              rewrite H7 in H.
              admit (* relate resinvs to Rx *).
           ++ assert (Hrel n m m' -> islock l Rx m -> islock l Rx m') by admit.
              auto.
        -- inversion ae; subst.
           inversion E; subst.
           apply Sa'.
      * intros m0 p0 H.
        apply safeN_S.
        eapply Sa; eauto.
Abort.




(* Hmmmm it seems both preservation and progress with the oracle-oblivious safety: *)

Definition Q_clean n (x : config) :=
  match x with (_, F, G, thd, pool) =>
    (forall l, precise (resinvs G l)) /\
    functions_safe G F /\
    selfjoins (reindex thd pool) /\
    lockpool_matches pool (resinvs G) /\
    (forall i oracle m p,
        nth thd i = Some (m, p) ->
        safeN_ clean_at_ext n oracle p m)
  end.

Theorem progress_Q_clean n x : Q_clean (S n) x -> exists y, x ===> y.
Proof.
  destruct x as (((([|i sch], F), G), thd), pool). eexists; constructor.
  intros (PR & FF & J & M & Safe).
  destruct (nth thd i) as [[m p]|] eqn:E; [ | eauto].
  destruct p as [v c | v c | c]; swap 1 3.
  - pose proof (Safe i nil _ _ E) as Sa.
    inversion Sa; subst.
    + eexists; eapply machine_core; eassumption.
    + discriminate.
  - eexists.
    (* before the eapply, should get the phi by deconstructing safeN_ *)
    eapply machine_release; [ apply E | .. ].
    + pose proof (Safe i nil _ _ E) as Sa.
      inversion Sa as [ | | n0 z c0 m0 ex x atex PRE POST]; subst.
      inversion atex; subst.
      destruct x as [vx Rx].
      simpl in PRE.
      (* destruct PRE as [-> [isl <-]]. *)
      (* should add the SEP clause to the spec. I anticipate no
      problem here. *)
      admit.
    + pose proof (Safe i nil _ _ E) as Sa.
      inversion Sa as [ | | n0 z c0 m0 ex x atex PRE POST]; subst.
      inversion atex; subst.
      destruct x as [vx Rx].
      simpl in PRE.
      (* destruct PRE as [-> [isl <-]]. *)
      (* here again the PRE should have given information that
      splitting is possible. (with precisely this join) *)
      admit.
  - specialize (M v).
    destruct (pool v) eqn:p.
    + eexists; eapply machine_acquire_success; [ apply E | .. ]. eassumption.
      (* implied by joinability condition *)
      admit.
    + eexists; eapply machine_acquire_failure; [ apply E | .. ]. eassumption.
Abort.

Theorem Q_subject_reduction_clean n x y : x ===> y -> Q_clean (S n) x -> Q_clean n y.
Proof.
  destruct x as (((([|i sch], F), G), thd), pool);
    intros xy; inversion xy; subst; intros (PR & FF & J & M & Sa);
      simpl fst in *; simpl snd in *.
  - (* out of schedule *)
    hnf; intuition; eauto.
    eapply safeN_S.
    eapply Sa; eauto.

  - (* schedule out of bound *)
    hnf; intuition; eauto.
    eapply safeN_S.
    eapply Sa; eauto.

  - (* corestep *)
    repeat split; auto.
    + eapply selfjoins_sameperms_compat; [..|apply J]; intros [k|]; simpl; eauto.
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      unfold map.
      rewrite H7.
      eapply sameperms_corestep; eassumption.
    + intros j oracle; specialize (Sa j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      * specialize (Sa _ _ H7).
        intros. rewr.
        intros <- <- .
        inversion Sa; subst.
        -- destruct (corestep_fun _ _ _ _ _ _ H6 H2) as [<- <-].
           assumption.
        -- inversion H1.
      * intros; apply safeN_S; eauto.

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
        intros [|] a b; [ | ifeq ].
        -- erewrite nth_nth_upd;[|eassumption].
           ifeq; congruence.
        -- subst. tauto.
        -- destruct (pool n); reflexivity.
      * apply join_empty; simpl.
        destruct (pool l) as [ml|]; unfold empty; auto.
      * erewrite nth_nth_upd;[|eassumption].
        ifeq; ifeq.
        rewr; eauto.
    + intros k; unfold upd; ifeq; subst; auto. apply M.
    + intros j oracle; specialize (Sa j oracle).
      erewrite nth_nth_upd; [|eassumption].
      ifeq; subst; auto.
      * specialize (Sa _ _ H6).
        intros. injection H as <- <-.
        inversion Sa as [ | | n0 z c m0 ex x ae PRE POST]; subst.
        assert (A:Hrel n m m') by admit.
        specialize (POST m' oracle n (le_n _) A).
        destruct POST as [c' [E Sa']].
        -- inversion ae; subst.
           destruct x as [vx Rx].
           simpl in PRE |- *.
           intuition.
           subst.
           assert (Hrel n m m' -> islock l Rx m -> islock l Rx m') by admit.
           auto.
        -- inversion ae; subst.
           inversion E; subst.
           apply Sa'.
      * intros m0 p0 H.
        apply safeN_S.
        eapply Sa; auto.

  - (* acquire (locked) *)
    repeat split; eauto.
    intros i0 oracle0 m0 p0 H.
    apply safeN_S.
    eapply Sa; eauto.

  - (* acquire (unlocked) *)
    repeat split; auto.
    + eapply (selfjoins_swapped natnateqdec (inl i) (inr l) J).
      * unfold swapped, reindex, upd; repeat split.
        intros [|] a b; try (ifeq; (congruence || subst; tauto)).
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
      * intros m0 p0 H. injection H as <- <-.
        specialize (Sa _ (mlock :: oracle) _ _ H6).
        inversion Sa as [ | | n0 z c m0 ex x ae PRE POST]; subst.
        assert (A:Hrel n m m') by admit.
        specialize (POST m' oracle n (le_n _) A).
        destruct POST as [c' [E Sa']].
        -- inversion ae; subst.
           destruct x as [vx Rx].
           simpl in PRE |- *.
           intuition; subst.
           assert (Hrel n m m' -> islock l Rx m -> islock l Rx m') by admit.
           auto.
        -- inversion ae; subst.
           inversion E; subst.
           apply Sa'.
      * intros m0 p0 H.
        apply safeN_S.
        eapply Sa; eauto.
Abort.
