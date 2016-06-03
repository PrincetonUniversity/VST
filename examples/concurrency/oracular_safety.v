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

Variable val : Set.

Variable C' : Set.
Inductive C : Set :=
  | acquire : val -> C -> C
  | release : val -> C -> C
  | normal : C' -> C.

Variable M : Set.
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

Definition acquire_spec l : ext :=
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

Definition at_external : C -> option ext :=
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

Inductive safeN_ : nat -> Z -> C -> M -> Prop :=
    safeN_0 : forall (z : Z) (c : C) (m : M), safeN_ 0 z c m
  | safeN_step : forall (n : nat) (z : Z) (c c' : C') (m m' : M),
      corestep c m c' m' ->
      safeN_ n z (normal c') m' ->
      safeN_ (S n) z (normal c) m
  | safeN_external : forall (n : nat) (z : Z) (c : C) (m : M) (e : ext) (x : ext_type e),
      at_external c = Some e ->
      Pre e x z m ->
      (forall (m' : M) (z' : Z) (n' : nat),
          n' <= n ->
          Hrel n' m m' ->
          Post e x z' m' ->
          exists c' : C,
            after_external c = Some c' /\
            safeN_ n' z' c' m') ->
      safeN_ (S n) z c m.

(*+ Intuition of "good oracle" rule *)

Lemma safeN_oracle_step_ n m l k R mlock :
  islock l R m ->
  R mlock ->
  (forall Ω, safeN_ (S n) Ω (acquire l k) m) ->
  forall m', Hrel n m m' ->
    (forall Ω, safeN_ n Ω k m').
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
              n' <= n -> Hrel n' m m' -> z' = Ωx'' /\ okx'' /\ islock l Rx'' m' -> safeN_ n' z' k m').
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
  (forall Ω, safeN_ (S n) (cons mlock Ω) (acquire l k) m).
Proof.
  intros isl nSat Ω.
  apply safeN_external with (acquire_spec l) (False, l, Ω, R); simpl; intuition; subst.
Qed.

Lemma safeN_oracle_step_rev_nil_ n m l k R :
  islock l R m ->
  safeN_ (S n) nil(acquire l k) m.
Proof.
  intros isl.
  apply safeN_external with (acquire_spec l) (False, l, nil, R); simpl; intuition; subst.
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

Definition clean_at_external : C -> option ext :=
  fun c =>
    match c with
    | acquire l _ => Some (clean_acquire_spec l)
    | release l _ => Some (clean_release_spec l)
    | _ => None
    end.
  
Inductive clean_safeN_ : nat -> Z -> C -> M -> Prop :=
    clean_safeN_0 : forall (z : Z) (c : C) (m : M), clean_safeN_ 0 z c m
  | clean_safeN_step : forall (n : nat) (z : Z) (c c' : C') (m m' : M),
      corestep c m c' m' ->
      clean_safeN_ n z (normal c') m' ->
      clean_safeN_ (S n) z (normal c) m
  | clean_safeN_external : forall (n : nat) (z : Z) (c : C) (m : M) (e : ext) (x : ext_type e),
      clean_at_external c = Some e ->
      Pre e x z m ->
      (forall (m' : M) (z' : Z) (n' : nat),
          n' <= n ->
          Hrel n' m m' ->
          Post e x z' m' ->
          exists c' : C,
            after_external c = Some c' /\
            clean_safeN_ n' z' c' m') ->
      clean_safeN_ (S n) z c m.

(*+ Proof that clean safety => dirty safety *)

Lemma strong_nat_ind (P : nat -> Prop) (IH : forall n, (forall i, i < n -> P i) -> P n) n : P n.
Proof.
  apply IH; induction n; intros i li; inversion li; eauto.
Qed.

Require Import Arith.

Open Scope list_scope.

(* no need for excluded middle thanks to the trick in the spec (ok <->
R mlock instead of doing the case analysis (e.g. ok = true <-> R
mlock) *)

Lemma clean_safeN_implies_safeN_ n Ω c m :
  clean_safeN_ n Ω c m ->
  safeN_ n Ω c m.
Proof.
  revert n Ω c m; induction n as [n SIH] using strong_nat_ind; intros Ω c m Safe.
  induction Safe as [ | | n Ω c m e x E PRE SPOST ];
    try solve [econstructor; eauto].
  destruct c as [ lock k | lock k | c ].
  - (* acquire *)
    injection E as <-; simpl in *.
    destruct x as (lx, R), PRE as [-> PRE].
    destruct Ω as [ | mlock Ω ].
    + simpl.
      apply safeN_external with
      (e := acquire_spec lock)
        (x := (False, lock, nil, R));
        simpl; intuition.
    + simpl.
      apply safeN_external with
      (e := acquire_spec lock)
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
