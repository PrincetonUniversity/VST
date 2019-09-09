Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Import VST.progs.invariants.
Require Import VST.progs.fupd.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Export Ensembles.

Set Bullet Behavior "Strict Subproofs".

(* Thoughts on invariants and the two-level structure:
   I expect that our version of the operational semantics will keep nonatomic locations as is,
   so that the points-to assertions won't need view parameters (and in fact will be objective?).
   The question then is: do we need the two-level structure in which iGPS-style assertions are
   functions from view to mpred, or can even protocol assertions simply be mpreds? We might be able
   to use something like the external state construction to use ghost state to remember per-thread
   timestamps, so that we don't need to include timestamps in the rmap (or as an extra argument
   to assertions). In this model, there would be no objectivity requirement at all: instead,
   protocol assertions from other threads would be incompatible with the current thread because
   they refer to a different location for their timestamp ghost state.
   On the other hand, if we do need the two-level structure, we should still define invariants
   without objectivity here (as Iris-level invariants), and define iGPS-level invariants elsewhere. *)
(* We will still, of course, have to choose between SC and RA atomics in any given proof/program,
   since there's no soundness proof (or operational model) for a language with both. And invariants
   must still be accessible only via atomics. Does this make the fancy-update style useless,
   since we can't insert it into the definition of semax? Well, iGPS still uses it in the RA atomic
   rules, so maybe it's still useful. *)

Section atomics.

Context {CS : compspecs} {inv_names : invG}.

Section atomicity.

(* The logical atomicity of Iris. *)
(* We use the cored predicate to mimic Iris's persistent modality. *)
Definition atomic_shift {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) :=
  EX P : mpred, |> P * ((|> P -* |={Eo,Ei}=> (EX x : A, a x *
    ((a x -* |={Ei,Eo}=> |> P) &&
     ALL y : B, b x y -* |={Ei,Eo}=> Q y))) && cored)%I.

End atomicity.

End atomics.

Definition atomic_spec_type W T := ProdType (ProdType W (ArrowType (ConstType T) Mpred)) (ConstType invG).

Definition super_non_expansive_a {A W} (a : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A -> predicates_hered.pred rmap) :=
  forall n ts w x, approx n (a ts w x) =
  approx n (a ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x).

Definition super_non_expansive_b {A B W} (b : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A -> B -> predicates_hered.pred rmap) :=
  forall n ts w x y, approx n (b ts w x y) =
  approx n (b ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x y).

Definition super_non_expansive_la {W} la := forall n ts w rho,
  Forall (fun l => approx n (!! locald_denote (l ts w) rho) = approx n (!! locald_denote (l ts
    (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w)) rho)) la.

Definition super_non_expansive_lb {B W} lb := forall n ts w (v : B) rho,
  Forall (fun l => approx n (!! locald_denote (l ts w v) rho) = approx n (!! locald_denote (l ts
    (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) v) rho)) lb.

Import List.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Notation atomic_spec1 T W args tz la P a t lb b Ei Eo :=
  (mk_funspec (pair args tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) '(w, Q, inv_names) =>
     PROP ()
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))))
   (fun (ts: list Type) '(w, Q, inv_names) => EX v : T,
     PROP () (LOCALx (map (fun l => l ts w v) lb)
     (SEP (Q v)))) _ _).

Lemma atomic_spec_nonexpansive_pre' : forall {A T} {t : Inhabitant T} W P L R S2 Ei Eo SQ
  (HP : Forall (fun x => super_non_expansive (fun ts w _ => !! (x ts w))) P)
  (HL : Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w) rho))) L)
  (HR : Forall (fun x => super_non_expansive (fun ts w _ => x ts w)) R),
  super_non_expansive_a S2 ->
  super_non_expansive_b SQ ->
  @super_non_expansive (atomic_spec_type W T)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) =>
    let '(w, Q, inv_names) := _a in
    PROPx (map (fun P => P ts w) P) (LOCALx (map (fun L => L ts w) L)
     (SEPx (atomic_shift(A := A)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q :: map (fun R => R ts w) R)))).
Proof.
  intros.
  replace _ with (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) rho =>
    PROPx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w) P)) (LOCALx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w) L))
     (SEPx (map (fun R => R ts _a) ((fun ts _a => let '(w, Q, inv_names) := _a in atomic_shift(A := A)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q) ::
        map (fun R ts _a => let '(w, _, _) := _a in R ts w) R)))) rho).
  apply PROP_LOCAL_SEP_super_non_expansive.
  - rewrite Forall_map.
    eapply Forall_impl, HP; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - rewrite Forall_map.
    eapply Forall_impl, HL; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - constructor.
    + intros ?? ((?, ?), ?) ?.
      unfold atomic_shift; simpl.
      rewrite !approx_exp; f_equal; extensionality.
      rewrite -> !approx_sepcon, !approx_andp; f_equal; f_equal.
      setoid_rewrite fview_shift_nonexpansive; f_equal; f_equal; f_equal.
      rewrite !approx_exp; f_equal; extensionality.
      rewrite -> !approx_sepcon, !approx_andp; f_equal; auto.
      f_equal.
      * setoid_rewrite fview_shift_nonexpansive; f_equal; f_equal; auto.
      * rewrite -> !approx_allp by auto; f_equal; extensionality.
        setoid_rewrite fview_shift_nonexpansive; f_equal; f_equal; auto.
        rewrite approx_idem; auto.
    + rewrite Forall_map.
      eapply Forall_impl, HR; simpl; intros.
      intros ?? ((?, ?), ?) ?; simpl; auto.
  - extensionality ts x rho.
    destruct x as ((?, ?), ?).
    simpl; rewrite !map_map; reflexivity.
Qed.

Lemma atomic_spec_nonexpansive_pre : forall {A T} {t : Inhabitant T} W P L R S2 Ei Eo SQ Pre
  (Heq : (forall ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG),
   Pre ts _a = let '(w, Q, inv_names) := _a in
    PROPx (map (fun P => P ts w) P) (LOCALx (map (fun L => L ts w) L)
     (SEPx (atomic_shift(A := A)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q :: map (fun R => R ts w) R)))))
  (HP : Forall (fun x => super_non_expansive (fun ts w _ => !! (x ts w))) P)
  (HL : Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w) rho))) L)
  (HR : Forall (fun x => super_non_expansive (fun ts w _ => x ts w)) R),
  super_non_expansive_a S2 ->
  super_non_expansive_b SQ ->
  @super_non_expansive (atomic_spec_type W T) Pre.
Proof.
  intros.
  evar (Pre' : forall ts : list Type, functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG -> environ -> mpred).
  replace Pre with Pre'; subst Pre'; [apply (atomic_spec_nonexpansive_pre'(A := A)); eauto|].
  extensionality ts x; auto.
Qed.

Lemma atomic_spec_nonexpansive_post' : forall {T} W L
  (HL : forall v, Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w v) rho))) L),
  @super_non_expansive (atomic_spec_type W T)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) =>
    let '(w, Q, inv_names) := _a in
    EX v : T,
    PROP () (LOCALx (map (fun L => L ts w v) L) (SEP (Q v)))).
Proof.
  intros.
  intros ?? ((w, Q), inv_names) ?; simpl.
  rewrite !approx_exp; f_equal; extensionality v.
  assert (@super_non_expansive (atomic_spec_type W T) (fun ts _a => let '(w, Q, inv_names) := _a in
    PROP () (LOCALx (map (fun L => L ts w v) L) (SEP (Q v))))); [|apply (H n ts (w, Q, inv_names))].
  replace _ with (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) rho =>
    PROP () (LOCALx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w v) L))
     (SEPx (map (fun P => P ts _a) [fun ts _a => let '(_, Q, _) := _a in Q v]))) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type W T) []); auto.
  - rewrite Forall_map.
    eapply Forall_impl, HL; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - repeat constructor.
    intros ?? ((?, ?), ?) ?; simpl.
    rewrite approx_idem; auto.
  - extensionality ts' x rho'.
    destruct x as ((?, ?), ?).
    simpl; rewrite !map_map; reflexivity.
Qed.

Lemma atomic_spec_nonexpansive_post : forall {T} W L Post
  (Heq : (forall ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG),
  Post ts _a = let '(w, Q, inv_names) := _a in
    EX v : T,
    PROP () (LOCALx (map (fun L => L ts w v) L) (SEP (Q v)))))
  (HL : forall v, Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w v) rho))) L),
  @super_non_expansive (atomic_spec_type W T) Post.
Proof.
  intros.
  evar (Post' : forall ts : list Type, functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG -> environ -> mpred).
  replace Post with Post'; subst Post'; [apply atomic_spec_nonexpansive_post'; eauto|].
  extensionality ts x; auto.
Qed.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Program Definition atomic_spec {A T} {t : Inhabitant T} W args tz la P a lb b Ei Eo
  (Hla : super_non_expansive_la la) (HP : super_non_expansive' P) (Ha : super_non_expansive_a(A := A) a)
  (Hlb : super_non_expansive_lb lb) (Hb : super_non_expansive_b b) :=
  mk_funspec (pair args tz) cc_default (atomic_spec_type W T)
  (fun (ts: list Type) '(w, Q, inv_names) =>
    PROP ()
    (LOCALx (map (fun l => l ts w) la)
    (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))))
  (fun (ts: list Type) '(w, Q, inv_names) => EX v : T,
    PROP () (LOCALx (map (fun l => l ts w v) lb)
    (SEP (Q v)))) _ _.
Next Obligation.
Proof.
  intros; eapply atomic_spec_nonexpansive_pre with (P0 := [])(R := [_]); try assumption.
  { intros ? ((?, ?), ?); reflexivity. }
  all: auto.
  - rewrite Forall_forall; repeat intro.
    exploit Hla.
    rewrite Forall_forall; intro X; apply X; auto.
  - repeat constructor; repeat intro; auto.
Qed.
Next Obligation.
Proof.
  intros; eapply atomic_spec_nonexpansive_post.
  { intros ? ((?, ?), ?); reflexivity. }
  intros; rewrite Forall_forall; repeat intro.
  exploit Hlb.
  rewrite Forall_forall; intro X; apply X; auto.
Qed.

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEPS' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEP (Q r))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6) := __a in LQy%logic) nil) ..) _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, x2 at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEPS' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () (SEP (Q r)))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W [] _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, x2 at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEPS' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEP (Q r))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7) := __a in LQy%logic) nil) ..) _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, x2 at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEPS' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () (SEP (Q r)))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W [] _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, x2 at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEPS' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEP (Q r))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in LQy%logic) nil) ..) _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, x2 at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEPS' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8), Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () (SEP (Q r)))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W [] _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, x2 at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEPS' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEP (Q r))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in LQy%logic) nil) ..) _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, x2 at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEPS' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9), Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () (SEP (Q r)))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W [] _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, x2 at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Global Obligation Tactic := repeat constructor || let x := fresh "x" in intros ?? x; repeat destruct x as [x ?]; reflexivity.

Ltac start_atomic_function :=
(*  match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH u : unit
               PRE  [] main_pre _ nil u
               POST [ tint ] main_post _ nil u) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end; unfold atomic_spec;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b] 
   | (fun i => _) => intros Espec DependedTypeList ((x, Q), inv_names)
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP; 
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH 
                 | Share.t => intros ?SH 
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax; simpl.*) start_function. (* legacy *)
