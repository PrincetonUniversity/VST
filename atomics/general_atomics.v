Require Export iris.algebra.list iris.bi.lib.atomic.
From VST.concurrency Require Export conclib.
Require Import VST.floyd.library.
Require Export VST.zlist.sublist.
Require Import Program.Equality.

Section atomicity.

(* The logical atomicity of Iris. *)

(* for people who don't want telescope notation *)
Definition tele_unwrap {A} (x : tele_arg (TeleS (fun _ : A => TeleO))) :=
  match x with
  | TeleArgCons x _ => x
  end.

Context `{!VSTGS OK_ty Σ}.

Definition atomic_shift {A B} (a : A -d> mpred) Eo Ei (b : A -d> B -d> mpred) (Q : B -d> mpred) : mpred :=
  atomic_update(TA := [tele _ : A]) (TB := [tele _ : B]) Eo Ei (λ.. x, a (tele_unwrap x)) (λ.. x y, b (tele_unwrap x) (tele_unwrap y)) (λ.. x y, Q (tele_unwrap y)).

Lemma atomic_commit_fupd : forall {A B} (a : A -> mpred) Eo Ei (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R ∗ a x ⊢ |==> (∃ y, b x y ∗ R' y)) ->
  atomic_shift a Eo Ei b Q ∗ R ⊢ |={Eo}=> (∃ y, Q y ∗ R' y).
Proof.
  intros.
  iIntros "[AS R]".
  unfold atomic_shift.
  iMod "AS" as (x) "[a [_ commit]]"; simpl.
  iMod (H with "[$R $a]") as (y) "[b Q]".
  iExists y; iMod ("commit" with "b") as "$"; auto.
Qed.

Lemma atomic_rollback_fupd : forall {A B} (a : A -> mpred) Eo Ei (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R ∗ a x ⊢ |==> a x ∗ R') ->
  atomic_shift a Eo Ei b Q ∗ R ⊢ |={Eo}=> atomic_shift a Eo Ei b Q ∗ R'.
Proof.
  intros.
  iIntros "[AS R]".
  unfold atomic_shift.
  iMod "AS" as (x) "[a [rollback _]]"; simpl.
  iMod (H with "[$R $a]") as "[a R]".
  iMod ("rollback" with "a") as "$"; auto.
Qed.

Lemma atomic_shift_mask_weaken {A B} Eo1 Eo2 Ei a (b : A -> B -> mpred) Q :
  Eo1 ⊆ Eo2 ->
  atomic_shift a Eo1 Ei b Q ⊢ atomic_shift a Eo2 Ei b Q.
Proof.
  intros; unfold atomic_shift.
  iApply atomic_update_mask_weaken; auto.
Qed.

(* use iInv instead of applying this lemma *)
Lemma inv_atomic_shift : forall {A B} a Eo Ei (b : A -> B -> mpred) Q N R P
  (Hi : ↑N ⊆ Eo) (Hio : Ei ⊆ Eo ∖ ↑N)
  (Ha1 : (inv N R ∗ ▷R ⊢ |={Eo ∖ ↑N}=> ∃ x, a x ∗ ((a x -∗ |={Ei}=> ▷R) ∧
    (∀ y, ▷ P ∗ b x y -∗ |={Ei}=> ▷R ∗ Q y)))),
  inv N R ∗ ▷ P ⊢ atomic_shift a Eo Ei b Q.
Proof.
  intros; unfold atomic_shift.
  iIntros "[#I P]". iAuIntro.
  rewrite /atomic_acc /=.
  iInv "I" as "R" "Hclose".
  iMod (Ha1 with "[$I $R]") as (x) "(a & shift)".
  iExists x; iFrame.
  iApply fupd_mask_intro.
  iIntros "Hclose'"; iSplit.
  - iIntros "a"; iMod ("shift" with "a") as "R".
    iMod "Hclose'"; iMod ("Hclose" with "R"); auto.
  - iIntros (y) "b".
    iMod ("shift" with "[$P $b]") as "[R Q]".
    iMod "Hclose'"; iMod ("Hclose" with "R"); auto.
Qed.

#[global] Instance atomic_shift_nonexpansive : forall {A B} n,
  Proper (dist n ==> eq ==> eq ==> dist n ==> dist n ==> dist n) (@atomic_shift A B).
Proof.
  repeat intro.
  rewrite /atomic_shift /=.
  subst; apply atomic_update_ne; intros []; solve_proper.
Qed.

Lemma atomic_shift_derives_frame : forall {A A' B B'} (a : A -> mpred) (a' : A' -> mpred) Eo Ei
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred) R
  (Ha : (forall x, a x ∗ ▷R ⊢ |={Ei}=> ∃ x' : A', a' x' ∗
    ((a' x' -∗ |={Ei}=> a x ∗ ▷R) ∧ ∀ y' : _, b' x' y' -∗ (|={Ei}=> ∃ y : _, b x y ∗ (Q y -∗ |={Eo}=> Q' y'))))),
  atomic_shift a Eo Ei b Q ∗ ▷R ⊢ atomic_shift a' Eo Ei b' Q'.
Proof.
  intros; unfold atomic_shift.
  iIntros "[AU P]". iAuIntro.
  iApply (aacc_aupd with "AU"); auto; simpl.
  iIntros (x) "a".
  iMod (Ha with "[$a $P]") as (x') "(a' & A)".
  rewrite /atomic_acc /=.
  iExists x'; iFrame "a'".
  iIntros "!>"; iSplit.
  - iIntros "a'".
    iMod ("A" with "a'") as "[$ $]"; auto.
  - iIntros (y') "b'".
    iMod ("A" with "b'") as (y) "[b HQ]".
    iRight; iExists y; iFrame; auto.
Qed.

Lemma atomic_shift_derives : forall {A A' B B'} (a : A -> mpred) (a' : A' -> mpred) Eo Ei
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred)
  (Ha : (forall x, a x  ⊢ |={Ei}=> ∃ x' : A', a' x' ∗
    ((a' x' -∗ |={Ei}=> a x) ∧ ∀ y' : _, b' x' y' -∗ (|={Ei}=> ∃ y : _, b x y ∗ (Q y -∗ |={Eo}=> Q' y'))))),
  atomic_shift a Eo Ei b Q ⊢ atomic_shift a' Eo Ei b' Q'.
Proof.
  intros; unfold atomic_shift.
  iIntros "AU". iAuIntro.
  iApply (aacc_aupd with "AU"); auto; simpl.
  iIntros (x) "a".
  iMod (Ha with "a") as (x') "[a' H']".
  iAaccIntro with "a'".
  - iIntros "a'". iMod ("H'" with "a'") as "$"; auto.
  - iIntros (y') "b'". iMod ("H'" with "b'") as (y) "[b H]".
    iRight; iExists y; iFrame; auto.
Qed.

Lemma atomic_shift_derives' : forall {A A' B} (a : A -> mpred) (a' : A' -> mpred) Eo Ei
  (b : A -> B -> mpred) (b' : A' -> B -> mpred) (Q : B -> mpred)
  (Ha : (forall x, a x ⊢ |={Ei}=> ∃ x' : A', a' x' ∗
    ((a' x' -∗ |={Ei}=> a x) ∧ ∀ y : _, b' x' y -∗ |={Ei}=> b x y))),
  atomic_shift a Eo Ei b Q ⊢ atomic_shift a' Eo Ei b' Q.
Proof.
  intros; apply atomic_shift_derives.
  iIntros (x) "a"; iMod (Ha with "a") as (x') "[a H]".
  iExists x'; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a"; iMod ("H" with "a") as "$"; auto.
  - iIntros (y) "b"; iExists y.
    iDestruct "H" as "[_ H]".
    iMod ("H" with "b") as "$".
    iIntros "!> $"; auto.
Qed.

Lemma atomic_shift_derives_simple : forall {A B} (a a' : A -> mpred) Eo Ei (b b' : A -> B -> mpred) (Q : B -> mpred)
  (Ha1 : forall x, a x ⊢ |={Ei}=> a' x)
  (Ha2 : forall x, a' x ⊢ |={Ei}=> a x)
  (Hb : forall x y, b' x y ⊢ |={Ei}=> b x y),
  atomic_shift a Eo Ei b Q ⊢ atomic_shift a' Eo Ei b' Q.
Proof.
  intros; apply atomic_shift_derives'; intros.
  iIntros "a"; iExists x; iMod (Ha1 with "a") as "$".
  iIntros "!>"; iSplit.
  - iApply Ha2.
  - iIntros (?); iApply Hb.
Qed.

Lemma atomic_shift_exists : forall {A B} a Eo Ei (b : A -> B -> mpred) Q,
  atomic_shift (fun (_ : unit) => ∃ x : A, a x) Eo Ei (fun (_ : unit) y => ∃ x : A, b x y) Q ⊢ atomic_shift a Eo Ei b Q.
Proof.
  intros; unfold atomic_shift.
  iIntros "AU". iAuIntro.
  iApply (aacc_aupd with "AU"); auto; simpl.
  iIntros (_) "a"; iDestruct "a" as (x) "a".
  rewrite /atomic_acc /=.
  iExists x; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a !>".
    iSplitR ""; auto.
  - iIntros (y) "b !>".
    iRight; iExists y.
    iSplitR ""; auto.
Qed.

End atomicity.

Global Hint Resolve empty_subseteq : core.

Definition atomic_spec_type W T := ProdType W (ArrowType (ConstType T) Mpred).
Definition atomic_spec_type0 W := ProdType W Mpred.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Program Definition atomic_spec `{!VSTGS OK_ty Σ} {A T} {t : Inhabitant T} W args (tz : type)
  (la : dtfr W -n> list.listO (leibnizO val)) (P : dtfr W -n> mpred) (G : dtfr W -n> leibnizO (list globals))
  (Qp : T -> dtfr W -n> mpred) (a : dtfr W -n> _) (lb : dtfr W -n> T -d> leibnizO (list localdef))
        (b : dtfr W -n> _) (E : dtfr W -n> leibnizO coPset)
   (*(HP : super_non_expansive' P) (HQp : forall v:T, super_non_expansive' (Qp v))
  (Ha : super_non_expansive_a(A := A) a) (Hla: forall n ts x, la ts x = la ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x))
  (HG: @super_non_expansive_list W (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)))
  (HE: super_non_expansive_E E)
  (Hlb : super_non_expansive_lb lb) (Hb : super_non_expansive_b b)*) :=
  mk_funspec(PROP1 := iProp Σ) (pair args tz) cc_default coPset_top (atomic_spec_type W T)
  (λne '(w, Q),
    PROP ()
    (PARAMSx (la w) (GLOBALSx (G w) (
    (SEP (atomic_shift(A := A) (a w) (⊤ ∖ E w) ∅ (b w) Q; P w))%assert5))))
  (λne '(w, Q), ∃ v : T,
    PROP () (LOCALx (lb w v)
    (SEP (Q v; Qp v w))%assert5)).
Next Obligation.
Proof.
  intros; intros (w1 & Q1) (w2 & Q2) (Hw & HQ) ?; simpl in *.
  assert (la w1 = la w2) as ->.
  { apply leibniz_equiv, (discrete_iff n); rewrite ?Hw //. apply _. }
  assert (G w1 = G w2) as ->.
  { apply leibniz_equiv, (discrete_iff n); rewrite ?Hw //. apply _. }
  assert (E w1 = E w2) as ->.
  { apply leibniz_equiv, (discrete_iff n); rewrite ?Hw //. apply _. }
  solve_proper.
Qed.
Next Obligation.
Proof.
  intros; intros (w1 & Q1) (w2 & Q2) (Hw & HQ) ?; simpl in *.
  do 2 f_equiv.
  intros v.
  assert (lb w1 v = lb w2 v) as ->.
  { assert (lb w1 ≡{n}≡ lb w2) as H by rewrite Hw //; apply H. }
  solve_proper.
Qed.

Inductive tlist := tnil : tlist | tcons : ofe → tlist → tlist.

(* Adapted from personal correspondence with Jason Gross, this lets us manipulate tuple types like they were lists. *)
Fixpoint tuple_type (A : tlist) : ofe :=
  match A with
  | tnil => unit
  | tcons A As => prodO A (tuple_type As)
  end.
Program Definition tcurry {A As B} (f : A -n> tuple_type As -n> B)
  : tuple_type (tcons A As) -n> B
  := λne '(a, b), f a b.
Next Obligation.
Proof.
  intros; simpl.
  intros (?, ?) (?, ?) (? & ?).
  solve_proper.
Qed.

Fixpoint tuple_type_rev' (A : tlist) (acc : ofe) : ofe
  := match A with
     | tnil => acc
     | tcons A As => tuple_type_rev' As (prodO acc A)
     end.

Definition tuple_type_rev (A : tlist) : ofe
  := match A with
     | tnil => unit
     | tcons A As => tuple_type_rev' As A
     end.

Program Fixpoint tcurry_rev' (A : tlist) (acc : ofe) {struct A}
  : tuple_type_rev' A acc -n> prodO acc (tuple_type A)
  := match A return tuple_type_rev' A acc -n> prodO acc (tuple_type A) with
     | tnil => λne v, (v, tt)
     | tcons A As => λne v, let '(sf, a, v) := tcurry_rev' As _ v in
                              (sf, (a, v))
     end.
Next Obligation.
Proof. solve_proper. Qed.
Next Obligation.
Proof.
  intros; simpl.
  intros ???; simpl.
  destruct (tcurry_rev' _ _ _) as ((x1, x2), x3) eqn: Hrevx.
  destruct (tcurry_rev' _ _ y) as ((y1, y2), y3) eqn: Hrevy.
  assert ((x1, x2, x3) ≡{n}≡ (y1, y2, y3)) as ((? & ?) & ?); last solve_proper.
  rewrite -Hrevx -Hrevy H //.
Defined.

Program Definition tcurry_rev (A : tlist) : tuple_type_rev A -n> tuple_type A
  := match A with
     | tnil => λne v, v
     | tcons A As => λne v, tcurry_rev' As A v
     end.
Next Obligation.
Proof. solve_proper. Qed.

Program Definition rev_curry {A B} (f : tuple_type A -n> B) : tuple_type_rev A -n> B
  := λne v, f (tcurry_rev _ v).
Next Obligation.
Proof. solve_proper. Qed.

(* There must be a way to simplify this. Maybe telescopes? *)
Notation "'ATOMIC' 'TYPE' W 'OBJ' x : A 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun _ : unit => S2) (⊤ ∖ E) ∅ (fun (_ : unit) _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) nil))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun (_ : unit) => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: nil))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' () 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' () '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx nil
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) nil))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: nil)))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type W T)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift (fun x => S2) (⊤ ∖ E) ∅ (fun x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) Q) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : T -> mpred) (_ : tuple_type tnil),
    bi_exist(A := T) (fun r =>
     PROP () (LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' () 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) nil))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEPx (Q :: nil)))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' () 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) nil))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: nil))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun _ : unit => S2) (⊤ ∖ E) ∅ (fun _ _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun _ : unit => S2) (⊤ ∖ E) ∅ (fun _ _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) nil))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: nil))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) nil))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: nil))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: nil))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun (_ : unit) => S2) (⊤ ∖ E) ∅ (fun (_ : unit) _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun (_ : unit) => S2) (⊤ ∖ E) ∅ (fun (_ : unit) _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default ⊤ (atomic_spec_type0 W)
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx nil
     (SEPx (cons (atomic_shift(B := unit) (fun x => S2) (⊤ ∖ E) ∅ (fun x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..)) (fun _ => Q)) (cons S1x%I .. (cons S1y%I nil) ..)))))))) ..)))
   (rev_curry (tcurry (λne x1, .. (tcurry (λne xn, tcurry (λne (Q : mpred) (_ : tuple_type tnil),  PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..))))) ..)))
   )
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).


(*Ltac atomic_nonexpansive_tac := try (let x := fresh "x" in intros ?? x;
  try match type of x with list Type => (let ts := fresh "ts" in rename x into ts; intros x) end;
  repeat destruct x as [x ?]; unfold rev_curry, tcurry; simpl; auto); repeat constructor.

Global Obligation Tactic := atomic_nonexpansive_tac.*)

(* change start_function to handle curried arguments -- also thanks to Jason *)
Ltac read_names term :=
  lazymatch term with
  | tcurry (λne x : ?T, ?f)
    => let f' := fresh in
       let rest := lazymatch
             constr:(
               λne x : T,
                  match f return _ with
                  | f' => ltac:(let f := (eval cbv delta [f'] in f') in
                                clear f';
                                let rest := read_names f in
                                refine rest)
                  end) with
           | λne _, ?rest => rest
           | ?e => fail 0 "Could not eliminate the functional dependencies of" e
           end in
       constr:(((λne x : unit, x), rest))
  | _ => constr:(tt)
  end.

Ltac destruct_args t i :=
  match t with
  | tt => idtac
  | (λne x, _, ?t') => destruct_args t' i; (destruct i as [i x] || rename i into x)
  end.

Ltac start_function1 ::=
 leaf_function;
   lazymatch goal with
   | |- semax_body ?V ?G ?F ?spec =>
         check_normalized F; function_body_unsupported_features F;
          (let s := fresh "spec" in
           pose (s := spec); hnf in s; cbn zeta in s;
            repeat
             lazymatch goal with
             | s:=(_, NDmk_funspec _ _ _ _ _):_ |- _ => fail
             | s:=(_, mk_funspec _ _ _ _ _ _):_ |- _ => fail
             | s:=(_, ?a _ _ _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _ _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _ _):_ |- _ => unfold a in s
             | s:=(_, ?a _):_ |- _ => unfold a in s
             | s:=(_, ?a):_ |- _ => unfold a in s
             end;
            lazymatch goal with
            | s:=(_, WITH _ : globals PRE [ ] main_pre _ _ _ POST [tint] _):_
              |- _ => idtac
            | s:=?spec':_ |- _ => check_canonical_funspec spec'
            end; change (semax_body V G F s); subst s)
   end; unfold NDmk_funspec;
   (let gv := fresh "gv" in
    match goal with
    | |- semax_body _ _ _ (_, mk_funspec _ _ _ _ ?Pre _) =>
          split3; [ check_parameter_types' | check_return_type |  ];
           match Pre with
           | λne _, monPred_at (convertPre _ _ (λ i, _)) =>
               intros Espec i
           | λne x, monPred_at match _ with
                               | (a, b) => _
                               end => intros Espec [a b]
           | λne i, _ => intros Espec i
           end; simpl fn_body; simpl fn_params; simpl fn_return
    end;
     cbv[dtfr dependent_type_functor_rec constOF idOF prodOF discrete_funOF ofe_morOF
        sigTOF listOF oFunctor_car ofe_car] in *; cbv[ofe_mor_car];
     rewrite_old_main_pre; rewrite ?argsassert_of_at ?assert_of_at;
     repeat
      match goal with
      | |- semax _ _ (match ?p with
                      | (a, b) => _
                      end ∗ _) _ _ => destruct p as [a b]
      | |- semax _ _ (close_precondition _ match ?p with
                                           | (a, b) => _
                                           end ∗ _) _ _ => 
        destruct p as [a b]
      | |-
        semax _ _
          (close_precondition _ (argsassert_of match ?p with
                                               | (a, b) => _
                                               end) ∗ _) _ _ => 
        destruct p as [a b]
      | |- semax _ _ (match ?p with
                      | (a, b) => _
                      end eq_refl ∗ _) _ _ => destruct p as [a b]
      | |-
        semax _ _
          (close_precondition _ (match ?p with
                                 | (a, b) => _
                                 end eq_refl) ∗ _) _ _ => 
        destruct p as [a b]
      | |-
        semax _ _
          (close_precondition _
             (argsassert_of (match ?p with
                             | (a, b) => _
                             end eq_refl)) ∗ _) _ _ => destruct p as [a b]
      | |-
        semax _ _
          (close_precondition _
             (λ ae,
                ⌜Datatypes.length ae.2 = ?A⌝
                ∧ ?B (make_args ?C ae.2 (mkEnviron ae.1 _ _))) ∗ _) _ _ =>
            match B with
            | match ?p with
              | (a, b) => _
              end => destruct p as [a b]
            end
      end; rewrite ?argsassert_of_at ?assert_of_at;
     rewrite ?difference_empty_L; (* added line *)
     try start_func_convert_precondition).

(* can we not do this? *)
Ltac start_function2 ::=
  first [ setoid_rewrite (* changed from erewrite *) compute_close_precondition_eq; [ | reflexivity | reflexivity]
        | rewrite close_precondition_main ].
