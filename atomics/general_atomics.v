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

Context `{!heapGS Σ}.

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
  iApply fupd_mask_intro; first done.
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

Definition atomic_spec_type W T := ProdType W (DiscreteFunType T Mpred).
Definition atomic_spec_type0 W := ProdType W Mpred.

Program Definition atomic_spec_pre' `{!heapGS Σ} {A T} W
  (P : dtfr W -n> _) (L : dtfr W -n> _) (G : dtfr W -n> leibnizO (list globals)) (R : dtfr W -n> _) (S2 : dtfr W -n> _)
  (E : dtfr W -n> leibnizO coPset) (SQ : dtfr W -n> _) :
  (prodO (@dtfr Σ W) (T -d> mpred)) -n> argsEnviron -d> mpred :=
  λne '(w, Q),
    PROPx (P w) (PARAMSx (L w) (GLOBALSx (G w)
     (SEPx (atomic_shift(A := A) (S2 w) (⊤ ∖ E w) ∅ (SQ w) Q :: R w)))).
Next Obligation.
Proof.
  intros.
  intros (w1, ?) (w2, ?) (Hw & ?) ?; simpl in *.
  do 2 f_equiv.
  { rewrite Hw //. }
  f_equiv.
  { apply leibniz_equiv, (discrete_iff n); [apply _ | rewrite Hw //]. }
  rewrite Hw H //.
Qed.

Program Definition atomic_spec_pre0 `{!heapGS Σ} {A} W
  (P : dtfr W -n> _) (L : dtfr W -n> _) (G : dtfr W -n> leibnizO (list globals)) (R : dtfr W -n> _) (S2 : dtfr W -n> _)
  (E : dtfr W -n> leibnizO coPset) (SQ : dtfr W -n> _) :
  (prodO (@dtfr Σ W) mpred) -n> argsEnviron -d> mpred :=
  λne '(w, Q),
    PROPx (P w) (PARAMSx (L w) (GLOBALSx (G w)
     (SEPx (atomic_shift(A := A)(B := unit) (S2 w) (⊤ ∖ E w) ∅ (SQ w) (fun _ => Q) :: R w)))).
Next Obligation.
Proof.
  intros.
  intros (w1, ?) (w2, ?) (Hw & ?) ?; simpl in *.
  do 2 f_equiv.
  { rewrite Hw //. }
  f_equiv.
  { apply leibniz_equiv, (discrete_iff n); [apply _ | rewrite Hw //]. }
  rewrite Hw; repeat f_equiv; solve_proper.
Qed.

Program Definition atomic_spec_post' `{!heapGS Σ} {T} W
  (L : dtfr W -n> _ -d> leibnizO _) (R : dtfr W -n> _ -d> _) :
  (prodO (@dtfr Σ W) (T -d> mpred)) -n> environ -d> mpred :=
    λne '(w, Q),
      ∃ v : T, PROP () (LOCALx (L w v) (SEPx (Q v :: R w v))).
Next Obligation.
Proof.
  intros.
  intros (w1, ?) (w2, ?) (Hw & ?) ?; simpl in *.
  do 5 f_equiv.
  { apply (leibniz_equiv(H := equivL)). unshelve rewrite -> (ofe_mor_ne _ _ L n); done. }
  do 2 f_equiv; first done.
  unshelve rewrite -> (ofe_mor_ne _ _ R n); done.
Qed.

Program Definition atomic_spec_post0 `{!heapGS Σ} W
  (L : dtfr W -n> leibnizO _) (R : dtfr W -n> _) :
  (prodO (@dtfr Σ W) mpred) -n> environ -d> mpred :=
    λne '(w, Q),
      PROP () (LOCALx (L w) (SEPx (Q :: R w))).
Next Obligation.
Proof.
  intros.
  intros (w1, ?) (w2, ?) (Hw & ?)? ; simpl in *.
  do 3 f_equiv.
  { apply (leibniz_equiv(H := equivL)). rewrite Hw //. }
  rewrite H Hw //.
Qed.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Program Definition atomic_spec `{!heapGS Σ} {A T} {t : Inhabitant T} W args (tz : type)
  (la : dtfr W -n> list.listO (leibnizO val)) (P : dtfr W -n> mpred) (G : dtfr W -n> leibnizO (list globals))
  (Qp : T -> dtfr W -n> mpred) (a : dtfr W -n> _) (lb : dtfr W -n> T -d> leibnizO (list localdef))
        (b : dtfr W -n> _) (E : dtfr W -n> leibnizO coPset)
   (*(HP : super_non_expansive' P) (HQp : forall v:T, super_non_expansive' (Qp v))
  (Ha : super_non_expansive_a(A := A) a) (Hla: forall n ts x, la ts x = la ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x))
  (HG: @super_non_expansive_list W (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)))
  (HE: super_non_expansive_E E)
  (Hlb : super_non_expansive_lb lb) (Hb : super_non_expansive_b b)*) :=
  mk_funspec(PROP1 := iProp Σ) (pair args tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
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

Require Import stdpp.hlist.

(* Adapted from personal correspondence with Jason Gross, this lets us manipulate tuple types like they were lists. *)
Fixpoint tuple_type (A : tlist) : Type :=
  match A with
  | tnil => unit
  | tcons A As => A * tuple_type As
  end.
Definition tcurry {A As B} (f : A -> tuple_type As -> B)
  : tuple_type (tcons A As) -> B
  := fun '(a, b) => f a b.

Fixpoint tuple_type_rev' (A : tlist) (acc : Type) : Type
  := match A with
     | tnil => acc
     | tcons A As => tuple_type_rev' As (acc * A)
     end.

Definition tuple_type_rev (A : tlist) : Type
  := match A with
     | tnil => unit
     | tcons A As => tuple_type_rev' As A
     end.

Fixpoint tcurry_rev' (A : tlist) (acc : Type) {struct A}
  : tuple_type_rev' A acc -> acc * tuple_type A
  := match A return tuple_type_rev' A acc -> acc * tuple_type A with
     | tnil => fun v => (v, tt)
     | tcons A As => fun v => let '(sf, a, v) := tcurry_rev' As _ v in
                              (sf, (a, v))
     end.
Definition tcurry_rev (A : tlist) : tuple_type_rev A -> tuple_type A
  := match A with
     | tnil => fun v => v
     | tcons A As => fun v => tcurry_rev' As A v
     end.

Definition rev_curry {A B} (f : tuple_type A -> B) : tuple_type_rev A -> B
  := fun v => f (tcurry_rev _ v).

(* There must be a way to simplify this. *)
Notation "'ATOMIC' 'TYPE' W 'OBJ' x : A 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre'(A := A)(T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
   (atomic_spec_post'(T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre'(T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
   (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre'(T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))       (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
   (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(B := leibnizO (list globals))(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(B := list mpred)(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_ : unit) => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_ : unit) _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list globals)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_ : unit) => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_ : unit) _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre'(T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre'(T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..)))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre'(T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre'(T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))       (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre' (T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' () 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' () '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre' (T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] '∃' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T) (λne _, ⊤)
   (atomic_spec_pre' (T := T) W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post' W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' () 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' () 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_:unit) => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) _ _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))       (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list globals)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_:unit) => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) _ _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' () '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list globals)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' () '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list globals)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _)(B := list mpred) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list globals)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list globals)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_ : unit) => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_ : unit) _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => cons Px%type .. (cons Py%type nil) ..)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list globals)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_ : unit) => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_ : unit) _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, E at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' E 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W) (λne _, ⊤)
   (atomic_spec_pre0 W
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list globals)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%I .. (cons S1y%I nil) ..))) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => E)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%I .. (cons SQy%I nil) ..))) ..)))))
  (atomic_spec_post0 W
      (OfeMor(ofe_mor_ne := _)(B := leibnizO (list localdef)) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..))))
      (OfeMor(ofe_mor_ne := _) (rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..)) ..))))))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, E at level 0, S2 at level 0).

Ltac atomic_nonexpansive_tac := try (let x := fresh "x" in let y := fresh "y" in let H := fresh "Hdist" in intros ? x y H;
  repeat (destruct x as [x ?]; try destruct y as [y ?]; try destruct H as [H ?];
    try (hnf in H; simpl in H; match type of H with _ = ?b => subst b end)); unfold rev_curry, tcurry; simpl; auto); try solve_proper.

#[export] Obligation Tactic := atomic_nonexpansive_tac.

(* We might want to make atomic_spec_post transparent/simplify it when we define
   funspecs, but for now, patching match_postcondition instead. *)
Ltac match_postcondition ::=
unfold atomic_spec_post', atomic_spec_post0, rev_curry, tcurry, tcurry_rev, tcurry_rev';
fix_up_simplified_postcondition;
cbv beta iota zeta; unfold_post;
constructor; let rho := fresh "rho" in intro rho; cbn [monPred_at assert_of ofe_mor_car];
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite monPred_at_exist;
tryif apply bi.exist_proper
 then (intros ?vret;
          generalize rho; rewrite -local_assert; apply PROP_LOCAL_SEP_ext';
          [reflexivity | | reflexivity];
          (reflexivity || fail "The funspec of the function has a POSTcondition
that is ill-formed.  The LOCALS part of the postcondition
should be (temp ret_temp ...), but it is not"))
 else fail "The funspec of the function should have a POSTcondition that starts
with an existential, that is,  ∃ _:_, PROP...LOCAL...SEP".

(* change start_function to handle curried arguments -- also thanks to Jason *)
Ltac read_names term :=
  lazymatch term with
  | tcurry (fun x : ?T => ?f)
    => let f' := fresh in
       let rest := lazymatch
             constr:(
               fun x : T
               => match f return _ with
                  | f' => ltac:(let f := (eval cbv delta [f'] in f') in
                                clear f';
                                let rest := read_names f in
                                refine rest)
                  end) with
           | fun _ => ?rest => rest
           | ?e => fail 0 "Could not eliminate the functional dependencies of" e
           end in
       constr:(((fun x : unit => x), rest))
  | _ => constr:(tt)
  end.

Ltac destruct_args t i :=
  match t with
  | tt => idtac
  | (fun x => _, ?t') => destruct_args t' i; (destruct i as [i x] || rename i into x)
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
   end;
   (let gv := fresh "gv" in
    match goal with
    | |- semax_body _ _ _ (_, mk_funspec _ _ _ _ ?Pre _) =>
          split3; [ check_parameter_types' | check_return_type |  ];
           match Pre with
           | atomic_spec_pre' _ _ _ _ _ (OfeMor(ofe_mor_ne := _) (rev_curry ?t)) _ _ =>
               let i := fresh in let x := read_names t in intros Espec i; destruct i as [i Q]; destruct_args x i; unfold atomic_spec_pre', atomic_spec_post', ofe_mor_car, rev_curry, tcurry; cbn [tcurry_rev tcurry_rev']; cbn match (* added line *)
           | atomic_spec_pre0 _ _ _ _ _ (OfeMor(ofe_mor_ne := _) (rev_curry ?t)) _ _ =>
               let i := fresh in let x := read_names t in intros Espec i; destruct i as [i Q]; destruct_args x i; unfold atomic_spec_pre0, atomic_spec_post0, ofe_mor_car, rev_curry, tcurry; cbn [tcurry_rev tcurry_rev']; cbn match (* added line *)
           | monPred_at (convertPre _ _ (λ i, _)) =>
               intros Espec i
           | λne x, monPred_at match _ with
                               | (a, b) => _
                               end => intros Espec [a b]
           | λne i, _ => intros Espec i
           end
    | |- semax_body _ _ _ (pair _ (NDmk_funspec _ _ _ ?Pre _)) =>
          split3; [check_parameter_types' | check_return_type | ];
           match Pre with
           | (convertPre _ _ (fun i => _)) =>  intros Espec (*DependedTypeList*) i
           | (fun x => match _ with (a,b) => _ end) => intros Espec (*DependedTypeList*) [a b]
           | (fun i => _) => intros Espec (*DependedTypeList*) i (* this seems to be named "a" no matter what *)
           end
    end; simpl fn_body; simpl fn_params; simpl fn_return;
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
