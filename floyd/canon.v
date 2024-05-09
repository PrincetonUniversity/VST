Require Export Coq.Sorting.Permutation.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.seplog.
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Import LiftNotation.

Inductive localdef : Type :=
 | temp: ident -> val -> localdef
 | lvar: ident -> type -> val -> localdef   (* local variable *)
 | gvars: globals -> localdef.              (* global variables *)

Arguments temp i%_positive v.

Definition lvar_denote (i: ident) (t: type) (v: val) rho :=
     match Map.get (ve_of rho) i with
         | Some (b, ty') => t=ty' /\ v = Vptr b Ptrofs.zero
         | None => False%type
         end.

Definition gvars_denote (gv: globals) rho :=
   gv = (fun i => match Map.get (ge_of rho) i with Some b => Vptr b Ptrofs.zero | None => Vundef end).

Definition locald_denote (d: localdef) : environ -> Prop :=
 match d with
 | temp i v => `and (`(eq v) (eval_id i)) `(v <> Vundef)
 | lvar i t v => lvar_denote i t v
 | gvars gv => gvars_denote gv
 end.

Fixpoint fold_right_andp rho (l: list (environ -> Prop)) : Prop :=
 match l with
 | nil => True
 | b::nil => b rho
 | b::r => b rho /\ fold_right_andp rho r
 end.

Declare Scope assert.  Delimit Scope assert with assert.
Global Set Warnings "-overwriting-delimiting-key".
Delimit Scope assert with argsassert.
(* Ideally we would like to disable this warning only for this Delimit command,
 and then do 
   Set Warnings "+overwriting-delimiting-key".
  afterward, but this doesn't really work, because we'd still
 get the warning in every file that imports this file.
*)
Declare Scope assert3. Delimit Scope assert3 with assert3.
Declare Scope assert4. Delimit Scope assert4 with assert4.
Declare Scope assert5. Delimit Scope assert5 with assert5.

Definition PROPx {A Σ} (P: list Prop): monPred A (iPropI Σ) -d> monPred A (iPropI Σ) :=
     bi_and ⌜fold_right and True P⌝.
Global Instance: Params (@PROPx) 2 := {}. (* could be 3 to turn off setoid rewriting in PROP *)

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z%assert3) (at level 10) : assert.
Notation "'PROP' ()   z" :=   (PROPx nil z%assert3) (at level 10) : assert.
Notation "'PROP' ( )   z" :=   (PROPx nil z%assert3) (at level 10) : assert.

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z%assert3) (at level 10).
Notation "'PROP' ()   z" :=   (PROPx nil z%assert3) (at level 10).
Notation "'PROP' ( )   z" :=   (PROPx nil z%assert3) (at level 10).

Definition LOCALx {Σ} (Q: list localdef) : @assert Σ -d> assert :=
                 bi_and (local (fold_right (`and) (`True%type) (map locald_denote Q))).
Global Instance: Params (@LOCALx) 1 := {}.

Notation " 'LOCAL' ( )   z" := (LOCALx nil z%assert5)  (at level 9) : assert3.
Notation " 'LOCAL' ()   z" := (LOCALx nil z%assert5)  (at level 9) : assert3.

Notation " 'LOCAL' ( x ; .. ; y )   z" := (LOCALx (cons x%type .. (cons y%type nil) ..) z%assert5)
         (at level 9) : assert3.


Notation " 'RETURN' () z" := (LOCALx nil z%assert5) (at level 9) : assert3.
Notation " 'RETURN' ( ) z" := (LOCALx nil z%assert5) (at level 9) : assert3.
Notation " 'RETURN' ( x ) z" := (LOCALx (temp ret_temp x :: nil) z%assert5) (at level 9) :assert3.

Definition GLOBALSx {Σ} (gs : list globals) (X : @argsassert Σ): argsassert :=
 argsassert_of (fun (gvals : argsEnviron) =>
           LOCALx (map gvars gs)
                  (argsassert2assert nil X)
                  (Clight_seplog.mkEnv (fst gvals) nil nil)).
Arguments GLOBALSx {_} gs _ : simpl never.
Global Instance: Params (@GLOBALSx) 1 := {}.

Definition PARAMSx {Σ} (vals:list val)(X : @argsassert Σ): argsassert :=
 argsassert_of (fun (gvals : argsEnviron) => ⌜snd gvals = vals⌝ ∧ X gvals).
Arguments PARAMSx {Σ} vals _ : simpl never.
Global Instance: Params (@PARAMSx) 1 := {}.

Notation " 'PARAMS' ( x ; .. ; y )  z" := (PARAMSx (cons x%I .. (cons y%I nil) ..) z%assert4)
         (at level 9) : assert3.

Notation " 'PARAMS' ( )  z" := (PARAMSx nil z%assert4) (at level 9) : assert3.
Notation " 'PARAMS' ()  z" := (PARAMSx nil z%assert4) (at level 9) : assert3.

Notation " 'GLOBALS' ( x ; .. ; y )  z" := (GLOBALSx (cons x%I .. (cons y%I nil) ..) z%assert5)
         (at level 9) : assert4.

Notation " 'GLOBALS' ( )  z" := (GLOBALSx nil z%assert5) (at level 9) : assert4.
Notation " 'GLOBALS' ()  z" := (GLOBALSx nil z%assert5) (at level 9) : assert4.

Definition SEPx {A Σ} (R: list (iProp Σ)) : monPred A (iPropI Σ) :=
    ⎡fold_right_sepcon R⎤.
Arguments SEPx {A _} R : simpl never.
Global Instance: Params (@SEPx) 2 := {}.

Notation " 'SEP' ( x ; .. ; y )" := (GLOBALSx nil (SEPx (cons x%I .. (cons y%I nil) ..)))
         (at level 8) : assert4.

Notation " 'SEP' ( ) " := (GLOBALSx nil (SEPx nil)) (at level 8) : assert4.
Notation " 'SEP' () " := (GLOBALSx nil (SEPx nil)) (at level 8) : assert4.

Notation " 'SEP' ( x ; .. ; y )" := (SEPx (cons x%I .. (cons y%I nil) ..))
         (at level 8) : assert5.

Notation " 'SEP' ( ) " := (SEPx nil) (at level 8) : assert5.
Notation " 'SEP' () " := (SEPx nil) (at level 8) : assert5.

Notation " 'ENTAIL' d ',' P '⊢' Q " :=
  (@bi_entails (monPredI environ_index (iPropI _)) (local (tc_environ d) ∧ P%assert) Q%assert) (at level 99, P at level 98, Q at level 98).

Arguments semax {_ _ _ _ _} E Delta Pre%_assert cmd Post%_assert.

Module CConseqFacts :=
  SeparationLogicFacts.GenCConseqFacts
    (SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.CSHL_Def)
    (SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic).

Module Conseq :=
  SeparationLogicFacts.GenConseq
    (SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.CSHL_Def)
    (SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic).

Module ConseqFacts :=
  SeparationLogicFacts.GenConseqFacts
    (SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.CSHL_Def)
    (Conseq).

Section mpred.

Context `{!VSTGS OK_ty Σ}.

#[global] Instance PROPx_proper {A} : Proper (equiv ==> equiv ==> equiv) (@PROPx A Σ).
Proof.
  intros ??????.
  rewrite /PROPx; f_equiv; last done.
  f_equiv.
  induction H; simpl; f_equiv; done.
Qed.

#[global] Instance LOCALx_proper : Proper (equiv(Equiv := list.list_equiv(H := equivL)) ==> equiv ==> equiv) (@LOCALx Σ).
Proof.
  intros ??????.
  rewrite /LOCALx; f_equiv; last done.
  f_equiv.
  induction H; simpl; f_equiv; try done.
  by inv H.
Qed.

#[global] Instance SEPx_proper {A} : Proper (equiv ==> equiv) (@SEPx A Σ).
Proof.
  intros ???.
  rewrite /SEPx; f_equiv.
  induction H; simpl; f_equiv; done.
Qed.

#[global] Instance PARAMSx_proper : Proper (eq ==> equiv ==> equiv) (@PARAMSx Σ).
Proof.
  intros ?? -> ?? H.
  rewrite /PARAMSx; constructor; intros; simpl.
  rewrite H //.
Qed.

#[global] Instance GLOBALSx_proper : Proper (eq ==> equiv ==> equiv) (@GLOBALSx Σ).
Proof.
  intros ?? -> ?? H.
  rewrite /GLOBALSx /LOCALx; constructor; intros; simpl.
  monPred.unseal.
  rewrite H //.
Qed.

#[global] Existing Instance list.list_dist.

#[global] Instance PROPx_ne {A} : NonExpansive2 (@PROPx A Σ).
Proof.
  rewrite /PROPx; repeat intro. f_equiv; last done. f_equiv.
  induction H; try tauto; simpl.
  rewrite H IHForall2 //.
Qed.

#[global] Instance LOCALx_ne n : Proper (eq ==> dist n ==> dist n) (@LOCALx Σ).
Proof. solve_proper. Qed.

#[global] Instance SEPx_ne {A} : NonExpansive (@SEPx A Σ).
Proof.
  intros ????.
  rewrite /SEPx; f_equiv.
  induction H; simpl; f_equiv; done.
Qed.

#[global] Instance PARAMSx_ne n : Proper (eq ==> dist n ==> dist n) (@PARAMSx Σ).
Proof.
  intros ????; subst.
  rewrite /PARAMSx; constructor; intros; simpl.
  rewrite H //.
Qed.

#[global] Instance GLOBALSx_ne n : Proper (eq ==> dist n ==> dist n) (@GLOBALSx Σ).
Proof.
  intros ????; subst.
  rewrite /GLOBALSx /LOCALx; constructor; intros; simpl.
  monPred.unseal.
  rewrite H //.
Qed.

Lemma PROPx_Permutation {A}: forall P Q R,
  Permutation P Q ->
  @PROPx A Σ P R = PROPx Q R.
Proof.
  intros.
  unfold PROPx.
  f_equal; f_equal; apply prop_ext.
  induction H; simpl; tauto.
Qed.

Local Notation LOCALx := (@LOCALx Σ).

Lemma LOCALx_Permutation: forall P Q R,
  Permutation P Q ->
  LOCALx P R = LOCALx Q R.
Proof.
  intros.
  unfold LOCALx.
  f_equal.
  unfold local, lift1; unfold_lift.
  apply assert_ext; intros; simpl.
  f_equal; apply prop_ext.
  induction H; simpl; tauto.
Qed.

Lemma SEPx_Permutation {A}: forall P Q,
  Permutation P Q ->
  @SEPx A Σ P = SEPx Q.
Proof.
  intros.
  unfold SEPx.
  f_equal.
  induction H; simpl.
  + auto.
  + rewrite IHPermutation //.
  + rewrite sep_assoc (sep_comm y x) -sep_assoc //.
  + rewrite IHPermutation1 //.
Qed.

Lemma insert_prop : forall {A} (P: Prop) PP QR, (⌜P⌝ ∧ (@PROPx A Σ PP QR)) = PROPx (P::PP) QR.
Proof.
  intros. apply assert_ext; intros.
  unfold PROPx; monPred.unseal.
  rewrite log_normalize.and_assoc pure_and //.
Qed.

Lemma insert_local': forall (Q1: localdef) P Q R,
  (local (locald_denote Q1) ∧ (PROPx P (LOCALx Q R))) = (PROPx P (LOCALx (Q1 :: Q) R)).
Proof.
  intros.
  rewrite /PROPx /LOCALx /= local_lift2_and !and_assoc' (and_comm' (⌜_⌝)) //.
Qed.

Lemma insert_local: forall Q1 P Q R,
  (local (locald_denote Q1) ∧ (PROPx P (LOCALx Q (SEPx R)))) = (PROPx P (LOCALx (Q1 :: Q) (SEPx R))).
Proof. intros. apply insert_local'. Qed.

Lemma go_lower_lem20:
  forall {A} QR QR',
    (QR ⊢ QR') ->
    @PROPx A Σ nil QR ⊢ QR'.
Proof. unfold PROPx; intros; normalize. Qed.

Lemma grab_nth_SEP:
   forall n P Q R,
    PROPx P (LOCALx Q (SEPx R)) = (PROPx P (LOCALx Q (SEPx (nth n R emp :: delete_nth n R)))).
Proof.
  intros.
  rewrite /PROPx /LOCALx /SEPx; do 3 f_equiv.
  revert R; induction n; intros; destruct R; simpl; rewrite ?sep_emp //.
  rewrite IHn /=.
  rewrite !sep_assoc (sep_comm o) //.
Qed.

Fixpoint insert {A} (n: nat) (x: A) (ys: list A) {struct n} : list A :=
 match n with
 | O => x::ys
 | S n' => match ys with nil => x::ys | y::ys' => y::insert n' x ys' end
end.

(* Note: in the grab_indexes function,
  it's important that the {struct} induction NOT be on xs, because
  that list might not be concrete all the way to the end, where the ns list will be concrete.
  Thus we do it this particular way.  *)
Fixpoint  grab_indexes' {A} (ns: list (option nat)) (xs: list A) {struct ns} : list A * list A :=
match ns, xs with
| nil, xs => (nil, xs)
| _, nil => (nil,nil)
| Some n::ns', x::xs' => let (al,bl) := grab_indexes' ns' xs'
                               in (insert n x al, bl)
| None :: ns', x::xs' => let (al,bl) := grab_indexes' ns' xs'
                                  in (al, x::bl)
end.

Fixpoint grab_calc' (k: Z) (z: nat) (ns: list (option nat)): list (option nat) :=
match z, ns with
| O, _::ns' => Some (Z.to_nat k) :: ns'
| S z', None::ns' => None :: grab_calc' k z' ns'
| S z', Some n :: ns => Some n :: grab_calc' (k-1) z' ns
| O, nil => Some O :: nil
| S z', nil => None :: grab_calc' k z' nil
end.

Fixpoint grab_calc (k: Z) (zs: list Z) (ns: list (option nat)) : list (option nat) :=
match zs with
| nil => ns
| z::zs' => grab_calc (k+1) zs' (grab_calc' k (Z.to_nat z) ns)
end.

(* Eval compute in grab_calc 0 (3::1::5::nil) nil. *)

Definition grab_indexes {A} (ns: list Z) (xs: list A) : list A :=
    let (al,bl) := grab_indexes' (grab_calc 0 ns nil) xs in Floyd_app al bl.

(* TESTING
Variables (a b c d e f g h i j : assert).
Eval compute in grab_indexes (1::4::6::nil) (a::b::c::d::e::f::g::h::i::j::nil).
Eval compute in grab_indexes (1::6::4::nil) (a::b::c::d::e::f::g::h::i::j::nil).
*)

Lemma fold_right_nil: forall {A B} (f: A -> B -> B) (z: B),
   fold_right f z nil = z.
Proof. reflexivity. Qed.

Lemma fold_right_cons: forall {A B} (f: A -> B -> B) (z: B) x y,
   fold_right f z (x::y) = f x (fold_right f z y).
Proof. reflexivity. Qed.

Lemma fold_right_and_app:
  forall (Q1 Q2: list (environ -> Prop)) rho,
   fold_right `(and) `(True%type) (Q1 ++ Q2) rho =
   (fold_right `(and) `(True%type) Q1 rho /\ fold_right `(and) `(True%type) Q2 rho).
Proof.
intros.
induction Q1; simpl; auto.
unfold_lift; apply prop_ext; simpl; intuition auto.
unfold_lift in IHQ1. unfold_lift.
rewrite IHQ1.
clear; apply prop_ext; tauto.
Qed.

Lemma fold_right_local_app:
  forall (Q1 Q2: list (environ -> Prop)),
   @local Σ (fold_right `(and) `(True%type) (Q1 ++ Q2)) =
   (local (fold_right `(and) `(True%type) Q1) ∧ local (fold_right `(and) `(True%type) Q2)).
Proof.
  intros; apply assert_ext; intros; rewrite /local; monPred.unseal.
  rewrite /lift1 fold_right_and_app pure_and //.
Qed.

Lemma fold_right_sepcon_app :
 forall (P Q : list mpred), fold_right_sepcon (P++Q) =
        (fold_right_sepcon P ∗ fold_right_sepcon Q).
Proof.
  intros; induction P; simpl.
  - rewrite emp_sep //.
  - rewrite -sep_assoc IHP //.
Qed.

Lemma grab_indexes_SEP {A}:
  forall (ns: list Z) xs, @SEPx A Σ xs = SEPx (grab_indexes ns xs).
Proof.
  intros.
  rewrite /SEPx; f_equal.
  unfold grab_indexes. change @Floyd_app with @app.
  forget (grab_calc 0 ns nil) as ks.
  revert xs; induction ks; intro; auto.
  destruct a.
  - destruct xs. reflexivity.
    unfold grab_indexes'; fold @grab_indexes'.
    simpl fold_right_sepcon.
    specialize (IHks xs).
    case_eq (grab_indexes' ks xs); intros.
    rewrite H in IHks.
    rewrite fold_right_sepcon_app.
    rewrite IHks.
    rewrite fold_right_sepcon_app.
    forget (fold_right_sepcon l0) as P.
    rewrite sep_assoc. f_equal.
    clear.
    revert l; induction n; intro l. reflexivity.
    simpl. destruct l; auto.
    simpl. rewrite sep_assoc (sep_comm o) -sep_assoc IHn //.
  - destruct xs. reflexivity.
    unfold grab_indexes';  fold @grab_indexes'.
    simpl.
    specialize (IHks xs).
    case_eq (grab_indexes' ks xs); intros.
    rewrite H in IHks.
    simpl.
    simpl in IHks; rewrite IHks.
    clear.
    induction l; simpl; auto.
    rewrite -IHl !sep_assoc (sep_comm o) //.
Qed.

(*
Lemma semax_post0:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (R' ⊢ R) ->
   semax E Delta P c R' ->  semax E Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
rewrite bi.and_elim_r; auto.
intros. rewrite bi.and_elim_r; auto.
apply H.
Qed.
*)

(* monPred.unseal should take care of this
Lemma local_unfold: forall P rho, @local Σ P rho = ⌜P rho⌝.
Proof. reflexivity. Qed.

Lemma lower_sepcon:
  forall P Q rho, @sepcon (assert) _ _ P Q rho = sepcon (P rho) (Q rho).
Proof. reflexivity. Qed.
Lemma lower_andp:
  forall P Q rho, @andp (assert) _ P Q rho = andp (P rho) (Q rho).
Proof. reflexivity. Qed.

Lemma lift_prop_unfold:
   forall P z,  @prop (assert) _ P z = @prop mpred Nveric P.
Proof.  reflexivity. Qed.

Lemma andp_unfold: forall (P Q: assert) rho,
  @andp (assert) _ P Q rho = @andp mpred Nveric (P rho) (Q rho).
Proof. reflexivity. Qed.

Lemma refold_andp:
  forall (P Q: assert),
     (fun rho: environ => P rho ∧ Q rho) = (P ∧ Q).
Proof. reflexivity. Qed.

Lemma exp_unfold : forall A P rho,
 @exp (assert) _ A P rho = @exp mpred Nveric A (fun x => P x rho).
Proof.
intros. reflexivity.
Qed.*)

Context {OK_spec : ext_spec OK_ty} {CS: compspecs}.

Lemma extract_exists_pre_later:
  forall  (A : Type) (Q: assert) (P : A -> assert) c E Delta (R: ret_assert),
  (forall x, semax E Delta (Q ∧ ▷ P x) c R) ->
  semax E Delta (Q ∧ ▷ ∃x, P x) c R.
Proof.
  intros.
  apply extract_exists_pre in H.
  eapply CConseqFacts.semax_pre_fupd, H.
  iIntros "(_ & ?)".
  rewrite -bi.and_exist_l.
  iApply fupd_except_0; iIntros "!>".
  iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r.
  by iApply bi.later_exist_except_0.
Qed.

Definition semax_pre_post_fupd := CConseqFacts.semax_pre_post_fupd.
Definition semax_pre_fupd := CConseqFacts.semax_pre_fupd.
Definition semax_pre := ConseqFacts.semax_pre.
Definition semax_pre_simple := semax_pre.

Lemma semax_pre0:
 forall P' E Delta P c R,
     (P ⊢ P') ->
     semax E Delta P' c R  ->
     semax E Delta P c R.
Proof.
  intros.
  eapply semax_pre_simple; try apply H0.
  rewrite bi.and_elim_r //.
Qed.

Definition semax_pre_post := Conseq.semax_pre_post.

#[global] Instance semax_proper E Delta : Proper (equiv ==> eq ==> equiv ==> iff) (semax E Delta).
Proof.
  intros ?? Hpre ?? -> [????] [????] (Hpost1 & Hpost2 & Hpost3 & Hpost4); simpl in *.
  split; eapply semax_pre_post; intros; rewrite ?Hpre /= ?Hpost1 ?Hpost2 ?Hpost3 ?Hpost4 bi.and_elim_r //.
Qed.

Lemma semax_frame_PQR:
  forall Q2 R2 E Delta R1 P Q P' Q' R1' c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     semax E Delta (PROPx P (LOCALx Q (SEPx R1))) c
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R1')))) ->
     semax E Delta (PROPx P (LOCALx (Q++Q2) (SEPx (R1++R2)))) c
                     (normal_ret_assert (PROPx P' (LOCALx (Q'++Q2) (SEPx (R1'++R2))))).
Proof.
  intros.
  assert (forall P Q R1, PROPx P (LOCALx (Q ++ Q2) (SEPx (R1 ++ R2))) ⊣⊢
    PROPx P (LOCALx Q (SEPx (R1))) ∗ (LOCALx Q2 (SEPx R2))) as Hequiv.
  { intros; rewrite /PROPx /LOCALx /SEPx map_app fold_right_local_app fold_right_sepcon_app embed_sep.
    iSplit.
    * iIntros "($ & L & $ & $)".
      rewrite bi.affinely_and; iDestruct "L" as "($ & $)".
    * iIntros "((? & ? & ?) & ? & $)"; auto. }
  rewrite Hequiv.
  eapply ConseqFacts.semax_post, semax_frame, H0; simpl; try done; intros; try by iIntros "(_ & [] & _)".
  rewrite Hequiv bi.and_elim_r //.
Qed.

Lemma semax_frame1:
 forall QFrame Frame E Delta Delta1
     P Q c R P1 Q1 R1 P2 Q2 R2,
    semax E Delta1 (PROPx P1 (LOCALx Q1 (SEPx R1))) c
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    Delta1 = Delta ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
    PROPx P1 (LOCALx (Q1++QFrame) (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c (LOCALx QFrame (SEPx Frame)) ->
    semax E Delta (PROPx P (LOCALx Q (SEPx R))) c
                      (normal_ret_assert (PROPx P2 (LOCALx (Q2++QFrame) (SEPx (R2++Frame))))).
Proof.
  intros. subst.
  eapply semax_pre.
  apply H1.
  apply semax_frame_PQR; auto.
Qed.

Definition semax_post_fupd := CConseqFacts.semax_post_fupd.
Definition semax_post := ConseqFacts.semax_post.

Lemma semax_post_flipped:
  forall (R' : ret_assert) E (Delta : tycontext) (R : ret_assert)
         (P : assert) (c : statement),
   semax E Delta P c R' ->
   ENTAIL Delta, RA_normal R' ⊢ RA_normal R ->
   ENTAIL Delta, RA_break R' ⊢ RA_break R ->
   ENTAIL Delta, RA_continue R' ⊢ RA_continue R ->
   (forall vl, ENTAIL Delta, RA_return R' vl ⊢ RA_return R vl) ->
       semax E Delta P c R.
Proof. intros; eapply semax_post; eassumption. Qed.

Definition semax_post' := ConseqFacts.semax_post'.
Definition semax_pre_post' := ConseqFacts.semax_pre_post'.

Lemma sequential:
  forall E Delta P c Q,
        semax E Delta P c (normal_ret_assert (RA_normal Q)) ->
          semax E Delta P c Q.
Proof.
  intros.
  destruct Q as [?Q ?Q ?Q ?Q].
  eapply semax_post; eauto; intros; rewrite bi.and_elim_r; simpl; auto; normalize.
Qed.

Lemma sequential':
    forall Q E Delta P c R,
               semax E Delta P c (normal_ret_assert Q) ->
               semax E Delta P c (overridePost Q R).
Proof.
  intros.
  apply semax_post with (normal_ret_assert Q); auto; simpl; intros;
    rewrite bi.and_elim_r; simpl; normalize.
  destruct R; simpl; auto.
Qed.

Lemma semax_seq':
 forall E Delta P c1 P' c2 Q,
         semax E Delta P c1 (normal_ret_assert P') ->
         semax E Delta P' c2 Q ->
         semax E Delta P (Ssequence c1 c2) Q.
Proof.
  intros. apply semax_seq with P'; auto.
  apply sequential'. auto.
Qed.

Lemma semax_frame_seq:
 forall QFrame Frame E Delta
     P Q c1 c2 R P1 Q1 R1 P2 Q2 R2 R3,
    semax E Delta (PROPx P1 (LOCALx Q1 (SEPx R1))) c1
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
    PROPx P1 (LOCALx (Q1++QFrame) (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c1 (LOCALx QFrame (SEPx Frame)) ->
    semax E Delta
         (PROPx P2 (LOCALx (Q2++QFrame) (SEPx (R2 ++ Frame)))) c2 R3 ->
    semax E Delta (PROPx P (LOCALx Q (SEPx R))) (Ssequence c1 c2) R3.
Proof.
  intros.
  eapply semax_seq'.
  eapply semax_pre.
  apply H0.
  apply semax_frame_PQR; auto.
  apply H.
  apply H2.
Qed.

Lemma derives_frame_PQR:
  forall R1 R2 Delta P Q P' Q' R1',
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R1)) ⊢ PROPx P' (LOCALx Q' (SEPx R1')) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx (R1++R2))) ⊢ PROPx P' (LOCALx Q' (SEPx (R1'++R2))).
Proof.
  intros.
  rewrite /PROPx /LOCALx /SEPx !fold_right_sepcon_app !embed_sep.
  rewrite !assoc; iIntros "(? & ? & $)".
  rewrite -!assoc; iApply H.
  rewrite /PROPx /LOCALx /SEPx; iFrame.
  rewrite /bi_affinely comm -!assoc //.
Qed.

Lemma fold_right_sepcon_eq {B : bi} (l : list B) : fold_right_sepcon l = fold_right bi_sep emp l.
Proof.
  induction l; auto; simpl.
  rewrite IHl //.
Qed.

Lemma gather_SEP {A}:
  forall R1 R2,
    @SEPx A Σ (R1 ++ R2) = SEPx (fold_right bi_sep emp R1 :: R2).
Proof.
  intros.
  unfold SEPx.
  rewrite fold_right_sepcon_app fold_right_sepcon_eq //.
Qed.

Fixpoint replace_nth {A} (n: nat) (al: list A) (x: A) {struct n}: list A :=
 match n, al with
 | O , a::al => x::al
 | S n', a::al' => a :: replace_nth n' al' x
 | _, nil => nil
 end.

Fixpoint my_nth {A} (n: nat) (al: list A) (default: A) {struct n} : A :=
  (* just like nth; make a new copy, for better control of unfolding *)
match n, al with
| O, a::al' => a
| S n', a::al' => my_nth n' al' default
| _, nil => default
end.

Lemma replace_nth_replace_nth: forall {A: Type} R n {Rn Rn': A},
  replace_nth n (replace_nth n R Rn) Rn' = replace_nth n R Rn'.
Proof.
  intros.
  revert R; induction n; destruct R; simpl in *.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
Qed.

Lemma replace_nth_nth_error: forall {A:Type} R n (Rn:A),
  nth_error R n = Some Rn ->
  R = replace_nth n R Rn.
Proof.
  intros.
  revert R H; induction n; intros; destruct R.
  + reflexivity.
  + simpl. inversion H. reflexivity.
  + inversion H.
  + inversion H. simpl.
    rewrite -> (IHn R) at 1; simpl; [reflexivity|exact H1].
Qed.

Lemma nth_error_replace_nth: forall {A:Type} R n (Rn Rn':A),
  nth_error R n = Some Rn ->
  nth_error (replace_nth n R Rn') n = Some Rn'.
Proof.
  intros.
  revert R H; induction n; intros; destruct R; simpl.
  + inversion H.
  + inversion H.
    reflexivity.
  + inversion H.
  + inversion H.
    apply IHn, H1.
Qed.

Lemma map_replace_nth:
  forall {A B} (f: A -> B) n R X, map f (replace_nth n R X) =
       replace_nth n (map f R) (f X).
Proof.
intros.
 revert R; induction n; destruct R; simpl; auto.
 f_equal; auto.
Qed.

Lemma replace_nth_commute:
  forall {A} i j R (a b: A),
   i <> j ->
   replace_nth i (replace_nth j R b) a =
   replace_nth j (replace_nth i R a) b.
Proof.
intros.
rename i into i'. rename j into j'. rename R into R'.
assert (forall i j R (a b: A),
             (i<j)%nat ->
              replace_nth i (replace_nth j R b) a = replace_nth j (replace_nth i R a) b). {
induction i; destruct j, R; simpl; intros; auto; try lia.
f_equal. apply IHi. lia.
}
assert (i'<j' \/ i'>j')%nat by lia.
clear H.
destruct H1.
apply H0; auto.
symmetry; apply H0; auto.
Qed.

Lemma nth_error_replace_nth':
  forall {A} i j R (a:A),
  (i <> j)%nat -> nth_error (replace_nth i R a) j = nth_error R j.
Proof.
induction i; destruct j,R; intros; simpl; auto.
contradiction H; auto.
Qed.

Lemma PROP_LOCAL_sep1 : forall P Q R1 R, PROPx P (LOCALx Q (SEPx (R1 :: R))) = (PROPx P (LOCALx Q (SEPx [R1])) ∗ SEPx R).
Proof.
  intros; rewrite /PROPx /LOCALx /SEPx /=.
  apply assert_ext; intros; monPred.unseal; unfold lift1.
  rewrite !log_normalize.and_assoc -!pure_and.
  normalize.
Qed.

Lemma PROP_LOCAL_sep2 : forall P Q R1 R, PROPx P (LOCALx Q (SEPx (R1 :: R))) = (⎡R1⎤ ∗ PROPx P (LOCALx Q (SEPx R))).
Proof.
  intros; rewrite /PROPx /LOCALx /SEPx /=.
  apply assert_ext; intros; monPred.unseal; unfold lift1.
  rewrite !log_normalize.and_assoc -!pure_and.
  normalize.
Qed.

Lemma replace_SEP'':
 forall n R' Delta P Q Rs Post,
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (my_nth n Rs True ::  nil))) ⊢ ⎡R'⎤ ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (replace_nth n Rs R'))) ⊢ Post ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx Rs)) ⊢ Post.
Proof.
  intros.
  rewrite -H0; clear - H.
  apply bi.and_intro; first by iIntros "($ & _)".
  apply bi.and_intro; first by iIntros "(_ & $ & _)".
  apply bi.and_intro; first by iIntros "(_ & _ & $ & _)".
  revert Rs H; induction n; destruct Rs; simpl; intros; try solve [iIntros "(_ & _ & _ & $)"].
  - rewrite PROP_LOCAL_sep1 /= bi.persistent_and_sep_assoc H /SEPx /= embed_sep //.
  - apply IHn in H.
    rewrite PROP_LOCAL_sep2 /SEPx /= embed_sep.
    rewrite -persistent_and_sep_assoc' H //.
Qed.

Lemma replace_SEP':
 forall n R' E Delta P Q Rs c Post,
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (my_nth n Rs True ::  nil))) ⊢ ⎡R'⎤ ->
 semax E Delta (PROPx P (LOCALx Q (SEPx (replace_nth n Rs R')))) c Post ->
 semax E Delta (PROPx P (LOCALx Q (SEPx Rs))) c Post.
Proof.
  intros.
  eapply semax_pre, H0.
  eapply replace_SEP''; eauto.
  iIntros "(_ & $)".
Qed.

Lemma replace_SEP''_fupd:
 forall n R' E Delta P Q Rs Post,
 (ENTAIL Delta, PROPx P (LOCALx Q (SEPx (my_nth n Rs True ::  nil))) ⊢ |={E}=> ⎡R'⎤) ->
 (ENTAIL Delta, PROPx P (LOCALx Q (SEPx (replace_nth n Rs R'))) ⊢ |={E}=> Post) ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx Rs)) ⊢ |={E}=> Post.
Proof.
  intros.
  rewrite -(fupd_trans _ E) -H0.
  clear - H.
  iIntros "(#? & #? & #? & H)".
  rewrite /SEPx.
  iInduction n as [|] "IH" forall (Rs H); destruct Rs; simpl.
  - iIntros "!>"; iFrame; auto.
  - rewrite !embed_sep; iDestruct "H" as "(? & $)".
    iMod (H with "[$]") as "$"; auto.
  - iIntros "!>"; iFrame; auto.
  - rewrite !embed_sep; iDestruct "H" as "($ & ?)".
    by iApply "IH".
Qed.

Lemma replace_SEP'_fupd:
 forall n R' E Delta P Q Rs c Post,
 (ENTAIL Delta, PROPx P (LOCALx Q (SEPx (my_nth n Rs True :: nil))) ⊢ |={E}=> ⎡R'⎤) ->
 semax E Delta (PROPx P (LOCALx Q (SEPx (replace_nth n Rs R')))) c Post ->
 semax E Delta (PROPx P (LOCALx Q (SEPx Rs))) c Post.
Proof.
  intros.
  eapply semax_pre_fupd, H0.
  eapply replace_SEP''_fupd; eauto.
  by iIntros "(_ & $)".
Qed.

Lemma semax_extract_PROP_True:
  forall E Delta (PP: Prop) P QR c Post,
        PP ->
        semax E Delta (PROPx P QR) c Post ->
       semax E Delta (PROPx (PP::P) QR) c Post.
Proof.
  intros.
  eapply semax_pre_simple, H0.
  rewrite /PROPx /= bi.pure_and.
  iIntros "(_ & (_ & $) & $)".
Qed.

Lemma semax_extract_PROP:
  forall E Delta (PP: Prop) P QR c Post,
       (PP -> semax E Delta (PROPx P QR) c Post) ->
       semax E Delta (PROPx (PP::P) QR) c Post.
Proof.
  intros.
  apply semax_extract_prop in H.
  eapply semax_pre_simple, H.
  rewrite /PROPx /= bi.pure_and.
  by iIntros "(_ & (% & $) & $)".
Qed.

Lemma PROP_later_derives:
 forall {A} P QR QR', (QR ⊢ ▷QR') ->
    @PROPx A Σ P QR ⊢ ▷ PROPx P QR'.
Proof.
  intros.
  rewrite /PROPx H; iIntros "($ & $)".
Qed.

Lemma LOCAL_later_derives:
 forall Q R R', (R ⊢ ▷R') -> LOCALx Q R ⊢ ▷ LOCALx Q R'.
Proof.
  intros.
  rewrite /LOCALx H; iIntros "(? & $)"; auto.
Qed.

Lemma SEP_later_derives:
  forall {A} P Q P' Q',
      (P ⊢ ▷ P') ->
      (@SEPx A Σ Q ⊢ ▷ SEPx Q') ->
      @SEPx A Σ (P::Q) ⊢ ▷ SEPx (P'::Q').
Proof.
  unfold SEPx; intros.
  rewrite /= !embed_sep H H0 embed_later.
  iIntros "($ & $)".
Qed.

Lemma local_lift0: forall P, @local Σ (lift0 P) = ⌜P⌝.
Proof.
  intros. rewrite /local /lift0; apply assert_ext; intros; monPred.unseal; done.
Qed.

Lemma extract_exists_post:
  forall {A: Type} (x: A) E Delta
       (P: assert) c (R: A -> assert),
  semax E Delta P c (normal_ret_assert (R x)) ->
  semax E Delta P c (normal_ret_assert (∃ x, R x)).
Proof.
  intros.
  eapply semax_pre_post, H; intros; rewrite bi.and_elim_r // /=; eauto.
Qed.

Lemma extract_exists_in_SEP:
  forall {A} (R1: A -> mpred) P Q R,
    PROPx P (LOCALx Q (SEPx ((∃ x, R1 x) :: R))) =
    (∃ x:A, PROPx P (LOCALx Q (SEPx (R1 x::R))))%assert.
Proof.
  intros.
  rewrite /PROPx /LOCALx /SEPx; apply assert_ext; intros; monPred.unseal.
  normalize.
Qed.

Lemma flatten_sepcon_in_SEP:
  forall P Q R1 R2 R,
           PROPx P (LOCALx Q (SEPx ((R1∗R2) :: R))) =
           PROPx P (LOCALx Q (SEPx (R1 :: R2 :: R))).
Proof.
  intros.
  rewrite /PROPx /LOCALx /SEPx /= -sep_assoc //.
Qed.

Lemma flatten_sepcon_in_SEP'':
  forall n P Q (R1 R2: mpred) (R: list mpred) R',
   nth_error R n = Some ((R1 ∗ R2)) ->
   R' = Floyd_firstn n R ++ R1 :: R2 :: Floyd_skipn (S n) R ->
   PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q (SEPx R')).
Proof.
  intros.
  rewrite /PROPx /LOCALx /SEPx; do 3 f_equiv.
  subst R'.
  revert R H; clear; induction n; destruct R; intros; simpl in *; try done.
  - inv H.
    rewrite sep_assoc //.
  - rewrite IHn //.
Qed.

Lemma semax_ff:
  forall E Delta c R,
   semax E Delta False c R.
Proof.
  intros.
  apply ConseqFacts.semax_pre_simple with (False ∧ False).
  { apply bi.False_elim. }
  apply semax_extract_prop; contradiction.
Qed.

Lemma extract_prop_in_SEP:
  forall n P1 Rn P Q R,
   nth n R emp = (⌜P1⌝ ∧ Rn) ->
   PROPx P (LOCALx Q (SEPx R)) = PROPx (P1::P) (LOCALx Q (SEPx (replace_nth n R Rn))).
Proof.
  intros.
  rewrite /PROPx /LOCALx /SEPx /= pure_and'.
  rewrite (and_comm' ⌜P1⌝) -and_assoc'; f_equal.
  rewrite and_assoc' (and_comm' ⌜P1⌝) -and_assoc'; f_equiv.
  apply assert_ext; intros; monPred.unseal.
  revert R H; induction n; destruct R; simpl; intros.
  - rewrite H log_normalize.and_assoc -pure_and (@prop_ext (P1 /\ P1) P1) //; tauto.
  - rewrite H sepcon_andp_prop' //.
  - rewrite H log_normalize.and_assoc -pure_and (@prop_ext (P1 /\ P1) P1) //; tauto.
  - rewrite IHn //.
    rewrite sepcon_andp_prop //.
Qed.

Lemma insert_SEP:
 forall R1 P Q R, (⎡R1⎤ ∗ PROPx P (LOCALx Q (SEPx R))) = PROPx P (LOCALx Q (SEPx (R1::R))).
Proof.
  intros; rewrite PROP_LOCAL_sep2 //.
Qed.

Lemma delete_emp_in_SEP {A}:
  forall n (R: list mpred),
    nth_error R n = Some emp ->
    @SEPx A Σ R = SEPx (firstn n R ++ list_drop (S n) R).
Proof.
  intros.
  rewrite /SEPx.
  f_equiv.
  revert R H; induction n; destruct R; simpl; intros; auto.
  - inv H; rewrite emp_sep //.
  - rewrite IHn //.
Qed.

Lemma nth_error_local:
  forall n Delta P Q R (Qn: localdef),
    nth_error Q n = Some Qn ->
    ENTAIL Delta, PROPx P (LOCALx Q R) ⊢ local (locald_denote Qn).
Proof.
  intros.
  rewrite /PROPx !bi.and_elim_r.
  rewrite /LOCALx bi.and_elim_l.
  revert Q H; induction n; destruct Q; intros; inv H; simpl.
  - rewrite local_lift2_and bi.and_elim_l //.
  - rewrite local_lift2_and bi.and_elim_r IHn //.
Qed.

Lemma in_nth_error: forall {A} (x: A) xs, In x xs -> exists n, nth_error xs n = Some x.
Proof.
  intros.
  induction xs.
  + inversion H.
  + destruct H.
    - subst; exists 0%nat.
      reflexivity.
    - destruct (IHxs H) as [?n ?H].
      exists (S n).
      simpl.
      tauto.
Qed.

Lemma in_local: forall Q0 Delta P Q R, In Q0 Q ->
   ENTAIL Delta, PROPx P (LOCALx Q R) ⊢ local (locald_denote Q0).
Proof.
  intros.
  destruct (in_nth_error _ _ H) as [?n ?H].
  eapply nth_error_local.
  eauto.
Qed.

Lemma lower_PROP_LOCAL_SEP:
  forall P Q R rho, PROPx P (LOCALx Q (SEPx R)) rho =
     (⌜fold_right and True P⌝ ∧ (local (fold_right (`and) (`True%type) (map locald_denote Q)) ∧ ⎡fold_right bi_sep emp R⎤)) rho.
Proof. intros; rewrite /PROPx /LOCALx /SEPx fold_right_sepcon_eq //. Qed.

(*Lemma lower_TT: forall rho, @TT (assert) _ rho = @TT mpred Nveric.
Proof. reflexivity. Qed.
#[export] Hint Rewrite lower_TT : norm2.

Lemma lower_FF: forall rho, @FF (assert) _ rho = @FF mpred Nveric.
Proof. reflexivity. Qed.
#[export] Hint Rewrite lower_FF : norm2.*)

Lemma assert_PROP:
 forall P1 E Delta PQR c Post,
    ENTAIL Delta, PQR ⊢ ⌜P1⌝ ->
   (P1 -> semax E Delta PQR c Post) ->
   semax E Delta PQR c Post.
Proof.
  intros.
  apply semax_extract_prop in H0.
  eapply semax_pre, H0.
  apply bi.and_intro; auto.
  rewrite bi.and_elim_r //.
Qed.

Lemma semax_extract_later_prop1:
  forall E Delta (PP: Prop) P c Q,
           (PP -> semax E Delta (▷ P) c Q) ->
           semax E Delta (▷ (⌜PP⌝ ∧ P)) c Q.
Proof.
  intros.
  apply semax_extract_later_prop in H.
  eapply semax_pre, H.
  rewrite bi.and_elim_r bi.later_and //.
Qed.

Lemma assert_later_PROP:
 forall P1 E Delta PQR c Post,
    ENTAIL Delta, PQR ⊢ ⌜P1⌝ ->
   (P1 -> semax E Delta (▷ PQR) c Post) ->
   semax E Delta (▷ PQR) c Post.
Proof.
  intros.
  apply semax_extract_later_prop1 in H0.
  eapply semax_pre, H0.
  iIntros "H"; iSplit.
  - iApply H; iNext; done.
  - iDestruct "H" as "(_ & $)".
Qed.

Lemma assert_PROP' {B : bi}:
 forall P Pre (Post : B),
   (Pre ⊢ ⌜P⌝) ->
   (P -> Pre ⊢ Post) ->
   Pre ⊢ Post.
Proof.
  intros; iIntros "H".
  iDestruct (H with "H") as %?.
  by iApply H0.
Qed.

Lemma assert_later_PROP':
 forall P1 E Delta PQR PQR' c Post,
    ENTAIL Delta, PQR' ⊢ ⌜P1⌝ ->
    (PQR ⊢ ▷ PQR') ->
   (P1 -> semax E Delta PQR c Post) ->
   semax E Delta PQR c Post.
Proof.
  intros.
  apply semax_extract_later_prop in H1.
  eapply semax_pre_simple, H1.
  iIntros "H"; iSplit.
  - rewrite -H H0; iNext; done.
  - rewrite bi.and_elim_r //.
Qed.

Lemma assert_LOCAL:
 forall Q1 E Delta P Q R c Post,
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ local (locald_denote Q1) ->
   semax E Delta (PROPx P (LOCALx (Q1::Q) (SEPx R))) c Post ->
   semax E Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros.
  eapply semax_pre, H0.
  rewrite <- (insert_local Q1); apply bi.and_intro; auto.
  rewrite bi.and_elim_r //.
Qed.

Lemma drop_LOCAL'':
  forall (n: nat)  P Q R Post,
   (PROPx P (LOCALx (delete_nth n Q) (SEPx R)) ⊢ Post) ->
   PROPx P (LOCALx Q (SEPx R)) ⊢ Post.
Proof.
  intros.
  rewrite -H.
  apply bi.and_mono; first done.
  apply bi.and_mono; last done.
  clear; revert Q; induction n; destruct Q; simpl; intros; intuition auto.
  - rewrite local_lift2_and bi.and_elim_r //.
  - rewrite !local_lift2_and IHn //.
Qed.

Lemma drop_LOCAL':
  forall (n: nat)  Delta P Q R Post,
   ENTAIL Delta, PROPx P (LOCALx (delete_nth n Q) (SEPx R)) ⊢ Post ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ Post.
Proof.
  intros.
  rewrite -H.
  apply bi.and_mono; first done.
  apply bi.and_mono; first done.
  apply bi.and_mono; last done.
  clear; revert Q; induction n; destruct Q; simpl; intros; intuition auto.
  - rewrite local_lift2_and bi.and_elim_r //.
  - rewrite !local_lift2_and IHn //.
Qed.

Lemma drop_LOCAL:
  forall (n: nat) E Delta P Q R c Post,
   semax E Delta (PROPx P (LOCALx (delete_nth n Q) (SEPx R))) c Post ->
   semax E Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros.
  eapply semax_pre, H.
  rewrite bi.and_elim_r; eapply drop_LOCAL''; done.
Qed.

Definition not_conj_notation (P: Prop) := True%type.

Lemma split_first_PROP {A}:
  forall P Q R S,
  not_conj_notation (P/\Q) ->
  @PROPx A Σ ((P/\Q)::R) S = PROPx (P::Q::R) S.
Proof.
  intros. unfold PROPx; simpl.
  f_equal; f_equal; apply prop_ext; rewrite assoc //.
Qed.

Lemma perm_derives:
  forall Delta P Q R P' Q' R',
    Permutation P P' ->
    Permutation Q Q' ->
    Permutation R R' ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ PROPx P' (LOCALx Q' (SEPx R')).
Proof.
  intros.
  erewrite bi.and_elim_r, PROPx_Permutation, LOCALx_Permutation, SEPx_Permutation; done.
Qed.

Lemma semax_frame_perm:
forall (Qframe : list localdef)
         (Rframe : list mpred)
         E
         (Delta : tycontext)
         (P : list Prop) (Q : list localdef) (c : statement)
         (R : list mpred)
         (Q1 : list localdef) (R1 : list mpred)
         (P2 : list Prop) (Q2 : list localdef)
         (R2 : list mpred),
       closed_wrt_modvars c (LOCALx Qframe (SEPx Rframe)) ->
       Permutation (Qframe ++ Q1) Q ->
       Permutation (Rframe ++ R1)  R ->
       semax E Delta (PROPx P (LOCALx Q1 (SEPx R1))) c
         (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
       semax E Delta (PROPx P (LOCALx Q (SEPx R))) c
         (normal_ret_assert
            (PROPx P2 (LOCALx (Q2 ++ Qframe) (SEPx (R2 ++ Rframe))))).
Proof.
  intros.
  eapply (semax_frame1 Qframe Rframe); try eassumption; auto.
  apply perm_derives.
  apply Permutation_refl.
  eapply perm_trans; [apply Permutation_sym; eassumption | apply Permutation_app_comm].
  eapply perm_trans; [apply Permutation_sym; eassumption | apply Permutation_app_comm].
Qed.

Lemma semax_post_flipped' :
   forall (R': assert) E (Delta: tycontext) (R P: assert) c,
       semax E Delta P c (normal_ret_assert R') ->
       ENTAIL Delta, R' ⊢ R ->
       semax E Delta P c (normal_ret_assert R).
Proof.
  intros; eapply semax_post_flipped; [ eassumption | .. ]; auto;
    intros; rewrite bi.and_elim_r; simpl; normalize.
Qed.


Lemma semax_pre_later:
 forall P' E Delta P1 P2 P3 c R,
     ENTAIL Delta, PROPx P1 (LOCALx P2 (SEPx P3)) ⊢ P' ->
     semax E Delta (▷ P') c R  ->
     semax E Delta (▷ (PROPx P1 (LOCALx P2 (SEPx P3)))) c R.
Proof.
  intros.
  eapply semax_pre_simple, H0.
  rewrite -H; iIntros "? !>"; done.
Qed.

Lemma PROP_LOCAL_SEP_cons: forall P1 P2 P3 F,
  PROPx P1 (LOCALx P2 (SEPx (F :: P3))) =
  (⎡F⎤ ∗ PROPx P1 (LOCALx P2 (SEPx P3))).
Proof.
  intros; apply PROP_LOCAL_sep2.
Qed.

Lemma semax_frame':
  forall E Delta P1 P2 P3 s Q1 Q2 Q3 F,
  semax E Delta
    (PROPx P1 (LOCALx P2 (SEPx P3))) s
      (normal_ret_assert (PROPx Q1 (LOCALx Q2 (SEPx Q3)))) ->
  semax E Delta
    (PROPx P1 (LOCALx P2 (SEPx (F :: P3)))) s
      (normal_ret_assert (PROPx Q1 (LOCALx Q2 (SEPx (F :: Q3))))).
Proof.
  intros.
  eapply semax_proper, semax_frame, H; auto.
  - rewrite PROP_LOCAL_SEP_cons comm //.
  - split3; last split; simpl; intros; rewrite ?bi.sep_False //.
    rewrite PROP_LOCAL_SEP_cons comm //.
  - hnf; intros; monPred.unseal; done.
Qed.

Lemma semax_frame'':
  forall E Delta P1 P2 P3 s t Q1 Q2 Q3 F,
  semax E Delta
    (PROPx P1 (LOCALx P2 (SEPx P3))) s
      (frame_ret_assert
        (function_body_ret_assert t (PROPx Q1 (LOCALx Q2 (SEPx Q3)))) emp) ->
  semax E Delta
    (PROPx P1 (LOCALx P2 (SEPx (F :: P3)))) s
      (frame_ret_assert
        (function_body_ret_assert t (PROPx Q1 (LOCALx Q2 (SEPx (F :: Q3))))) emp).
Proof.
  intros.
  eapply semax_proper, semax_frame, H; auto.
  - rewrite PROP_LOCAL_SEP_cons comm //.
  - split3; last split; simpl; intros; rewrite ?bi.sep_False ?bi.sep_emp // /=.
    + destruct t; [| rewrite bi.sep_False //..].
      split => rho; monPred.unseal.
      rewrite PROP_LOCAL_SEP_cons comm; monPred.unseal; done.
    + destruct v; simpl.
      * rewrite -bi.persistent_and_sep_assoc; f_equiv.
        split => rho; monPred.unseal.
        rewrite PROP_LOCAL_SEP_cons comm; monPred.unseal; done.
      * destruct t; [| rewrite bi.sep_False //..].
        split => rho; monPred.unseal.
        rewrite PROP_LOCAL_SEP_cons comm; monPred.unseal; done.
  - hnf; intros; monPred.unseal; done.
Qed.

Definition is_void_type (ty: type) : bool :=
 match ty with Tvoid => true | _ => false end.

Definition ret_tycon (Delta: tycontext): tycontext :=
  mk_tycontext
    (if is_void_type (ret_type Delta)
      then (Maps.PTree.empty _)
      else (Maps.PTree.set ret_temp (ret_type Delta) (Maps.PTree.empty _)))
     (Maps.PTree.empty _)
     (ret_type Delta)
     (glob_types Delta)
     (glob_specs Delta)
     (annotations Delta).

Lemma tc_environ_Tvoid:
  forall Delta rho, tc_environ Delta rho -> ret_type Delta = Tvoid ->
   tc_environ (ret_tycon Delta) (globals_only rho).
Proof.
  intros.
  unfold ret_tycon. rewrite H0. simpl is_void_type. cbv beta iota.
  destruct H as [? [? ?]]; split3; auto.
  unfold globals_only; simpl.
  hnf; intros. setoid_rewrite Maps.PTree.gempty in H3; inv H3.
  simpl.
  clear - H1.
  unfold ret_tycon, var_types.
  hnf; intros. setoid_rewrite (Maps.PTree.gempty _ id).
  split; intro. inv H. destruct H as [v ?].
  unfold ve_of, globals_only, Map.get, Map.empty in H. inv H.
Qed.


Lemma semax_post'': forall R' E Delta R P c t,
           t = ret_type Delta ->
           ENTAIL ret_tycon Delta, R' ⊢ R ->
      semax E Delta P c (frame_ret_assert (function_body_ret_assert t R') emp) ->
      semax E Delta P c (frame_ret_assert (function_body_ret_assert t R) emp).
Proof.
  intros. eapply semax_post, H1; simpl; intros; rewrite ?bi.sep_False ?bi.sep_emp ?bi.and_False // /=.
  + destruct t; [| rewrite bi.and_False //..].
    split => rho; monPred.unseal.
    rewrite -H0; monPred.unseal. apply bi.and_mono; last done.
    apply bi.pure_mono; intros.
    apply tc_environ_Tvoid; auto.
  + destruct vl; simpl.
    * split => rho; monPred.unseal.
      rewrite -H0; monPred.unseal.
      iIntros "((% & % & %) & % & $)"; iPureIntro.
      split; first done; split; last done.
      split3; simpl; auto.
      simple_if_tac; intros ??; first done.
      destruct (eq_dec id ret_temp); last by setoid_rewrite Maps.PTree.gso.
      subst; setoid_rewrite Maps.PTree.gss; inversion 1; subst.
      rewrite Map.gss; eexists; split; first done.
      apply tc_val_tc_val'; done.
      { split; first done.
        intros (? & ?); done. }
    * destruct t; [| rewrite bi.and_False //..].
      split => rho; monPred.unseal.
      rewrite -H0; monPred.unseal. apply bi.and_mono; last done.
      apply bi.pure_mono; intros.
      apply tc_environ_Tvoid; auto.
Qed.

Definition ret0_tycon (Delta: tycontext): tycontext :=
  mk_tycontext (Maps.PTree.empty _) (Maps.PTree.empty _) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta).

Definition ret1_tycon (Delta: tycontext): tycontext :=
  mk_tycontext (Maps.PTree.set ret_temp (ret_type Delta) (Maps.PTree.empty _))
    (Maps.PTree.empty _) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta).

Lemma make_args0_tc_environ: forall rho Delta,
  tc_environ Delta rho ->
  tc_environ (ret0_tycon Delta) (make_args nil nil rho).
Proof.
  intros.
  destruct H as [? [? ?]].
  split; [| split]; simpl.
  + hnf; intros.
    setoid_rewrite Maps.PTree.gempty in H2; inversion H2.
  + hnf; split; intros.
    - setoid_rewrite Maps.PTree.gempty in H2; inversion H2.
    - destruct H2 as [v ?].
      inversion H2.
  + auto.
Qed.

Lemma make_args1_tc_environ: forall rho Delta v,
  tc_environ Delta rho ->
  tc_val (ret_type Delta) v ->
  tc_environ (ret1_tycon Delta) (make_args (ret_temp :: nil) (v :: nil) rho).
Proof.
  intros.
  rename H0 into HH.
  destruct H as [? [? ?]].
  simpl.
  split; [| split].
  + hnf; intros.
    unfold ret1_tycon, temp_types in H2.
    setoid_rewrite Maps.PTree.gsspec in H2.
    destruct (peq id ret_temp).
    - subst.
      inversion H2; subst.
      exists v; simpl.
      split; auto.
      apply tc_val_tc_val'; auto.
    - rewrite Maps.PTree.gempty in H2; inversion H2.
  + hnf; split; intros.
    - setoid_rewrite Maps.PTree.gempty in H2; inversion H2.
    - destruct H2 as [v' ?].
      inversion H2.
  + auto.
Qed.

Lemma semax_post_ret1: forall P' R' E Delta P v R Pre c,
  ret_type Delta <> Tvoid ->
  ENTAIL (ret1_tycon Delta),
    PROPx P' (LOCALx (temp ret_temp v::nil) (SEPx R')) ⊢ PROPx P (LOCALx (temp ret_temp v::nil) (SEPx R)) ->
  semax E Delta Pre c
    (frame_ret_assert (function_body_ret_assert (ret_type Delta)
      (PROPx P' (LOCALx (temp ret_temp v::nil) (SEPx R')))) emp) ->
  semax E Delta Pre c
    (frame_ret_assert (function_body_ret_assert (ret_type Delta)
      (PROPx P (LOCALx (temp ret_temp v::nil) (SEPx R)))) emp).
Proof.
  intros.
  eapply semax_post, H1; simpl; intros; rewrite ?bi.sep_emp; try solve [rewrite bi.and_elim_r //].
  - destruct (ret_type Delta); [| rewrite bi.and_elim_r //..].
    split => rho; monPred.unseal.
    rewrite -H0; monPred.unseal; done.
  - destruct vl; simpl.
    + split => rho; monPred.unseal.
      rewrite -H0; monPred.unseal.
      iIntros "(% & % & $)"; iPureIntro.
      split; first done; split; last done.
      apply make_args1_tc_environ; auto.
    + destruct (ret_type Delta); [done | rewrite bi.and_elim_r //..].
Qed.

Lemma semax_post_ret0: forall P' R' E Delta P R Pre c,
  ret_type Delta = Tvoid ->
  ENTAIL (ret0_tycon Delta),
    PROPx P' (LOCALx nil (SEPx R')) ⊢ PROPx P (LOCALx nil (SEPx R)) ->
  semax E Delta Pre c
    (frame_ret_assert (function_body_ret_assert (ret_type Delta)
      (PROPx P' (LOCALx nil (SEPx R')))) emp) ->
  semax E Delta Pre c
    (frame_ret_assert (function_body_ret_assert (ret_type Delta)
      (PROPx P (LOCALx nil (SEPx R)))) emp).
Proof.
  intros.
  eapply semax_post, H1; simpl; intros; rewrite ?bi.sep_emp; try solve [rewrite bi.and_elim_r //].
  - destruct (ret_type Delta); [| rewrite bi.and_elim_r //..].
    split => rho; monPred.unseal.
    rewrite -H0; monPred.unseal.
    apply bi.and_mono; last done.
    apply bi.pure_mono; intros.
    apply make_args0_tc_environ; auto.
  - rewrite H; destruct vl; simpl.
    + iIntros "(_ & [] & _)".
    + split => rho; monPred.unseal.
      rewrite -H0; monPred.unseal.
      apply bi.and_mono; last done.
      apply bi.pure_mono; intros.
      apply make_args0_tc_environ; auto.
Qed.

Inductive return_outer_gen: @ret_assert Σ -> ret_assert -> Prop :=
| return_outer_gen_refl: forall P t sf,
    return_outer_gen
      (frame_ret_assert (function_body_ret_assert t P) sf)
      (frame_ret_assert (function_body_ret_assert t P) sf)
| return_outer_gen_switch: forall P Q,
    return_outer_gen P Q ->
    return_outer_gen (switch_ret_assert P) Q
| return_outer_gen_post: forall post P Q,
    return_outer_gen P Q ->
    return_outer_gen (overridePost post P) Q
| return_outer_gen_for: forall P' P Q,
    return_outer_gen P Q ->
    return_outer_gen (for_ret_assert P' P) Q
| return_outer_gen_loop1: forall inv P Q,
    return_outer_gen P Q ->
    return_outer_gen (loop1_ret_assert inv P) Q
| return_outer_gen_loop1x: forall inv P Q,
    return_outer_gen P Q ->
    return_outer_gen (loop1x_ret_assert inv P) Q
| return_outer_gen_loop2: forall inv P Q,
    return_outer_gen P Q ->
    return_outer_gen (loop2_ret_assert inv P) Q.

Lemma return_outer_gen_spec: forall P Q,
  return_outer_gen P Q ->
  RA_return P = RA_return Q.
Proof.
  intros.
  destruct P as [?P ?P ?P ?P]; destruct Q as [?Q ?Q ?Q ?Q].
  induction H; simpl in *; auto; rewrite <- IHreturn_outer_gen;
  destruct P3; auto.
Qed.

Inductive return_inner_gen (S: list mpred): option val -> (assert) -> (assert) -> Prop :=
| return_inner_gen_main: forall ov_gen P u,
    return_inner_gen S ov_gen (main_post P u) (PROPx nil (LOCALx nil (SEPx (True :: S))))
| return_inner_gen_canon_nil':
    forall ov_gen P R,
      return_inner_gen S ov_gen
        (PROPx P (LOCALx nil (SEPx R)))
        (PROPx P (LOCALx nil (SEPx (R ++ S))))
| return_inner_gen_canon_Some':
    forall P v R v_gen,
      return_inner_gen S (Some v_gen)
        (PROPx P (LOCALx (temp ret_temp v :: nil) (SEPx R)))
        (PROPx (P ++ (v_gen = v) :: nil) (LOCALx nil (SEPx (R ++ S))))
| return_inner_gen_EX':
    forall ov_gen (A: Type) (post1 post2: A -> assert),
      (forall a: A, return_inner_gen S ov_gen (post1 a) (post2 a)) ->
      return_inner_gen S ov_gen (∃ x, post1 x) (∃ x, post2 x).

Lemma return_inner_gen_EX: forall S ov_gen A post1 post2,
  (forall a: A, exists P, return_inner_gen S ov_gen (post1 a) P /\ post2 a = P) ->
  return_inner_gen S ov_gen (∃ x, post1 x) (∃ x, post2 x).
Proof.
  intros.
  apply return_inner_gen_EX'.
  intro a; specialize (H a).
  destruct H as [? [? ?]]; subst.
  auto.
Qed.

Lemma return_inner_gen_canon_nil S: forall ov_gen P R Res,
  PROPx P (LOCALx nil (SEPx (VST_floyd_app R S))) = Res ->
  return_inner_gen S ov_gen (PROPx P (LOCALx nil (SEPx R))) Res.
Proof.
  intros.
  subst Res.
  apply return_inner_gen_canon_nil'.
Qed.

Lemma return_inner_gen_canon_Some S: forall P v R v_gen Res,
  PROPx (VST_floyd_app P ((v_gen = v) :: nil)) (LOCALx nil (SEPx (VST_floyd_app R S))) = Res ->
  return_inner_gen S (Some v_gen) (PROPx P (LOCALx (temp ret_temp v :: nil) (SEPx R))) Res.
Proof.
  intros.
  subst Res.
  apply return_inner_gen_canon_Some'.
Qed.

Lemma return_inner_gen_None_spec: forall S post1 post2,
  return_inner_gen S None post1 post2 ->
  post2 ⊢ assert_of (fun rho => post1 (make_args nil nil rho)) ∗ SEPx S.
Proof.
  intros.
  remember None eqn:?H.
  revert H0; induction H; intros; subst.
  + unfold main_post.
    split => rho; rewrite /PROPx /LOCALx /SEPx; monPred.unseal; simpl.
    rewrite !bi.and_elim_r //.
  + rewrite /PROPx /LOCALx /SEPx fold_right_sepcon_app embed_sep.
    split => rho; monPred.unseal.
    iIntros "($ & $ & $ & $)".
  + inversion H0.
  + iIntros "(%a & ?)".
    iDestruct (H0 with "[$]") as "(? & $)"; first done.
    iStopProof; split => rho; monPred.unseal; eauto.
Qed.

Lemma return_inner_gen_Some_spec: forall S v_gen post1 post2,
  v_gen <> Vundef ->
  return_inner_gen S (Some v_gen) post1 post2 ->
  post2 ⊢ assert_of (fun rho => post1 (make_args (ret_temp :: nil) (v_gen :: nil) rho)) ∗ SEPx S.
Proof.
  intros.
  remember (Some v_gen) eqn:?H.
  revert v_gen H H1; induction H0; intros; subst.
  + unfold main_post.
    split => rho; rewrite /PROPx /LOCALx /SEPx; monPred.unseal; simpl.
    rewrite !bi.and_elim_r //.
  + rewrite /PROPx /LOCALx /SEPx fold_right_sepcon_app embed_sep.
    split => rho; monPred.unseal.
    iIntros "($ & $ & $ & $)".
  + erewrite PROPx_Permutation by apply Permutation_app_comm.
    rewrite gather_SEP PROP_LOCAL_sep1; apply bi.sep_mono; last done.
    rewrite /PROPx /LOCALx /SEPx; split => rho; monPred.unseal.
    rewrite fold_right_sepcon_eq.
    iIntros "((% & $) & _ & $ & _)"; inv H1.
    iPureIntro; unfold_lift.
    rewrite eval_id_same //.
  + iIntros "(% & H)".
    rewrite H0 //.
    iDestruct "H" as "(? & $)"; iStopProof; split => rho; monPred.unseal; eauto.
Qed.

Lemma semax_return_None: forall E Delta Ppre Qpre Rpre Post1 sf SEPsf post2 post3,
  ret_type Delta = Tvoid ->
  return_outer_gen Post1 (frame_ret_assert (function_body_ret_assert (ret_type Delta) post2) sf) ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx SEPsf)) ⊢ sf ->
  return_inner_gen SEPsf None post2 post3 ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ⊢ post3 ->
  semax E Delta (PROPx Ppre (LOCALx Qpre (SEPx Rpre))) (Sreturn None) Post1.
Proof.
  intros.
  eapply semax_pre, semax_return.
  apply return_outer_gen_spec in H0.
  rewrite H0; clear Post1 H0.
  apply return_inner_gen_None_spec in H2.
  apply bi.and_intro; auto.
  unfold cast_expropt, id; simpl.
  iIntros "(#? & #? & #? & ?)".
  iPoseProof (H3 with "[-]") as "H".
  { rewrite /PROPx /LOCALx; iFrame; auto. }
  rewrite H2.
  iDestruct "H" as "(? & sf)".
  iPoseProof (H1 with "[sf]") as "sf".
  { rewrite /PROPx /LOCALx; iFrame; auto. }
  rewrite /bind_ret H; unfold_lift.
  iClear "#"; iStopProof; split => rho; monPred.unseal; done.
Qed.

Local Arguments typecheck_expr : simpl never.

Lemma semax_return_Some: forall E Delta Ppre Qpre Rpre Post1 sf SEPsf post2 post3 ret v_gen,
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ⊢ local (`(eq v_gen) (eval_expr (Ecast ret (ret_type Delta)))) ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ⊢ tc_expr Delta (Ecast ret (ret_type Delta)) ->
  return_outer_gen Post1 (frame_ret_assert (function_body_ret_assert (ret_type Delta) post2) sf) ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx SEPsf)) ⊢ sf ->
  return_inner_gen SEPsf (Some v_gen) post2 post3 ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ⊢ post3 ->
  semax E Delta (PROPx Ppre (LOCALx Qpre (SEPx Rpre))) (Sreturn (Some ret)) Post1.
Proof.
  intros.
  eapply semax_pre, semax_return.
  apply return_outer_gen_spec in H1.
  rewrite H1; clear Post1 H1.
  apply bi.and_intro; [exact H0 |].
  eapply bi.pure_elim.
  { rewrite (add_andp _ _ H) (add_andp _ _ H0).
    split => rho; rewrite /local /lift1; monPred.unseal.
    rewrite -!assoc; iIntros "(% & H)".
    setoid_rewrite typecheck_expr_sound; simpl; last done.
    unfold_lift.
    iDestruct "H" as "(? & %Ht & %Hv)"; rewrite -Hv in Ht.
    iPureIntro; exact Ht. }
  intros Ht.
  destruct (Val.eq v_gen Vundef).
  { subst; apply tc_val_Vundef in Ht; done. }
  apply return_inner_gen_Some_spec in H3; [| auto].
  unfold frame_ret_assert, function_body_ret_assert, bind_ret, cast_expropt; simpl.
  iIntros "(#? & #? & #? & ?)".
  iPoseProof (H with "[-]") as "#?".
  { rewrite /PROPx /LOCALx; iFrame; auto. }
  iPoseProof (H4 with "[-]") as "H".
  { rewrite /PROPx /LOCALx; iFrame; auto. }
  rewrite H3.
  iDestruct "H" as "(? & sf)".
  iPoseProof (H2 with "[sf]") as "?".
  { rewrite /PROPx /LOCALx; iFrame; auto. }
  iStopProof; rewrite /local /lift1; split => rho; monPred.unseal. rewrite monPred_at_intuitionistically /=.
  unfold_lift; simpl.
  iIntros "((% & % & % & %) & ? & $)"; subst; iSplit; done.
Qed.

Lemma remove_PROP_LOCAL_left: forall P Q R S, (R ⊢ S) -> PROPx P (LOCALx Q R) ⊢ S.
Proof.
  intros.
  rewrite /PROPx /LOCALx H !bi.and_elim_r //.
Qed.

Lemma remove_PROP_LOCAL_left':
     forall P Q R S, (⎡R⎤ ⊢ S) ->
     PROPx P (LOCALx Q (SEPx (R::nil))) ⊢ S.
Proof.
  intros.
  rewrite /PROPx /LOCALx /SEPx /= bi.sep_emp H !bi.and_elim_r //.
Qed.

Lemma replace_nth_sepcon : forall n R (Rn : mpred), nth_error R n = Some Rn ->
  fold_right_sepcon R = (Rn ∗ fold_right_sepcon (replace_nth n R emp)).
Proof.
  induction n; destruct R; simpl; try done.
  - inversion 1; rewrite emp_sep //.
  - intros; erewrite IHn by done.
    rewrite !sep_assoc (sep_comm m) //.
Qed.

Lemma SEP_nth_isolate {A}:
  forall n R Rn, nth_error R n = Some Rn ->
      @SEPx A Σ R = SEPx (Rn :: replace_nth n R emp).
Proof.
  intros; unfold SEPx.
  f_equiv; simpl.
  apply replace_nth_sepcon; done.
Qed.

Lemma nth_error_SEP_sepcon_TT: forall P Q R n Rn S,
  (PROPx P (LOCALx Q (SEPx (Rn :: nil))) ⊢ S) ->
  nth_error R n = Some Rn ->
  PROPx P (LOCALx Q (SEPx R)) ⊢ S ∗ True.
Proof.
  intros.
  erewrite SEP_nth_isolate by eauto.
  rewrite PROP_LOCAL_sep1 H.
  apply bi.sep_mono; auto.
Qed.

Lemma SEP_replace_nth_isolate {A}:
  forall n R Rn Rn',
       nth_error R n = Some Rn ->
      @SEPx A Σ (replace_nth n R Rn') = SEPx (Rn' :: replace_nth n R emp).
Proof.
  intros; unfold SEPx.
  f_equiv; simpl.
  erewrite replace_nth_sepcon; last by eapply nth_error_replace_nth.
  rewrite replace_nth_replace_nth //.
Qed.

Lemma local_andp_lemma:
  forall P Q, (P ⊢ local Q) -> P ⊣⊢ (@local Σ Q ∧ P).
Proof.
  intros; rewrite comm; apply add_andp; done.
Qed.

Lemma SEP_TT_right {A}:
  forall R, R ⊢ @SEPx A Σ (True::nil).
Proof. intros; rewrite /SEPx /= bi.sep_emp embed_pure; auto. Qed.

Lemma replace_nth_SEP: forall P Q R n Rn Rn', (Rn ⊢ Rn') -> PROPx P (LOCALx Q (SEPx (replace_nth n R Rn))) ⊢ PROPx P (LOCALx Q (SEPx (replace_nth n R Rn'))).
Proof.
  intros.
  apply bi.and_mono; first done.
  apply bi.and_mono; first done.
  rewrite /SEPx; apply embed_mono.
  revert R; induction n; destruct R; simpl; auto.
  - rewrite H //.
  - rewrite IHn //.
Qed.

Lemma replace_nth_SEP':
  forall A P Q R n Rn Rn', (local A ∧ PROPx P (LOCALx Q (SEPx (Rn::nil))) ⊢ ⎡Rn'⎤) ->
  (local A ∧ PROPx P (LOCALx Q (SEPx (replace_nth n R Rn)))) ⊢ (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn')))).
Proof.
  intros.
  iIntros "(#? & #? & #? & H)"; iSplit; first done; iSplit; first done.
  rewrite /SEPx; iInduction n as [|] "IH" forall (R); destruct R; simpl; try done.
  - rewrite !embed_sep.
    iDestruct "H" as "(? & $)".
    iApply H.
    rewrite /SEPx /= bi.sep_emp; iFrame; auto.
  - rewrite !embed_sep.
    iDestruct "H" as "($ & ?)".
    by iApply "IH".
Qed.

Lemma nth_error_SEP_prop:
  forall P Q R n (Rn: mpred) (Rn': Prop),
    nth_error R n = Some Rn ->
    (Rn ⊢ ⌜Rn'⌝) ->
    PROPx P (LOCALx Q (SEPx R)) ⊢ ⌜Rn'⌝.
Proof.
  intros.
  erewrite SEP_nth_isolate by done.
  rewrite /PROPx /LOCALx /SEPx /= embed_sep H0 embed_pure.
  iIntros "(_ & _ & $ & _)".
Qed.

Lemma LOCAL_2_hd: forall P Q R Q1 Q2,
  (PROPx P (LOCALx (Q1 :: Q2 :: Q) (SEPx R))) =
  (PROPx P (LOCALx (Q2 :: Q1 :: Q) (SEPx R))).
Proof.
  intros.
  erewrite LOCALx_Permutation by constructor; done.
Qed.

Lemma lvar_eval_lvar:
  forall i t v rho, locald_denote (lvar i t v) rho -> eval_lvar i t rho = v.
Proof.
unfold eval_lvar; intros. hnf in H.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct H; subst. rewrite eqb_type_refl; auto.
Qed.

Lemma lvar_eval_var:
 forall i t v rho, locald_denote (lvar i t v) rho -> eval_var i t rho = v.
Proof.
intros.
unfold eval_var. hnf in H.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct H; subst. rewrite eqb_type_refl; auto.
Qed.

Lemma gvars_eval_var:
 forall Delta gv i rho t, tc_environ Delta rho -> (var_types Delta) !! i = None -> locald_denote (gvars gv) rho -> eval_var i t rho = gv i.
Proof.
intros.
unfold eval_var. hnf in H1. subst.
 red in H.
destruct_var_types i.
rewrite Heqo0.
auto.
Qed.

Lemma lvar_isptr:
  forall i t v rho, locald_denote (lvar i t v) rho -> isptr v.
Proof.
intros. hnf in H.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct H; subst; apply Coq.Init.Logic.I.
Qed.

Lemma gvars_isptr:
  forall Delta gv i rho t, tc_environ Delta rho -> (glob_types Delta) !! i = Some t -> locald_denote (gvars gv) rho -> isptr (gv i).
Proof.
intros. hnf in H1.
subst.
red in H.
destruct_glob_types i.
rewrite Heqo0.
apply Coq.Init.Logic.I.
Qed.

Lemma lvar_isptr_eval_var :
 forall i t v rho, locald_denote (lvar i t v) rho -> isptr (eval_var i t rho).
Proof.
intros.
erewrite lvar_eval_var; eauto.
eapply lvar_isptr; eauto.
Qed.

Lemma semax_extract_later_prop'':
    forall E (Delta : tycontext) (PP : Prop) P Q R c post P1 P2,
      (P2 ⊢ ⌜PP⌝) ->
      (PP -> semax E Delta (PROPx P (LOCALx Q (SEPx ((P1 ∧ ▷P2) :: R)))) c post) ->
      semax E Delta (PROPx P (LOCALx Q (SEPx ((P1 ∧ ▷P2) :: R)))) c post.
Proof.
  intros.
  erewrite (add_andp P2) by eauto.
  apply semax_pre0 with (P' := ▷⌜PP⌝ ∧ PROPx P (LOCALx Q (SEPx ((P1 ∧ ▷P2) :: R)))).
  { apply bi.and_intro.
    - rewrite /SEPx /= embed_sep embed_and embed_later embed_and embed_pure; iIntros "(_ & _ & (_ & _ & $) & _)".
    - iIntros "(? & ? & H)".
      rewrite /SEPx /=.
      rewrite (bi.and_elim_l P2); iFrame. }
  apply semax_extract_later_prop; auto.
Qed.

Lemma monPred_at_assert_of : forall P, monPred_at (@assert_of Σ P) = P.
Proof.
  reflexivity.
Qed.

Lemma monPred_at_argsassert_of : forall P, monPred_at (@argsassert_of Σ P) = P.
Proof.
  reflexivity.
Qed.

Lemma bind_ret_noret : forall P (R : list mpred), bind_ret None tvoid (PROPx P (LOCALx [] (SEPx R))) = PROPx P (LOCALx [] (SEPx R)).
Proof.
  intros.
  unfold bind_ret; simpl.
  apply assert_ext; intros.
  unfold PROPx, LOCALx, SEPx; monPred.unseal; reflexivity.
Qed.

Lemma bind_ret_exist : forall {A} (P : A -> assert), bind_ret(Σ := Σ) None tvoid (∃ x : A, P x) = ∃ x : A, bind_ret None tvoid (P x).
Proof.
  intros.
  unfold bind_ret; simpl.
  apply assert_ext; intros.
  unfold PROPx, LOCALx, SEPx; monPred.unseal; reflexivity.
Qed.

End mpred.

#[export] Hint Rewrite @insert_local :  norm2.

#[export] Hint Rewrite @fold_right_nil : norm1.
#[export] Hint Rewrite @fold_right_nil : subst.
#[export] Hint Rewrite @fold_right_cons : norm1.
#[export] Hint Rewrite @fold_right_cons : subst.

(*#[export] Hint Rewrite local_unfold : norm2.
#[export] Hint Rewrite lower_sepcon lower_andp : norm2.
#[export] Hint Rewrite lift_prop_unfold: norm2.
#[export] Hint Rewrite andp_unfold: norm2.
#[export] Hint Rewrite refold_andp : norm2.
#[export] Hint Rewrite exp_unfold: norm2.*)

#[export] Hint Resolve PROP_later_derives LOCAL_later_derives SEP_later_derives : derives.
#[export] Hint Rewrite @local_lift0: norm2.
#[export] Hint Rewrite @lower_PROP_LOCAL_SEP : norm2.

Ltac not_conj_notation :=
 match goal with
 | |- not_conj_notation (_ <= _ <= _)%Z => fail 1
 | |- not_conj_notation (_ <= _ < _)%Z => fail 1
 | |- not_conj_notation (_ < _ <= _)%Z => fail 1
 | |- not_conj_notation (_ <= _ <= _)%nat => fail 1
 | |- not_conj_notation (_ <= _ < _)%nat => fail 1
 | |- not_conj_notation (_ < _ <= _)%nat => fail 1
 | |- _ => apply Coq.Init.Logic.I
 end.

#[export] Hint Rewrite @split_first_PROP using not_conj_notation : norm1.

#[export] Hint Extern 1 (isptr (eval_var _ _ _)) => (eapply lvar_isptr_eval_var; eassumption) : norm2.

(* The simpl_nat_of_P tactic is a complete hack,
  needed for compatibility between Coq 8.3/8.4,
  because the name of the thing to unfold varies
  between the two versions *)
Ltac simpl_nat_of_P :=
match goal with |- context [nat_of_P ?n] =>
  match n with xI _ => idtac | xO _ => idtac | xH => idtac | _ => fail end;
  let N := fresh "N" in
  set (N:= nat_of_P n);
  compute in N;
  unfold N; clear N
end.

Ltac grab_indexes_SEP ns :=
  rewrite (grab_indexes_SEP ns);
    unfold grab_indexes; simpl grab_calc;
   unfold grab_indexes', insert;
   repeat simpl_nat_of_P; cbv beta iota;
   unfold Floyd_app; fold @Floyd_app.

Tactic Notation "focus_SEP" constr(a) :=
  grab_indexes_SEP (a::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) :=
  grab_indexes_SEP (a::b::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) :=
  grab_indexes_SEP (a::b::c::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) constr(d) :=
  grab_indexes_SEP (a::b::c::d::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) :=
  grab_indexes_SEP (a::b::c::d::e::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) :=
  grab_indexes_SEP (a::b::c::d::e::f::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) :=
  grab_indexes_SEP (a::b::c::d::e::f::g::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) :=
  grab_indexes_SEP (a::b::c::d::e::f::g::h::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) :=
  grab_indexes_SEP (a::b::c::d::e::f::g::h::i::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) :=
  grab_indexes_SEP (a::b::c::d::e::f::g::h::i::j::nil).

(* TESTING
Variables (a b c d e f g h i j : assert).
Goal (SEP (a;b;c;d;e;f;g;h;i;j) = SEP (b;d;a;c;e;f;g;h;i;j)).
focus_SEP 1 3.
auto.
Qed.
Goal (SEP (a;b;c;d;e;f;g;h;i;j) = SEP (d;b;a;c;e;f;g;h;i;j)).
focus_SEP 3 1.
auto.
Qed.

*)

Ltac go_lowerx' simpl_tac :=
   unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift; split => rho; monPred.unseal; simpl_tac;
   repeat rewrite <- and_assoc;
   repeat ((simple apply go_lower_lem1 || apply bi.pure_elim_l || apply bi.pure_elim_r); intro);
   try apply bi.pure_elim';
   repeat rewrite -> prop_true_andp by assumption;
   try apply entails_refl.

Ltac go_lowerx := go_lowerx' simpl.

Ltac go_lowerx_no_simpl := go_lowerx' idtac.

Ltac find_in_list A L :=
 match L with
  | A :: _ => constr:(O)
  | _ :: ?Y => let n := find_in_list A Y in constr:(S n)
  | nil => fail
  end.

Ltac length_of R :=
 match R with
  |  nil => constr:(O)
  |  _:: ?R1 => let n := length_of R1 in constr:(S n)
 end.

Ltac frame_SEP' L :=  (* this should be generalized to permit framing on LOCAL part too *)
 grab_indexes_SEP L;
 match goal with
 | |- semax _ _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  rewrite <- (Floyd_firstn_skipn (length L) R);
  rewrite (app_nil_r Q);
    simpl length; unfold Floyd_firstn, Floyd_skipn;
    eapply (semax_frame_PQR);
      [ unfold closed_wrt_modvars;  auto 50 with closed
     | ]
 | |- ENTAIL _ , (PROPx _ (LOCALx ?Q (SEPx ?R))) ⊢ _ =>
  rewrite <- (Floyd_firstn_skipn (length L) R);
    simpl length; unfold Floyd_firstn, Floyd_skipn;
    apply derives_frame_PQR
end.

Tactic Notation "frame_SEP" constr(a) :=
  frame_SEP' (a::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) :=
  frame_SEP' (a::b::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) :=
  frame_SEP' (a::b::c::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) constr(d) :=
  frame_SEP' (a::b::c::d::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) :=
  frame_SEP' (a::b::c::d::e::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) :=
  frame_SEP' (a::b::c::d::e::f::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) :=
  frame_SEP' (a::b::c::d::e::f::g::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) :=
  frame_SEP' (a::b::c::d::e::f::g::h::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) :=
  frame_SEP' (a::b::c::d::e::f::g::h::i::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) :=
  frame_SEP' (a::b::c::d::e::f::g::h::i::j::nil).

Ltac gather_SEP' L :=
   grab_indexes_SEP L;
 match goal with |- context [SEPx ?R] =>
    let r := fresh "R" in
    set (r := (SEPx R));
    revert r;
     rewrite <- (Floyd_firstn_skipn (length L) R);
      unfold length at 1 2;
      unfold Floyd_firstn at 1; unfold Floyd_skipn at 1;
      rewrite gather_SEP;
   unfold fold_right at 1; try  rewrite bi.sep_emp;
   try (intro r; unfold r; clear r)
 end.

Tactic Notation "replace_SEP" constr(n) constr(R) :=
  first [apply (replace_SEP' (Z.to_nat n) R) | apply (replace_SEP'' (Z.to_nat n) R)];
  unfold my_nth,replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota.

Tactic Notation "replace_SEP" constr(n) constr(R) "by" tactic1(t):=
  first [apply (replace_SEP' (Z.to_nat n) R) | apply (replace_SEP'' (Z.to_nat n) R)];
  unfold my_nth,replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota; [ now t | ].

Tactic Notation "viewshift_SEP" constr(n) constr(R) :=
  first [apply (replace_SEP'_fupd (Z.to_nat n) R) | apply (replace_SEP''_fupd (Z.to_nat n) R)];
  unfold my_nth,replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota.

Tactic Notation "viewshift_SEP" constr(n) constr(R) "by" tactic1(t):=
  first [apply (replace_SEP'_fupd (Z.to_nat n) R) | apply (replace_SEP''_fupd (Z.to_nat n) R)];
  unfold my_nth,replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota; [ now t | ].

Ltac replace_in_pre S S' :=
 match goal with |- semax _ _ ?P _ _ =>
  match P with context C[S] =>
     let P' := context C[S'] in
      apply semax_pre with P'; [ | ]
  end
 end.

Ltac repeat_extract_exists_pre :=
   first [(apply extract_exists_pre;
             let x := fresh "x" in intro x; normalize;
                repeat_extract_exists_pre;
                revert x)
           | autorewrite with canon
          ].

Ltac extract_exists_in_SEP :=
 match goal with |- semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ bi_exist ?z :: _] =>
        let n := find_in_list (bi_exist z) R
         in rewrite (grab_nth_SEP n); unfold nth, delete_nth; rewrite extract_exists_in_SEP;
             repeat_extract_exists_pre
  end
end.

Ltac flatten_in_SEP PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [(?R1 ∗ ?R2) :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      erewrite(flatten_sepcon_in_SEP'' n' P Q R1 R2 R _ (eq_refl _));
      [ |
        let RR := fresh "RR" in set (RR := R);
        let RR1 := fresh "RR1" in set (RR1 := R1);
        let RR2 := fresh "RR2" in set (RR2 := R2);
        unfold Floyd_firstn, app, Floyd_skipn; subst RR RR1 RR2; cbv beta iota;
        apply eq_refl
      ]
   end
 end.

Ltac flatten_sepcon_in_SEP :=
  match goal with
  | |- semax _ _ ?PQR _ _ => flatten_in_SEP PQR
  | |- ENTAIL _, ?PQR ⊢ _ => flatten_in_SEP PQR
end.

Ltac delete_emp_in_SEP :=
 repeat
 match goal with |- context [SEPx ?R] =>
   match R with context [emp:: ?R'] =>
     rewrite -> (delete_emp_in_SEP (length R - S (length R')) R) by reflexivity;
     simpl length; simpl minus; unfold firstn, app, list_drop; fold app
   end
 end.

Ltac move_from_SEP :=
  (* combines extract_exists_in_SEP, move_prop_from_SEP, (*move_local_from_SEP, *)
                  flatten_sepcon_in_SEP *)
match goal with |- context [PROPx _ (LOCALx _ (SEPx ?R))] =>
  match R with
  | context [(⌜?P1⌝ ∧ ?Rn) :: ?R'] =>
      let n := length_of R in let n' := length_of R' in
        rewrite -> (extract_prop_in_SEP (n-S n')%nat P1 Rn) by reflexivity;
        simpl minus; unfold replace_nth
  | context [ ∃ x, ?z x :: _] =>
        let n := find_in_list (∃ x, z x) R
         in rewrite (grab_nth_SEP n); unfold nth, delete_nth; rewrite extract_exists_in_SEP;
             repeat_extract_exists_pre
  | context [ (?x ∗ ?y) :: ?R'] =>
        let n := length_of R in let n' := length_of R' in
         rewrite (grab_nth_SEP (n-S n')); simpl minus; unfold nth, delete_nth;
         rewrite flatten_sepcon_in_SEP
 end
end.

Tactic Notation "assert_LOCAL" constr(A) :=
  apply (assert_LOCAL A).

Tactic Notation "assert_LOCAL" constr(A) "by" tactic1(t) :=
  apply (assert_LOCAL A); [ now t | ].

Ltac drop_LOCAL n :=
   first [apply (drop_LOCAL n) | apply (drop_LOCAL' n) | apply (drop_LOCAL'' n)];
    unfold delete_nth.

Fixpoint find_LOCAL_index (name: ident) (current: nat) (l : list localdef) : option nat :=
  match l with
  | h :: t => match h with
    | temp  i _   => if (i =? name)%positive then Some current else find_LOCAL_index name (S current) t
    | lvar  i _ _ => if (i =? name)%positive then Some current else find_LOCAL_index name (S current) t
    | gvars _ => find_LOCAL_index name (S current) t
    end
  | nil => None
  end.

Ltac drop_LOCAL_by_name name := match goal with
  | |- semax _ _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let r := eval hnf in (find_LOCAL_index name O Q) in match r with
    | Some ?i => drop_LOCAL i
    | None => fail 1 "No variable named" name "found"
    end
  end.

Ltac drop_LOCALs l := match l with
| ?h :: ?t => drop_LOCAL_by_name h; drop_LOCALs t
| nil => idtac
end.

Ltac clean_up_app_carefully := (* useful after rewriting by SEP_PROP *)
 repeat
  match goal with
  | |- context [@app Prop (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (environ->Prop) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (lifted (LiftEnviron Prop)) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (assert) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (lifted (LiftEnviron mpred)) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app Prop nil ?c] =>
     change (app nil c) with c
  | |- context [@app (environ->Prop) nil ?c] =>
     change (app nil c) with c
  | |- context [@app (lifted (LiftEnviron Prop)) nil ?c] =>
     change (app nil c) with c
  | |- context [@app (lifted (assert)) nil ?c] =>
     change (app nil c) with c
  | |- context [@app (lifted (LiftEnviron mpred)) nil ?c] =>
     change (app nil c) with c
 end.

Tactic Notation "semax_frame" constr(Qframe) constr(Rframe) :=
 first
    [ (*simple*) eapply (semax_frame_perm Qframe Rframe);
          [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
    | eapply semax_post_flipped';
      [(*simple*) eapply (semax_frame_perm Qframe Rframe);
        [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
      | try solve [apply perm_derives; solve_perm]]
  ].

Tactic Notation "semax_frame" "[" "]" constr(Rframe) :=
 first
    [ (*simple*) eapply (semax_frame_perm nil Rframe);
          [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
    | eapply semax_post_flipped';
      [(*simple*) eapply (semax_frame_perm nil Rframe);
        [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
      | try solve [apply perm_derives; solve_perm]]
  ].

Ltac simpl_ret_assert ::=
 cbn [RA_normal RA_break RA_continue RA_return 
      normal_ret_assert overridePost loop1_ret_assert
      loop2_ret_assert function_body_ret_assert frame_ret_assert
      switch_ret_assert loop1x_ret_assert loop1y_ret_assert
      for_ret_assert loop_nocontinue_ret_assert];
  try (match goal with
      | |- context[bind_ret None tvoid ?P] =>
        assert (bind_ret None tvoid P = P) as -> by (repeat (rewrite bind_ret_exist; f_equal; extensionality); apply bind_ret_noret)
      end).
