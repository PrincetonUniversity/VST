Require Export Coq.Sorting.Permutation.
Require Import VST.veric.seplog.
Require Import VST.floyd.base2.
Import LiftNotation.
Import compcert.lib.Maps.

Local Open Scope logic.

Inductive localdef : Type :=
 | temp: ident -> val -> localdef
 | lvar: ident -> type -> val -> localdef   (* local variable *)
 | gvars: globals -> localdef.              (* global variables *)

Arguments temp i%_positive v.

Definition lvar_denote (i: ident) (t: type) (v: val) rho :=
     match Map.get (ve_of rho) i with
         | Some (b, ty') => t=ty' /\ v = Vptr b Ptrofs.zero
         | None => False
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

Definition PROPx {A} (P: list Prop): forall (Q: A->mpred), A->mpred :=
     andp (prop (fold_right and True P)).

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z%assert3) (at level 10) : assert.
Notation "'PROP' ()   z" :=   (PROPx nil z%assert3) (at level 10) : assert.
Notation "'PROP' ( )   z" :=   (PROPx nil z%assert3) (at level 10) : assert.

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z%assert3) (at level 10).
Notation "'PROP' ()   z" :=   (PROPx nil z%assert3) (at level 10).
Notation "'PROP' ( )   z" :=   (PROPx nil z%assert3) (at level 10).

Definition LOCALx (Q: list localdef) : forall (R: environ->mpred), environ->mpred :=
                 andp (local (fold_right (`and) (`True) (map locald_denote Q))).
Notation " 'LOCAL' ( )   z" := (LOCALx nil z%assert5)  (at level 9) : assert3.
Notation " 'LOCAL' ()   z" := (LOCALx nil z%assert5)  (at level 9) : assert3.

Notation " 'LOCAL' ( x ; .. ; y )   z" := (LOCALx (cons x%type .. (cons y%type nil) ..) z%assert5)
         (at level 9) : assert3.


Notation " 'RETURN' () z" := (LOCALx nil z%assert5) (at level 9) : assert3.
Notation " 'RETURN' ( ) z" := (LOCALx nil z%assert5) (at level 9) : assert3.
Notation " 'RETURN' ( x ) z" := (LOCALx (temp ret_temp x :: nil) z%assert5) (at level 9) :assert3.

Definition GLOBALSx (gs : list globals) (X : argsassert): argsassert :=
 fun (gvals : argsEnviron) =>
           LOCALx (map gvars gs)
                  (argsassert2assert nil X)
                  (Clight_seplog.mkEnv (fst gvals) nil nil).
Arguments GLOBALSx gs _ : simpl never.

Definition PARAMSx (vals:list val)(X : argsassert): argsassert :=
 fun (gvals : argsEnviron) => !! (snd gvals = vals) && X gvals.
Arguments PARAMSx vals _ : simpl never.

Notation " 'PARAMS' ( x ; .. ; y )  z" := (PARAMSx (cons x%logic .. (cons y%logic nil) ..) z%assert4)
         (at level 9) : assert3.

Notation " 'PARAMS' ( )  z" := (PARAMSx nil z%assert4) (at level 9) : assert3.
Notation " 'PARAMS' ()  z" := (PARAMSx nil z%assert4) (at level 9) : assert3.

Notation " 'GLOBALS' ( x ; .. ; y )  z" := (GLOBALSx (cons x%logic .. (cons y%logic nil) ..) z%assert5)
         (at level 9) : assert4.

Notation " 'GLOBALS' ( )  z" := (GLOBALSx nil z%assert5) (at level 9) : assert4.
Notation " 'GLOBALS' ()  z" := (GLOBALSx nil z%assert5) (at level 9) : assert4.

Definition SEPx {A} (R: list mpred) : A->mpred :=
    fun _ => (fold_right_sepcon R).
Arguments SEPx A R _ : simpl never.

Notation " 'SEP' ( x ; .. ; y )" := (GLOBALSx nil (SEPx (cons x%logic .. (cons y%logic nil) ..)))
         (at level 8) : assert4.

Notation " 'SEP' ( ) " := (GLOBALSx nil (SEPx nil)) (at level 8) : assert4.
Notation " 'SEP' () " := (GLOBALSx nil (SEPx nil)) (at level 8) : assert4.

Notation " 'SEP' ( x ; .. ; y )" := (SEPx (cons x%logic .. (cons y%logic nil) ..))
         (at level 8) : assert5.

Notation " 'SEP' ( ) " := (SEPx nil) (at level 8) : assert5.
Notation " 'SEP' () " := (SEPx nil) (at level 8) : assert5.

Lemma PROPx_Permutation {A}: forall P Q,
  Permutation P Q ->
  @PROPx A P = PROPx Q.
Proof.
  intros.
  unfold PROPx.
  f_equal.
  apply ND_prop_ext.
  induction H.
  + tauto.
  + simpl; tauto.
  + simpl; tauto.
  + tauto.
Qed.

Lemma LOCALx_Permutation: forall P Q,
  Permutation P Q ->
  LOCALx P = LOCALx Q.
Proof.
  intros.
  unfold LOCALx.
  f_equal.
  unfold local, lift1; unfold_lift.
  extensionality rho.
  apply ND_prop_ext.
  induction H.
  + tauto.
  + simpl; tauto.
  + simpl; tauto.
  + tauto.
Qed.

Lemma SEPx_Permutation {A}: forall P Q,
  Permutation P Q ->
  @SEPx A P = SEPx Q.
Proof.
  intros.
  unfold SEPx.
  extensionality rho.
  induction H.
  + auto.
  + simpl; f_equal; auto.
  + simpl.
    rewrite <- !sepcon_assoc, (sepcon_comm x y).
    auto.
  + congruence.
Qed.

Lemma approx_sepcon: forall (P Q: mpred) n,
  compcert_rmaps.RML.R.approx n (P * Q) =
  compcert_rmaps.RML.R.approx n P *
  compcert_rmaps.RML.R.approx n Q.
Proof.
  intros.
  apply seplog.approx_sepcon.
Qed.

Lemma approx_andp: forall (P Q: mpred) n,
  compcert_rmaps.RML.R.approx n (P && Q) =
  compcert_rmaps.RML.R.approx n P &&
  compcert_rmaps.RML.R.approx n Q.
Proof.
  intros.
  apply approx_andp.
Qed.

Lemma approx_orp: forall (P Q: mpred) n,
  compcert_rmaps.RML.R.approx n (P || Q) =
  compcert_rmaps.RML.R.approx n P ||
  compcert_rmaps.RML.R.approx n Q.
Proof.
  intros.
  apply approx_orp.
Qed.

Lemma approx_exp: forall A (P: A -> mpred) n,
  compcert_rmaps.RML.R.approx n (exp P) =
  EX a: A, compcert_rmaps.RML.R.approx n (P a).
Proof.
  intros.
  apply seplog.approx_exp.
Qed.

Lemma approx_allp: forall A (P: A -> mpred) n,
  A ->
  compcert_rmaps.RML.R.approx n (allp P) =
  ALL a: A, compcert_rmaps.RML.R.approx n (P a).
Proof.
  intros.
  eapply seplog.approx_allp; auto.
Qed.

Lemma approx_jam {B: Type} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l}) (P Q: B -> mpred) n (b : B) :
  compcert_rmaps.RML.R.approx n (res_predicates.jam S P Q b) =
  res_predicates.jam
    S (base.compose (compcert_rmaps.RML.R.approx n) P)
    (base.compose (compcert_rmaps.RML.R.approx n) Q) b.
Proof.
  intros.
  eapply seplog.approx_jam; auto.
Qed.
Opaque rmaps.dependent_type_functor_rec.
(*
Possible ??
 *)

Lemma SEPx_args_super_non_expansive: forall A R ,
  Forall (fun R0 => @args_super_non_expansive A (fun ts a _ => R0 ts a)) R ->
  @args_super_non_expansive A (fun ts a ae => SEPx (map (fun R0 => R0 ts a) R) ae).
Proof.
  intros.
  hnf; intros.
  unfold SEPx.
  induction H.
  + simpl; auto.
  + simpl in *.
    rewrite !approx_sepcon.
    f_equal;
    auto.
Qed.

Lemma SEPx_super_non_expansive: forall A R ,
  Forall (fun R0 => @super_non_expansive A (fun ts a _ => R0 ts a)) R ->
  @super_non_expansive A (fun ts a rho => SEPx (map (fun R0 => R0 ts a) R) rho).
Proof.
  intros.
  hnf; intros.
  unfold SEPx.
  induction H.
  + simpl; auto.
  + simpl in *.
    rewrite !approx_sepcon.
    f_equal;
    auto.
Qed.

Lemma SEPx_super_non_expansive': forall A R,
  @super_non_expansive_list A (fun ts a _ => R ts a) ->
  @super_non_expansive A (fun ts a rho => SEPx (R ts a) rho).
Proof.
  intros.
  hnf; intros.
  unfold SEPx; unfold super_non_expansive_list in H.
  specialize (H n ts x rho).
  induction H.
  + simpl; auto.
  + simpl in *.
    rewrite !approx_sepcon.
    f_equal;
    auto.
Qed.

Lemma LOCALx_super_non_expansive: forall A Q R,
  super_non_expansive R ->
  Forall (fun Q0 => @super_non_expansive A (fun ts a rho => prop (locald_denote (Q0 ts a) rho))) Q ->
  @super_non_expansive A (fun ts a rho => LOCALx (map (fun Q0 => Q0 ts a) Q) (R ts a) rho).
Proof.
  intros.
  hnf; intros.
  unfold LOCALx.
  simpl.
  rewrite !approx_andp.
  f_equal; auto.
  induction H0.
  + auto.
  + simpl.
    unfold local, lift1.
    unfold_lift.
    rewrite !prop_and.
    rewrite !approx_andp.
    f_equal; auto.
Qed.

Lemma PROPx_args_super_non_expansive: forall A P Q,
  args_super_non_expansive Q ->
  Forall (fun P0 => @args_super_non_expansive A (fun ts a ae => prop (P0 ts a))) P ->
  @args_super_non_expansive A (fun ts a ae => PROPx (map (fun P0 => P0 ts a) P) (Q ts a) ae).
Proof.
  intros.
  hnf; intros.
  unfold PROPx.
  simpl.
  rewrite !approx_andp.
  f_equal; auto.
  induction H0.
  + auto.
  + simpl.
    rewrite !prop_and.
    rewrite !approx_andp.
    f_equal; auto.
Qed.

Lemma LOCALx_super_non_expansive': forall A Q R,
  super_non_expansive R ->
  @super_non_expansive_list A (fun ts a rho => map (fun Q0 => prop (locald_denote Q0 rho)) (Q ts a)) ->
  @super_non_expansive A (fun ts a rho => LOCALx (Q ts a) (R ts a) rho).
Proof.
  intros.
  hnf; intros.
  unfold LOCALx.
  simpl.
  rewrite !approx_andp.
  f_equal; auto.
  specialize (H0 n ts x rho).
  simpl in H0.
  match goal with H : Forall2 _ _ (map _ ?l) |- _ => forget l as Q1 end.
  generalize dependent Q1; induction (Q ts x); intros; inv H0; destruct Q1; try discriminate.
  + auto.
  + inv H3.
    simpl.
    unfold local, lift1 in IHl |- *.
    unfold_lift in IHl; unfold_lift.
    rewrite !prop_and.
    rewrite !approx_andp.
    f_equal; auto.
Qed.

Lemma PROPx_super_non_expansive: forall A P Q,
  super_non_expansive Q ->
  Forall (fun P0 => @super_non_expansive A (fun ts a (rho: environ) => prop (P0 ts a))) P ->
  @super_non_expansive A (fun ts a rho => PROPx (map (fun P0 => P0 ts a) P) (Q ts a) rho).
Proof.
  intros.
  hnf; intros.
  unfold PROPx.
  simpl.
  rewrite !approx_andp.
  f_equal; auto.
  induction H0.
  + auto.
  + simpl.
    rewrite !prop_and.
    rewrite !approx_andp.
    f_equal; auto.
Qed.

Lemma PROPx_super_non_expansive': forall A P Q,
  super_non_expansive Q ->
  @super_non_expansive_list A (fun ts a (rho: environ) => map prop (P ts a)) ->
  @super_non_expansive A (fun ts a rho => PROPx (P ts a) (Q ts a) rho).
Proof.
  intros.
  hnf; intros.
  unfold PROPx.
  simpl.
  rewrite !approx_andp.
  f_equal; auto.
  specialize (H0 n ts x rho).
  simpl in H0.
  match goal with H : Forall2 _ _ (map _ ?l) |- _ => forget l as P1 end.
  generalize dependent P1; induction (P ts x); intros; inv H0; destruct P1; try discriminate.
  + auto.
  + inv H3.
    simpl.
    rewrite !prop_and.
    rewrite !approx_andp.
    f_equal; auto.
Qed.

Lemma PROP_LOCAL_SEP_super_non_expansive: forall A P Q R,
  Forall (fun P0 => @super_non_expansive A (fun ts a _ => prop (P0 ts a))) P ->
  Forall (fun Q0 => @super_non_expansive A (fun ts a rho => prop (locald_denote (Q0 ts a) rho))) Q ->
  Forall (fun R0 => @super_non_expansive A (fun ts a _ => R0 ts a)) R ->
  @super_non_expansive A (fun ts a rho =>
     PROPx (map (fun P0 => P0 ts a) P)
      (LOCALx (map (fun Q0 => Q0 ts a) Q)
        (SEPx (map (fun R0 => R0 ts a) R))) rho).
Proof.
  intros.
  apply PROPx_super_non_expansive; auto.
  apply LOCALx_super_non_expansive; auto.
  apply SEPx_super_non_expansive; auto.
Qed.

Lemma PROP_LOCAL_SEP_super_non_expansive': forall A P Q R,
  @super_non_expansive_list A (fun ts a (rho: environ) => map prop (P ts a)) ->
  @super_non_expansive_list A (fun ts a rho => map (fun Q0 => prop (locald_denote Q0 rho)) (Q ts a)) ->
  @super_non_expansive_list A (fun ts a _ => R ts a) ->
  @super_non_expansive A (fun ts a rho =>
     PROPx (P ts a)
      (LOCALx (Q ts a)
        (SEPx (R ts a))) rho).
Proof.
  intros.
  apply PROPx_super_non_expansive'; auto.
  apply LOCALx_super_non_expansive'; auto.
  apply SEPx_super_non_expansive'; auto.
Qed.

Lemma SEPx_nonexpansive {A}: forall R rho,
  Forall (fun R0 => predicates_rec.nonexpansive R0) R ->
  nonexpansive (fun S => @SEPx A (map (fun R0 => R0 S) R) rho).
Proof.
  intros.
  unfold SEPx.
  induction R.
  + simpl.
    apply const_nonexpansive.
  + simpl.
    apply sepcon_nonexpansive.
    - inversion H; auto.
    - apply IHR.
      inversion H; auto.
Qed.

Lemma LOCALx_nonexpansive: forall Q R rho,
  nonexpansive (fun S => R S rho) ->
  nonexpansive (fun S => LOCALx Q (R S) rho).
Proof.
  intros.
  unfold LOCALx.
  apply (conj_nonexpansive (fun S => local (fold_right `(and) `(True) (map locald_denote Q)) rho) (fun S => R S rho)); [| auto].
  apply const_nonexpansive.
Qed.

Lemma PARAMSx_nonexpansive: forall Q R rho,
  nonexpansive (fun S => R S rho) ->
  nonexpansive (fun S => PARAMSx Q (R S) rho).
Proof.
  intros.
  unfold PARAMSx.
  specialize (conj_nonexpansive (fun S => (!! (snd rho = Q)) rho) (fun S => R S rho)).
  intros CN; apply CN; clear CN; trivial.
   red; intros. red; intros. simpl in *; intros. destruct (H0 y H1); clear H0.
   split; trivial.
Qed.

Lemma PROPx_nonexpansive {A}: forall P Q rho,
  Forall (fun P0 => nonexpansive (fun S => prop (P0 S))) P ->
  nonexpansive (fun S => Q S rho) ->
  nonexpansive (fun S => @PROPx A (map (fun P0 => P0 S) P) (Q S) rho).
Proof.
  intros.
  unfold PROPx.
  apply (conj_nonexpansive (fun S => @prop mpred Nveric (fold_right and True
         (map
            (fun P0 : mpred -> Prop
             => P0 S) P))) (fun S => Q S rho)); [| auto].
  clear - H.
  induction P.
  + simpl.
    apply const_nonexpansive.
  + simpl.
    replace
      (fun P0 => (prop (a P0 /\ fold_right and True (map (fun P1 => P1 P0) P)))%logic)
    with
      (fun P0 => (prop (a P0) && prop (fold_right and True (map (fun P1 => P1 P0) P)))%logic).
    2: {
      extensionality S.
      rewrite prop_and; auto.
    }
    apply (conj_nonexpansive (fun S => @prop mpred Nveric (a S)) _).
    - inversion H; auto.
    - apply IHP.
      inversion H; auto.
Qed.

Lemma PROP_LOCAL_SEP_nonexpansive: forall P Q R rho,
  Forall (fun P0 => nonexpansive (fun S => prop (P0 S))) P ->
  Forall (fun R0 => nonexpansive R0) R ->
  nonexpansive (fun S => PROPx (map (fun P0 => P0 S) P) (LOCALx Q (SEPx (map (fun R0 => R0 S) R))) rho).
Proof.
  intros.
  apply PROPx_nonexpansive; auto.
  apply LOCALx_nonexpansive.
  apply SEPx_nonexpansive; auto.
Qed.

Lemma PROP_PARAMS_GLOBALS_SEP_nonexpansive: forall P U Q R rho,
  Forall (fun P0 => nonexpansive (fun S => prop (P0 S))) P ->
  Forall (fun R0 => nonexpansive R0) R ->
  nonexpansive (fun S => PROPx (map (fun P0 => P0 S) P) (PARAMSx U (GLOBALSx Q (SEPx (map (fun R0 => R0 S) R)))) rho).
Proof.
  intros.
  apply PROPx_nonexpansive; auto.
  apply PARAMSx_nonexpansive.
  apply LOCALx_nonexpansive.
  apply SEPx_nonexpansive; auto.
Qed.

Notation "'EX' x .. y , P " :=
  (@exp (environ->mpred) _ _ (fun x =>
    ..
    (@exp (environ->mpred) _ _ (fun y => P%assert))
    ..
    )) (at level 65, x binder, y binder, right associativity) : assert.

Notation " 'ENTAIL' d ',' P '|--' Q " :=
  (@derives (environ->mpred) _ (andp (local (tc_environ d)) P%assert) Q%assert) (at level 99, P at level 79, Q at level 79).

Arguments semax {CS} {Espec} Delta Pre%_assert cmd Post%_assert.

Lemma insert_prop : forall (P: Prop) PP QR, prop P && (PROPx PP QR) = PROPx (P::PP) QR.
Proof.
intros. unfold PROPx. simpl. extensionality rho.
apply pred_ext. apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
apply andp_right; auto. apply prop_right; auto.
apply derives_extract_prop; intros [? ?].
repeat apply andp_right; auto. apply prop_right; auto. apply prop_right; auto.
Qed.

Lemma insert_local': forall (Q1: localdef) P Q R,
  local (locald_denote Q1) && (PROPx P (LOCALx Q R)) = (PROPx P (LOCALx (Q1 :: Q) R)).
Proof.
intros. extensionality rho.
unfold PROPx, LOCALx, local; super_unfold_lift. simpl.
apply pred_ext; gather_prop; normalize.
repeat apply andp_right; auto.
apply prop_right; repeat split; auto.
apply andp_right; auto.
apply prop_right; repeat split; auto.
Qed.

Lemma insert_local: forall Q1 P Q R,
  local (locald_denote Q1) && (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx (Q1 :: Q) (SEPx R))).
Proof. intros. apply insert_local'. Qed.

#[export] Hint Rewrite insert_local :  norm2.

Lemma go_lower_lem20:
  forall QR QR',
    (QR |-- QR') ->
    PROPx nil QR |-- QR'.
Proof. unfold PROPx; intros; intro rho; normalize. Qed.

Ltac go_lowerx' simpl_tac :=
   unfold PROPx, LOCALx,SEPx, local, lift1; unfold_lift; intro rho; simpl_tac;
   repeat rewrite andp_assoc;
   repeat ((simple apply go_lower_lem1 || apply derives_extract_prop || apply derives_extract_prop'); intro);
   try apply prop_left;
   repeat rewrite prop_true_andp by assumption;
   try apply derives_refl.

Ltac go_lowerx := go_lowerx' simpl.

Ltac go_lowerx_no_simpl := go_lowerx' idtac.

Lemma grab_nth_SEP:
   forall n P Q R,
    PROPx P (LOCALx Q (SEPx R)) = (PROPx P (LOCALx Q (SEPx (nth n R emp :: delete_nth n R)))).
Proof.
intros.
f_equal. f_equal.
extensionality rho; unfold SEPx.
revert R; induction n; intros; destruct R.
simpl. rewrite sepcon_emp; auto.
simpl nth.
unfold delete_nth.
auto.
simpl.
rewrite sepcon_emp; auto.
simpl.
rewrite IHn.
simpl.
repeat rewrite <- sepcon_assoc.
f_equal.
apply sepcon_comm.
Qed.

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
#[export] Hint Rewrite @fold_right_nil : norm1.
#[export] Hint Rewrite @fold_right_nil : subst.

Lemma fold_right_cons: forall {A B} (f: A -> B -> B) (z: B) x y,
   fold_right f z (x::y) = f x (fold_right f z y).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @fold_right_cons : norm1.
#[export] Hint Rewrite @fold_right_cons : subst.

Lemma fold_right_and_app:
  forall (Q1 Q2: list (environ -> Prop)) rho,
   fold_right `(and) `(True) (Q1 ++ Q2) rho =
   (fold_right `(and) `(True) Q1 rho /\  fold_right `(and) `(True) Q2 rho).
Proof.
intros.
induction Q1; simpl; auto.
apply prop_ext; intuition.
unfold_lift in IHQ1. unfold_lift.
rewrite IHQ1.
clear; apply prop_ext; tauto.
Qed.

Lemma fold_right_sepcon_app :
 forall P Q, fold_right_sepcon (P++Q) =
        fold_right_sepcon P * fold_right_sepcon Q.
Proof.
intros; induction P; simpl.
rewrite emp_sepcon; auto.
rewrite sepcon_assoc;
f_equal; auto.
Qed.

Lemma grab_indexes_SEP {A}:
  forall (ns: list Z) xs, @SEPx A xs = SEPx (grab_indexes ns xs).
Proof.
intros.
unfold SEPx; extensionality rho.
unfold grab_indexes. change @Floyd_app with  @app.
forget (grab_calc 0 ns nil) as ks.
revert xs; induction ks; intro.
unfold grab_indexes'. simpl app. auto.
destruct a.
destruct xs. reflexivity.
unfold grab_indexes'.
fold @grab_indexes'.
simpl fold_right_sepcon.
specialize (IHks xs).
case_eq (grab_indexes' ks xs); intros.
rewrite H in IHks.
rewrite fold_right_sepcon_app.
rewrite IHks.
rewrite fold_right_sepcon_app.
forget (fold_right_sepcon l0) as P.
rewrite <- sepcon_assoc. f_equal.
clear.
revert l; induction n; intro l. reflexivity.
simpl. destruct l. simpl. auto.
simpl. rewrite <- sepcon_assoc. rewrite (sepcon_comm m).
rewrite sepcon_assoc. f_equal.
specialize (IHn l). simpl in IHn.
auto.
destruct xs. reflexivity.
unfold grab_indexes'.
fold @grab_indexes'.
simpl.
specialize (IHks xs).
case_eq (grab_indexes' ks xs); intros.
rewrite H in IHks.
simpl.
simpl in IHks; rewrite IHks.
clear.
induction l; simpl; auto.
rewrite <- IHl.
clear IHl.
repeat rewrite <- sepcon_assoc.
f_equal.
rewrite sepcon_comm; auto.
Qed.

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

(*
Lemma semax_post0:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   (R' |-- R) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
intros. apply andp_left2; auto.
apply H.
Qed.
*)

Lemma local_unfold: forall P rho, local P rho = !! (P rho).
Proof. reflexivity. Qed.
#[export] Hint Rewrite local_unfold : norm2.

Lemma lower_sepcon:
  forall P Q rho, @sepcon (environ->mpred) _ _ P Q rho = sepcon (P rho) (Q rho).
Proof. reflexivity. Qed.
Lemma lower_andp:
  forall P Q rho, @andp (environ->mpred) _ P Q rho = andp (P rho) (Q rho).
Proof. reflexivity. Qed.
#[export] Hint Rewrite lower_sepcon lower_andp : norm2.

Lemma lift_prop_unfold:
   forall P z,  @prop (environ->mpred) _ P z = @prop mpred Nveric P.
Proof.  reflexivity. Qed.
#[export] Hint Rewrite lift_prop_unfold: norm2.

Lemma andp_unfold: forall (P Q: environ->mpred) rho,
  @andp (environ->mpred) _ P Q rho = @andp mpred Nveric (P rho) (Q rho).
Proof. reflexivity. Qed.
#[export] Hint Rewrite andp_unfold: norm2.

Lemma refold_andp:
  forall (P Q: environ -> mpred),
     (fun rho: environ => P rho && Q rho) = (P && Q).
Proof. reflexivity. Qed.
#[export] Hint Rewrite refold_andp : norm2.

Lemma exp_unfold : forall A P rho,
 @exp (environ->mpred) _ A P rho = @exp mpred Nveric A (fun x => P x rho).
Proof.
intros. reflexivity.
Qed.
#[export] Hint Rewrite exp_unfold: norm2.

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

Lemma extract_exists_pre_later {CS: compspecs} {Espec: OracleKind}:
  forall  (A : Type) (Q: assert) (P : A -> assert) c Delta (R: ret_assert),
  (forall x, semax Delta (Q && |> P x) c R) ->
  semax Delta (Q && |> exp P) c R.
Proof.
  intros.
  apply extract_exists_pre in H.
  eapply semax_conseq; [.. | exact H].
  + reduceL.
    eapply derives_trans, except_0_fupd.
    eapply derives_trans; [apply andp_derives, later_exp''; apply derives_refl|].
    rewrite andp_comm, distrib_orp_andp.
    apply orp_left.
    - apply orp_right2.
      eapply derives_trans, fupd_intro.
      rewrite <- exp_andp2, andp_comm; apply derives_refl.
    - apply orp_right1, andp_left1, derives_refl.
  + reduce2derives; apply derives_refl.
  + reduce2derives; apply derives_refl.
  + reduce2derives; apply derives_refl.
  + intros; reduce2derives; apply derives_refl.
Qed.

Lemma semax_pre_post_fupd:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- (|={Ensembles.Full_set}=> P')) ->
    (local (tc_environ Delta) && RA_normal R' |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
    (local (tc_environ Delta) && RA_break R' |-- (|={Ensembles.Full_set}=> RA_break R)) ->
    (local (tc_environ Delta) && RA_continue R' |-- (|={Ensembles.Full_set}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- (RA_return R vl)) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Proof. exact @CConseqFacts.semax_pre_post_fupd. Qed.

Lemma semax_pre_fupd:
 forall P' Espec {cs: compspecs} Delta P c R,
     ENTAIL Delta , P |-- (|={Ensembles.Full_set}=> P') ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof. exact @CConseqFacts.semax_pre_fupd. Qed.

Lemma semax_pre:
 forall P' Espec {cs: compspecs} Delta P c R,
     ENTAIL Delta , P |-- P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof. intros ? ? ?; apply ConseqFacts.semax_pre. Qed.

Lemma semax_pre_simple:
 forall P' Espec {cs: compspecs} Delta P c R,
     ENTAIL Delta , P |-- P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof. exact semax_pre. Qed.

Lemma semax_pre0:
 forall P' Espec  {cs: compspecs} Delta P c R,
     (P |-- P') ->
     @semax cs Espec Delta P' c R  ->
     @semax cs Espec Delta P c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
 apply andp_left2; auto.
Qed.

Lemma semax_pre_post : forall {Espec: OracleKind}{CS: compspecs},
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
    (local (tc_environ Delta) && RA_normal R' |-- RA_normal R) ->
    (local (tc_environ Delta) && RA_break R' |-- RA_break R) ->
    (local (tc_environ Delta) && RA_continue R' |-- RA_continue R) ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Proof.
  intros; eapply semax_pre_post_fupd; eauto; intros; eapply derives_trans, fupd_intro; auto.
Qed.

Lemma semax_frame_PQR:
  forall Q2 R2 Espec {cs: compspecs} Delta R1 P Q P' Q' R1' c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R1')))) ->
     @semax cs Espec Delta (PROPx P (LOCALx (Q++Q2) (SEPx (R1++R2)))) c
                     (normal_ret_assert (PROPx P' (LOCALx (Q'++Q2) (SEPx (R1'++R2))))).
Proof.
intros.
replace (PROPx P (LOCALx (Q++Q2) (SEPx (R1 ++ R2))))
   with (PROPx P (LOCALx Q (SEPx (R1))) * (LOCALx Q2 (SEPx R2))).
eapply semax_pre_post; try (apply semax_frame; try eassumption).
apply andp_left2; auto.
apply andp_left2. intro rho; simpl; normalize.
 unfold PROPx, SEPx, LOCALx, local, lift1.
normalize.
rewrite fold_right_sepcon_app.
normalize; autorewrite with norm1 norm2; normalize.
rewrite prop_true_andp; auto.
rewrite map_app. rewrite fold_right_and_app; split; auto.
apply andp_left2; simpl; normalize.
apply andp_left2; simpl; normalize.
intro; apply andp_left2; simpl; normalize.
clear.
extensionality rho.
simpl.
unfold PROPx, LOCALx, local, lift1, SEPx.
rewrite fold_right_sepcon_app.
simpl. normalize.
f_equal.
rewrite map_app. rewrite fold_right_and_app.
apply pred_ext; normalize.
Qed.

Lemma semax_frame1:
 forall {Espec: OracleKind} {cs: compspecs} QFrame Frame Delta Delta1
     P Q c R P1 Q1 R1 P2 Q2 R2,
    semax Delta1 (PROPx P1 (LOCALx Q1 (SEPx R1))) c
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    Delta1 = Delta ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    PROPx P1 (LOCALx (Q1++QFrame) (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c (LOCALx QFrame (SEPx Frame)) ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) c
                      (normal_ret_assert (PROPx P2 (LOCALx (Q2++QFrame) (SEPx (R2++Frame))))).
Proof.
intros. subst.
eapply semax_pre.
apply H1.
apply semax_frame_PQR; auto.
Qed.

Lemma semax_post_fupd:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   ENTAIL Delta, RA_normal R' |-- (|={Ensembles.Full_set}=> RA_normal R) ->
   ENTAIL Delta, RA_break R' |-- (|={Ensembles.Full_set}=> RA_break R) ->
   ENTAIL Delta, RA_continue R' |-- (|={Ensembles.Full_set}=> RA_continue R) ->
   (forall vl, ENTAIL Delta, RA_return R' vl |-- (RA_return R vl)) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post_fupd; try eassumption.
apply andp_left2, fupd_intro; auto.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   ENTAIL Delta, RA_normal R' |-- RA_normal R ->
   ENTAIL Delta, RA_break R' |-- RA_break R ->
   ENTAIL Delta, RA_continue R' |-- RA_continue R ->
   (forall vl, ENTAIL Delta, RA_return R' vl |-- RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
Qed.

Lemma semax_post_flipped:
  forall (R' : ret_assert) Espec {cs: compspecs} (Delta : tycontext) (R : ret_assert)
         (P : environ->mpred) (c : statement),
   @semax cs Espec Delta P c R' ->
   ENTAIL Delta, RA_normal R' |-- RA_normal R ->
   ENTAIL Delta, RA_break R' |-- RA_break R ->
   ENTAIL Delta, RA_continue R' |-- RA_continue R ->
   (forall vl, ENTAIL Delta, RA_return R' vl |-- RA_return R vl) ->
       @semax cs Espec Delta P c R.
Proof. intros; eapply semax_post; eassumption. Qed.


Lemma semax_post': forall R' Espec {cs: compspecs} Delta R P c,
           ENTAIL Delta, R' |-- R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros. eapply semax_post; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_pre_post': forall P' R' Espec {cs: compspecs} Delta R P c,
      ENTAIL Delta, P |-- P' ->
      ENTAIL Delta, R' |-- R ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros.
 eapply semax_pre; eauto.
 eapply semax_post'; eauto.
Qed.

Lemma sequential:
  forall Espec {cs: compspecs} Delta P c Q,
        @semax cs Espec Delta P c (normal_ret_assert (RA_normal Q)) ->
          @semax cs Espec Delta P c Q.
intros.
 destruct Q as [?Q ?Q ?Q ?Q].
 eapply semax_post; eauto; intros; apply andp_left2; simpl; auto; normalize.
Qed.

Lemma sequential':
    forall Q Espec {cs: compspecs} Delta P c R,
               @semax cs Espec Delta P c (normal_ret_assert Q) ->
               @semax cs Espec Delta P c (overridePost Q R).
Proof.
intros.
apply semax_post with (normal_ret_assert Q); auto; simpl; intros;
 apply andp_left2; simpl; normalize.
destruct R; simpl; auto.
Qed.

Lemma semax_seq':
 forall Espec {cs: compspecs} Delta P c1 P' c2 Q,
         @semax cs Espec Delta P c1 (normal_ret_assert P') ->
         @semax cs Espec Delta P' c2 Q ->
         @semax cs Espec Delta P (Ssequence c1 c2) Q.
Proof.
 intros. apply semax_seq with P'; auto.
 apply sequential'. auto.
Qed.

Lemma semax_frame_seq:
 forall {Espec: OracleKind} {cs: compspecs} QFrame Frame Delta
     P Q c1 c2 R P1 Q1 R1 P2 Q2 R2 R3,
    semax Delta (PROPx P1 (LOCALx Q1 (SEPx R1))) c1
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
    PROPx P1 (LOCALx (Q1++QFrame) (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c1 (LOCALx QFrame (SEPx Frame)) ->
    semax Delta
         (PROPx P2 (LOCALx (Q2++QFrame) (SEPx (R2 ++ Frame)))) c2 R3 ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) (Ssequence c1 c2) R3.
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
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R1)) |-- PROPx P' (LOCALx Q' (SEPx R1')) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx (R1++R2))) |-- PROPx P' (LOCALx Q' (SEPx (R1'++R2))).
Proof.
intros.
eapply derives_trans; [ | eapply derives_trans].
2: apply sepcon_derives; [ apply H | apply (derives_refl  (fun _ => (fold_right sepcon emp R2)))].
unfold PROPx, LOCALx, SEPx, local; super_unfold_lift; intros.
rewrite fold_right_sepcon_app.
intro rho; simpl; normalize.
apply andp_right; auto.
apply prop_right; auto.
apply derives_refl.
unfold PROPx, LOCALx, SEPx, local; super_unfold_lift; intros.
rewrite fold_right_sepcon_app.
intro rho; simpl; normalize.
apply andp_right; auto.
apply prop_right; auto.
apply derives_refl.
Qed.

Ltac frame_SEP' L :=  (* this should be generalized to permit framing on LOCAL part too *)
 grab_indexes_SEP L;
 match goal with
 | |- @semax _ _ _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  rewrite <- (Floyd_firstn_skipn (length L) R);
  rewrite (app_nil_r Q);
    simpl length; unfold Floyd_firstn, Floyd_skipn;
    eapply (semax_frame_PQR);
      [ unfold closed_wrt_modvars;  auto 50 with closed
     | ]
 | |- ENTAIL _ , (PROPx _ (LOCALx ?Q (SEPx ?R))) |-- _ =>
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

Lemma gather_SEP {A}:
  forall R1 R2,
    @SEPx A (R1 ++ R2) = SEPx (fold_right sepcon emp R1 :: R2).
Proof.
intros.
unfold SEPx.
extensionality rho.
induction R1; simpl. rewrite emp_sepcon; auto.
rewrite sepcon_assoc; f_equal; auto.
Qed.

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
   unfold fold_right at 1; try  rewrite sepcon_emp;
   try (intro r; unfold r; clear r)
 end.

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
    rewrite (IHn R) at 1; simpl; [reflexivity|exact H1].
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

Lemma replace_SEP':
 forall n R' Espec {cs: compspecs} Delta P Q Rs c Post,
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (my_nth n Rs TT ::  nil))) |-- `R' ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (replace_nth n Rs R')))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx Rs))) c Post.
Proof.
intros.
eapply semax_pre; [ | apply H0].
clear - H.
unfold PROPx, LOCALx, SEPx in *; intro rho; specialize (H rho).
unfold local, lift1 in *.
simpl in *; unfold_lift; unfold_lift in H.
normalize.
rewrite !prop_true_andp in H by auto.
rewrite sepcon_emp in H.
apply andp_right; auto.
apply prop_right; auto.
revert Rs H; induction n; destruct Rs; simpl ; intros; auto;
apply sepcon_derives; auto.
Qed.

Lemma replace_SEP'':
 forall n R' Delta P Q Rs Post,
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (my_nth n Rs TT ::  nil))) |-- `R' ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (replace_nth n Rs R'))) |-- Post ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx Rs)) |-- Post.
Proof.
intros.
eapply derives_trans; [ | apply H0].
clear - H.
unfold PROPx, LOCALx, SEPx in *; intro rho; specialize (H rho).
unfold local, lift1 in *.
simpl in *; unfold_lift; unfold_lift in H.
normalize.
rewrite !prop_true_andp in H by auto.
rewrite sepcon_emp in H.
apply andp_right; auto.
apply prop_right; auto.
revert Rs H; induction n; destruct Rs; simpl ; intros; auto;
apply sepcon_derives; auto.
Qed.

Tactic Notation "replace_SEP" constr(n) constr(R) :=
  first [apply (replace_SEP' (Z.to_nat n) R) | apply (replace_SEP'' (Z.to_nat n) R)];
  unfold my_nth,replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota.

Tactic Notation "replace_SEP" constr(n) constr(R) "by" tactic1(t):=
  first [apply (replace_SEP' (Z.to_nat n) R) | apply (replace_SEP'' (Z.to_nat n) R)];
  unfold my_nth,replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota; [ now t | ].

Lemma replace_SEP'_fupd:
 forall n R' Espec {cs: compspecs} Delta P Q Rs c Post,
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (my_nth n Rs TT ::  nil))) |-- `(|={Ensembles.Full_set}=> R') ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (replace_nth n Rs R')))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx Rs))) c Post.
Proof.
intros.
eapply semax_pre_fupd; [ | apply H0].
clear - H.
unfold PROPx, LOCALx, SEPx in *; intro rho; specialize (H rho).
unfold local, lift1 in *.
simpl in *; unfold_lift; unfold_lift in H.
normalize.
rewrite !prop_true_andp in H by auto.
rewrite sepcon_emp in H.
rewrite prop_true_andp by auto.
change fupd with (ghost_seplog.fupd Ensembles.Full_set Ensembles.Full_set).
revert Rs H; induction n; destruct Rs; intros; auto; try solve [apply fupd_intro; auto].
- eapply derives_trans, fupd_frame_r; apply sepcon_derives; auto.
- eapply derives_trans, fupd_frame_l; apply sepcon_derives; auto.
Qed.

Lemma replace_SEP''_fupd:
 forall n R' Delta P Q Rs Post,
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (my_nth n Rs TT ::  nil))) |-- `(|={Ensembles.Full_set}=> R') ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx (replace_nth n Rs R'))) |-- (|={Ensembles.Full_set}=> Post) ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx Rs)) |-- (|={Ensembles.Full_set}=> Post).
Proof.
intros.
eapply derives_trans, fupd_trans.
eapply derives_trans; [ | apply fupd_mono, H0].
clear - H.
unfold PROPx, LOCALx, SEPx in *; intro rho; specialize (H rho).
unfold local, lift1 in *.
simpl in *; unfold_lift; unfold_lift in H.
normalize.
rewrite !prop_true_andp in H by auto.
rewrite sepcon_emp in H.
rewrite !prop_true_andp by auto.
change fupd with (ghost_seplog.fupd Ensembles.Full_set Ensembles.Full_set).
revert Rs H; induction n; destruct Rs; intros; auto; try solve [apply fupd_intro; auto].
- eapply derives_trans, fupd_frame_r; apply sepcon_derives; auto.
- eapply derives_trans, fupd_frame_l; apply sepcon_derives; auto.
Qed.

Tactic Notation "viewshift_SEP" constr(n) constr(R) :=
  first [apply (replace_SEP'_fupd (Z.to_nat n) R) | apply (replace_SEP''_fupd (Z.to_nat n) R)];
  unfold my_nth,replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota.

Tactic Notation "viewshift_SEP" constr(n) constr(R) "by" tactic1(t):=
  first [apply (replace_SEP'_fupd (Z.to_nat n) R) | apply (replace_SEP''_fupd (Z.to_nat n) R)];
  unfold my_nth,replace_nth; simpl Z.to_nat;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota; [ now t | ].

Ltac replace_in_pre S S' :=
 match goal with |- @semax _ _ _ ?P _ _ =>
  match P with context C[S] =>
     let P' := context C[S'] in
      apply semax_pre with P'; [ | ]
  end
 end.

Lemma semax_extract_PROP_True:
  forall Espec {cs: compspecs} Delta (PP: Prop) P QR c Post,
        PP ->
        @semax cs Espec Delta (PROPx P QR) c Post ->
       @semax cs Espec Delta (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply semax_pre_simple with (PROPx P QR); auto.
clear.
intro rho; unfold PROPx in *; simpl. normalize.
autorewrite with norm1 norm2; normalize.
Qed.

Lemma semax_extract_PROP:
  forall Espec {cs: compspecs} Delta (PP: Prop) P QR c Post,
       (PP -> @semax cs Espec Delta (PROPx P QR) c Post) ->
       @semax cs Espec Delta (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply semax_pre_simple with (!!PP && PROPx P QR).
intro rho; unfold PROPx in *; simpl; normalize.
autorewrite with norm1 norm2; normalize.
apply andp_right; auto.
apply prop_right; auto.
apply semax_extract_prop.
auto.
Qed.

Lemma PROP_later_derives:
 forall P QR QR', (QR |-- |>QR') ->
    PROPx P QR |-- |> PROPx P QR'.
Proof.
intros.
unfold PROPx.
normalize.
Qed.

Lemma LOCAL_later_derives:
 forall Q R R', (R |-- |>R') -> LOCALx Q R |-- |> LOCALx Q R'.
Proof.
unfold LOCALx; intros; normalize.
rewrite later_andp.
apply andp_derives; auto.
apply now_later.
Qed.

Lemma SEP_later_derives:
  forall P Q P' Q',
      (P |-- |> P') ->
      (SEPx Q |-- |> SEPx Q') ->
      SEPx (P::Q) |-- |> SEPx (P'::Q').
Proof.
unfold SEPx.
intros.
intro rho.
specialize (H0 rho).
intros; normalize.
simpl.
rewrite later_sepcon.
apply sepcon_derives; auto.
Qed.
#[export] Hint Resolve PROP_later_derives LOCAL_later_derives SEP_later_derives : derives.

Lemma local_lift0: forall P, local (lift0 P) = prop P.
Proof.
intros. extensionality rho. reflexivity.
Qed.
#[export] Hint Rewrite @local_lift0: norm2.

Lemma extract_exists_post:
  forall {Espec: OracleKind} {cs: compspecs} {A: Type} (x: A) Delta
       (P: environ -> mpred) c (R: A -> environ -> mpred),
  semax Delta P c (normal_ret_assert (R x)) ->
  semax Delta P c (normal_ret_assert (exp R)).
Proof.
intros.
eapply semax_pre_post; try apply H;
intros; apply andp_left2; auto; try apply derives_refl.
apply exp_right with x; normalize; apply derives_refl.
Qed.

Ltac repeat_extract_exists_pre :=
   first [(apply extract_exists_pre;
             let x := fresh "x" in intro x; normalize;
                repeat_extract_exists_pre;
                revert x)
           | autorewrite with canon
          ].

Lemma extract_exists_in_SEP:
  forall {A} (R1: A -> mpred) P Q R,
    PROPx P (LOCALx Q (SEPx (exp R1 :: R))) =
    (EX x:A, PROPx P (LOCALx Q (SEPx (R1 x::R))))%assert.
Proof.
intros.
extensionality rho.
unfold PROPx, LOCALx, SEPx; simpl.
normalize.
Qed.

Ltac extract_exists_in_SEP :=
 match goal with |- @semax _ _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ exp ?z :: _] =>
        let n := find_in_list (exp z) R
         in rewrite (grab_nth_SEP n); unfold nth, delete_nth; rewrite extract_exists_in_SEP;
             repeat_extract_exists_pre
  end
end.

Lemma flatten_sepcon_in_SEP:
  forall P Q R1 R2 R,
           PROPx P (LOCALx Q (SEPx ((R1*R2) :: R))) =
           PROPx P (LOCALx Q (SEPx (R1 :: R2 :: R))).
Proof.
intros.
f_equal. f_equal. extensionality rho.
unfold SEPx.
simpl. rewrite sepcon_assoc. auto.
Qed.

Lemma flatten_sepcon_in_SEP'':
  forall n P Q (R1 R2: mpred) (R: list mpred) R',
   nth_error R n = Some ((R1 * R2)) ->
   R' = Floyd_firstn n R ++ R1 :: R2 :: Floyd_skipn (S n) R ->
   PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
f_equal.
f_equal.
unfold SEPx.
extensionality rho.
subst R'.
revert R H.
clear.
induction n; destruct R; intros.
inv H.
simpl nth_error in H. inv H.
unfold Floyd_firstn, Floyd_skipn, app.
simpl.
repeat rewrite <- sepcon_assoc.
reflexivity.
inv H.
specialize (IHn _ H). clear H.
simpl Floyd_firstn.
change (m :: Floyd_firstn n R) with (app (m::nil) (Floyd_firstn n R)).
rewrite <- app_assoc. unfold app at 1.
simpl.
f_equal.
auto.
Qed.

Ltac flatten_in_SEP PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [(?R1 * ?R2) :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      erewrite(@flatten_sepcon_in_SEP'' n' P Q R1 R2 R _ (eq_refl _));
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
  | |- semax _ ?PQR _ _ => flatten_in_SEP PQR
  | |-  ENTAIL _, ?PQR |-- _ => flatten_in_SEP PQR
end.

Lemma semax_ff:
  forall Espec {cs: compspecs} Delta c R,
   @semax cs Espec Delta FF c R.
Proof.
intros.
apply semax_pre with (FF && FF).
apply andp_left2. apply andp_right; auto.
apply semax_extract_prop. intros; contradiction.
Qed.

Lemma extract_prop_in_SEP:
  forall n P1 Rn P Q R,
   nth n R emp = prop P1 && Rn ->
   PROPx P (LOCALx Q (SEPx R)) = PROPx (P1::P) (LOCALx Q (SEPx (replace_nth n R Rn))).
Proof.
intros.
extensionality rho.
unfold PROPx,LOCALx,SEPx,local,lift1.
simpl.
apply pred_ext; normalize.
* match goal with |- _ |-- !! ?PP && _ => replace PP with P1
   by (apply prop_ext; tauto)
  end.
  clear - H.
  revert R H; induction n; destruct R; simpl; intros.
  apply andp_right; auto.
  rewrite H; apply andp_left1; auto.
  rewrite H.
  normalize.
  apply andp_right; auto.
  rewrite H; apply andp_left1; auto.
  rewrite <- sepcon_andp_prop.
  apply sepcon_derives; auto.
*
  rewrite prop_true_andp by auto.
 clear - H H0.
  revert R H; induction n; destruct R; simpl; intros; auto.
  subst m. rewrite prop_true_andp; auto.
  apply sepcon_derives; auto.
Qed.

Lemma insert_SEP:
 forall R1 P Q R, `R1 * PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q (SEPx (R1::R))).
Proof.
intros.
unfold PROPx,LOCALx,SEPx,local,lift1.
extensionality rho; simpl.
repeat rewrite sepcon_andp_prop. f_equal; auto.
Qed.

Lemma delete_emp_in_SEP {A}:
  forall n (R: list mpred),
    nth_error R n = Some emp ->
    @SEPx A R = SEPx (firstn n R ++ list_drop (S n) R).
Proof.
intros.
unfold SEPx; extensionality rho.
revert R H; induction n; destruct R; simpl; intros; auto.
inv H. rewrite emp_sepcon; auto.
f_equal.
etransitivity.
apply IHn; auto.
reflexivity.
Qed.

Ltac delete_emp_in_SEP :=
 repeat
 match goal with |- context [SEPx ?R] =>
   match R with context [emp:: ?R'] =>
     rewrite (delete_emp_in_SEP (length R - S (length R')) R) by reflexivity;
     simpl length; simpl minus; unfold firstn, app, list_drop; fold app
   end
 end.

Ltac move_from_SEP :=
  (* combines extract_exists_in_SEP, move_prop_from_SEP, (*move_local_from_SEP, *)
                  flatten_sepcon_in_SEP *)
match goal with |- context [PROPx _ (LOCALx _ (SEPx ?R))] =>
  match R with
  | context [(prop ?P1 && ?Rn) :: ?R'] =>
      let n := length_of R in let n' := length_of R' in
        rewrite (extract_prop_in_SEP (n-S n')%nat P1 Rn) by reflexivity;
        simpl minus; unfold replace_nth
  | context [ exp ?z :: _] =>
        let n := find_in_list (exp z) R
         in rewrite (grab_nth_SEP n); unfold nth, delete_nth; rewrite extract_exists_in_SEP;
             repeat_extract_exists_pre
  | context [ (sepcon ?x  ?y) :: ?R'] =>
        let n := length_of R in let n' := length_of R' in
         rewrite (grab_nth_SEP (n-S n')); simpl minus; unfold nth, delete_nth;
         rewrite flatten_sepcon_in_SEP
 end
end.

Lemma nth_error_local:
  forall n Delta P Q R (Qn: localdef),
    nth_error Q n = Some Qn ->
    ENTAIL Delta, PROPx P (LOCALx Q R) |-- local (locald_denote Qn).
Proof.
intros.
apply andp_left2. apply andp_left2. apply andp_left1.
go_lowerx. normalize.
revert Q H H0; induction n; destruct Q; intros; inv H.
destruct H0; auto.
destruct H0. apply (IHn Q); auto.
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
   ENTAIL Delta, PROPx P (LOCALx Q R) |-- local (locald_denote Q0).
Proof.
  intros.
  destruct (in_nth_error _ _ H) as [?n ?H].
  eapply nth_error_local.
  eauto.
Qed.

Lemma lower_PROP_LOCAL_SEP:
  forall P Q R rho, PROPx P (LOCALx Q (SEPx R)) rho =
     (!!fold_right and True P && (local (fold_right (`and) (`True) (map locald_denote Q)) && `(fold_right sepcon emp R))) rho.
Proof. reflexivity. Qed.
#[export] Hint Rewrite lower_PROP_LOCAL_SEP : norm2.

Lemma lower_TT: forall rho, @TT (environ->mpred) _ rho = @TT mpred Nveric.
Proof. reflexivity. Qed.
#[export] Hint Rewrite lower_TT : norm2.

Lemma lower_FF: forall rho, @FF (environ->mpred) _ rho = @FF mpred Nveric.
Proof. reflexivity. Qed.
#[export] Hint Rewrite lower_FF : norm2.

Lemma assert_PROP:
 forall P1 Espec {cs: compspecs} Delta PQR c Post,
    ENTAIL Delta, PQR |-- !! P1 ->
   (P1 -> @semax cs Espec Delta PQR c Post) ->
   @semax cs Espec Delta PQR c Post.
Proof.
intros.
eapply semax_pre.
apply andp_right.
apply H.
apply andp_left2; apply derives_refl.
apply semax_extract_prop.
auto.
Qed.

Lemma semax_extract_later_prop1:
  forall {cs: compspecs} {Espec: OracleKind} Delta (PP: Prop) P c Q,
           (PP -> semax Delta (|> P) c Q) ->
           semax Delta (|> (!!PP && P)) c Q.
Proof.
  intros.
  rewrite later_andp.
  apply semax_extract_later_prop; auto.
Qed.

Lemma assert_later_PROP:
 forall P1 Espec {cs: compspecs} Delta PQR c Post,
    ENTAIL Delta, PQR|-- !! P1 ->
   (P1 -> @semax cs Espec Delta (|> PQR) c Post) ->
   @semax cs Espec Delta (|> PQR) c Post.
Proof.
intros.
eapply semax_pre_simple.
apply later_left2.
apply andp_right.
apply H.
apply andp_left2; apply derives_refl.
apply semax_extract_later_prop1.
auto.
Qed.

Lemma assert_PROP' {A}{NA: NatDed A}:
 forall P Pre (Post: A),
   (Pre |-- !! P) ->
   (P -> Pre |-- Post) ->
   Pre |-- Post.
Proof.
intros.
apply derives_trans with (!!P && Pre).
apply andp_right; auto.
apply derives_extract_prop. auto.
Qed.

Lemma assert_later_PROP':
 forall P1 Espec {cs: compspecs} Delta PQR PQR' c Post,
    ENTAIL Delta, PQR' |-- !! P1 ->
    (PQR |-- |> PQR') ->
   (P1 -> @semax cs Espec Delta PQR c Post) ->
   @semax cs Espec Delta PQR c Post.
Proof.
intros.
apply semax_extract_later_prop in H1.
eapply semax_pre_simple, H1.
apply andp_right.
+ eapply derives_trans, later_derives, H.
  rewrite later_andp; apply andp_derives; auto.
  apply now_later.
+ apply andp_left2; trivial.
Qed.

Lemma assert_LOCAL:
 forall Q1 Espec {cs: compspecs} Delta P Q R c Post,
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (locald_denote Q1) ->
   @semax cs Espec Delta (PROPx P (LOCALx (Q1::Q) (SEPx R))) c Post ->
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; try apply H0.
rewrite <- (insert_local Q1); apply andp_right; auto.
apply andp_left2; auto.
Qed.

Tactic Notation "assert_LOCAL" constr(A) :=
  apply (assert_LOCAL A).

Tactic Notation "assert_LOCAL" constr(A) "by" tactic1(t) :=
  apply (assert_LOCAL A); [ now t | ].

Lemma drop_LOCAL'':
  forall (n: nat)  P Q R Post,
   (PROPx P (LOCALx (delete_nth n Q) (SEPx R)) |-- Post) ->
   PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
intros.
eapply derives_trans; try apply H.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. apply prop_derives; simpl.
clear.
revert Q; induction n; destruct Q; simpl; intros; intuition.
Qed.

Lemma drop_LOCAL':
  forall (n: nat)  Delta P Q R Post,
   ENTAIL Delta, PROPx P (LOCALx (delete_nth n Q) (SEPx R)) |-- Post ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
intros.
eapply derives_trans; try apply H.
apply andp_derives; auto.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. apply prop_derives; simpl.
clear.
revert Q; induction n; destruct Q; simpl; intros; intuition.
Qed.

Lemma drop_LOCAL:
  forall (n: nat) Espec {cs: compspecs} Delta P Q R c Post,
   @semax cs Espec Delta (PROPx P (LOCALx (delete_nth n Q) (SEPx R))) c Post ->
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; try apply H.
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. apply prop_derives; simpl.
clear.
revert Q; induction n; destruct Q; simpl; intros; intuition.
Qed.

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
  | |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
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
  | |- context [@app (environ->mpred) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (lifted (LiftEnviron mpred)) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app Prop nil ?c] =>
     change (app nil c) with c
  | |- context [@app (environ->Prop) nil ?c] =>
     change (app nil c) with c
  | |- context [@app (lifted (LiftEnviron Prop)) nil ?c] =>
     change (app nil c) with c
  | |- context [@app (lifted (environ->mpred)) nil ?c] =>
     change (app nil c) with c
  | |- context [@app (lifted (LiftEnviron mpred)) nil ?c] =>
     change (app nil c) with c
 end.

Definition not_conj_notation (P: Prop) := True.

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

Lemma split_first_PROP {A}:
  forall P Q R S,
  not_conj_notation (P/\Q) ->
  @PROPx A ((P/\Q)::R) S = PROPx (P::Q::R) S.
Proof.
intros. unfold PROPx; simpl.
extensionality rho.
apply pred_ext; apply andp_derives; auto;
  apply prop_derives; tauto.
Qed.
#[export] Hint Rewrite @split_first_PROP using not_conj_notation : norm1.

Lemma perm_derives:
  forall Delta P Q R P' Q' R',
    Permutation P P' ->
    Permutation Q Q' ->
    Permutation R R' ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- PROPx P' (LOCALx Q' (SEPx R')).
Proof.
  intros.
  erewrite PROPx_Permutation by eauto.
  erewrite LOCALx_Permutation by eauto.
  erewrite SEPx_Permutation by eauto.
  apply andp_left2; auto.
Qed.

Lemma semax_frame_perm:
forall (Qframe : list localdef)
         (Rframe : list mpred)
         (Espec : OracleKind) {cs: compspecs}
         (Delta : tycontext)
         (P : list Prop) (Q : list localdef) (c : statement)
         (R : list mpred)
         (Q1 : list localdef) (R1 : list mpred)
         (P2 : list Prop) (Q2 : list localdef)
         (R2 : list mpred),
       closed_wrt_modvars c (LOCALx Qframe (SEPx Rframe)) ->
       Permutation (Qframe ++ Q1) Q ->
       Permutation (Rframe ++ R1)  R ->
       semax Delta (PROPx P (LOCALx Q1 (SEPx R1))) c
         (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
       semax Delta (PROPx P (LOCALx Q (SEPx R))) c
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
   forall (R': environ->mpred) Espec {cs: compspecs} (Delta: tycontext) (R P: environ->mpred) c,
       @semax cs Espec Delta P c (normal_ret_assert R') ->
       ENTAIL Delta, R' |-- R ->
       @semax cs Espec Delta P c (normal_ret_assert R).
 Proof. intros; eapply semax_post_flipped; [ eassumption | .. ];
 auto;
 intros; apply andp_left2; simpl; normalize.
Qed.

Tactic Notation "semax_frame" constr(Qframe) constr(Rframe) :=
 first
    [ simple eapply (semax_frame_perm Qframe Rframe);
          [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
    | eapply semax_post_flipped';
      [simple eapply (semax_frame_perm Qframe Rframe);
        [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
      | try solve [apply perm_derives; solve_perm]]
  ].

Tactic Notation "semax_frame" "[" "]" constr(Rframe) :=
 first
    [ simple eapply (semax_frame_perm nil Rframe);
          [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
    | eapply semax_post_flipped';
      [simple eapply (semax_frame_perm nil Rframe);
        [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
      | try solve [apply perm_derives; solve_perm]]
  ].


Lemma semax_pre_later:
 forall P' Espec {cs: compspecs} Delta P1 P2 P3 c R,
     ENTAIL Delta, PROPx P1 (LOCALx P2 (SEPx P3)) |-- P' ->
     @semax cs Espec Delta (|> P') c R  ->
     @semax cs Espec Delta (|> (PROPx P1 (LOCALx P2 (SEPx P3)))) c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
eapply derives_trans; [ | apply later_derives; apply H ].
eapply derives_trans.
2: apply later_derives; apply derives_refl.
rewrite later_andp; apply andp_derives; auto; apply now_later.
Qed.

Lemma PROP_LOCAL_SEP_cons: forall P1 P2 P3 F,
  PROPx P1 (LOCALx P2 (SEPx (F :: P3))) =
  `F * PROPx P1 (LOCALx P2 (SEPx P3)).
Proof.
  intros.
  change (SEPx (F :: P3)) with (`F * SEPx P3).
  unfold PROPx, LOCALx.
  unfold_lift; extensionality rho.
  unfold local, lift1.
  simpl.
  apply pred_ext.
  + normalize.
    apply andp_right; auto.
    apply prop_right; auto.
  + normalize.
    apply andp_right; auto.
    apply prop_right; auto.
Qed.

Lemma semax_frame': forall {Espec: OracleKind}{CS: compspecs},
  forall Delta P1 P2 P3 s Q1 Q2 Q3 F,
  @semax CS Espec Delta
    (PROPx P1 (LOCALx P2 (SEPx P3))) s
      (normal_ret_assert (PROPx Q1 (LOCALx Q2 (SEPx Q3)))) ->
  @semax CS Espec Delta
    (PROPx P1 (LOCALx P2 (SEPx (F :: P3)))) s
      (normal_ret_assert (PROPx Q1 (LOCALx Q2 (SEPx (F :: Q3))))).
Proof.
  intros.
  rewrite !PROP_LOCAL_SEP_cons.
  replace (normal_ret_assert (` F * PROPx Q1 (LOCALx Q2 (SEPx Q3))))
    with (frame_ret_assert (normal_ret_assert (PROPx Q1 (LOCALx Q2 (SEPx Q3)))) (`F)).
  + rewrite sepcon_comm.
    apply semax_frame; auto.
    hnf. intros; auto.
  +
    rewrite frame_normal. f_equal. apply sepcon_comm.
Qed.

Lemma semax_frame'': forall {Espec: OracleKind}{CS: compspecs},
  forall Delta P1 P2 P3 s t Q1 Q2 Q3 F,
  @semax CS Espec Delta
    (PROPx P1 (LOCALx P2 (SEPx P3))) s
      (frame_ret_assert
        (function_body_ret_assert t (PROPx Q1 (LOCALx Q2 (SEPx Q3)))) emp) ->
  @semax CS Espec Delta
    (PROPx P1 (LOCALx P2 (SEPx (F :: P3)))) s
      (frame_ret_assert
        (function_body_ret_assert t (PROPx Q1 (LOCALx Q2 (SEPx (F :: Q3))))) emp).
Proof.
  intros.
  rewrite !PROP_LOCAL_SEP_cons.
  replace (frame_ret_assert (function_body_ret_assert t (` F * PROPx Q1 (LOCALx Q2 (SEPx Q3)))) emp)
    with (frame_ret_assert (frame_ret_assert (function_body_ret_assert t (PROPx Q1 (LOCALx Q2 (SEPx Q3)))) emp) (`F)).
  + rewrite sepcon_comm.
    apply semax_frame; auto.
    hnf. intros; auto.
  +
    simpl. f_equal; extensionality; try extensionality; normalize.
    rewrite sepcon_comm.
    unfold bind_ret; unfold_lift;
    destruct x; simpl; normalize.
    destruct t; simpl; normalize.
    unfold bind_ret. destruct x;
    unfold_lift; simpl; normalize.
    rewrite sepcon_comm; auto.
    destruct t; simpl; normalize.
    apply sepcon_comm.
Qed.

Definition is_void_type (ty: type) : bool :=
 match ty with Tvoid => true | _ => false end.

Definition ret_tycon (Delta: tycontext): tycontext :=
  mk_tycontext
    (if is_void_type (ret_type Delta)
      then (PTree.empty _)
      else (PTree.set ret_temp (ret_type Delta) (PTree.empty _)))
     (PTree.empty _)
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
  hnf; intros. rewrite PTree.gempty in H3; inv H3.
  simpl.
  clear - H1.
  unfold ret_tycon, var_types.
  hnf; intros. rewrite PTree.gempty.
  split; intro. inv H. destruct H as [v ?].
   unfold ve_of, globals_only, Map.get, Map.empty in H. inv H.
Qed.


Lemma semax_post'': forall R' Espec {cs: compspecs} Delta R P c t,
           t = ret_type Delta ->
           ENTAIL ret_tycon Delta, R' |-- R ->
      @semax cs Espec Delta P c (frame_ret_assert (function_body_ret_assert t R') emp) ->
      @semax cs Espec Delta P c (frame_ret_assert (function_body_ret_assert t R) emp).
Proof. intros. eapply semax_post; eauto. subst t. clear - H0. rename H0 into H.
  intros.
  all: try solve [intro rho; simpl; normalize].
  simpl RA_normal.
  destruct (ret_type Delta) eqn:?H; normalize.
  simpl; intro rho; unfold_lift.
  rewrite !sepcon_emp.
  unfold local, lift1.
  normalize.
  pose proof (tc_environ_Tvoid _ _ H1 H0).
  eapply derives_trans; [ | apply H]. clear H.
  simpl.
  normalize. apply andp_right; auto.
  apply prop_right. auto.
  intro vl.
  intro rho; simpl in H0|-*; normalize.
  clear H1.
  unfold local, lift1 in *. normalize.
  subst t. rename H0 into H. rename H1 into H0.
  assert (H8: typecheck_var_environ (ve_of (globals_only rho))
               (var_types (ret_tycon Delta))). {
   clear - H0.
  unfold ret_tycon, var_types.
  hnf; intros. rewrite PTree.gempty.
  split; intro. inv H. destruct H as [v ?].
   unfold ve_of, globals_only, Map.get, Map.empty in H. inv H.
 }
  unfold bind_ret.
  destruct vl; autorewrite with norm1 norm2; normalize.
-
  unfold_lift.  unfold make_args.
  specialize (H (env_set (globals_only rho) ret_temp v)).
  simpl in H.
  rewrite prop_true_andp in H. auto.
  clear H.
  destruct H0 as [? [? ?]]; split3; auto.
  + unfold te_of, env_set.
    unfold temp_types, ret_tycon.
    hnf; intros.
    destruct (is_void_type (ret_type Delta)).
    * rewrite PTree.gempty in H3; inv H3.
    * destruct (ident_eq id ret_temp).
      2: rewrite PTree.gso in H3 by auto; rewrite PTree.gempty in H3; inv H3.
      subst id. rewrite PTree.gss in H3. inv H3.
      rewrite Map.gss. exists v. split; auto.
      apply tc_val_tc_val'; auto.
-
  destruct (ret_type Delta) eqn:?; auto.
  unfold_lift. simpl.
  specialize (H (globals_only rho)).
  simpl in H. rewrite prop_true_andp in H; auto.
  apply tc_environ_Tvoid; auto.
Qed.

Definition ret0_tycon (Delta: tycontext): tycontext :=
  mk_tycontext (PTree.empty _) (PTree.empty _) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta).

Definition ret1_tycon (Delta: tycontext): tycontext :=
  mk_tycontext (PTree.set ret_temp (ret_type Delta) (PTree.empty _))
    (PTree.empty _) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta).

Lemma make_args0_tc_environ: forall rho Delta,
  tc_environ Delta rho ->
  tc_environ (ret0_tycon Delta) (make_args nil nil rho).
Proof.
  intros.
  destruct H as [? [? ?]].
  split; [| split]; simpl.
  + hnf; intros.
    rewrite PTree.gempty in H2; inversion H2.
  + hnf; split; intros.
    - rewrite PTree.gempty in H2; inversion H2.
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
    rewrite PTree.gsspec in H2.
    destruct (peq id ret_temp).
    - subst.
      inversion H2; subst.
      exists v; simpl.
      split; auto.
      apply tc_val_tc_val'; auto.
    - rewrite PTree.gempty in H2; inversion H2.
  + hnf; split; intros.
    - rewrite PTree.gempty in H2; inversion H2.
    - destruct H2 as [v' ?].
      inversion H2.
  + auto.
Qed.

Lemma semax_post_ret1: forall P' R' Espec {cs: compspecs} Delta P v R Pre c,
  ret_type Delta <> Tvoid ->
  ENTAIL (ret1_tycon Delta),
    PROPx P' (LOCALx (temp ret_temp v::nil) (SEPx R')) |-- PROPx P (LOCALx (temp ret_temp v::nil) (SEPx R)) ->
  @semax cs Espec Delta Pre c
    (frame_ret_assert (function_body_ret_assert (ret_type Delta)
      (PROPx P' (LOCALx (temp ret_temp v::nil) (SEPx R')))) emp) ->
  @semax cs Espec Delta Pre c
    (frame_ret_assert (function_body_ret_assert (ret_type Delta)
      (PROPx P (LOCALx (temp ret_temp v::nil) (SEPx R)))) emp).
Proof.
  intros.
  eapply semax_post; eauto; try solve [intro rho; simpl; normalize].
  simpl RA_normal.
  destruct (ret_type Delta); try congruence; normalize.
  intros vl rho; simpl. unfold local, lift1.
  simpl; rewrite !sepcon_emp.
  unfold bind_ret; unfold_lift; destruct vl; [| destruct (ret_type Delta) eqn:?H]; simpl; normalize ; try congruence.
  eapply derives_trans; [| apply (H0 _)].
    Opaque PTree.set. simpl; apply andp_right; auto. Transparent PTree.set.
    apply prop_right.
    apply make_args1_tc_environ; auto.
Qed.

Lemma semax_post_ret0: forall P' R' Espec {cs: compspecs} Delta P R Pre c,
  ret_type Delta = Tvoid ->
  ENTAIL (ret0_tycon Delta),
    PROPx P' (LOCALx nil (SEPx R')) |-- PROPx P (LOCALx nil (SEPx R)) ->
  @semax cs Espec Delta Pre c
    (frame_ret_assert (function_body_ret_assert (ret_type Delta)
      (PROPx P' (LOCALx nil (SEPx R')))) emp) ->
  @semax cs Espec Delta Pre c
    (frame_ret_assert (function_body_ret_assert (ret_type Delta)
      (PROPx P (LOCALx nil (SEPx R)))) emp).
Proof.
  intros.
  eapply semax_post; eauto; try solve [intro rho; simpl; normalize].
  intros.
  intro rho; unfold frame_ret_assert, function_body_ret_assert; normalize.
  simpl; rewrite ?sepcon_emp. unfold local, lift1.
  rewrite H.
  unfold_lift.
  normalize.
  eapply derives_trans; [ | apply H0].
  simpl.
  apply andp_right; auto.
  apply prop_right.
    apply make_args0_tc_environ; auto.
  unfold bind_ret; unfold_lift; destruct vl; [| destruct (ret_type Delta) eqn:?H]; simpl; normalize.
  + rewrite H in H2.
    inversion H2.
  + intro rho.
      unfold_lift; simpl.
     eapply derives_trans; [| apply (H0 _)].
     simpl.
     apply andp_derives; auto.
    apply prop_derives; intros.
    apply make_args0_tc_environ; auto.
Qed.

Inductive return_outer_gen: ret_assert -> ret_assert -> Prop :=
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

Inductive return_inner_gen (S: list mpred): option val -> (environ -> mpred) -> (environ -> mpred) -> Prop :=
| return_inner_gen_main: forall ov_gen P u,
    return_inner_gen S ov_gen (main_post P u) (PROPx nil (LOCALx nil (SEPx (TT :: S))))
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
    forall ov_gen (A: Type) (post1 post2: A -> environ -> mpred),
      (forall a: A, return_inner_gen S ov_gen (post1 a) (post2 a)) ->
      return_inner_gen S ov_gen (exp post1) (exp post2).

Lemma return_inner_gen_EX: forall S ov_gen A post1 post2,
  (forall a: A, exists P, return_inner_gen S ov_gen (post1 a) P /\ post2 a = P) ->
  return_inner_gen S ov_gen (exp post1) (exp post2).
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
  post2 |-- (fun rho => post1 (make_args nil nil rho)) * SEPx S.
Proof.
  intros.
  remember None eqn:?H.
  revert H0; induction H; intros; subst.
  + unfold main_post.
    go_lowerx.
  + rewrite gather_SEP.
    go_lowerx.
  + inversion H0.
  + apply exp_left; intro a.
    apply (derives_trans _ _ _ (H0 a eq_refl)).
    intro rho.
    simpl.
    apply sepcon_derives; auto.
    apply (exp_right a); auto.
Qed.

Lemma return_inner_gen_Some_spec: forall S v_gen post1 post2,
  v_gen <> Vundef ->
  return_inner_gen S (Some v_gen) post1 post2 ->
  post2 |-- (fun rho => post1 (make_args (ret_temp :: nil) (v_gen :: nil) rho)) * SEPx S.
Proof.
  intros.
  remember (Some v_gen) eqn:?H.
  revert v_gen H H1; induction H0; intros; subst.
  + unfold main_post.
    go_lowerx.
  + rewrite gather_SEP.
    go_lowerx.
  + erewrite PROPx_Permutation by apply Permutation_app_comm.
    rewrite gather_SEP.
    go_lowerx.
    unfold_lift.
    apply sepcon_derives; auto.
    apply andp_right; auto.
    apply prop_right; split; auto.
    subst.
    inversion H1.
    unfold globals_only, eval_id, env_set, te_of.
    rewrite Map.gss; auto.
    apply derives_refl.
  + apply exp_left; intro a.
    apply (derives_trans _ _ _ (H0 a _ H1 eq_refl)).
    intro rho.
    simpl.
    apply sepcon_derives; auto.
    apply (exp_right a); auto.
Qed.

Lemma semax_return_None: forall {cs Espec} Delta Ppre Qpre Rpre Post1 sf SEPsf post2 post3,
  ret_type Delta = Tvoid ->
  return_outer_gen Post1 (frame_ret_assert (function_body_ret_assert (ret_type Delta) post2) sf) ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx SEPsf)) |-- sf ->
  return_inner_gen SEPsf None post2 post3 ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre)) |-- post3 ->
  @semax cs Espec Delta (PROPx Ppre (LOCALx Qpre (SEPx Rpre))) (Sreturn None) Post1.
Proof.
  intros.
  eapply semax_pre; [| apply semax_return].
  apply return_outer_gen_spec in H0.
  rewrite H0; clear Post1 H0.
  apply return_inner_gen_None_spec in H2.
  apply andp_right.
  + unfold tc_expropt.
    unfold_lift; intros rho; apply prop_right; auto.
  + unfold cast_expropt, id.
    apply (derives_trans _ _ _ H3) in H2; clear H3.
    revert H1 H2; unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift.
    simpl; intros ? ? rho.
    specialize (H1 rho); specialize (H2 rho).
    normalize.
    normalize in H1.
    normalize in H2.
    eapply derives_trans; [exact H2 |].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply H1] |].
    unfold frame_ret_assert, function_body_ret_assert, bind_ret, make_args.
    rewrite H.
    unfold_lift; simpl.
    auto.
Qed.

Lemma semax_return_Some: forall {cs Espec} Delta Ppre Qpre Rpre Post1 sf SEPsf post2 post3 ret v_gen,
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre)) |-- local (`(eq v_gen) (eval_expr (Ecast ret (ret_type Delta)))) ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre)) |-- tc_expr Delta (Ecast ret (ret_type Delta)) ->
  return_outer_gen Post1 (frame_ret_assert (function_body_ret_assert (ret_type Delta) post2) sf) ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx SEPsf)) |-- sf ->
  return_inner_gen SEPsf (Some v_gen) post2 post3 ->
  ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre)) |-- post3 ->
  @semax cs Espec Delta (PROPx Ppre (LOCALx Qpre (SEPx Rpre))) (Sreturn (Some ret)) Post1.
Proof.
  intros.
  eapply semax_pre; [| apply semax_return].
  apply return_outer_gen_spec in H1.
  rewrite H1; clear Post1 H1.
  apply andp_right; [exact H0 |].
  destruct (Val.eq v_gen Vundef).
  {
    subst.
    rewrite (add_andp _ _ H), (add_andp _ _ H0).
    rewrite (andp_comm _ (PROPx _ _)), !andp_assoc.
    apply andp_left2.
    go_lowerx.
    eapply derives_trans; [apply typecheck_expr_sound; auto |].
    simpl.
    rewrite <- H5.
    apply (derives_trans _ FF); [| normalize].
    apply prop_derives.
    apply tc_val_Vundef.
  }
  apply return_inner_gen_Some_spec in H3; [| auto].
  assert (ENTAIL Delta, PROPx Ppre (LOCALx Qpre (SEPx Rpre))
            |-- ` (RA_return (frame_ret_assert (function_body_ret_assert (ret_type Delta) post2) sf) (Some v_gen)) id).
  + unfold frame_ret_assert, function_body_ret_assert, bind_ret, cast_expropt.
    apply (derives_trans _ _ _ H4) in H3; clear H4.
    revert H H0 H2 H3.
    unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift.
    simpl; intros ? ? ? ? rho.
    specialize (H rho); specialize (H0 rho).
    specialize (H2 rho); specialize (H3 rho).
    normalize.
    normalize in H.
    normalize in H0.
    normalize in H2.
    normalize in H3.
    rewrite (add_andp _ _ H); normalize; clear H.
    apply andp_right.
    - apply (derives_trans _ _ _ H0).
      eapply derives_trans; [apply typecheck_expr_sound; auto |].
      unfold_lift; apply derives_refl.
    - apply (derives_trans _ _ _ H3).
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply H2] |].
      apply derives_refl.
  + rewrite (add_andp _ _ H1), (add_andp _ _ H).
    rewrite (andp_comm _ (PROPx _ _)), !andp_assoc.
    apply andp_left2.
    go_lowerx.
    subst.
    unfold id.
    normalize.
Qed.

Lemma remove_PROP_LOCAL_left: forall P Q R S, (R |-- S) -> PROPx P (LOCALx Q R) |-- S.
Proof.
  intros.
  go_lowerx.
  normalize.
Qed.

Lemma remove_PROP_LOCAL_left':
     forall P Q R S, (`R |-- S) ->
     PROPx P (LOCALx Q (SEPx (R::nil))) |-- S.
Proof.
  intros.
  go_lowerx.
  normalize. apply H.
Qed.

Lemma SEP_nth_isolate {A}:
  forall n R Rn, nth_error R n = Some Rn ->
      @SEPx A R = SEPx (Rn :: replace_nth n R emp).
Proof.
 unfold SEPx.
 intros. extensionality rho.
 revert R H;
 induction n; destruct R; intros; inv H.
 simpl; rewrite emp_sepcon; auto.
 unfold replace_nth; fold @replace_nth.
 transitivity (m * fold_right_sepcon R).
 reflexivity.
 rewrite (IHn R H1).
 simpl.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm Rn).
 simpl.
 repeat rewrite sepcon_assoc.
 f_equal. rewrite sepcon_comm; reflexivity.
Qed.

Lemma nth_error_SEP_sepcon_TT: forall P Q R n Rn S,
  (PROPx P (LOCALx Q (SEPx (Rn :: nil))) |-- S) ->
  nth_error R n = Some Rn ->
  PROPx P (LOCALx Q (SEPx R)) |-- S * TT.
Proof.
  intros.
  erewrite SEP_nth_isolate by eauto.
  unfold PROPx, LOCALx, SEPx in *.
  unfold local, lift1 in H |- *.
  unfold_lift in H.
  unfold_lift.
  simpl in H |- *.
  intros rho.
  specialize (H rho).
  rewrite <- !andp_assoc in H |- *.
  rewrite <- !prop_and in H |- *.
  rewrite sepcon_emp in H.
  rewrite <- sepcon_andp_prop'.
  apply sepcon_derives.
  exact H.
  apply prop_right.
  auto.
Qed.

Lemma SEP_replace_nth_isolate {A}:
  forall n R Rn Rn',
       nth_error R n = Some Rn ->
      @SEPx A (replace_nth n R Rn') = SEPx (Rn' :: replace_nth n R emp).
Proof.
 unfold SEPx.
 intros.
 extensionality rho.
 revert R H.
 induction n; destruct R; intros; inv H; intros.
 simpl; rewrite emp_sepcon; auto.
 unfold replace_nth; fold @replace_nth.
 transitivity (m * fold_right_sepcon (replace_nth n R Rn')).
 reflexivity.
 rewrite (IHn R H1). clear IHn.
 simpl.
 repeat rewrite <- sepcon_assoc.
 rewrite (sepcon_comm Rn').
 rewrite sepcon_assoc.
 reflexivity.
Qed.

Lemma local_andp_lemma:
  forall P Q, (P |-- local Q) -> P = local Q && P.
Proof.
intros.
apply pred_ext.
apply andp_right; auto.
apply andp_left2; auto.
Qed.

Lemma SEP_TT_right:
  forall R, R |-- SEPx(TT::nil).
Proof. intros. go_lowerx. rewrite sepcon_emp. apply TT_right.
Qed.

Lemma replace_nth_SEP: forall P Q R n Rn Rn', (Rn |-- Rn') -> PROPx P (LOCALx Q (SEPx (replace_nth n R Rn))) |-- PROPx P (LOCALx Q (SEPx (replace_nth n R Rn'))).
Proof.
  simpl.
  intros.
  normalize.
  autorewrite with subst norm1 norm2; normalize.
  apply andp_right; [apply prop_right; auto | auto].
  unfold_lift.
  revert R.
  induction n.
  + destruct R.
    - simpl. auto.
    - simpl. cancel.
  + destruct R.
    - simpl. cancel.
    - intros. simpl in *. cancel.
Qed.

Lemma replace_nth_SEP':
  forall A P Q R n Rn Rn', (local A && PROPx P (LOCALx Q (SEPx (Rn::nil))) |-- `Rn') ->
  (local A && PROPx P (LOCALx Q (SEPx (replace_nth n R Rn)))) |-- (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn')))).
Proof.
  simpl. unfold local, lift1.
  intros.
  specialize (H x).
  normalize. rewrite prop_true_andp in H by auto. clear H0.
      autorewrite with subst norm1 norm2; normalize.
    autorewrite with subst norm1 norm2 in H; normalize in H.
  apply andp_right; [apply prop_right; auto | auto].
  unfold_lift.
  revert R.
  induction n.
  + destruct R.
    - simpl. cancel.
    - simpl. cancel.
  + destruct R.
    - simpl. cancel.
    - intros. simpl in *. cancel.
Qed.

Lemma nth_error_SEP_prop:
  forall P Q R n (Rn: mpred) (Rn': Prop),
    nth_error R n = Some Rn ->
    (Rn |-- !! Rn') ->
    PROPx P (LOCALx Q (SEPx R)) |-- !! Rn'.
Proof.
  intros.
  apply andp_left2.
  apply andp_left2.
  unfold SEPx.
  hnf; simpl; intros _.
  revert R H; induction n; intros; destruct R; inv H.
  + simpl.
    rewrite (add_andp _ _ H0).
    normalize.
  + apply IHn in H2.
    simpl.
    rewrite (add_andp _ _ H2).
    normalize.
Qed.

Lemma LOCAL_2_hd: forall P Q R Q1 Q2,
  (PROPx P (LOCALx (Q1 :: Q2 :: Q) (SEPx R))) =
  (PROPx P (LOCALx (Q2 :: Q1 :: Q) (SEPx R))).
Proof.
  intros.
  extensionality.
  apply pred_ext; normalize;
  autorewrite with subst norm1 norm2; normalize;
  (apply andp_right; [apply prop_right; auto | auto]);
  unfold_lift;
  unfold_lift in H0;
  split; simpl in *; tauto.
Qed.

Lemma lvar_eval_lvar {cs: compspecs}:
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
 forall Delta gv i rho t, tc_environ Delta rho -> (var_types Delta) ! i = None -> locald_denote (gvars gv) rho -> eval_var i t rho = gv i.
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
  forall Delta gv i rho t, tc_environ Delta rho -> (glob_types Delta) ! i = Some t -> locald_denote (gvars gv) rho -> isptr (gv i).
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

Lemma PARAMSx_args_super_non_expansive: forall A Q R,
  args_super_non_expansive R ->
  (forall n ts x, Q ts x = Q ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x)) ->
  @args_super_non_expansive A (fun ts a ae => PARAMSx (Q ts a) (R ts a) ae).
Proof. intros. simpl in *.
  hnf; intros.
  unfold PARAMSx.
  simpl.
  rewrite !approx_andp.
  f_equal; auto.
  f_equal; f_equal; f_equal.
  apply H0.
Qed.

Lemma GLOBALSx_args_super_non_expansive: forall A G R,
  args_super_non_expansive R ->
  @super_non_expansive_list A (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)) ->
  @args_super_non_expansive A (fun ts a ae => GLOBALSx (G ts a) (R ts a) ae).
Proof.
  intros. simpl in *.
  hnf; intros.
  unfold GLOBALSx, LOCALx. simpl. rewrite ! approx_andp. f_equal; [|apply H].
  specialize (H0 n ts x (Clight_seplog.mkEnv (fst gargs) nil nil)).
  simpl in H0.
  match goal with H : Forall2 _ _ (map _ ?l) |- _ => forget l as Q1 end.
  generalize dependent Q1; induction (G ts x); intros; inv H0; destruct Q1; try discriminate.
  + auto.
  + inv H3.
    simpl.
    unfold local, lift1 in IHl |- *.
    unfold_lift in IHl; unfold_lift.
    rewrite !prop_and.
    rewrite !approx_andp.
    f_equal; auto.
Qed.

Lemma PROP_PARAMS_GLOBALS_SEP_args_super_non_expansive: forall A P Q G R
  (HypP: Forall (fun P0 => @args_super_non_expansive A (fun ts a _ => prop (P0 ts a))) P)
  (HypQ: forall n ts x, Q ts x = Q ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x))
  (HypG: @super_non_expansive_list A (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)))
  (HypR: Forall (fun R0 => @args_super_non_expansive A (fun ts a _ => R0 ts a)) R),
  @args_super_non_expansive A (fun ts a =>
    PROPx (map (fun P0 => P0 ts a) P)
       (PARAMSx (Q ts a)
         (GLOBALSx (G ts a) (SEPx (map (fun R0 => R0 ts a) R))))).
Proof. intros. simpl.
 apply (PROPx_args_super_non_expansive A P) ; [ clear P HypP| apply HypP].
  apply (PARAMSx_args_super_non_expansive A Q); [|apply HypQ].
  apply (GLOBALSx_args_super_non_expansive A G); [|apply HypG].
  apply (SEPx_args_super_non_expansive A R); apply HypR.
Qed.

Lemma super_non_expansive_args_super_non_expansive {A P}
      (H: @super_non_expansive A (fun ts a _ => P ts a)):
      @args_super_non_expansive A (fun ts a _ => P ts a).
Proof. red; intros. apply H. apply any_environ. Qed.

Lemma PROPx_args_super_non_expansive': forall A P Q,
  args_super_non_expansive Q ->
  @super_non_expansive_list A (fun ts a _ => map prop (P ts a)) ->
  @args_super_non_expansive A (fun ts a => PROPx (P ts a) (Q ts a)).
Proof.
  intros.
  hnf; intros.
  unfold PROPx.
  simpl.
  rewrite !approx_andp.
  f_equal; auto.
  specialize (H0 n ts x any_environ).
  simpl in H0.
  match goal with H : Forall2 _ _ (map _ ?l) |- _ => forget l as P1 end.
  generalize dependent P1; induction (P ts x); intros; inv H0; destruct P1; try discriminate.
  + auto.
  + inv H3.
    simpl.
    rewrite !prop_and.
    rewrite !approx_andp.
    f_equal; auto.
Qed.

Lemma SEPx_args_super_non_expansive': forall A R ,
  @super_non_expansive_list A (fun ts a _ => R ts a) ->
  @args_super_non_expansive A (fun ts a ae => SEPx (R ts a) ae).
Proof.
  intros.
  hnf; intros.
  unfold SEPx; unfold super_non_expansive_list in H.
  specialize (H n ts x any_environ).
  induction H.
  + simpl; auto.
  + simpl in *.
    rewrite !approx_sepcon.
    f_equal;
    auto.
Qed.

Lemma PROP_PARAMS_GLOBALS_SEP_args_super_non_expansive': forall A P Q G R
  (HypP: @super_non_expansive_list A (fun ts a _ => map prop (P ts a)))
  (HypQ: forall n ts x, Q ts x = Q ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x))
  (HypG: @super_non_expansive_list A (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)))
  (HypR: @super_non_expansive_list A (fun ts a _ => R ts a)),
  @args_super_non_expansive A (fun ts a =>
    PROPx (P ts a)
       (PARAMSx (Q ts a)
         (GLOBALSx (G ts a) (SEPx (R ts a))))).
Proof. intros.
  apply PROPx_args_super_non_expansive'; [|auto].
  apply PARAMSx_args_super_non_expansive; [|auto].
  apply GLOBALSx_args_super_non_expansive; [|auto].
  apply SEPx_args_super_non_expansive'; auto.
Qed.

Lemma PARAMSx_super_non_expansive: forall A Q R,
  super_non_expansive R ->
  @super_non_expansive A (fun ts a rho => PARAMSx Q (fun ae:argsEnviron => R ts a rho) (ge_of rho, nil)).
Proof. intros. simpl in *.
  hnf; intros.
  unfold PARAMSx.
  simpl.
  rewrite !approx_andp.
  f_equal; auto.
Qed.

Lemma GLOBALSx_super_non_expansive: forall A G R,
  super_non_expansive R ->
  @super_non_expansive A (fun ts a rho => GLOBALSx G (fun ae : argsEnviron => let (g, _) := ae in !! gvars_denote (initialize.globals_of_genv g) rho && R ts a rho)
  (Map.empty block, nil)).
Proof.
  intros. simpl in *.
  hnf; intros.
  unfold GLOBALSx, LOCALx, argsassert2assert, Clight_seplog.mkEnv.
  simpl. rewrite ! approx_andp. f_equal. f_equal. apply H.
Qed.

Lemma PROP_PARAMS_GLOBALS_SEP_super_non_expansive: forall A P (Q:list val)(G : list globals) R
  (HypP: Forall (fun P0 => @super_non_expansive A (fun ts a _ => prop (P0 ts a))) P)
  (HypR: Forall (fun R0 => @super_non_expansive A (fun ts a _ => R0 ts a)) R),
  @super_non_expansive A (fun ts a rho =>
    PROPx (map (fun P0 => P0 ts a) P)
       (PARAMSx Q (fun _ : argsEnviron =>
         GLOBALSx G (fun ae0 : argsEnviron =>
            let (g, _) := ae0 in
            !! gvars_denote (initialize.globals_of_genv g) rho
            && SEPx (map (fun R0 => R0 ts a) R) rho) (Map.empty block, nil))) (ge_of rho, nil)).
Proof. intros. simpl.
 apply (PROPx_super_non_expansive A P) ; [ clear P HypP| apply HypP].
  apply (PARAMSx_super_non_expansive A Q).
  apply (GLOBALSx_super_non_expansive A G).
  apply (SEPx_super_non_expansive A R); apply HypR.
Qed.

#[export] Hint Extern 1 (isptr (eval_var _ _ _)) => (eapply lvar_isptr_eval_var; eassumption) : norm2.

Lemma semax_extract_later_prop'':
  forall {CS : compspecs} {Espec: OracleKind},
    forall (Delta : tycontext) (PP : Prop) P Q R c post P1 P2,
      (P2 |-- !!PP) ->
      (PP -> semax Delta (PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))) c post) ->
      semax Delta (PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))) c post.
Proof.
  intros.
  erewrite (add_andp P2) by eauto.
  apply semax_pre0 with (P' := |>!!PP && PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))).
  { go_lowerx.
    rewrite later_andp, <- andp_assoc, andp_comm, corable_andp_sepcon1; auto.
    apply corable_later; auto. }
  apply semax_extract_later_prop; auto.
Qed.

Lemma approx_imp : forall n P Q, compcert_rmaps.RML.R.approx n (predicates_hered.imp P Q) =
  compcert_rmaps.RML.R.approx n (predicates_hered.imp (compcert_rmaps.RML.R.approx n P)
    (compcert_rmaps.RML.R.approx n Q)).
Proof.
  intros; apply predicates_hered.pred_ext; intros ? (? & Himp); split; auto; intros ? ? Ha' Hext HP.
  - destruct HP; split; eauto.
  - eapply Himp; eauto; split; auto.
    pose proof (ageable.necR_level _ _ Ha'); apply predicates_hered.ext_level in Hext; lia.
Qed.

Definition super_non_expansive' {A} P := forall n ts x, compcert_rmaps.RML.R.approx n (P ts x) =
  compcert_rmaps.RML.R.approx n (P ts (functors.MixVariantFunctor.fmap (rmaps.dependent_type_functor_rec ts A)
        (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x)).

Lemma approx_0 : forall P, compcert_rmaps.RML.R.approx 0 P = FF.
Proof.
  intros; apply predicates_hered.pred_ext.
  - intros ? []; lia.
  - intros ??; contradiction.
Qed.

Require Import VST.msl.predicates_hered.
Require Import VST.msl.ageable.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.age_sepalg.
Import FashNotation.

Lemma approx_eq : forall n (P : mpred) r, app_pred (compcert_rmaps.RML.R.approx n P) r = (if lt_dec (level r) n then app_pred P r else False).
Proof.
  intros; apply prop_ext; split.
  - intros []; if_tac; auto.
  - if_tac; split; auto; lia.
Qed.

Lemma approx_iter_sepcon' : forall {B} n f (lP : list B) P,
  compcert_rmaps.RML.R.approx n (iter_sepcon f lP)  * compcert_rmaps.RML.R.approx n P =
  iter_sepcon (compcert_rmaps.RML.R.approx n oo f) lP * compcert_rmaps.RML.R.approx n P.
Proof.
  induction lP; simpl; intros.
  - apply predicates_hered.pred_ext; intros ? (? & ? & ? & ? & ?).
    + destruct H0; do 3 eexists; eauto.
    + do 3 eexists; eauto; split; auto; split; auto.
      destruct H1; apply join_level in H as []; lia.
  - rewrite approx_sepcon, !sepcon_assoc, IHlP; auto.
Qed.

Corollary approx_iter_sepcon: forall {B} n f (lP : list B), lP <> nil ->
  compcert_rmaps.RML.R.approx n (iter_sepcon f lP) =
  iter_sepcon (compcert_rmaps.RML.R.approx n oo f) lP.
Proof.
  destruct lP; [contradiction | simpl].
  intros; rewrite approx_sepcon, !(sepcon_comm (compcert_rmaps.RML.R.approx n (f b))), approx_iter_sepcon'; auto.
Qed.

Lemma approx_FF : forall n, compcert_rmaps.RML.R.approx n FF = FF.
Proof.
  intro; apply predicates_hered.pred_ext; intros ??; try contradiction.
  destruct H; contradiction.
Qed.

Lemma later_nonexpansive' : nonexpansive (@later mpred _ _).
Proof.
  apply contractive_nonexpansive, later_contractive.
  intros ??; auto.
Qed.

Lemma later_nonexpansive : forall n P, compcert_rmaps.RML.R.approx n (|> P)%pred =
  compcert_rmaps.RML.R.approx n (|> compcert_rmaps.RML.R.approx n P)%pred.
Proof.
  intros.
  intros; apply predicates_hered.pred_ext.
  - intros ? []; split; auto.
    intros ? Hlater; split; auto.
    apply laterR_level in Hlater; lia.
  - intros ? []; split; auto.
    intros ? Hlater.
    specialize (H0 _ Hlater) as []; auto.
Qed.

Lemma allp_nonexpansive : forall {A} n P, compcert_rmaps.RML.R.approx n (ALL y : A, P y)%pred =
  compcert_rmaps.RML.R.approx n (ALL y, compcert_rmaps.RML.R.approx n (P y))%pred.
Proof.
  intros.
  apply predicates_hered.pred_ext; intros ? [? Hall]; split; auto; intro; simpl in *.
  - split; auto.
  - apply Hall.
Qed.

Lemma fold_right_sepcon_nonexpansive : forall lP1 lP2, Zlength lP1 = Zlength lP2 ->
  ((ALL i : Z, Znth i lP1 <=> Znth i lP2) |--
  fold_right sepcon emp lP1 <=> fold_right sepcon emp lP2).
Proof.
  induction lP1; intros.
  - symmetry in H; apply Zlength_nil_inv in H; subst.
    apply eqp_refl.
  - destruct lP2; [apply Zlength_nil_inv in H; discriminate|].
    rewrite !Zlength_cons in H.
    simpl fold_right; apply eqp_sepcon.
    + apply predicates_hered.allp_left with 0.
      rewrite !Znth_0_cons; auto.
    + eapply predicates_hered.derives_trans, IHlP1; [|lia].
      apply predicates_hered.allp_right; intro i.
      apply predicates_hered.allp_left with (i + 1).
      destruct (zlt i 0).
      { rewrite !(Znth_underflow _ _ l); apply eqp_refl. }
      rewrite !Znth_pos_cons, Z.add_simpl_r by lia; auto.
Qed.
