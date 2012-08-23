Require Import msl.seplog.
Require Import msl.base.
Require Import msl.ageable.
Require Import msl.sepalg.
Require Import msl.age_sepalg.
Require Import msl.predicates_hered.
Require Import msl.predicates_sl.
Require Import msl.subtypes.
Require Import msl.subtypes_sl.
Require Import msl.predicates_rec.
Require Import msl.contractive.

Local Open Scope logic.

Definition algNatDed (T: Type){agT: ageable T} : NatDed (pred T).
  apply (mkNatDed _ andp orp
                    (@exp _ _) (@allp _ _)
                    imp prop
                    (@derives _ _)).
 apply pred_ext.
 apply derives_refl.
 apply @derives_trans.
 apply andp_right.
 apply andp_left1.
 apply andp_left2.
 apply orp_left.
 apply orp_right1.
 apply orp_right2.
 intros ? ?; apply @exp_right.
 intros ? ?; apply @exp_left.
 intros ? ?; apply @allp_left.
 intros ? ?; apply @allp_right.
 apply imp_andp_adjoint.
 repeat intro. destruct H. apply H0; auto.
 repeat intro. hnf in H0; contradiction. 
 repeat intro. hnf; auto.
Defined.

Definition algSepLog (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
      @SepLog (pred T) (algNatDed T).
 apply (mkSepLog _ (algNatDed T) emp sepcon wand).
 apply sepcon_assoc.
 apply sepcon_comm.
 apply @wand_sepcon_adjoint.
 intros. apply predicates_hered.pred_ext; intros ? ?; try destruct H as [? [? [? [? ?]]]]; contradiction.
 intros. simpl. apply exp_sepcon1.
 intros; simpl. apply predicates_hered.pred_ext; simpl.
          intros ? [w1 [w2 [? [? [? ?]]]]];  split; auto. exists w1; exists w2; repeat split; auto.
          intros ? [? [w1 [w2 [? [? ?]]]]];  exists w1; exists w2; repeat split; auto.
Defined.

Definition algClassicalSep (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{CancT: Canc_alg T}{AgeT: Age_alg T}:
     @ClassicalSep (pred T) (algNatDed T)(algSepLog T).
 constructor; intros. simpl. apply predicates_sl.sepcon_emp.
Qed.

Definition Triv := predicates_hered.pred nat.
Instance TrivNatDed: NatDed Triv := algNatDed nat.
Instance TrivSeplog: SepLog Triv := @algSepLog nat _ _ _ _ (asa_nat).
Instance TrivClassical: ClassicalSep Triv := @algClassicalSep _ _ _ _ _ _ asa_nat.

Section SL. Import msl.seplog.

Class Indir (A: Type) {ND: NatDed A} := mkIndir {
  later: A -> A;
  fash : A -> Triv;
  unfash : Triv -> A; 
  now_later: forall P, P |-- later P;
  later_K: forall P Q, later (P --> Q) |-- later P --> later Q;
  fash_K: forall P Q, fash (P --> Q) |-- fash P --> fash Q;
  later_derives: forall P Q, P |-- Q -> later P |-- later Q;
  fash_derives: forall P Q, P |-- Q -> fash P |-- fash Q;
  later_andp: forall P Q, later (P && Q) = later P && later Q;
  fash_andp: forall P Q, fash (P && Q) = fash P && fash Q;
  later_allp: forall T (F: T -> A),  later (allp F) = All x:T, later (F x);
  later_exp: forall T (F: T-> A), Ex x:T, later (F x) |-- later (exp F);
  later_exp': forall T (any:T) F, later (exp F) = Ex x:T, later (F x);
  later_orp: forall P Q, later (P || Q) = later P || later Q;
  later_imp: forall P Q,  later(P --> Q) = later P --> later Q;
  goedel_loeb: forall P Q,   Q && later P |-- P ->  Q |-- P
}.
End SL.

Definition algIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T}{nattyT: natty T} :
         @Indir (pred T) (algNatDed T).
 apply (@mkIndir (pred T) (algNatDed T) (box laterM) subtypes.fash subtypes.fash').
 apply @predicates_hered.now_later.
 apply @predicates_hered.axiomK.
 apply @subtypes.fash_K.
 apply @predicates_hered.later_derives.
 apply @subtypes.fash_derives.
 apply @predicates_hered.later_andp.
 apply @subtypes.fash_and.
 apply @predicates_hered.later_allp.
 simpl. intros; apply @box_ex.
  simpl. intros; apply @later_ex; auto.
 apply @later_or.
 apply @predicates_hered.later_imp.
 apply @predicates_hered.goedel_loeb.
Defined.


Instance LiftIndir (A: Type) (any: A) (B: Type)  {NB: NatDed B} {IB: Indir B} : Indir (A -> B).
 apply (@mkIndir (A -> B) _ (fun P rho => later (P rho)) (fun P => fash (P any)) (fun P rho => unfash P)).
 simpl; intros. apply now_later.
 simpl; intros. apply later_K.
 simpl; intros. apply @fash_K.
 simpl; intros. apply later_derives; auto.
 simpl; intros. apply fash_derives; auto.
 simpl; intros. extensionality rho. apply later_andp.
 simpl; intros. apply @fash_andp.
 simpl; intros. extensionality rho. apply later_allp.
 simpl; intros. apply later_exp.
 simpl; intros. extensionality rho. apply later_exp'; auto.
 simpl; intros. extensionality rho. apply later_orp.
 simpl; intros. extensionality rho. apply later_imp.
 simpl; intros. apply goedel_loeb; auto.
Defined.

Notation "'|>' e" := (later e) (at level 30, right associativity): logic.

Instance TrivIndir: Indir Triv := @algIndir nat _ _ _ _ asa_nat _.

Section SL2. Import msl.seplog.

Class RecIndir (A: Type) {NA: NatDed A}{IA: Indir A} := mkRecIndir {
  HORec : forall {X} (f: (X -> A) -> (X -> A)), X -> A;
  HOcontractive: forall (X: Type) (f: (X -> A) -> (X -> A)), Prop :=
         fun X f => forall P Q,  (All x:X, later (fash (P x <--> Q x))) |-- (All x:X, fash (f P x <--> f Q x)); 
  HORec_fold_unfold : forall X f (H: HOcontractive X f), HORec f = f (HORec f)
}.

Definition HOnonexpansive {A}{NA: NatDed A}{IA: Indir A}
        {X: Type} (f: (X -> A) -> (X -> A)) :=
         forall P Q,  (All x:X, fash (P x <--> Q x)) |-- (All x:X, fash (f P x <--> f Q x)).
End SL2.

Definition algRecIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T}{nattyT: natty T} :
         @RecIndir (pred T) (algNatDed T) (algIndir T).
 apply (mkRecIndir _ _ _ HoRec.HORec).
 intros. apply HoRec.HORec_fold_unfold.
 hnf.  apply H.
Defined.

Instance TrivRecIndir: RecIndir Triv := algRecIndir nat.

Class SepIndir (A: Type) {ND: NatDed A}{SL: SepLog A}{ID: Indir A} := mkSepIndir {
  later_sepcon: forall P Q, |> (P * Q) = |>P * |>Q
}.

