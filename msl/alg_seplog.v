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
Require msl.normalize.

Local Open Scope logic.

Instance algNatDed (T: Type){agT: ageable T} : NatDed (pred T).
  apply (mkNatDed _ 
                    predicates_hered.andp 
                    predicates_hered.orp
                    (@predicates_hered.exp _ _) 
                    (@predicates_hered.allp _ _)
                    predicates_hered.imp predicates_hered.prop
                    (@predicates_hered.derives _ _)).
 apply pred_ext.
 apply derives_refl.
 apply derives_trans.
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
 repeat intro. eapply H; eauto. hnf; auto.
 repeat intro. hnf; auto.
 intros. apply exp_andp1.
Defined.

Instance algSepLog (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
      @SepLog (pred T) (algNatDed T).
 apply (mkSepLog _ (algNatDed T) predicates_sl.emp predicates_sl.sepcon predicates_sl.wand).
 apply sepcon_assoc.
 apply sepcon_comm.
 apply @wand_sepcon_adjoint.
 intros. apply predicates_hered.pred_ext; intros ? ?; try destruct H as [? [? [? [? ?]]]]; contradiction.
 intros. simpl. apply exp_sepcon1.
 intros; simpl. apply predicates_hered.pred_ext; simpl.
          intros ? [w1 [w2 [? [? [? ?]]]]];  split; auto. exists w1; exists w2; repeat split; auto.
          intros ? [? [w1 [w2 [? [? ?]]]]];  exists w1; exists w2; repeat split; auto.
 intros; intro; apply sepcon_derives; auto.
 intros. simpl. apply normalize.sepcon_pure_andp;simpl; auto.
 intros. simpl. apply normalize.pure_sepcon_TT_andp; auto.
Defined.

Instance algClassicalSep (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{CancT: Canc_alg T}{AgeT: Age_alg T}:
     @ClassicalSep (pred T) (algNatDed T)(algSepLog T).
 constructor; intros. simpl. apply predicates_sl.sepcon_emp.
Qed.

Definition Triv := predicates_hered.pred nat.
Instance TrivNatDed: NatDed Triv := algNatDed nat.
Instance TrivSeplog: SepLog Triv := @algSepLog nat _ _ _ _ (asa_nat).
Instance TrivClassical: ClassicalSep Triv := @algClassicalSep _ _ _ _ _ _ asa_nat.
Instance TrivIntuitionistic: IntuitionisticSep Triv.
 constructor. intros. hnf. intros. destruct H as [w1 [w2 [? [? _]]]].
 destruct H; subst; auto.
Qed.

Class IndirOps (A: Type) {ND: NatDed A} := mkIndirOps {
  later: A -> A;
  fash : A -> Triv;
  unfash : Triv -> A
}.

Instance algIndirOps (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
         @IndirOps (pred T) (algNatDed T).
 apply (@mkIndirOps (pred T) (algNatDed T) (box laterM) subtypes.fash subtypes.fash').
Defined.

Section SL. Import msl.seplog.

Instance TrivIndirOps: IndirOps Triv := 
     (*Hidden inside a Section, on purpose! *)
   @algIndirOps nat _ _ _ _ asa_nat. 
 

Class Indir (A: Type) {ND: NatDed A} := mkIndir {
  indir_ops :> IndirOps A;
  now_later: forall P, P |-- later P;
  later_K: forall P Q, later (P --> Q) |-- later P --> later Q;
  fash_K: forall P Q, fash (P --> Q) |-- fash P --> fash Q;
  later_derives: forall P Q, P |-- Q -> later P |-- later Q;
  fash_derives: forall P Q, P |-- Q -> fash P |-- fash Q;
  later_fash:  forall P, later (fash P) = fash (later P);
  later_andp: forall P Q, later (P && Q) = later P && later Q;
  fash_andp: forall P Q, fash (P && Q) = fash P && fash Q;
  later_allp: forall T (F: T -> A),  later (allp F) = ALL x:T, later (F x);
  later_exp: forall T (F: T-> A), EX x:T, later (F x) |-- later (exp F);
  later_exp': forall T (any:T) F, later (exp F) = EX x:T, later (F x);
  later_orp: forall P Q, later (P || Q) = later P || later Q;
  later_imp: forall P Q,  later(P --> Q) = later P --> later Q;
  loeb: forall P,   later P |-- P ->  TT |-- P;
  subp_allp: forall G B (X Y:B -> A),  (forall x:B, G |-- fash (imp (X x) (Y x))) ->  G |-- fash (imp (allp X) (allp Y));
  subp_exp: forall G B (X Y:B -> A),  (forall x:B, G |-- fash (imp (X x) (Y x))) ->  G |-- fash (imp (exp X) (exp Y));
  fash_TT: forall G, G |-- fash TT
}.
End SL.

Notation "'|>' e" := (later e) (at level 30, right associativity): logic.
Notation "'#' e" := (fash e) (at level 30, right associativity): logic.
Notation "'!' e" := (unfash e) (at level 30, right associativity): logic.
Notation "P '>=>' Q" := (# (P --> Q)) (at level 55, right associativity) : logic.
Notation "P '<=>' Q" := (# (P <--> Q)) (at level 57, no associativity) : logic.

Instance algIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}
                {AgeT: Age_alg T}:
         @Indir (pred T) (algNatDed T).
 apply (mkIndir _ _ (algIndirOps T)); intros; simpl in *.
 apply @predicates_hered.now_later.
 apply @predicates_hered.axiomK.
 apply @subtypes.fash_K.
 apply @predicates_hered.later_derives; auto.
 apply @subtypes.fash_derives; auto.
 apply @subtypes.later_fash; auto.
 apply @predicates_hered.later_andp.
 apply @subtypes.fash_and.
 apply @predicates_hered.later_allp.
 simpl. intros; apply @box_ex.
  simpl. intros; apply @later_ex; auto.
 apply @later_or.
 apply @predicates_hered.later_imp.
 apply @predicates_hered.loeb; auto.
 apply @subtypes.subp_allp; auto.
 eapply @subtypes.subp_exp; auto. 
 repeat intro; hnf; auto.
Defined.

Instance TrivIndir: Indir Triv := @algIndir nat _ _ _ _ asa_nat.


Lemma fash_triv: forall P: Triv, fash P = P.
Proof.
 intros.
 apply pred_ext; intros ? ?.
 eapply H. unfold level; simpl.  unfold natLevel; auto.
 hnf; intros. eapply pred_nec_hereditary; try eapply H.
 apply nec_nat. auto.
Qed.


Instance LiftIndirOps (A: Type) (any: A) (B: Type)  {NB: NatDed B} {IB: IndirOps B} : IndirOps (A -> B).
 apply (@mkIndirOps (A -> B) _ (fun P rho => later (P rho)) (fun P => fash (P any)) 
            (fun P rho => unfash P)).
Defined.

Instance LiftIndir (A: Type) (any: A) (B: Type)  {NB: NatDed B}{IXB: Indir B} :
         @Indir (A -> B) (LiftNatDed A B).
 apply (mkIndir _ _ (LiftIndirOps A any B)); intros; simpl in *; intros.
 apply now_later.
 apply later_K.
 apply @fash_K; auto.
 apply later_derives; auto.
 apply fash_derives; auto.
 rewrite <- later_fash. simpl. auto.
 extensionality rho. apply later_andp.
 simpl; intros. apply @fash_andp; auto.
 simpl; intros. extensionality rho. apply later_allp.
 simpl; intros. apply later_exp.
 simpl; intros. extensionality rho. apply later_exp'; auto.
 simpl; intros. extensionality rho. apply later_orp.
 simpl; intros. extensionality rho. apply later_imp.
 simpl; intros. apply loeb; auto.
 apply subp_allp; auto.
 apply subp_exp; auto.
 apply fash_TT.
Defined.

Section SL2. Import msl.seplog.

Class RecIndir (A: Type) {NA: NatDed A}{IA: Indir A} := mkRecIndir {
  HORec : forall {X} (f: (X -> A) -> (X -> A)), X -> A;
  HOcontractive: forall {X: Type} (f: (X -> A) -> (X -> A)), Prop :=
         fun {X} f => forall P Q,  (ALL x:X, later (fash (P x <--> Q x))) |-- (ALL x:X, fash (f P x <--> f Q x)); 
  HORec_fold_unfold : forall X (f: (X -> A) -> (X -> A)) (H: HOcontractive f), HORec f = f (HORec f)
}.

Definition HOnonexpansive {A}{NA: NatDed A}{IA: Indir A}
        {X: Type} (f: (X -> A) -> (X -> A)) :=
         forall P Q,  (ALL x:X, fash (P x <--> Q x)) |-- (ALL x:X, fash (f P x <--> f Q x)).
End SL2.

Definition algRecIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
         @RecIndir (pred T) (algNatDed T) (algIndir T).
 apply (mkRecIndir _ _ _ HoRec.HORec).
 intros. apply HoRec.HORec_fold_unfold; auto.
Defined.

Instance TrivRecIndir: RecIndir Triv := algRecIndir nat.

Section SL3. Import msl.seplog.
Class SepIndir (A: Type) {NA: NatDed A}{SA: SepLog A}{IA: Indir A} := mkSepIndir {
  later_sepcon: forall P Q, |> (P * Q) = |>P * |>Q;
  sub_sepcon': forall P P' Q Q': A, (P >=> P') && (Q >=> Q') |-- (P * Q) >=> (P' * Q')
}.
End SL3.

Instance algSepIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
         @SepIndir (pred T) (algNatDed T) (algSepLog T) (algIndir T).
 apply mkSepIndir.
 simpl.
 apply @predicates_sl.later_sepcon; auto.

  repeat intro. destruct H.
  destruct H2 as [w1 [w2 [? [? ?]]]].
  exists w1; exists w2; split; auto.
  split.
  eapply H; auto.
  assert (level w1 = level a').
  apply comparable_fashionR.  eapply join_sub_comparable; eauto.
 apply necR_level in H1. omega.
  eapply H3; auto.
  assert (level w2 = level a').
  apply comparable_fashionR. eapply join_sub_comparable; eauto.
 apply necR_level in H1. omega.
Qed.

Instance LiftSepIndir  (A: Type) (any: A) (B: Type)  {NB: NatDed B} {SB: SepLog B}{IB: Indir B}{SIB: SepIndir B} : 
     @SepIndir (A -> B) (LiftNatDed A B) (LiftSepLog A B) (LiftIndir A any B).
 constructor.
 intros; simpl. extensionality rho.  apply later_sepcon.
 intros; simpl. intros rho ?. apply sub_sepcon'. auto.
Qed.


