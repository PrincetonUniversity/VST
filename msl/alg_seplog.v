Require Import VST.msl.seplog.
Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.predicates_sl.
Require Import VST.msl.subtypes.
Require Import VST.msl.subtypes_sl.
Require Import VST.msl.predicates_rec.
Require Import VST.msl.contractive.
Require VST.msl.normalize.

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
 repeat intro. eapply H; eauto. hnf; auto.
 repeat intro. hnf; auto.
 repeat intro. specialize (H a (necR_refl _)). simpl in H. auto.
 repeat intro. specialize (H b). simpl in H. auto.
Defined.

Instance algSepLog (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
      @SepLog (pred T) (algNatDed T).
 apply (mkSepLog _ (algNatDed T) predicates_sl.emp predicates_sl.sepcon
            predicates_sl.wand predicates_sl.ewand).
 apply sepcon_assoc.
 apply sepcon_comm.
 intros. pose proof (wand_sepcon_adjoint P Q R). simpl. rewrite H; split; auto.
 intros; simpl. apply predicates_hered.pred_ext; simpl.
          intros ? [w1 [w2 [? [? [? ?]]]]];  split; auto. exists w1; exists w2; repeat split; auto.
          intros ? [? [w1 [w2 [? [? ?]]]]];  exists w1; exists w2; repeat split; auto.
 intros; intro; apply sepcon_derives; auto.
 intros; simpl; apply ewand_sepcon; auto.
 intros; simpl. apply ewand_TT_sepcon; auto.
 intros; simpl. intros w [w1 [w2 [? [? ?]]]]. exists w1,w2; repeat split; auto. exists w2; exists w; repeat split; auto.
  intros; simpl. apply ewand_conflict; auto.
Defined.

Instance algClassicalSep (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T}:
     @ClassicalSep (pred T) (algNatDed T)(algSepLog T).
 constructor; intros. simpl. apply predicates_sl.sepcon_emp.
Qed.

Definition Triv := predicates_hered.pred nat.
Instance TrivNatDed: NatDed Triv := algNatDed nat.
Instance TrivSeplog: SepLog Triv := @algSepLog nat _ _ _ _ (asa_nat).
Instance TrivClassical: ClassicalSep Triv := @algClassicalSep _ _ _ _ _ asa_nat.
Instance TrivIntuitionistic: IntuitionisticSep Triv.
 constructor. intros. hnf. intros. destruct H as [w1 [w2 [? [? _]]]].
 destruct H; subst; auto.
Qed.

Instance algIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}
                {AgeT: Age_alg T}:
         @Indir (pred T) (algNatDed T).
 apply (mkIndir _ _ (box laterM)); intros; simpl in *.
 apply @predicates_hered.now_later.
 apply @predicates_hered.axiomK.
 apply @predicates_hered.later_allp.
 simpl. intros; apply @box_ex.
 simpl. intros; apply @later_ex; auto.
 simpl. intros; apply @later_ex''.
 apply @predicates_hered.later_imp.
 apply @predicates_hered.later_prop.
 apply @predicates_hered.loeb; auto.
Defined.

Instance TrivIndir: Indir Triv := @algIndir nat _ _ _ _ asa_nat.

Section SL2. Import VST.msl.seplog.

Class RecIndir (A: Type) {NA: NatDed A}{IA: Indir A} := mkRecIndir {
  fash : A -> Triv;
  unfash : Triv -> A;
  HORec : forall {X} (f: (X -> A) -> (X -> A)), X -> A;
  unfash_fash:  forall P: A, unfash (fash P) |-- P;
  fash_K: forall P Q, fash (P --> Q) |-- fash P --> fash Q;
  fash_derives: forall P Q, P |-- Q -> fash P |-- fash Q;
  unfash_derives:  forall P Q,  P |-- Q -> unfash P |-- unfash Q;
  later_fash:  forall P, later (fash P) = fash (later P);
  later_unfash:  forall P, later (unfash P) = unfash (later P);
  fash_andp: forall P Q, fash (P && Q) = fash P && fash Q;
  unfash_allp:  forall {B} (P: B -> Triv), unfash (allp P) = ALL x:B, unfash (P x);  subp_allp: forall G B (X Y:B -> A),  (forall x:B, G |-- fash (imp (X x) (Y x))) ->  G |-- fash (imp (allp X) (allp Y));
  subp_exp: forall G B (X Y:B -> A),  (forall x:B, G |-- fash (imp (X x) (Y x))) ->  G |-- fash (imp (exp X) (exp Y));
  subp_e: forall (P Q : A), TT |-- fash (P --> Q) -> P |-- Q;
  subp_i1: forall P (Q R: A), unfash P && Q |-- R -> P |-- fash (Q --> R);
 fash_TT: forall G, G |-- fash TT;
  HOcontractive: forall {X: Type} (f: (X -> A) -> (X -> A)), Prop :=
         fun {X} f => forall P Q,  (ALL x:X, later (fash (P x <--> Q x))) |-- (ALL x:X, fash (f P x <--> f Q x));
  HORec_fold_unfold : forall X (f: (X -> A) -> (X -> A)) (H: HOcontractive f), HORec f = f (HORec f)
}.

Definition HOnonexpansive {A}{NA: NatDed A}{IA: Indir A}{RA: RecIndir A}
        {X: Type} (f: (X -> A) -> (X -> A)) :=
         forall P Q: X -> A,  (ALL x:X, fash (P x <--> Q x)) |-- (ALL x:X, fash (f P x <--> f Q x)).
End SL2.


Notation "'#' e" := (fash e) (at level 30, right associativity): logic.
Notation "'!' e" := (unfash e) (at level 30, right associativity): logic.
Notation "P '>=>' Q" := (# (P --> Q)) (at level 55, right associativity) : logic.
Notation "P '<=>' Q" := (# (P <--> Q)) (at level 57, no associativity) : logic.

Definition algRecIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
         @RecIndir (pred T) (algNatDed T) (algIndir T).
 apply (mkRecIndir _ _ _ subtypes.fash subtypes.unfash HoRec.HORec); intros; simpl.
 repeat intro. do 3 red in H. apply H; auto.
 apply @subtypes.fash_K.
 apply @subtypes.fash_derives; auto.
 intros ? ?. do 3 red in H0. apply H in H0. apply H0.
 apply @subtypes.later_fash; auto.
 apply @subtypes.later_unfash.
 apply @subtypes.fash_and.
 apply pred_ext; repeat intro; do 3 red in H; apply (H b); auto.
 apply @subtypes.subp_allp; auto.
 eapply @subtypes.subp_exp; auto.
 eapply @subtypes.subp_e; eauto.
 eapply @subtypes.subp_i1; eauto.
 repeat intro; hnf; auto.
 intros. apply HoRec.HORec_fold_unfold; auto.
Defined.

Instance TrivRecIndir: RecIndir Triv := algRecIndir nat.

Section SL3. Import VST.msl.seplog.

Lemma fash_triv: forall P: Triv, fash P = P.
Proof.
 intros.
 apply pred_ext; intros ? ?.
 eapply H. unfold level; simpl.  unfold natLevel; auto.
 hnf; intros. eapply pred_nec_hereditary; try eapply H.
 apply nec_nat. auto.
Qed.

Class SepRec  (A: Type) {NA: NatDed A}{SA: SepLog A}{IA: Indir A}{RA: RecIndir A} := mkSepRec {
  unfash_sepcon_distrib: forall (P: Triv) (Q R: A),
                 andp (unfash P) (sepcon Q R) = sepcon (andp (unfash P) Q) (andp (unfash P) R)
}.

End SL3.

Instance algSepIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
         @SepIndir (pred T) (algNatDed T) (algSepLog T) (algIndir T).
 apply mkSepIndir; simpl.
 apply @predicates_sl.later_sepcon; auto.
 apply @predicates_sl.later_wand; auto.
 apply @predicates_sl.later_ewand; auto.
Qed.

Instance algSepRec (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
         @SepRec (pred T) (algNatDed T) (algSepLog T) (algIndir T)(algRecIndir T).
constructor.
 intros; simpl. apply subtypes_sl.unfash_sepcon_distrib.
Qed.

Instance algCorableSepLog (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
         @CorableSepLog (pred T) (algNatDed T) (algSepLog T).
  apply mkCorableSepLog with (corable := corable.corable).
  + apply corable.corable_prop.
  + apply corable.corable_andp.
  + apply corable.corable_orp.
  + apply corable.corable_imp.
  + intros; apply corable.corable_allp; auto.
  + intros; apply corable.corable_exp; auto.
  + apply corable.corable_sepcon.
  + apply corable.corable_wand.
  + intros; simpl.
    apply corable.corable_andp_sepcon1; auto.
Defined.

Instance algCorableIndir (T: Type) {agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T} :
         @CorableIndir (pred T) (algNatDed T) (algSepLog T) (algCorableSepLog T) (algIndir T).
  unfold CorableIndir; simpl.
  apply corable.corable_later.
Defined.