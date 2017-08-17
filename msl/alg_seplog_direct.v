Require Import VST.msl.Extensionality.
Require Import VST.msl.seplog.
Require Import VST.msl.base.
Require Import VST.msl.boolean_alg.
Require Import VST.msl.sepalg.
Require Import VST.msl.predicates_sa.
Require Import VST.msl.corable_direct.

Local Open Scope logic.

Instance algNatDed (T: Type) : NatDed (pred T).
  apply (mkNatDed _
                    predicates_sa.andp
                    predicates_sa.orp
                    (@predicates_sa.exp _)
                    (@predicates_sa.allp _)
                    predicates_sa.imp predicates_sa.prop
                    (@predicates_sa.derives _)).
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
 repeat intro. eapply H; eauto.
 repeat intro. hnf; auto.
 repeat intro. unfold imp, prop in H. auto.
 repeat intro. specialize (H b); unfold prop in H. auto.
Defined.

Instance algSepLog (T: Type) {JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T} :
      @SepLog (pred T) (algNatDed T).
 apply (mkSepLog _ (algNatDed T) identity predicates_sa.sepcon predicates_sa.wand
                             predicates_sa.ewand).
 apply sepcon_assoc.
 apply sepcon_comm.
 intros. pose proof (wand_sepcon_adjoint P Q R). simpl. rewrite H; split; auto.
 intros. apply (predicates_sa.sepcon_andp_prop P Q R).
 intros; intro; apply sepcon_derives; auto.
 intros; apply predicates_sa.ewand_sepcon.
 intros; simpl. apply ewand_TT_sepcon; auto.
 intros; simpl. intros w [w1 [w2 [? [? ?]]]]. exists w1,w2; repeat split; auto. exists w2; exists w; repeat split; auto.
 intros; simpl. apply ewand_conflict; auto.
Defined.

Instance algClassicalSep (T: Type) {JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{CancT: Canc_alg T}:
     @ClassicalSep (pred T) (algNatDed T)(algSepLog T).
 constructor; intros. simpl. apply predicates_sa.sepcon_emp.
Defined.

Instance algCorableSepLog (T: Type){JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}:
         @CorableSepLog (pred T) (algNatDed T) (algSepLog T).
  apply mkCorableSepLog with (corable := corable_direct.corable); unfold algNatDed, algSepLog; simpl.
  + apply corable_prop.
  + apply corable_andp.
  + apply corable_orp.
  + apply corable_imp.
  + intros. apply corable_allp; auto.
  + intros; apply corable_exp; auto.
  + apply corable_sepcon.
  + apply corable_wand.
  + intros; simpl.
    apply corable_andp_sepcon1; auto.
Defined.
