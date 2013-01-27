Require Import msl.Extensionality.
Require Import msl.seplog.
Require Import msl.base.
Require Import msl.boolean_alg.
Require Import msl.sepalg.
Require Import msl.predicates_sa.

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
 intros. intro; intros. intro.  specialize (H H1 _ H0). apply H.
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
 admit. 
 admit.
 admit.
Defined.

Instance algClassicalSep (T: Type) {JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{CancT: Canc_alg T}:
     @ClassicalSep (pred T) (algNatDed T)(algSepLog T).
 constructor; intros. simpl. apply predicates_sa.sepcon_emp.
Qed.

