Require Import msl.examples.cont.language.
Require Import msl.examples.cont.sep_base.
Require Import msl.msl_standard.
Require Import msl.Coqlib2.

Local Open Scope pred.

Definition next e1 e2: pred rmap := !! (e1 > 0) && mapsto e1 e2.

Lemma next_gt_0: 
  forall x y, next x y = !! (x>0) && next x y.
Proof.
 intros. unfold next.
 rewrite <- andp_assoc. f_equal. rewrite andp_dup. auto.
Qed.

Lemma next_neq_0: forall y, next 0 y |-- FF.   (* W1 *)
Proof.
 intros. rewrite next_gt_0. apply prop_andp_left. intro. inv H.
Qed.

Definition listcons' (R: (adr * adr) -> pred rmap) (lp: adr * adr) : pred rmap :=
      !! (fst lp <> snd lp) && Ex tail:adr, next (fst lp) tail * |> R (tail, snd lp).

Definition listempty (lp: adr*adr) : pred rmap :=
             !! (fst lp = snd lp) && emp.
 
Definition listrep' (R: adr*adr -> pred rmap) (lp: adr*adr) : pred rmap :=
        listcons' R lp || listempty lp.

Definition listrep : adr*adr -> pred rmap := HORec listrep'.

Definition lseg (e1 e2: adr) : pred rmap := listrep (e1,e2).


Lemma orp_HOcontractive {A}{agA: ageable A}: forall X (P Q: (X -> pred A) -> (X -> pred A)),
       HOcontractive P -> HOcontractive Q -> HOcontractive (fun R x => P R x || Q R x).
Proof.
 intros.
 intros F G n H2 x y Hy.
 specialize (H F G n H2 x y Hy). specialize (H0 F G n H2 x y Hy).
 destruct H, H0.
 split; (intros z Hz [?|?]; [left|right]); auto.
Qed.
Lemma andp_HOcontractive {A}{agA: ageable A}: forall X (P Q: (X -> pred A) -> (X -> pred A)),
       HOcontractive P -> HOcontractive Q -> HOcontractive (fun R x => P R x && Q R x).
Proof.
 intros.
 intros F G n H2 x y Hy.
 specialize (H F G n H2 x y Hy). specialize (H0 F G n H2 x y Hy).
 destruct H, H0.
 split; (intros z Hz [? ?]); split; auto.
Qed.
Lemma sepcon_HOcontractive {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}{NA: natty A}: forall X (P Q: (X -> pred A) -> (X -> pred A)),
       HOcontractive P -> HOcontractive Q -> HOcontractive (fun R x => P R x * Q R x).
Proof.
 intros.
 unfold HOcontractive in *|-.
 apply prove_HOcontractive; intros F G ?.
 specialize (H F G). specialize (H0 F G).
 apply subp_sepcon.
 eapply derives_trans.
 apply allp_derives; intro. rewrite <- eq_later. apply derives_refl.
 eapply derives_trans; [ apply H | ].
 apply allp_left with x.
 apply fash_derives. apply andp_left1. auto.
 eapply derives_trans.
 apply allp_derives; intro. rewrite <- eq_later. apply derives_refl.
 eapply derives_trans; [ apply H0 | ].
 apply allp_left with x.
 apply fash_derives. apply andp_left1. auto.
Qed.

Lemma const_HOcontractive{A}{agA: ageable A}: forall X (P : X -> pred A), HOcontractive (fun _ => P).
Proof.
 intros.
 apply prove_HOcontractive. intros. apply sub_refl.
Qed.

Lemma exp_HOcontractive {A}{agA: ageable A}{NA: natty A}:
  forall X Y (G: Y -> X -> X) (F: Y -> X -> pred A -> pred A),
   (forall y x, contractive (F y x)) ->
   HOcontractive (fun (R: X -> pred A) (x: X) => Ex y: Y, F y x (R (G y x))).
Proof.
 intros.
 apply prove_HOcontractive; intros.
 apply sub_exp; intro y.
 specialize (H y x (P (G y x)) (Q (G y x))).
 eapply derives_trans; [ | apply equ_sub; apply H].
 rewrite eq_later.
 apply allp_left with (G y x). auto.
Qed.
Lemma const_contractive {A}{agA: ageable A}: forall P : pred A, contractive (fun _ => P).
Proof.
 intros.
 apply prove_contractive. intros. apply sub_refl.
Qed.
Lemma later_contractive' {A} `{natty A} : contractive (box laterM).
Proof.
  unfold contractive; intros.
  apply sub_equ.
  rewrite <- sub_later.
  apply box_positive; auto.
  apply equ_sub; auto.
  rewrite <- sub_later.
  apply box_positive; auto.
  apply equ_sub2; auto.
Qed.

Lemma lseg_unfold: forall e1 e2, 
   (lseg e1 e2 = (!! (e1<> e2)  && Ex tail:adr, next e1 tail * |> lseg tail e2)
                        || (!! (e1=e2) && emp))%pred.
Proof.
 intros.
 unfold lseg. unfold listrep at 1.
 rewrite HORec_fold_unfold. reflexivity.

 apply prove_HOcontractive. intros. unfold listrep', listcons'.

 unfold listrep'.
 apply orp_HOcontractive.
 unfold listcons'.
 apply andp_HOcontractive.
 apply const_HOcontractive.
 apply exp_HOcontractive with (G:= fun y x => (y, snd x))
                   (F := fun tail x P => next (fst x) tail * |> P);  
   intros.
 apply sepcon_contractive.
 apply const_contractive.
 apply later_contractive'.
 apply const_HOcontractive.
Qed.

Lemma exists_contractive {A} `{ageable A} : forall B (X : pred A -> B -> pred A),
  (forall x, (contractive (fun y => X y x))) ->
  contractive (fun x => (exp (X x))).
Proof.
  unfold contractive; intros.
  apply sub_equ; apply sub_exp; intros.
  apply equ_sub; auto.
  apply equ_sub2; auto.
Qed.


Print const_HOcontractive.


Print Hint.
 intros ? ? ?.
 -> (X -> pred A)),
Search HOcontractive.

Print Hint.
 auto with contractive.




 auto 50 with contractive.
 auto 50 with contractive.
 do 3 red in H0.
Qed.

Lemma lseg_neq: forall p q: adr, p<>q -> 
        lseg p q = Ex y:adr, next p y *  |> lseg y q.
Proof.
 intros.
 apply pred_ext.
 rewrite lseg_unfold at 1.
 apply orp_left.
 apply andp_left2. apply exp_derives; intro y.
 apply sepcon_derives; auto.
 apply prop_andp_left; contradiction.
 rewrite (lseg_unfold p q). apply orp_right1.
 apply prop_andp_right; auto.
Qed.

Lemma lseg_eq: forall a, lseg a a = emp.
Proof.
 intros. rewrite lseg_unfold.
 apply pred_ext.
 apply orp_left.
 apply prop_andp_left; congruence.
 apply prop_andp_left; auto.
 apply orp_right2. apply prop_andp_right; auto. 
Qed.

Lemma lseg_cons: (* U2 *)
 forall x y z, x<>z -> next x y * lseg y z |-- lseg x z.
Proof.
 intros.
 pattern lseg at 1; rewrite lseg_unfold.
 apply orp_right1.
 apply prop_andp_right; auto.
 apply exp_right with y.
 apply sepcon_derives; auto.
 unfold lseg.
 apply now_later.
Qed.

Lemma lseg_neq_0:  forall y, lseg 0 y |-- !! (y=0).  (* W2 *)
Proof.
  intros. 
  rewrite lseg_unfold.
 apply orp_left.
 apply andp_left2.
 apply exp_left; intro v.
 rewrite next_gt_0.
 rewrite sepcon_andp_prop1.
 apply prop_andp_left; intro. inv H.
 apply andp_left1.
 intros w ?; hnf in *; auto.
Qed.

Lemma next_lseg:  (* U1 *)
  forall x y, x<>y ->  next x y |-- lseg x y.
Proof.
  intros.
  rewrite <- (sepcon_emp (next x _)).
  rewrite <- (lseg_eq y).
  eapply derives_trans; [ apply lseg_cons | ]; auto.
Qed.


Lemma mapsto_conflict:
   forall a b c, mapsto a b  *  mapsto a c |-- FF.
  Proof.
    intros. intros w  [w1 [w2 [? [? ?]]]]; hnf.
    specialize (H0 a). specialize (H1 a).
    rewrite if_true in * by auto.
    apply (resource_at_join _ _ _ a) in H.
    rewrite H0 in H; rewrite H1 in H; inv H.
    pfullshare_join.
 Qed.

Lemma next_conflict:  (*  W3 *)
   forall x y y', next x y * next x y' |-- FF.
Proof.
  unfold next; intros.
  eapply derives_trans; [ | apply (mapsto_conflict x y y')].
  apply sepcon_derives; apply andp_left2; auto.
Qed.

Lemma not_prop_right: forall P (Q: Prop), (Q -> P |-- FF) -> P |-- !! (not Q).
 Proof. intros. intros w ? ?. specialize (H H1 w H0); auto. 
  Qed.

 Lemma next_conflict_list: (* W4 *)
     forall x y z, next x y * lseg z 0 |-- !!(x<>z).
 Proof.
   intros.
   unfold next.
   rewrite lseg_unfold.
  rewrite sepcon_comm.
  rewrite distrib_orp_sepcon.
  apply orp_left.
  repeat rewrite sepcon_andp_prop1. 
  apply andp_left2.
  rewrite exp_sepcon1.
  apply exp_left; intro v. 
  rewrite sepcon_comm.
  rewrite <- sepcon_assoc.
  apply @derives_trans with (!! (x<>z) && TT * TT).
  apply sepcon_derives; auto.
  apply andp_right; auto. 
  apply not_prop_right; intros; subst; apply next_conflict.
  rewrite sepcon_andp_prop1.
  apply andp_left1; auto.
  rewrite sepcon_andp_prop1. rewrite emp_sepcon.
  apply prop_andp_left; intro.
  subst.
  unfold next.
  apply prop_andp_left; intro.
  intros ? ?; hnf; omega.
Qed.

Lemma lseg_W5: forall x y z,   (* W5 *)
    lseg x y * lseg x z |-- !!(x=y \/ x=z).
Proof.
  intros.
  destruct (eq_dec x y).
  apply prop_right; auto.
  destruct (eq_dec x z).
  apply prop_right; auto.
  rewrite (lseg_neq x y); auto.
  rewrite exp_sepcon1; apply exp_left; intro.
  rewrite (lseg_neq x z); auto.
  rewrite exp_sepcon2; apply exp_left; intro.
  rewrite sepcon_assoc. 
  rewrite <- (sepcon_assoc (|> _)).
  rewrite (sepcon_comm (|> _)).
  repeat rewrite <- sepcon_assoc. rewrite sepcon_assoc.
  eapply derives_trans. apply sepcon_derives. apply next_conflict. apply derives_refl.
  rewrite FF_sepcon. auto.
Qed.

(* This lemma is not currently used, 
    but it might be useful in a different proof of lseg_cons_in_mapsto_context, etc. *)
Lemma sepcon_andp_fash'1 {A}{JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A}:  
    forall (P: pred nat) (Q R : pred A),  fash' P && Q * R = fash' P && (Q * R).
 Proof.
  intros. apply pred_ext; intros w ?.
   destruct H as [w1 [w2 [? [? ?]]]].
   destruct H0. split.
   hnf in H0|-*. replace (level w) with (level w1); auto.
   apply join_level in H; intuition.
    exists w1; exists w2; split3; auto.
   destruct H.
   destruct H0 as [w1 [w2 [? [? ?]]]]; exists w1; exists w2; split3; auto.
   split; auto.
   hnf in H|-*. replace (level w1) with (level w); auto.
   apply join_level in H0; intuition.
Qed.

Lemma lseg_cons_in_next_context:   (*  U4 *)
    forall x y z v, lseg x y * next y z * next z v |-- lseg x z * next z v.
Proof.
  intros.
  apply @derives_trans with ((lseg x y * next y z) && (ewand (next z v) TT) *  next z v).
  intros w [w1 [w2 [? [ ? ?]]]]. exists w1; exists w2; split3; auto. split; auto.
  exists w2; exists w; split3; auto.
  apply sepcon_derives; auto.
  generalize (goedel_loeb (All x:adr,  
    lseg x y * next y z && ewand (next z v) TT >=> lseg x z) TT) ; intro.
  spec H.
  2:  intros w ?; apply (H (@level _ R.ag_rmap w) I x w (le_refl _)); auto.
  clear.
  apply allp_right; intro x.
  apply subp_i1.
  intros w [[_ ?] [? ?]].
  rewrite lseg_unfold. left.
  split.
  do 3 red. intro; subst x.
  clear - H0 H1.
  destruct H1 as [w1 [w2 [? [? _]]]].
  assert (app_pred (next z v * (lseg z y * next y z)) w2) by (do 2 eexists; split3; eauto).
  rewrite <- sepcon_assoc in H2.
  destruct H2 as [wa [wb [? [? ?]]]].
  assert (app_pred (lseg z y * (next y z * next z v)) w2).
  rewrite sepcon_comm.
  rewrite sepcon_assoc.
  exists wb; exists wa; split3; auto.
  clear - H5.
  rewrite (lseg_unfold z y) in H5.
  rewrite distrib_orp_sepcon in H5.
  destruct H5.
  repeat rewrite sepcon_andp_prop1 in H.
  destruct H as [_ H].
  repeat rewrite exp_sepcon1 in H.
  destruct H as [u ?].
  rewrite (sepcon_comm (next z u)) in H.
  rewrite sepcon_assoc in H.
  rewrite sepcon_comm in H.
  rewrite (sepcon_comm (next y z)) in H.
  rewrite <- sepcon_assoc in H.
  rewrite sepcon_assoc in H.
  destruct H as [w1 [w3 [? [? _]]]].
  apply next_conflict in H0; auto.
  rewrite sepcon_andp_prop1 in H. rewrite emp_sepcon in H.
  destruct H. hnf in H. subst y.
  apply next_conflict in H0; auto.
  rewrite lseg_unfold in H0.
  rewrite distrib_orp_sepcon in H0.
  destruct H0.
  repeat rewrite sepcon_andp_prop1 in H0.
  destruct H0.
  repeat rewrite exp_sepcon1 in H2.
  destruct H2 as [u H2].
  do 3 red in H0. exists u.
 rewrite later_allp in H.
  specialize (H u).
  rewrite sepcon_assoc in H2.
  destruct H2 as [w1 [w2 [? [? ?]]]].
  red in H. rewrite sub_later in H.
  specialize (H w2).
  spec H. apply join_level in H2; destruct H2; omega.
  exists w1; exists w2; split3; auto.
  apply H; auto.
  rewrite later_andp. split.
  rewrite later_sepcon.
  eapply sepcon_derives; try apply H4; auto.
  apply now_later.
  eapply now_later; eauto.
  clear - H2 H1.
  destruct H1 as [w3 [w4 [? [? _]]]].
  destruct (join_assoc H2 (join_com H)) as [f [? ?]].
  exists w3; exists f; split3; auto.
  exists z.
  rewrite lseg_eq.
  rewrite sepcon_andp_prop1 in H0.
  destruct H0. hnf in H0; subst y.
  rewrite sepcon_comm in H2.
  eapply sepcon_derives; try apply H2; auto.
  apply now_later.
Qed.

Lemma list_append:  (* U3 *)
   forall x y, lseg x y * lseg y 0 |-- lseg x 0.
Proof.
 intros.
  generalize (goedel_loeb (All x:adr, lseg x y * lseg y 0  >=> lseg x 0) TT) ; intro.
  spec H; [ clear  | intros w ?; apply (H (@level _ R.ag_rmap w) I x w (le_refl _)); auto].
  apply andp_left2.
  apply allp_right; intro x.
  apply subp_i1.
  intros w [? ?].
  destruct (eq_dec x 0).
  subst. rewrite lseg_eq.
  rewrite lseg_unfold in H0.
  rewrite distrib_orp_sepcon in H0.
  destruct H0.
  rewrite sepcon_andp_prop1 in H0. destruct H0.
  rewrite exp_sepcon1 in H1.
  destruct H1 as [u ?]. unfold next in H1.
  repeat rewrite sepcon_andp_prop1 in H1.
  destruct H1 as [H1 _]; hnf in H1. inv H1. 
  rewrite sepcon_andp_prop1 in H0. destruct H0. hnf in H0. subst.
  rewrite lseg_eq in H1. rewrite sepcon_emp in H1. auto.
  rewrite (lseg_unfold x y) in H0.
  rewrite distrib_orp_sepcon in H0.
  destruct H0.
  rewrite sepcon_andp_prop1 in H0. destruct H0.
  rewrite exp_sepcon1 in H1.
  destruct H1 as [z H1].
  rewrite lseg_neq; auto.
  exists z.
  rewrite sepcon_assoc in H1.
  rewrite later_allp in H.
  specialize (H z).
  destruct H1 as [w1 [w2 [? [? ?]]]].
  red in H. rewrite sub_later in H.
  specialize (H w2).
  spec H. apply join_level in H1; destruct H1; omega.
  exists w1; exists w2; split3; auto.
  apply H; auto.
  rewrite later_sepcon.
  eapply sepcon_derives; try apply H3; auto.
  apply now_later.
  rewrite sepcon_andp_prop1 in H0.
  destruct H0. hnf in H0; subst y. rewrite emp_sepcon in H1; auto.
Qed.

Lemma lseg_U5:
    forall x y z w, z<>w -> lseg x y * next y z * lseg z w |-- lseg x z * lseg z w.
Proof.
 intros.
 rewrite (lseg_neq z w); auto.
 repeat rewrite exp_sepcon2.
 apply exp_derives; intro v.
 repeat rewrite <- sepcon_assoc.
 apply sepcon_derives; auto.
 apply lseg_cons_in_next_context.
Qed.

Lemma lseg_cons_in_list_context: 
    forall x y z, lseg x y * next y z * lseg z 0 |-- lseg x z * lseg z 0.
Proof.
  intros.
  destruct (eq_dec z 0).
  subst. rewrite lseg_eq. repeat  rewrite sepcon_emp. 
  eapply derives_trans; try apply list_append.
  apply sepcon_derives; eauto.
  rewrite next_gt_0.
  apply prop_andp_left; intro.
  apply next_lseg; omega.
  apply lseg_U5; auto.
Qed.

