Require Import msl.msl_standard.
Require Import msl.Coqlib2.
Require Import veric.seplog.
Require Import veric.normalize.
Require veric.compcert_rmaps.
Require Import compcert.Ctypes.

Local Open Scope pred.

Definition rmap := compcert_rmaps.RML.R.rmap.
Definition valt := (val * type)%type.

Definition val_mapsto (sh: Share.t) (v1: val) (t: type) (v2: val) : pred rmap :=
 match access_mode t with
 | By_value ch =>  address_mapsto ch v2 (unrel Lsh sh) (unrel Rsh sh) (val2adr' v1)
 | _ => FF
 end.

Fixpoint type_of_field (f: fieldlist) (fld: ident) : type :=
 match f with
 | Fnil => Tvoid
 | Fcons i t fl => if eq_dec i fld then t else type_of_field fl fld
 end.

Definition field_of (vt: valt) (fld: ident) : valt :=
 match vt with
 | (Vptr l ofs, Tstruct id fList att) =>
         match field_offset id fList with 
         | Errors.OK delta => (Vptr l (Int.add ofs (Int.repr delta)), type_of_field fList fld)
         | _ => (Vundef, Tvoid)
         end
  | _ => (Vundef, Tvoid)
 end.

Definition field_mapsto (sh: Share.t) (v1: val*type) (fld: ident) (v2: valt) : pred rmap :=
 match v1 with
  | (Vptr l ofs, Tstruct id fList  att) =>
    let t2 := type_of_field fList fld in
     match field_offset fld fList, access_mode t2 with
     | Errors.OK delta, By_value ch => 
          !! (snd v2 = t2) && 
           address_mapsto ch (fst v2) (unrel Lsh sh) (unrel Rsh sh)  (l, Int.unsigned ofs + delta)
     | _, _ => FF
     end
  | _  => FF
  end.

Fixpoint fields_mapto_aux (sh: Share.t) (v1: val*type) (flds: fieldlist) (v2: list (valt)) : pred rmap :=
  match flds, v2 with
  | Fnil, nil => emp
  | Fcons i t flds', vt::v2' => field_mapsto sh v1 i vt * fields_mapto_aux sh v1 flds' v2'
  | _, _ => FF
  end.

Definition fields_mapto (sh: Share.t) (v1: valt) (v2: list (valt)) : pred rmap :=
  match snd v1 with
  | Tstruct id fList  att =>
         fields_mapto_aux sh v1 fList v2
  | _  => FF
  end.

Definition next (fld: ident) (v1 v2: valt) : pred rmap := 
 !! (bool_val (fst v1) (snd v1) = Some true) && field_mapsto Share.top v1 fld v2.

Lemma next_nonnull: 
  forall fld x y, next fld x y = !! (bool_val (fst x) (snd x) = Some true) && next fld x y.
Proof.
 intros. unfold next.
 rewrite <- andp_assoc. f_equal. rewrite andp_dup. auto.
Qed.

Definition nullval : val := Vint Int.zero.

Lemma next_neq_0: forall fld t y, next fld (nullval,t) y |-- FF.   (* W1 *)
Proof.
 intros. 
 intros ? [? ?].
 hnf in H.  simpl in H. destruct t; discriminate.
Qed.

Definition listcons' (fld: ident) (R: (valt * valt) -> pred rmap) (lp: valt * valt) : pred rmap :=
      !! (fst lp <> snd lp) && Ex tail:valt, next fld (fst lp) tail * |> R (tail, snd lp).

Definition listempty (lp: valt*valt) : pred rmap :=
             !! (fst lp = snd lp) && emp.
 
Definition listrep' fld (R: valt*valt -> pred rmap) (lp: valt*valt) : pred rmap :=
        listcons' fld R lp || listempty lp.

Definition listrep (fld: ident):  valt*valt -> pred rmap := HORec (listrep' fld).

XXXXX.
done to here.  The rest of this file is from the version in msl/examples/cont/lseg.v

Definition lseg (e1 e2: adr) : pred rmap := listrep (e1,e2).

Lemma lseg_unfold: forall e1 e2, 
   (lseg e1 e2 = (!! (e1<> e2)  && Ex tail:adr, next e1 tail * |> lseg tail e2)
                        || (!! (e1=e2) && emp))%pred.
Proof.
 intros.
 unfold lseg. unfold listrep at 1.
 rewrite HORec_fold_unfold. reflexivity.
 auto 50 with contractive.
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

