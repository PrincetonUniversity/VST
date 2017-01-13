Require Import language.
Require Import msl.base.
Require Import msl.seplog.
Require Import msl.alg_seplog.
Require Import seplogic.
Require Import msl.Coqlib2.
Require Import msl.log_normalize.
Require Import msl.eq_dec.

Local Open Scope logic.


Declare Module Semax : SEMAX.
 (* Remark:  "Declare Module" is a hack.
  We want to emphasize that the client proofs (in lseg.v, client_lemmas.v,
   and sample_program.v) can be done independently of the
   model.v that implements the Module Semax.  The correct way to do
   this in Coq is to use a parameterized Module (that is, a Functor),
   which is not difficult but in this example we wanted to avoid
   a heavyweight use of the module system. *)

Import Semax.

Definition next e1 e2: mpred := !! (e1 > 0) && mapsto e1 e2.

Lemma next_gt_0:
  forall x y, next x y = !! (x>0) && next x y.
Proof.
 intros. unfold next.
 rewrite <- andp_assoc. f_equal. rewrite andp_dup. auto.
Qed.

Lemma next_neq_0: forall y, next 0 y |-- FF.   (* W1 *)
Proof.
 intros. rewrite next_gt_0. normalize. inv H.
Qed.

Definition listcons' (R: (adr * adr) -> mpred) (lp: adr * adr) : mpred :=
      !! (fst lp <> snd lp) && EX tail:adr, next (fst lp) tail * |> R (tail, snd lp).

Definition listempty (lp: adr*adr) : mpred :=
             !! (fst lp = snd lp) && emp.

Definition listrep' (R: adr*adr -> mpred) (lp: adr*adr) : mpred :=
        listcons' R lp || listempty lp.

Definition listrep : adr*adr -> mpred := HORec listrep'.

Definition lseg (e1 e2: adr) : mpred := listrep (e1,e2).

Lemma lseg_unfold: forall e1 e2,
   (lseg e1 e2 = (!! (e1<> e2)  && EX tail:adr, next e1 tail * |> lseg tail e2)
                        || (!! (e1=e2) && emp)).
Proof.
 intros.
 unfold lseg. unfold listrep at 1.
 rewrite HORec_fold_unfold. reflexivity.
 unfold listrep', listcons'.
 apply prove_HOcontractive. auto 50 with contractive typeclass_instances.
Qed.

Lemma lseg_neq: forall p q: adr, p<>q ->
        lseg p q = EX y:adr, next p y *  |> lseg y q.
Proof.
 intros.
 apply pred_ext.
 rewrite lseg_unfold at 1.
 apply orp_left.
 normalize. apply exp_right with tail. auto.
 normalize.
 normalize; intro y.
 rewrite (lseg_unfold p q). apply orp_right1.
 normalize. apply exp_right with y. normalize.
Qed.

Lemma lseg_eq: forall a, lseg a a = emp.
Proof.
 intros. rewrite lseg_unfold.
 apply pred_ext.
 apply orp_left.
 normalize.  congruence.
 normalize.
 apply orp_right2. normalize.
Qed.

Lemma lseg_cons: (* U2 *)
 forall x y z, x<>z -> next x y * lseg y z |-- lseg x z.
Proof.
 intros.
 pattern lseg at 1; rewrite lseg_unfold.
 apply orp_right1.
 normalize.
 apply exp_right with y.
 normalize.
 apply sepcon_derives; auto.
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
 normalize. inv H.
 normalize.
Qed.

Lemma next_lseg:  (* U1 *)
  forall x y, x<>y ->  next x y |-- lseg x y.
Proof.
  intros.
  rewrite <- (sepcon_emp (next x _)).
  rewrite <- (lseg_eq y).
  eapply derives_trans; [ apply lseg_cons | ]; auto.
Qed.


Lemma next_conflict:  (*  W3 *)
   forall x y y', next x y * next x y' |-- FF.
Proof.
  unfold next; intros.
  eapply derives_trans; [ | apply (mapsto_conflict x y y')].
  apply sepcon_derives; apply andp_left2; auto.
Qed.

 Lemma next_conflict_list: (* W4 *)
     forall x y z, next x y * lseg z 0 |-- !!(x<>z).
 Proof.
   intros.
  apply not_prop_right. intro; subst z.
   rewrite lseg_unfold.
  rewrite sepcon_comm.
  rewrite distrib_orp_sepcon.
  apply orp_left.
  normalize.
  rewrite sepcon_comm.
  rewrite <- sepcon_assoc.
  eapply derives_trans with (FF * TT).
  apply sepcon_derives; normalize.
  apply next_conflict.
  normalize.
  unfold next;   normalize.
  inv H.
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
  rewrite FF_sepcon. normalize.
Qed.

Lemma unfash_andp_distrib:
        forall {A}{ND: NatDed A}{IA: Indir A}{RA: RecIndir A} (P: Triv) (Q R: A),
               !P && (Q && R) = (!P && Q) && (!P && R).
Proof.
intros. apply pred_ext;  repeat apply andp_right.
apply andp_left1; auto. apply andp_left2; apply andp_left1; auto.
apply andp_left1; auto. apply andp_left2; apply andp_left2; auto.
apply andp_left1; auto. apply andp_left1; auto.
apply andp_left1; auto. apply andp_left2; auto.
apply andp_left2; auto. apply andp_left2; auto.
Qed.


Lemma lseg_cons_in_next_context:   (*  U4 *)
    forall x y z v, lseg x y * next y z * next z v |-- lseg x z * next z v.
Proof.
  intros.
  apply derives_trans with (((lseg x y * next y z) && (ewand (next z v) TT)) *  next z v).
  apply exclude_elsewhere.
  generalize (goedel_loeb (ALL x:adr,
    lseg x y * next y z && ewand (next z v) TT >=> lseg x z) TT) ; intro.
  spec H.
Focus 2.
  apply sepcon_derives; auto.
  apply subp_e.
  eapply derives_trans; [ apply H |].
  apply allp_left with x. auto.
  clear.
  apply allp_right; intro x.
  apply subp_i1.
  rewrite (lseg_unfold x z).
  apply orp_right1.
  apply andp_right.
  apply not_prop_right; intro; subst x.
  apply andp_left2.
  apply derives_trans with ((EX u:_, (next z u * TT)) && ewand (next z v) TT).
  apply andp_derives.
  rewrite lseg_unfold.
  rewrite distrib_orp_sepcon.
  apply orp_left; normalize.
  apply exp_right with tail. rewrite sepcon_assoc. apply sepcon_derives; normalize.
  apply exp_right with z. apply sepcon_TT. auto.
  normalize.
  apply ewand_conflict.
  rewrite sepcon_comm.
  rewrite <- sepcon_assoc.
  apply derives_trans with (FF * TT); [ | normalize].
  apply sepcon_derives; auto.
  apply next_conflict.

   normalize.
   match goal with |- ! ?P && _ |-- _ => remember P as S end.
   rewrite (lseg_unfold x y).
   rewrite andp_comm.
  rewrite distrib_orp_sepcon.
  rewrite distrib_orp_andp.
  rewrite distrib_orp_andp.
  apply orp_left. normalize. apply exp_right with tail.
  apply derives_trans with (next x tail * (|>lseg tail y * next y z && ewand (next z v) TT && !S)).
  rewrite andp_comm. rewrite <- andp_assoc.
  rewrite sepcon_assoc.
  rewrite unfash_sepcon_distrib.
  eapply derives_trans; [eapply ewand_TT_sepcon | ].
  apply sepcon_derives; auto.
  apply andp_left1. apply andp_left2; auto.
  subst S.
  apply andp_right. apply andp_right. apply andp_left1. apply andp_left2; auto.
  apply andp_left2; auto.
  apply andp_left1; auto. apply andp_left1;auto.
  apply sepcon_derives; auto.
  apply derives_trans with (|> (lseg tail y * next y z && ewand (next z v) TT) && !S).
  apply andp_derives; auto.
  repeat rewrite later_andp. rewrite later_sepcon.
  apply andp_derives; auto. apply sepcon_derives; auto.
   apply now_later. apply now_later.
  subst.
  rewrite <- later_unfash.
  rewrite <- later_andp. apply later_derives.
  apply derives_trans with (lseg tail y * next y z && ewand (next z v) TT &&
           !( lseg tail y * next y z && ewand (next z v) TT >=> lseg tail z)).
 apply andp_derives; auto.
 apply unfash_derives.
 apply allp_left with tail. auto.
 eapply derives_trans; [ eapply andp_derives; [ apply derives_refl | apply unfash_fash] | ].
 apply modus_ponens.
 normalize. apply exp_right with z.
 apply andp_left1. apply andp_left1.
 rewrite lseg_eq. apply derives_trans with (next x z * emp).
  rewrite sepcon_emp; auto. apply sepcon_derives; auto.
 apply now_later.
Qed.

 Lemma allp_andp1 {A}{NA: NatDed A}{B}: forall (any: B) (P: B -> A) Q,
   allp P && Q = ALL x:B, P x && Q.
Proof. intros. apply pred_ext. apply allp_right; intro x.
   apply andp_derives; auto. apply allp_left with x; auto.
   apply andp_right. apply allp_right; intro x; apply allp_left with x.
  apply andp_left1; auto. apply allp_left with any. apply andp_left2; auto.
Qed.


Lemma list_append:  (* U3 *)
   forall x y, lseg x y * lseg y 0 |-- lseg x 0.
Proof.
 intros.
  generalize (loeb (ALL x:adr, lseg x y * lseg y 0  >=> lseg x 0)) ; intro.
 apply subp_e.
  eapply derives_trans; [ apply H; clear H | apply allp_left with x; auto].
  apply allp_right; intro z.
  apply subp_i1.
  match goal with |- ! |> ?S' && _ |-- _ => remember S' as S end.
  rewrite (lseg_unfold z y).
  rewrite distrib_orp_sepcon.
  rewrite andp_comm.
  rewrite distrib_orp_andp.
  apply orp_left; normalize.
  apply derives_trans with (next z tail * |> (lseg tail y * lseg y 0) && !|>S).
  apply andp_derives; auto.
  rewrite sepcon_assoc; apply sepcon_derives; auto.
  rewrite later_sepcon; apply sepcon_derives; auto. apply now_later.
  rewrite (lseg_unfold z 0). apply orp_right1.
  apply andp_right.
  unfold next. normalize. apply prop_right. omega.
  apply exp_right with tail.
  rewrite andp_comm; rewrite unfash_sepcon_distrib.
  apply sepcon_derives. apply andp_left2; auto.
  rewrite <- later_unfash; rewrite <- later_andp; apply later_derives.
  subst. rewrite unfash_allp.
 rewrite allp_andp1; [ | apply 0].
 apply allp_left with tail.
 rewrite andp_comm.
 eapply derives_trans; [ eapply andp_derives; [ apply derives_refl | apply unfash_fash] | ].
 apply modus_ponens.
  apply andp_left1; auto.
Qed.

Lemma lseg_U5:
    forall x y z w, z<>w -> lseg x y * next y z * lseg z w |-- lseg x z * lseg z w.
Proof.
 intros.
 rewrite (lseg_neq z w); auto.
 repeat rewrite exp_sepcon2.
 normalize. intro v. apply exp_right with v.
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
  rewrite next_gt_0. normalize.
  apply next_lseg; omega.
  apply lseg_U5; auto.
Qed.

