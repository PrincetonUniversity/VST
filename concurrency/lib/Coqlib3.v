Require Import Omega.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import VST.concurrency.lib.tactics.

From mathcomp.ssreflect Require Import seq.

Lemma cat_app:
  forall {T} (l1 l2:list T),
    seq.cat l1 l2 = app l1 l2.
Proof. intros. induction l1; eauto. Qed.
Lemma trivial_map1:
  forall {A} (t : PTree.t A),
    PTree.map1 (fun (a : A) => a) t = t.
Proof.
  intros ? t; induction t; auto.
  simpl; f_equal; eauto.
  destruct o; reflexivity.
Qed.
Lemma map_map1:
  forall {A B} f m,
    @PTree.map1 A B f m = PTree.map (fun _=> f) m.
Proof.
  intros. unfold PTree.map.
  remember 1%positive as p eqn:Heq.
  clear Heq; revert p.
  induction m; try reflexivity.
  intros; simpl; rewrite <- IHm1.
  destruct o; simpl; (*2 goals*)
    rewrite <- IHm2; auto.
Qed.
Lemma trivial_map:
  forall {A} (t : PTree.t A),
    PTree.map (fun (_ : positive) (a : A) => a) t = t.
Proof.
  intros; rewrite <- map_map1; eapply trivial_map1.
Qed.


Definition merge_func {A} (f1 f2:Z -> option A):
  (BinNums.Z -> option A):=
  fun ofs => if f1 ofs then f1 ofs else f2 ofs.


Lemma xmap_compose:
  forall A B C t f1 f2 p,
    @PTree.xmap B C f2 (@PTree.xmap A B f1 t p) p =
    (@PTree.xmap A C (fun p x => f2 p (f1 p x)) t p).
Proof. induction t.
       - reflexivity.
       - simpl; intros; f_equal.
         + eapply IHt1.
         + destruct o; reflexivity.
         + eapply IHt2.
Qed.


Lemma xmap_step:
  forall {A B} t f p,
    @PTree.xmap A B f t p =
    PTree.xmap (fun b => f (PTree.prev_append p b)) t 1.
Proof.
  intros A B t; induction t.
  - reflexivity.
  - intros; simpl; f_equal.
    + rewrite IHt1; symmetry.
      rewrite IHt1; f_equal.
    + rewrite IHt2; symmetry.
      rewrite IHt2; f_equal.
Qed.

Lemma trivial_ptree_map:
  forall {A} t F,
    (forall b f, t ! b = Some f -> F b f = f) ->
    @PTree.map A A F t = t.
Proof.
  intros ? ?.
  unfold PTree.map.
  (* remember 1%positive as p eqn:HH; clear HH; revert p.*)
  induction t; try reflexivity.
  unfold PTree.map; simpl.
  intros. f_equal.
  - intros.
    erewrite xmap_step.
    erewrite <- IHt1 at 2.
    reflexivity.
    intros; simpl. rewrite H; auto.
  - destruct o; eauto.
  - f_equal. eapply H; eauto.
  - intros. erewrite xmap_step.
    erewrite <- IHt2 at 2.
    reflexivity.
    intros; simpl. rewrite H; auto.
Qed.


Lemma finite_ptree:
  forall {A} (t:PTree.t A), exists b, forall b', (b < b')%positive -> (t ! b') = None.
Proof.
  intros ? t; induction t.
  - exists xH; intros; simpl. eapply PTree.gleaf.
  - normal_hyp.
    exists (Pos.max (x0~0) (x~1)); intros.
    destruct b'; simpl;
      first [eapply H0| eapply H| idtac].
    + cut (x~1 <  b'~1)%positive.
      * unfold Pos.lt, Pos.compare in *; auto.
      * eapply Pos.max_lub_lt_iff in H1 as [? ?].
        auto.
    + cut (x0~0 <  b'~0)%positive.
      * unfold Pos.lt, Pos.compare in *; auto.
      * eapply Pos.max_lub_lt_iff in H1 as [? ?]; auto.
    + exfalso. eapply Pos.nlt_1_r; eassumption.
Qed.

Infix "++":= seq.cat.