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
  intros; apply PTree.extensionality; intros.
  rewrite PTree.gmap1.
  destruct (t ! i); auto.
Qed.
Lemma map_map1:
  forall {A B} f m,
    @PTree.map1 A B f m = PTree.map (fun _=> f) m.
Proof.
  intros; apply PTree.extensionality; intros.
  rewrite PTree.gmap1, PTree.gmap; reflexivity.
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


(*Lemma xmap_compose:
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
Qed.*)

Lemma trivial_ptree_map:
  forall {A} t F,
    (forall b f, t ! b = Some f -> F b f = f) ->
    @PTree.map A A F t = t.
Proof.
  intros; apply PTree.extensionality; intros.
  rewrite PTree.gmap.
  destruct (t ! i) eqn: Hi; [simpl | reflexivity].
  rewrite H; auto.
Qed.

Lemma max_maximum : forall l, Forall (Pos.ge (fold_right Pos.max 1 l))%positive l.
Proof.
  induction l; auto.
  constructor; simpl.
  - lia.
  - eapply Forall_impl, IHl; lia.
Qed.

Lemma finite_ptree:
  forall {A} (t:PTree.t A), exists b, forall b', (b < b')%positive -> (t ! b') = None.
Proof.
  intros.
  exists (fold_right Pos.max 1 (map fst (PTree.elements t)))%positive; intros.
  destruct (t ! b') eqn: Hb'; [|auto].
  apply PTree.elements_correct in Hb'.
  pose proof (max_maximum (map fst (PTree.elements t))) as Hmax.
  rewrite Forall_forall in Hmax; specialize (Hmax b').
  lapply Hmax; [lia|].
  rewrite in_map_iff; do 2 eexists; eauto; auto.
Qed.

Infix "++":= seq.cat.