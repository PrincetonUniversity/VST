Require Import Coqlib.
Require Import Maps.

Section FINITE.

Variable A: Type.

Lemma ptree_finite:
  forall (t: PTree.t A), exists p, forall n, (p <= n)%positive -> PTree.get n t = None.
Proof.
  induction t.
- (* Leaf case *)
  exists 1%positive; intros. apply PTree.gempty. 
- (* Node case *)
  destruct IHt1 as [p1 N1]. destruct IHt2 as [p2 N2].
  exists (Pos.max (xO p1) (xI p2)); intros.
  destruct n; simpl.
  apply N2. zify; omega. 
  apply N1. zify; omega.
  zify; omegaContradiction.
Qed.

Lemma pmap_finite:
  forall (m: PMap.t A), exists p, forall n, (p <= n)%positive -> PMap.get n m = fst m.
Proof.
  intros. destruct m as [dfl t]; simpl.
  destruct (ptree_finite t) as [p N].
  exists p; intros. unfold PMap.get. simpl. rewrite N; auto. 
Qed. 

Lemma pmap_construct:
  forall (f: positive -> A) hi dfl,
  (forall n, (n >= hi)%positive -> f n = dfl) ->
  exists m: PMap.t A, forall n, PMap.get n m = f n.
Proof.
  intros until dfl; intros OUTSIDE.
  assert (REC: forall x, (x <= hi)%positive ->
          exists m, forall n, (n < x \/ n >= hi)%positive -> 
                    PMap.get n m = f n).
  {
    intros x0; pattern x0.
    apply Pos.peano_rect; intros.
    exists (PMap.init dfl). intros. rewrite PMap.gi.
      destruct H0. xomega.
      symmetry. apply OUTSIDE. assumption. 
  - (* Inductive case *)
    assert (HP: (p <= hi)%positive). xomega.
    destruct (H HP) as [m P]. clear H HP.
    exists (PMap.set p (f p) m); intros.
    rewrite PMap.gsspec.
    destruct (peq n p). 
    congruence.
    apply P. destruct H. left. xomega. right; assumption. 
  }
  destruct (REC hi) as [m P]. xomega. 
  exists m; intros. apply P. xomega.
Qed.

Lemma zmap_finite:
  forall (m: ZMap.t A), exists lo, exists hi, forall n, n < lo \/ n > hi -> ZMap.get n m = fst m.
Proof.
  intros.
  destruct (pmap_finite m) as [p D].
  exists (-2 * Z.pos p); exists (2 * Z.pos p); intros.
  unfold ZMap.get. apply D. 
  unfold ZIndexed.index. destruct n; zify; omega. 
Qed.

Require Import Zwf.

Lemma zmap_construct:
  forall (f: Z -> A) lo hi dfl,
  (forall n, n < lo \/ n > hi -> f n = dfl) ->
  exists m: ZMap.t A, forall n, ZMap.get n m = f n.
Proof.
  intros until dfl; intros OUTSIDE.
  assert (REC: forall x, x <= hi ->
          exists m, forall n, n <= x \/ n > hi -> ZMap.get n m = f n).
  {
    intros x0; pattern x0; apply (well_founded_ind (Zwf_well_founded lo)); intros.
    destruct (zlt x lo).
  - (* Base case *)
    exists (ZMap.init dfl). intros. rewrite ZMap.gi. symmetry. apply OUTSIDE. omega. 
  - (* Inductive case *)
    destruct (H (x - 1)) as [m P].
    red. omega. omega. 
    exists (ZMap.set x (f x) m); intros.
    rewrite ZMap.gsspec. unfold ZIndexed.eq. destruct (zeq n x). 
    congruence.
    apply P. omega. 
  }
  destruct (REC hi) as [m P]. omega. 
  exists m; intros. apply P. omega.
Qed.

End FINITE.

Section FINITE_CONSTRUCTIVE.

Variable A: Type.

Fixpoint p_tree_finite_c (t: PTree.t A) : positive :=
  match t with
    PTree.Leaf => 1%positive
  | PTree.Node l _ r => Pos.max (xO (p_tree_finite_c l)) (xI (p_tree_finite_c r))
  end.

Lemma ptree_finite_c_sound:
  forall (t: PTree.t A) n, ((p_tree_finite_c t) <= n)%positive -> PTree.get n t = None.
Proof.
  induction t.
- (* Leaf case *)
  simpl. intros. apply PTree.gempty. 
- (* Node case *)
  (*destruct IHt1 as [p1 N1]. destruct IHt2 as [p2 N2].
  exists (Pos.max (xO p1) (xI p2));*)
  intros.
  destruct n; simpl in *.
  apply IHt2. zify; omega. 
  apply IHt1. zify; omega. 
  zify; omegaContradiction.
Qed.

Definition pmap_finite_c (m: PMap.t A) : positive :=
           p_tree_finite_c (snd m). 

Lemma pmap_finite_sound_c:
  forall (m: PMap.t A) n, ((pmap_finite_c m) <= n)%positive -> PMap.get n m = fst m.
Proof.
  intros. unfold pmap_finite_c in H. 
  destruct m as [dfl t]; simpl in *.
  unfold PMap.get. simpl.
  rewrite (ptree_finite_c_sound _ _ H); trivial.
Qed. 

Definition REC_p (f: positive -> A) (hi:positive) (dfl:A)
  (OUTSIDE: forall n, (n >= hi)%positive -> f n = dfl):
 forall x, (x <= hi)%positive ->
   {m: PMap.t A | fst m = dfl /\ 
                  forall n, (n < x \/ n >= hi)%positive -> 
                            PMap.get n m = f n}.
Proof. 
    intros x0; pattern x0.
    apply Pos.peano_rect; intros.
    exists (PMap.init dfl). simpl.
    split; trivial.
    intros. rewrite PMap.gi.
      destruct H0. xomega.
      symmetry. apply OUTSIDE. assumption. 
  - (* Inductive case *)
    assert (HP: (p <= hi)%positive). xomega.
    destruct (X HP) as [m [PDef P]]. clear X HP.
    exists (PMap.set p (f p) m); simpl.
    split; trivial.
    intros. rewrite PMap.gsspec.
       destruct (peq n p). 
       congruence.
       apply P. destruct H0. left. xomega. right; assumption. 
Defined.

Definition pmap_construct_c
          (f: positive -> A) hi dfl
          (OUTSIDE: forall n, (n >= hi)%positive -> f n = dfl):
   {m: PMap.t A | fst m = dfl /\ 
                  forall n, PMap.get n m = f n}.
Proof.
 destruct (REC_p f hi dfl OUTSIDE hi) as [m [PDef P]].
   xomega.
   exists m.
   split; trivial.
   intros. apply P. xomega.
Defined. 

(*I'd really like to replace dfl hi with dfl n in OUTSIDE, 
 so that unreachable elements can have different defaults -- but
  what should I replace fst m = dfl hi with then?*)
Definition REC_d (f: positive -> A) (hi:positive) (dfl:positive -> A)
  (OUTSIDE: forall n, (n >= hi)%positive -> f n = dfl hi):
 forall x, (x <= hi)%positive ->
   {m: PMap.t A | fst m = (dfl hi) /\ 
                  forall n, (n < x \/ n >= hi)%positive -> 
                            PMap.get n m = f n}.
Proof. 
    intros x0; pattern x0.
    apply Pos.peano_rect; intros.
    exists (PMap.init (dfl hi)). simpl.
    split; trivial.
    intros. rewrite PMap.gi.
      destruct H0. xomega.
      symmetry. apply OUTSIDE. assumption. 
  - (* Inductive case *)
    assert (HP: (p <= hi)%positive). xomega.
    destruct (X HP) as [m [PDef P]]. clear X HP.
    exists (PMap.set p (f p) m); simpl.
    split; trivial.
    intros. rewrite PMap.gsspec.
       destruct (peq n p). 
       congruence.
       apply P. destruct H0. left. xomega. right; assumption. 
Defined.

Definition pmap_construct_dep
          (f: positive -> A) hi (dfl : positive -> A)
          (OUTSIDE: forall n, (n >= hi)%positive -> f n = dfl hi):
   {m: PMap.t A | fst m = dfl hi /\ 
                  forall n, PMap.get n m = f n}.
Proof.
 destruct (REC_d f hi dfl OUTSIDE hi) as [m [PDef P]].
   xomega.
   exists m.
   split; trivial.
   intros. apply P. xomega.
Defined. 

Definition zmap_finite_c (m: ZMap.t A): Z * Z :=
  (-2 * Z.pos (pmap_finite_c m), 2 * Z.pos (pmap_finite_c m)).

Lemma zmap_finite_sound_c:
  forall (m: ZMap.t A) lo hi, zmap_finite_c m = (lo,hi) ->
    forall n, n < lo \/ n > hi -> ZMap.get n m = fst m.
Proof.
  intros. 
  assert (D:= pmap_finite_sound_c m).
  unfold zmap_finite_c in H. inv H.
  unfold ZMap.get. apply D. 
  unfold ZIndexed.index. destruct n; zify; omega.
Qed. 

Definition REC (f: Z -> A) (lo hi:Z) (dfl:A)
  (OUTSIDE: forall n, n < lo \/ n > hi -> f n = dfl):
 forall x,
  x <= hi -> {m: ZMap.t A | fst m = dfl /\ forall n, n <= x \/ n > hi -> ZMap.get n m = f n}.
intros x0; pattern x0.
apply (well_founded_induction_type (Zwf_well_founded lo)); intros.
    destruct (zlt x lo).
  - (* Base case *)
     exists (ZMap.init dfl).
      split. reflexivity.
      intros. rewrite ZMap.gi.
              symmetry. apply OUTSIDE. omega.
  - (* Inductive case *)
    destruct (X (x - 1)) as [m [Pdef P]].
    red. omega. omega. 
    exists (ZMap.set x (f x) m); intros.
    simpl.
    split; trivial.
    intros. rewrite ZMap.gsspec. unfold ZIndexed.eq.
    destruct (zeq n x). 
           congruence.
           apply P. omega.
Defined.

Definition zmap_construct_c
    (f: Z -> A) (lo hi:Z) (dfl:A)
    (OUTSIDE: forall n, n < lo \/ n > hi -> f n = dfl) : 
  { m : ZMap.t A | fst m = dfl /\ forall n,  ZMap.get n m = f n}. 
 destruct (REC f lo hi dfl OUTSIDE hi) as [m [PDef P]].
   omega.
   exists m. split; trivial. intros. apply P. omega.
Defined. 

End FINITE_CONSTRUCTIVE.

