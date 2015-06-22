Require Import floyd.base.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.


Open Scope Z.

Section ZLIST.

Fixpoint force_lengthn {A} n (xs: list A) (default: A) :=
  match n, xs with
  | O, _ => nil
  | S n0, nil => default :: force_lengthn n0 nil default
  | S n0, hd :: tl => hd :: force_lengthn n0 tl default
  end.

Fixpoint list_gen {A} lo (n: nat) (f: Z -> A) : list A :=
  match n with
  | O => nil
  | S n0 => f lo :: list_gen (lo + 1) n0 f
  end.

Class Zlist (A: Type) (default: A) : Type := mkZlist {
  zlist: Z -> Z -> Type;
  zl_constr': forall lo hi, list A -> zlist lo hi;
  zl_concat: forall {lo mid hi}, zlist lo mid -> zlist mid hi -> zlist lo hi;
  zl_sublist: forall {lo hi} lo' hi', zlist lo hi -> zlist lo' hi';
  zl_shift: forall {lo hi} lo' hi', zlist lo hi -> zlist lo' hi';
  zl_gen: forall lo hi (f: Z -> A), zlist lo hi;
  zl_singleton: forall i, A -> zlist i (i + 1);
  zl_empty: forall i, zlist i i;
  zl_default: forall lo hi, zlist lo hi;
  zl_nth: forall {lo hi}, Z -> zlist lo hi -> A
}.

Global Arguments zlist A {_} {_} _ _.

Instance list_zlist (A: Type) (default: A) : Zlist A default.
  apply (mkZlist A default (fun _ _ => list A)).
  + exact (fun _ _ l => l).
  + exact (fun lo mid hi l1 l2 =>
             if zle lo mid
             then force_lengthn (nat_of_Z (mid - lo)) l1 default ++ l2
             else skipn (nat_of_Z (mid - lo)) l2).
  + exact (fun lo hi  lo' hi' l => if zle lo lo' then skipn (nat_of_Z (lo' - lo)) l else nil).
  + exact (fun lo hi  lo' hi' l => l).
  + exact (fun lo hi f => list_gen lo (nat_of_Z (hi - lo)) f).
  + exact (fun i v => v :: nil).
  + exact (fun _ => nil).
  + exact (fun _ _ => nil).
  + exact (fun lo hi i l => if zle lo i then Znth (i - lo) l default else default).
Defined.

Definition zl_equiv {A d} `{Zlist A d} {lo hi} (l1 l2: zlist A lo hi) : Prop :=
  forall i, lo <= i < hi -> zl_nth i l1 = zl_nth i l2.

Notation "A '===' B" := (zl_equiv A B) (at level 80, no associativity).

Definition zl_equiv1 {A d} `{Zlist A d} {lo hi lo' hi'} (f1 f2: zlist A lo' hi' -> zlist A lo hi) : Prop :=
  forall l, f1 l === f2 l.

Class Zlist_Correct {A d} `(Zlist A d) : Type := mkZlistCorrect {
  zl_constr'_correct:
    forall lo hi i (l: list A),
    lo <= i < hi ->
    zl_nth i (zl_constr' lo hi l) = Znth (i - lo) l d;
  zl_concat_correct:
    forall lo mid hi i (l1: zlist A lo mid) (l2: zlist A mid hi),
    lo <= i < hi ->
    zl_nth i (zl_concat l1 l2) = if zlt i mid then zl_nth i l1 else zl_nth i l2;
  zl_sublist_correct:
    forall lo hi lo' hi' i (l: zlist A lo hi),
    lo <= lo' ->
    lo' <= i < hi' ->
    hi' <= hi ->
    zl_nth i (zl_sublist lo' hi' l) = zl_nth i l;
  zl_shift_correct:
    forall lo hi lo' hi' i (l: zlist A lo hi) mv,
    lo - lo' = mv ->
    hi - hi' = mv ->
    lo' <= i < hi' ->
    zl_nth i (zl_shift lo' hi' l) = zl_nth (i + mv) l;
  zl_gen_correct:
    forall lo hi f i,
    lo <= i < hi ->
    zl_nth i (zl_gen lo hi f) = f i;
  zl_singleton_correct:
    forall i v,
    zl_nth i (zl_singleton i v) = v;
  zl_default_correct:
    forall lo hi i,
    lo <= i < hi ->
    zl_nth i (zl_default lo hi) = d
}.

Instance list_zlist_correct (A: Type) (default: A) : Zlist_Correct (list_zlist A default).
split.
+ intros.
  simpl.
  if_tac; [| omega].
  reflexivity.
+ intros.
  simpl.
  destruct (zle lo mid). (* Normal case | Abnormal case *)
  - destruct (zlt i mid). (* left | right *)
    * if_tac; [| omega].
      admit.
    * if_tac; [| omega].
      if_tac; [| omega].
      admit.
  - admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
Defined.

Lemma zl_nth_LZ: forall {A d} i lo hi (l: @zlist A d (list_zlist _ _) lo hi),
  lo <= i < hi ->
  zl_nth i l = Znth (i - lo) l d.
Proof.
  intros.
  simpl.
  if_tac; [| omega].
  reflexivity.
Qed.

Lemma zl_concat_correct_l: forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} i lo mid hi (l1 : zlist A lo mid) (l2: zlist A mid hi),
  lo <= i < mid ->
  lo <= mid <= hi ->
  zl_nth i (zl_concat l1 l2) = zl_nth i l1.
Proof.
  intros.
  rewrite zl_concat_correct by omega.
  if_tac; auto.
  omega.
Qed.

Lemma zl_concat_correct_r: forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} i lo mid hi (l1 : zlist A lo mid) (l2: zlist A mid hi),
  mid <= i < hi ->
  lo <= mid <= hi ->
  zl_nth i (zl_concat l1 l2) = zl_nth i l2.
Proof.
  intros.
  rewrite zl_concat_correct by omega.
  if_tac; auto.
  omega.
Qed.

Lemma zl_concat_assoc:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo i1 i2 hi (l1: zlist A lo i1) (l2: zlist A i1 i2) (l3: zlist A i2 hi),
  lo <= i1 /\ i1 <= i2 /\ i2 <= hi ->
  zl_concat l1 (zl_concat l2 l3) === zl_concat (zl_concat l1 l2) l3.
Proof.
  unfold zl_equiv.
  intros.
  rewrite zl_concat_correct by omega.
  if_tac.
  + rewrite !zl_concat_correct by omega.
    if_tac; [| omega].
    if_tac; [| omega].
    auto.
  + rewrite !zl_concat_correct by omega.
    if_tac.
    - rewrite !zl_concat_correct by omega.
      if_tac; [omega |].
      auto.
    - auto.
Qed.

Lemma zl_sub_singleton':
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} i i' lo hi (l: zlist A lo hi),
  i = i' ->
  lo <= i < hi ->
  zl_equiv (zl_singleton i (zl_nth i' l))  (zl_sublist i (i + 1) l) .
Proof.
  intros.
  intro; intros. subst i'.
  assert (i = i0) by omega; subst.
  rewrite zl_sublist_correct by omega.
  rewrite zl_singleton_correct by omega.
  auto.
Qed.

Lemma zl_sub_singleton'':
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} i v,
  zl_equiv (zl_sublist i (i+1) (zl_singleton i v)) (zl_singleton i v).
Proof.
  intros.
  intro; intros.
  assert (i = i0) by omega; subst i0.
  rewrite zl_sublist_correct by omega. auto.
Qed.

Lemma zl_concat_sub:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo mid hi lo' hi' 
     (l: zlist A lo' hi'),
  lo' <= lo -> hi <= hi' ->
  lo <= mid <= hi ->
  zl_equiv (zl_concat (zl_sublist lo mid l) (zl_sublist mid hi l)) (zl_sublist lo hi l).
Proof.
  unfold zl_equiv.
  intros.
  rewrite zl_concat_correct by omega.
  if_tac; rewrite !zl_sublist_correct by omega; auto.
Qed.

(* old version, less general 
Lemma zl_concat_sub:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo mid hi (l: zlist A lo hi),
  lo <= mid <= hi ->
  zl_concat (zl_sublist lo mid l) (zl_sublist mid hi l) === l.
Proof.
  unfold zl_equiv.
  intros.
  rewrite zl_concat_correct by omega.
  if_tac; rewrite zl_sublist_correct by omega; auto.
Qed.
*)

Lemma zl_sub_self:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo hi (l: zlist A lo hi),
  lo <= hi ->
  zl_sublist lo hi l === l.
Proof.
  unfold zl_equiv.
  intros.
  rewrite zl_sublist_correct by omega; auto.
Qed.

Lemma zl_sub_sub:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo hi lo' hi' lo'' hi'' (l: zlist A lo hi),
  lo <= lo' <= lo'' ->
  hi'' <= hi' <= hi ->
  lo'' <= hi'' ->
  zl_sublist lo'' hi'' (zl_sublist lo' hi' l) === zl_sublist lo'' hi'' l.
Proof.
  unfold zl_equiv.
  intros.
  rewrite !zl_sublist_correct by omega; auto.
Qed.

Lemma zl_sub_concat_l:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo mid hi lo' hi' (l1: zlist A lo mid) (l2: zlist A mid hi),
  lo <= mid <= hi ->
  lo' <= hi' ->
  lo <= lo' ->
  hi' <= mid ->
  zl_sublist lo' hi' (zl_concat l1 l2) === zl_sublist lo' hi' l1.
Proof.
  unfold zl_equiv.
  intros.
  rewrite !zl_sublist_correct by omega.
  rewrite zl_concat_correct by omega.
  if_tac; [| omega].
  auto.
Qed.

Lemma zl_sub_concat_r:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo mid hi lo' hi' (l1: zlist A lo mid) (l2: zlist A mid hi),
  lo <= mid <= hi ->
  lo' <= hi' ->
  mid <= lo' ->
  hi' <= hi ->
  zl_sublist lo' hi' (zl_concat l1 l2) === zl_sublist lo' hi' l2.
Proof.
  unfold zl_equiv.
  intros.
  rewrite !zl_sublist_correct by omega.
  rewrite zl_concat_correct by omega.
  if_tac; [omega |].
  auto.
Qed.

Lemma zl_sub_concat_mid:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo mid hi lo' hi' (l1: zlist A lo mid) (l2: zlist A mid hi),
  lo <= mid <= hi ->
  lo' <= hi' ->
  lo <= lo' <= mid->
  mid <= hi' <= hi ->
  zl_sublist lo' hi' (zl_concat l1 l2) === zl_concat (zl_sublist lo' mid l1) (zl_sublist mid hi' l2).
Proof.
  unfold zl_equiv.
  intros.
  rewrite zl_concat_correct by omega.
  if_tac; rewrite !zl_sublist_correct by omega.
  + rewrite zl_concat_correct by omega.
    if_tac; [| omega].
    auto.
  + rewrite zl_concat_correct by omega.
    if_tac; [omega |].
    auto.
Qed.

Lemma zl_sub_singleton:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} i lo hi (l: zlist A lo hi),
  lo <= i < hi ->
  zl_equiv (zl_sublist i (i + 1) l) (zl_singleton i (zl_nth i l)).
Proof.
  intros.
  intro; intros.
  assert (i = i0) by omega; subst.
  rewrite zl_sublist_correct by omega.
  rewrite zl_singleton_correct by omega.
  auto.
Qed.

Lemma zl_sub_empty:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} i lo hi (l: zlist A lo hi),
  lo <= i <= hi ->
  zl_equiv (zl_sublist i i l) (zl_empty i).
Proof.
  intros.
  intro; intros; omega.
Qed.

Lemma zl_concat_empty_l:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo hi (l: zlist A lo hi),
  lo <= hi ->
  zl_equiv (zl_concat (zl_empty lo) l) l.
Proof.
  intros.
  intro; intros.
  rewrite zl_concat_correct by omega.
  if_tac; [omega |].
  auto.
Qed.

Lemma zl_concat_empty_r:
  forall {A} {d} {ZL: Zlist A d} `{@Zlist_Correct A d ZL} lo hi (l: zlist A lo hi),
  lo <= hi ->
  zl_equiv (zl_concat l (zl_empty hi)) l.
Proof.
  intros.
  intro; intros.
  rewrite zl_concat_correct by omega.
  if_tac; [| omega].
  auto.
Qed.

Instance Equiv_zl_equiv A d (ZL: Zlist A d) lo hi: Equivalence (@zl_equiv A d ZL lo hi).
  unfold zl_equiv.
  split.
  + intro; intros.
    reflexivity.
  + intro; intros.
    rewrite H by auto.
    reflexivity.
  + intro; intros.
    rewrite H, H0 by auto.
    reflexivity.
Defined.

Instance Proper_concat: forall A d (ZL: Zlist A d) `{@Zlist_Correct _ _ ZL} lo mid hi,
  Proper ((@zl_equiv A d ZL lo mid) ==> (@zl_equiv A d ZL mid hi) ==> (@zl_equiv A d ZL lo hi)) zl_concat.
Proof.
  unfold zl_equiv.
  intros; intro; intros; intro; intros.
  rewrite !zl_concat_correct by auto.
  if_tac.
  + apply H0; omega.
  + apply H1; omega.
Defined.

(* Example *)
Goal forall A d (ZL: Zlist A d) `{@Zlist_Correct _ _ ZL} (l1: zlist A 0 10) (l2: zlist A 10 20) (l3: zlist A 20 30),
  zl_sublist 5 25 (zl_concat l1 (zl_concat l2 l3)) ===
  zl_concat (zl_sublist 5 10 l1) (zl_concat l2 (zl_sublist 20 25 l3)).
Proof.
  intros.
  rewrite zl_sub_concat_mid by omega.
  rewrite zl_sub_concat_mid by omega.
  rewrite zl_sub_self by omega; reflexivity.
Qed.

End ZLIST.

Global Existing Instance list_zlist_correct.
Global Existing Instance Equiv_zl_equiv.
Global Existing Instance Proper_concat.
Global Opaque zl_concat. 
Global Opaque zl_sublist. 
Global Opaque zl_constr'.
Global Opaque zl_shift.
Global Opaque zl_gen.
Global Opaque zl_singleton.
Global Opaque zl_empty.
Global Opaque zl_default.
Global Opaque zl_nth.