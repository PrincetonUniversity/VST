Require Import VST.floyd.base2.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.jmeq_lemmas.
Require Export VST.floyd.fieldlist.
Require Export VST.floyd.compact_prod_sum.
Require Export VST.floyd.sublist.

Definition proj_struct (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (d: A (i, field_type i m)): A (i, field_type i m) :=
  proj_compact_prod (i, field_type i m) m v d member_dec.

Definition proj_union (i : ident) (m : members) {A: ident * type -> Type} (v: compact_sum (map A m)) (d: A (i, field_type i m)): A (i, field_type i m) :=
  proj_compact_sum (i, field_type i m) m v d member_dec.

Definition members_union_inj {m: members} {A} (v: compact_sum (map A m)) (it: ident * type): Prop :=
  compact_sum_inj v it member_dec.

Definition upd_sublist {X: Type} (lo hi: Z) (l: list X) (l0: list X) : list X :=
  firstn (Z.to_nat lo) l ++ l0 ++ skipn (Z.to_nat hi) l.

(* TODO: We should use the following two definition in replace_refill lemmas in the future. And avoid using compact prod/sum directly. *)

Definition upd_struct (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (v0: A (i, field_type i m)): compact_prod (map A m) :=
  upd_compact_prod _ v (i, field_type i m) v0 member_dec.

Definition upd_union (i : ident) (m : members) {A: ident * type -> Type} (v: compact_sum (map A m)) (v0: A (i, field_type i m)): compact_sum (map A m) :=
  upd_compact_sum _ v (i, field_type i m) v0 member_dec.

Lemma proj_struct_JMeq: forall (i: ident) (m : members) {A1 A2: ident * type -> Type} (v1: compact_prod (map A1 m)) (v2: compact_prod (map A2 m)) (d1: A1 (i, field_type i m)) (d2: A2 (i, field_type i m)),
  (forall i, in_members i m -> @eq Type (A1 (i, field_type i m)) (A2 (i, field_type i m))) ->
  members_no_replicate m = true ->
  in_members i m ->
  JMeq v1 v2 ->
  JMeq (proj_struct i m v1 d1) (proj_struct i m v2 d2).
Proof.
  intros.
  apply proj_compact_prod_JMeq; auto.
  + clear - H H0.
    intros.
    pose proof In_field_type _ _ H0 H1.
    destruct i as [i t].
    simpl fst in H2; simpl snd in H2.
    rewrite <- H2.
    apply H; auto.
    apply List.in_map with (f := fst) in H1.
    auto.
  + apply in_members_field_type; auto.
Qed.

Lemma members_union_inj_JMeq: forall (m : members) {A1 A2: ident * type -> Type} (v1: compact_sum (map A1 m)) (v2: compact_sum (map A2 m)),
  (forall i, in_members i m -> @eq Type (A1 (i, field_type i m)) (A2 (i, field_type i m))) ->
  members_no_replicate m = true ->
  JMeq v1 v2 ->
  (forall it, members_union_inj v1 it <-> members_union_inj v2 it).
Proof.
  intros.
  apply compact_sum_inj_JMeq; auto.
  intros [? ?] ?.
  specialize (H i).
  spec H.
  + change i with (fst (i, t)).
    apply in_map.
    auto.
  + apply In_field_type in H2; auto.
    simpl snd in H2.
    rewrite <- H2; simpl fst.
    auto.
Qed.

Lemma proj_union_JMeq: forall (i: ident) (m : members) {A1 A2: ident * type -> Type} (v1: compact_sum (map A1 m)) (v2: compact_sum (map A2 m)) (d1: A1 (i, field_type i m)) (d2: A2 (i, field_type i m)),
  (forall i, in_members i m -> @eq Type (A1 (i, field_type i m)) (A2 (i, field_type i m))) ->
  members_no_replicate m = true ->
  members_union_inj v1 (i, field_type i m) ->
  JMeq v1 v2 ->
  JMeq (proj_union i m v1 d1) (proj_union i m v2 d2).
Proof.
  intros.
  apply proj_compact_sum_JMeq; auto.
  + clear - H H0.
    intros.
    pose proof In_field_type _ _ H0 H1.
    destruct i as [i t].
    simpl fst in H2; simpl snd in H2.
    rewrite <- H2.
    apply H; auto.
    apply List.in_map with (f := fst) in H1.
    auto.
Qed.


