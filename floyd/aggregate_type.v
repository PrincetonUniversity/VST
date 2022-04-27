Require Import VST.floyd.base2.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.jmeq_lemmas.
Require Export VST.floyd.fieldlist.
Require Export VST.floyd.compact_prod_sum.
Require Export VST.zlist.sublist.

Definition proj_struct (i : ident) (m : members) {A: member -> Type} (v: compact_prod (map A m)) 
    (d: A (get_member i m)): A (get_member i m) :=
  proj_compact_prod (get_member i m) m v d member_dec.

Definition proj_union (i : ident) (m : members) {A: member -> Type} (v: compact_sum (map A m)) 
   (d: A (get_member i m)): A (get_member i m) :=
  proj_compact_sum (get_member i m) m v d member_dec.

Definition members_union_inj {m: members} {A} (v: compact_sum (map A m)) (it: member): Prop :=
  compact_sum_inj v it member_dec.

(* TODO: We should use the following two definition in replace_refill lemmas in the future. And avoid using compact prod/sum directly. *)

Definition upd_struct (i : ident) (m : members) {A: member -> Type} (v: compact_prod (map A m)) 
   (v0: A (get_member i m)): compact_prod (map A m) :=
  upd_compact_prod _ v (get_member i m) v0 member_dec.

Definition upd_union (i : ident) (m : members) {A: member -> Type} (v: compact_sum (map A m)) 
   (v0: A (get_member i m)): compact_sum (map A m) :=
  upd_compact_sum _ v (get_member i m) v0 member_dec.

Lemma get_member_name: forall a m,
  members_no_replicate m = true ->
  In a m ->
  get_member (name_member a) m = a.
Proof.
 intros.
 unfold members_no_replicate in H.
 apply compute_list_norepet_e in H.
 induction m.
 inv H0.
 simpl in H. inv H.
  destruct H0.
 subst. simpl. rewrite if_true by auto. auto.
 simpl. rewrite if_false; auto.
 contradict H3.
 rewrite <- H3.
 apply in_map. auto.
Qed.

Lemma in_get_member:
  forall i m,
   in_members i m ->
   In (get_member i m) m.
Proof.
intros.
 induction m.
 inv H.
 simpl in *.
  if_tac. auto.
  destruct H. subst. contradiction.
  right. auto.
Qed.
 

Lemma proj_struct_JMeq: forall (i: ident) (m : members) 
   {A1 A2: member -> Type} 
   (v1: compact_prod (map A1 m)) (v2: compact_prod (map A2 m)) 
  (d1: A1 (get_member i m)) (d2: A2 (get_member i m)),
  (forall i, in_members i m -> @eq Type (A1 (get_member i m)) (A2 (get_member i m))) ->
  members_no_replicate m = true ->
  in_members i m ->
  JMeq v1 v2 ->
  JMeq (proj_struct i m v1 d1) (proj_struct i m v2 d2).
Proof.
  intros.
  apply proj_compact_prod_JMeq; auto.
  + clear - H H0.
    intros.
    rewrite <- (get_member_name i m); auto.
    apply H.
    apply List.in_map with (f := name_member) in H1.
    auto.
  +
   apply in_get_member; auto.
Qed.

Lemma members_union_inj_JMeq: forall (m : members) 
  {A1 A2: member -> Type} (v1: compact_sum (map A1 m)) (v2: compact_sum (map A2 m)),
  (forall i, in_members i m -> @eq Type (A1 (get_member i m)) (A2 (get_member i m))) ->
  members_no_replicate m = true ->
  JMeq v1 v2 ->
  (forall it, members_union_inj v1 it <-> members_union_inj v2 it).
Proof.
  intros.
  apply compact_sum_inj_JMeq; auto.
  intros a ?.
  specialize (H (name_member a)).
  spec H.
  + 
    apply in_map; auto.
  +
     rewrite <- (get_member_name a m); auto.
Qed.

Lemma proj_union_JMeq: forall (i: ident) (m : members)
  {A1 A2: member -> Type} (v1: compact_sum (map A1 m)) (v2: compact_sum (map A2 m)) (d1: A1 (get_member i m)) (d2: A2 (get_member i m)),
  (forall i, in_members i m -> @eq Type (A1 (get_member i m)) (A2 (get_member i m))) ->
  members_no_replicate m = true ->
  members_union_inj v1 (get_member i m) ->
  JMeq v1 v2 ->
  JMeq (proj_union i m v1 d1) (proj_union i m v2 d2).
Proof.
  intros.
  apply proj_compact_sum_JMeq; auto.
  + clear - H H0.
    intros.
    rewrite <- (get_member_name i m); auto.
    apply H.
    apply List.in_map with (f := name_member) in H1.
    auto.
Qed.


