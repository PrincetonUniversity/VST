From VST.msl Require Import ghost ghost_seplog sepalg_generators sepalg.
From VST.veric Require Import compcert_rmaps shares own mpred ghosts.
Require Import VST.zlist.sublist.
Import List ListNotations.

Section Invariants.

#[global] Program Instance unit_PCM : Ghost := { valid a := True; Join_G a b c := True }.
Next Obligation.
  apply fsep_sep, _.
Defined.

Definition pred_of (P : mpred) := SomeP rmaps.Mpred (fun _ => P).

Definition agree g (P : mpred) : mpred := own(RA := unit_PCM) g tt (pred_of P).

Lemma agree_dup : forall g P, (agree g P = agree g P * agree g P)%pred.
Proof.
  intros; apply ghost_op; constructor.
Qed.

Lemma agree_join : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P1.
Proof.
  intros.
  intros ? (? & ? & ? & H1 & H2).
  do 3 eexists; [apply id_core_unit|].
  pose proof (ghost_of_join _ _ _ H) as J.
  change (agree g P1) with (own.own(RA := unit_PCM) g tt (pred_of P1)) in H1.
  destruct H1 as (? & Hid & ? & H1).
  change (agree g P2) with (own.own(RA := unit_PCM) g tt (pred_of P2)) in H2.
  destruct H2 as (? & ? & ? & H2).
  rewrite ghost_fmap_singleton in H1, H2.
  destruct (join_assoc (join_comm H1) J) as (? & J1 & ?).
  destruct (join_assoc (join_comm H2) (join_comm J1)) as (? & J2 & ?).
  apply singleton_join_inv in J2 as ([] & J2 & ?); subst.
  inv J2; simpl in *.
  destruct H6 as [Heq1 ?].
  apply SomeP_inj in Heq1.
  destruct (join_level _ _ _ H) as [Hl1 Hl2]; erewrite Hl1, Hl2 in *.
  assert (approx (level a) P1 = approx (level a) P2) as Heq.
  { apply (@equal_f _ _ (fun _ : list Type => approx (level a) P1) (fun _ : list Type => approx (level a) P2));
      auto.
    apply nil. }
  clear J.
  split.
  - intros ??? Hl J HP1 ? Ha'.
    pose proof (id_core_level a).
    pose proof (necR_level _ _ Hl).
    apply nec_identity in Hl; [|apply id_core_identity].
    destruct (join_level _ _ _ J).
    apply Hl in J; subst.
    specialize (HP1 _ Ha').
    apply laterR_level in Ha'.
    assert ((approx (level a) P1) a') as HP1'.
    { split; auto; lia. }
    rewrite Heq in HP1'; destruct HP1'; auto.
  - exists I; split.
    + intro l; simpl.
      apply (resource_at_join _ _ _ l) in H.
      apply Hid in H as <-; auto.
    + rewrite ghost_fmap_singleton; simpl.
      eapply join_sub_trans; [|eexists; apply join_comm; eauto].
      eexists; eauto.
      replace _ with I in J1 by (apply proof_irr); eauto.
Qed.

Lemma agree_join2 : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P2.
Proof.
  intros.
  intros ? (? & ? & ? & H1 & H2).
  do 3 eexists; [apply id_core_unit|].
  pose proof (ghost_of_join _ _ _ H) as J.
  change (agree g P1) with (own.own(RA := unit_PCM) g tt (pred_of P1)) in H1.
  destruct H1 as (? & Hid & ? & H1).
  change (agree g P2) with (own.own(RA := unit_PCM) g tt (pred_of P2)) in H2.
  destruct H2 as (? & ? & ? & H2).
  rewrite ghost_fmap_singleton in H1, H2.
  destruct (join_assoc (join_comm H1) J) as (? & J1 & ?).
  destruct (join_assoc (join_comm H2) (join_comm J1)) as (? & J2 & ?).
  apply singleton_join_inv in J2 as ([] & J2 & ?); subst.
  inv J2; simpl in *.
  destruct H6 as [Heq1 ?].
  apply SomeP_inj in Heq1.
  destruct (join_level _ _ _ H) as [Hl1 Hl2]; erewrite Hl1, Hl2 in *.
  assert (approx (level a) P1 = approx (level a) P2) as Heq.
  { apply (@equal_f _ _ (fun _ : list Type => approx (level a) P1) (fun _ : list Type => approx (level a) P2));
      auto.
    apply nil. }
  clear J.
  split.
  - intros ??? Hl J HP1 ? Ha'.
    pose proof (id_core_level a).
    pose proof (necR_level _ _ Hl).
    apply nec_identity in Hl; [|apply id_core_identity].
    destruct (join_level _ _ _ J).
    apply Hl in J; subst.
    specialize (HP1 _ Ha').
    apply laterR_level in Ha'.
    assert ((approx (level a) P1) a') as HP1'.
    { split; auto; lia. }
    rewrite Heq in HP1'; destruct HP1'; auto.
  - exists I; split.
    + intro l; simpl.
      apply (resource_at_join _ _ _ l) in H.
      apply Hid in H as <-; auto.
    + rewrite ghost_fmap_singleton; simpl.
      eapply join_sub_trans; [|eexists; apply join_comm, ghost_of_join; eauto].
      eexists; eauto.
      replace _ with I in H2 by (apply proof_irr); eauto.
Qed.

Inductive list_join {P : Ghost} : Join (list (option G)) :=
  | list_join_nil_l m: list_join nil m m
  | list_join_nil_r m: list_join m nil m
  | list_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> list_join m1 m2 m3 ->
      list_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
#[global] Existing Instance list_join.

Lemma list_join_inv: forall {P : Ghost} (l1 l2 l3 : list (option G)), list_join l1 l2 l3 ->
match l1, l2 with
| nil, _ => l3 = l2
| _, nil => l3 = l1
| a1 :: l1, a2 :: l2 => match l3 with nil => False
                        | a3 :: l3 => join a1 a2 a3 /\ list_join l1 l2 l3 end
end.
Proof.
  induction 1; simpl; auto.
  destruct m; simpl; auto.
Qed.

#[global] Program Instance list_PCM (P : Ghost) : Ghost := { valid a := True; Join_G := list_join }.
Next Obligation.
Proof.
  intros; exists (fun _ => nil); auto; intros; repeat econstructor.
Defined.
Next Obligation.
Proof.
  constructor.
    + intros until 1.
      revert z'; induction H; inversion 1; auto; subst.
      f_equal; eauto.
      eapply join_eq; eauto.
    + induction a; intros ???? J1 J2; eapply list_join_inv in J1; subst.
      { exists e; split; auto; constructor. }
      destruct b; subst; [eexists; split; eauto; constructor|].
      destruct d; [contradiction|].
      destruct J1 as [Jc1 J1].
      apply list_join_inv in J2.
      destruct c; subst; [eexists; split; eauto; constructor; auto|].
      destruct e; [contradiction|].
      destruct J2 as [Jc2 J2].
      destruct (join_assoc Jc1 Jc2) as (f & ? & ?).
      destruct (IHa _ _ _ _ J1 J2) as (f' & ? & ?).
      exists (f :: f'); split; constructor; auto.
    + induction 1; constructor; auto.
    + intros until 1.
      revert b'; induction H; inversion 1; auto; subst.
      f_equal; eauto.
      eapply join_positivity; eauto.
Qed.

Definition ghost_list {P : Ghost} g l := own(RA := list_PCM P) g l NoneP.

Definition list_singleton {A} n (a : A) := repeat None n ++ [Some a].

Definition list_incl {A} (l1 l2 : list (option A)) := (length l1 <= length l2)%nat /\
  forall n a, nth n l1 None = Some a -> nth n l2 None = Some a.

(* up *)
Lemma app_nth : forall {A} n l1 l2 (d : A),
  nth n (l1 ++ l2) d = if lt_dec n (length l1) then nth n l1 d else nth (n - length l1) l2 d.
Proof.
  intros.
  if_tac; [rewrite app_nth1 | rewrite app_nth2]; auto; lia.
Qed.

Fixpoint replace_nth {A} (n: nat) (al: list A) (x: A) {struct n}: list A :=
 match n, al with
 | O , a::al => x::al
 | S n', a::al' => a :: replace_nth n' al' x
 | _, nil => nil
 end.

Lemma replace_nth_length : forall {A} n l (a : A),
  length (replace_nth n l a) = length l.
Proof.
  induction n; destruct l; simpl; intros; try lia.
  erewrite IHn by lia; auto.
Qed.

Lemma replace_nth_app : forall {A} n l1 l2 (a : A),
  replace_nth n (l1 ++ l2) a = if lt_dec n (length l1) then replace_nth n l1 a ++ l2
  else l1 ++ replace_nth (n - length l1) l2 a.
Proof.
  induction n; destruct l1; auto; simpl; intros.
  rewrite IHn.
  if_tac; if_tac; auto; lia.
Qed.

Lemma list_join_app : forall {P : Ghost} l1 l2 m1 m2 n1 n2,
  length l1 = length m1 -> length l1 = length n1 ->
  list_join l1 m1 n1 -> list_join l2 m2 n2 ->
  list_join (l1 ++ l2) (m1 ++ m2) (n1 ++ n2).
Proof.
  induction 3.
  - destruct m; auto; discriminate.
  - destruct m; auto; discriminate.
  - simpl in *.
    intros; constructor; auto.
Qed.

Lemma list_join_None : forall {P : Ghost} n l, (n <= length l)%nat ->
  list_join (repeat None n) l l.
Proof.
  induction n; [constructor|].
  destruct l; simpl; [lia|].
  repeat constructor.
  apply IHn; lia.
Qed.

Lemma list_join_over : forall {P : Ghost} l l1 l2 l1', (length l <= length l1)%nat ->
  list_join l l1 l1' -> list_join l (l1 ++ l2) (l1' ++ l2).
Proof.
  induction 2; simpl in *.
  - constructor.
  - destruct m; [constructor | simpl in *; lia].
  - constructor; auto.
    apply IHlist_join; lia.
Qed.

Lemma singleton_length : forall {A} n (a : A), length (list_singleton n a) = S n.
Proof.
  intros; unfold list_singleton.
  erewrite app_length, repeat_length; simpl; lia.
Qed.

Lemma list_join_singleton : forall {P : Ghost} n a c l
  (Hn : (n < length l)%nat) (Hjoin: join (Some a) (nth n l None) (Some c)),
  list_join (list_singleton n a) l (replace_nth n l (Some c)).
Proof.
  induction l using rev_ind; simpl; intros; try lia.
  rewrite app_length in Hn; simpl in Hn.
  destruct (eq_dec n (length l)).
  - subst.
    erewrite app_nth2, Nat.sub_diag in Hjoin by lia; simpl in Hjoin.
    erewrite replace_nth_app, if_false, Nat.sub_diag by lia; simpl.
    apply list_join_app; try (rewrite repeat_length; auto).
    + apply list_join_None; auto.
    + repeat constructor; auto.
  - assert (n < length l)%nat by lia.
    erewrite app_nth1 in Hjoin by auto.
    erewrite replace_nth_app, if_true by auto.
    apply list_join_over, IHl; auto.
    rewrite singleton_length; lia.
Qed.

(* up *)
Lemma replace_nth_same : forall {A} n l (d : A), replace_nth n l (nth n l d) = l.
Proof.
  induction n; destruct l; auto; simpl; intro.
  rewrite IHn; auto.
Qed.

Lemma nth_replace_nth : forall {A} n l a (d : A), (n < length l)%nat ->
  nth n (replace_nth n l a) d = a.
Proof.
  induction n; destruct l; auto; simpl; intros; try lia.
  apply IHn; lia.
Qed.

Lemma nth_replace_nth' : forall {A} n m l a (d : A), m <> n ->
  nth m (replace_nth n l a) d = nth m l d.
Proof.
  induction n; destruct l; auto; destruct m; auto; simpl; intros; try lia.
  apply IHn; lia.
Qed.

Lemma Znth_replace_nth : forall {A} {d : Inhabitant A} n l (a : A), (n < length l)%nat ->
  Znth (Z.of_nat n) (replace_nth n l a) = a.
Proof.
  intros; rewrite <- nth_Znth'.
  apply nth_replace_nth; auto.
Qed.

Lemma Znth_replace_nth' : forall {A} {d : Inhabitant A} n m l (a : A), m <> Z.of_nat n ->
  Znth m (replace_nth n l a) = Znth m l.
Proof.
  intros.
  destruct (zlt m 0); [rewrite !Znth_underflow; auto|].
  rewrite <- (Z2Nat.id m) by lia.
  rewrite <- !nth_Znth'; apply nth_replace_nth'.
  intro; contradiction H; subst.
  erewrite Z2Nat.id by lia; auto.
Qed.

Lemma replace_nth_replace_nth: forall {A: Type} R n {Rn Rn': A},
  replace_nth n (replace_nth n R Rn) Rn' = replace_nth n R Rn'.
Proof.
  intros.
  revert R; induction n; destruct R; simpl in *.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
Qed.

Lemma ghost_list_nth : forall {P : Ghost} g n l (a : G) (Ha : nth n l None = Some a),
  (ghost_list g l = ghost_list g (list_singleton n a) * ghost_list g (replace_nth n l None))%pred.
Proof.
  intros; apply ghost_op.
  rewrite <- (replace_nth_same n l None) at 2.
  destruct (lt_dec n (length l)); [|erewrite nth_overflow in Ha by lia; discriminate].
  exploit (list_join_singleton n a a (replace_nth n l None)).
  { rewrite replace_nth_length; auto. }
  { erewrite nth_replace_nth by auto; constructor. }
  erewrite replace_nth_replace_nth, Ha; auto.
Qed.

Lemma list_join_length : forall {P : Ghost} l1 l2 l3, list_join l1 l2 l3 ->
  (length l1 <= length l3)%nat.
Proof.
  induction 1; auto; simpl; lia.
Qed.

Lemma list_join_filler : forall {P : Ghost} l1 l2 l3 n, list_join l1 l2 l3 ->
  (n <= length l3 - length l1)%nat -> list_join (l1 ++ repeat None n) l2 l3.
Proof.
  induction 1; simpl; intros.
  - apply list_join_None; lia.
  - destruct n; [|lia].
    rewrite app_nil_r; constructor.
  - constructor; auto.
Qed.

Lemma list_join_nth : forall {P : Ghost} l1 l2 l3 n, list_join l1 l2 l3 ->
  join (nth n l1 None) (nth n l2 None) (nth n l3 None).
Proof.
  intros; revert n.
  induction H; intro.
  - erewrite nth_overflow by (simpl; lia); constructor.
  - erewrite (nth_overflow []) by (simpl; lia); constructor.
  - destruct n; simpl; auto.
Qed.

Lemma list_join_max : forall {P : Ghost} l1 l2 l3, list_join l1 l2 l3 ->
  length l3 = Nat.max (length l1) (length l2).
Proof.
  induction 1; simpl; auto.
  rewrite Nat.max_l; auto; lia.
Qed.

Lemma list_join_nth_error : forall {P : Ghost} l1 l2 l3 n, list_join l1 l2 l3 ->
  join (nth_error l1 n) (nth_error l2 n) (nth_error l3 n).
Proof.
  intros; revert n.
  induction H; intro.
  - rewrite nth_error_nil; constructor.
  - rewrite nth_error_nil; constructor.
  - destruct n; simpl; auto.
    constructor; auto.
Qed.

Lemma list_join_alt : forall {P : Ghost} l1 l2 l3,
  list_join l1 l2 l3 <-> forall n, join (nth_error l1 n) (nth_error l2 n) (nth_error l3 n).
Proof.
  split; [intros; apply list_join_nth_error; auto|].
  revert l2 l3; induction l1; simpl; intros.
  - assert (l2 = l3); [|subst; constructor].
    apply list_nth_error_eq; intro.
    specialize (H j); rewrite nth_error_nil in H; inv H; auto.
  - destruct l2.
    + assert (a :: l1 = l3); [|subst; constructor].
      apply list_nth_error_eq; intro.
      specialize (H j); rewrite nth_error_nil in H; inv H; auto.
    + destruct l3.
      { specialize (H O); inv H. }
      constructor.
      * specialize (H O); inv H; auto.
      * apply IHl1; intro.
        apply (H (S n)).
Qed.

Lemma nth_error_replace_nth : forall {A} n l (a : A), (n < length l)%nat ->
  nth_error (replace_nth n l a) n = Some a.
Proof.
  induction n; destruct l; auto; simpl; intros; try lia.
  apply IHn; lia.
Qed.

Lemma nth_error_replace_nth' : forall {A} n m l (a : A), m <> n ->
  nth_error (replace_nth n l a) m = nth_error l m.
Proof.
  induction n; destruct l; auto; destruct m; auto; simpl; intros; try lia.
  apply IHn; lia.
Qed.

#[global] Instance list_order A : @PCM_order (list_PCM (discrete_PCM A)) list_incl.
Proof.
  constructor.
  - constructor.
    + repeat intro; split; auto.
    + repeat intro.
      destruct H, H0; split; auto; lia.
  - intro a.
    remember (length a) as n.
    revert dependent a; induction n; intros.
    + destruct a; inv Heqn.
      exists b; split; auto.
      change [] with (core b); apply core_unit.
    + assert (a <> []) by (intro; subst; discriminate).
      erewrite (app_removelast_last None) in H, Heqn by auto.
      erewrite app_length in Heqn; simpl in Heqn.
      erewrite Nat.add_1_r in Heqn; inv Heqn.
      specialize (IHn _ eq_refl).
      destruct (IHn b c) as (c' & ? & ?); auto.
      { destruct H as [Hlen H].
        split.
        { rewrite app_length in Hlen; simpl in *; lia. }
        intros ?? Hnth.
        specialize (H n a0).
        rewrite app_nth in H.
        if_tac in H; auto.
        rewrite nth_overflow in Hnth; [discriminate|].
        apply not_lt; auto. }
      pose proof (list_join_length _ _ _ H2).
      pose proof (list_join_length _ _ _ (join_comm H2)).
      destruct (eq_dec (length (removelast a)) (length c')).
      * exists (c' ++ [List.last a None]); split.
        -- erewrite (app_removelast_last None) at 1 by auto.
           apply join_comm, list_join_over; try lia.
           apply join_comm in H2; auto.
        -- split.
            { destruct H.
              erewrite app_length in *; simpl in *; lia. }
            intros ?? Hnth.
            rewrite app_nth in Hnth.
            if_tac in Hnth; [apply H3; auto|].
            destruct (n - length c')%nat eqn: Hminus; [|destruct n0; discriminate].
            simpl in Hnth.
            apply H.
            erewrite app_nth2 by lia.
            replace (_ - _)%nat with O by lia; auto.
       * destruct (List.last a None) eqn: Ha.
         -- exists (replace_nth (length (removelast a)) c' (Some g)).
            split.
            ++ apply list_join_alt; intro.
               pose proof (list_join_max _ _ _ H2) as Hlen.
               destruct (Nat.max_spec (length (removelast a)) (length b)) as [[? Hmax] | [? Hmax]];
                 setoid_rewrite Hmax in Hlen; try lia.
               hnf in H2; erewrite list_join_alt in H2.
               specialize (H2 n0).
               erewrite (app_removelast_last None) at 1 by auto.
               rewrite Ha.
               destruct (lt_dec n0 (length (removelast a))).
               ** erewrite nth_error_app1 by auto.
                  erewrite nth_error_replace_nth' by lia; auto.
               ** erewrite nth_error_app2 by lia.
                  destruct (eq_dec n0 (length (removelast a))).
                  { subst; rewrite Nat.sub_diag; simpl.
                    erewrite nth_error_replace_nth by (simpl in *; lia).
                    destruct (nth_error b (length (removelast a))) eqn: Hb; setoid_rewrite Hb; constructor.
                    destruct o; constructor.
                    destruct H0 as [_ Hc].
                    erewrite sublist.nth_error_nth in Hb by lia.
                    inv Hb.
                    apply Hc in H7.
                    destruct H as [_ Hc'].
                    specialize (Hc' (length (removelast a))).
                    erewrite app_nth2, Nat.sub_diag in Hc' by auto.
                    setoid_rewrite Hc' in H7; [|reflexivity].
                    inv H7; constructor; auto. }
                  { destruct (_ - _)%nat eqn: Hminus; [lia | simpl].
                    erewrite nth_error_nil, nth_error_replace_nth' by (simpl in *; lia).
                    destruct (nth_error_length n0 (removelast a)) as [_ Hnone].
                    setoid_rewrite Hnone in H2; [auto | lia]. }
            ++ destruct H3.
               split.
               { rewrite replace_nth_length; auto. }
               intros ?? Hnth.
               destruct (eq_dec n0 (length (removelast a)));
                 [|rewrite nth_replace_nth' in Hnth; auto].
               subst; erewrite nth_replace_nth in Hnth by (simpl in *; lia).
               inv Hnth.
               apply H.
               erewrite app_nth2, Nat.sub_diag; auto.
         -- exists c'; split; auto.
            erewrite (app_removelast_last None), Ha by auto.
            apply @list_join_filler with (n := 1%nat); auto; simpl in *; lia.
  - split.
    + split; [eapply list_join_length; eauto|].
      intros ?? Hnth.
      apply @list_join_nth with (n := n) in H.
      rewrite Hnth in H; inv H; auto.
      inv H3; auto.
    + split; [apply join_comm in H; eapply list_join_length; eauto|].
      intros ?? Hnth.
      apply @list_join_nth with (n := n) in H.
      rewrite Hnth in H; inv H; auto.
      inv H3; auto.
  - induction a; unfold list_incl; intros.
    + destruct b; [constructor|].
      simpl in *; lia.
    + destruct H as [? Hnth].
      destruct b; constructor.
      * destruct o; [|constructor].
        specialize (Hnth O _ eq_refl); simpl in Hnth.
        subst; repeat constructor.
      * apply IHa.
        split; [simpl in *; lia|].
        intros.
        apply (Hnth (S n)); auto.
Qed.

(*Notation union := base.union.

#[global] Program Instance set_PCM : Ghost := { valid := fun _ : coPset => True;
  Join_G a b c := a ## b /\ c = union a b(*; core2 a := empty*) }.
Next Obligation.
Proof.
  exists (fun _ => empty); auto.
  intro; split; set_solver.
Defined.
Next Obligation.
  constructor.
    + intros.
      inv H; inv H0; auto.
    + intros.
      inv H; inv H0.
      eexists; split; [split; eauto | split]; set_solver.
    + intros.
      inv H.
      split; set_solver.
    + intros.
      inv H; inv H0.
      set_solver.
Qed.*)

Import Ensembles.

Lemma Union_comm: forall {A} S T, Union A S T = Union A T S.
Proof.
  intros; extensionality; apply prop_ext; split; intro H; inv H; solve [constructor 1; auto] || solve [constructor 2; auto].
Qed.

Lemma Union_assoc: forall {A} S T U, Union A (Union A S T) U = Union A S (Union A T U).
Proof.
  intros; extensionality; apply prop_ext; split; intro H; inv H.
  - inv H0; [constructor 1 | constructor 2; constructor 1]; auto.
  - constructor 2; constructor 2; auto.
  - constructor 1; constructor 1; auto.
  - inv H0; [constructor 1; constructor 2 | constructor 2]; auto.
Qed.

Lemma Union_Empty : forall {A} S, Union A (Empty_set A) S = S.
Proof.
  intros; extensionality; apply prop_ext; split; intro H.
  - inv H; auto; contradiction.
  - constructor 2; auto.
Qed.

Lemma Intersection_comm: forall {A} S T, Intersection A S T = Intersection A T S.
Proof.
  intros; extensionality; apply prop_ext; split; intro H; inv H; constructor; auto.
Qed.

Lemma Intersection_assoc: forall {A} S T U, Intersection A (Intersection A S T) U = Intersection A S (Intersection A T U).
Proof.
  intros; extensionality; apply prop_ext; split; intro H; inv H.
  - inv H0; repeat constructor; auto.
  - inv H1; repeat constructor; auto.
Qed.

Lemma Intersection_Empty : forall {A} S, Intersection A (Empty_set A) S = Empty_set A.
Proof.
  intros; extensionality; apply prop_ext; split; intro H; inv H; auto.
Qed.

Global Arguments Union {_} _ _.
Global Arguments Intersection {_} _ _.
Global Arguments Disjoint {_} _ _.
Global Arguments Add {_} _ _.
Global Arguments Setminus {_} _ _.
Global Arguments Subtract {_} _ _.
Global Arguments Full_set {_}.
Global Arguments Empty_set {_}.
Global Arguments Singleton {_} _.
Global Arguments In {_} _ _.
Global Arguments Included {_} _ _.
Global Arguments Same_set {_} _ _.

#[global] Polymorphic Program Instance set_PCM : Ghost := { valid := fun _ : Ensemble nat => True;
  Join_G a b c := Disjoint a b /\ c = Union a b }.
Next Obligation.
Proof.
  apply fsep_sep; exists (fun _ => Empty_set); auto.
  intro; split.
  - constructor; intros ? X.
    rewrite Intersection_Empty in X; contradiction.
  - rewrite Union_Empty; auto.
Defined.
Next Obligation.
  constructor.
    + intros ???? [] []; subst; auto.
    + intros ????? [Hd1] [Hd2]; subst.
      inv Hd1; inv Hd2.
      exists (Union b c); repeat (split; auto).
      * intros ? X; inv X.
        contradiction (H0 x).
        constructor; auto.
        right; auto.
      * intros ? X; inv X.
        inv H2.
        -- contradiction (H x); constructor; auto.
        -- contradiction (H0 x); constructor; auto.
           left; auto.
      * apply Union_assoc.
    + intros ??? []; subst.
      split.
      * inv H; constructor.
        intros x X; inv X; contradiction (H0 x); constructor; auto.
      * apply Union_comm.
    + intros ???? [] []; subst.
      extensionality; apply prop_ext; split; intro X.
      { left; auto. }
      rewrite H2; left; auto.
Qed.

Definition ghost_set g s := own(RA := set_PCM) g s NoneP.

Lemma ghost_set_join : forall g s1 s2,
  (ghost_set g s1 * ghost_set g s2 = !!(Disjoint s1 s2) && ghost_set g (Union s1 s2))%pred.
Proof.
  intros.
  setoid_rewrite own_op_gen.
  - instantiate (1 := Union s1 s2).
    unfold ghost_set; apply pred_ext.
    + apply prop_andp_left; intros (? & (? & []) & ?).
      apply prop_andp_right; auto.
    + apply prop_andp_left; intros.
      apply prop_andp_right; auto.
      eexists; repeat (split; auto).
  - intros (? & H & ?); inv H; split; auto.
Qed.

Lemma ghost_set_subset : forall g s s' (Hdec : forall a, In s' a \/ ~In s' a),
  (Included s' s -> ghost_set g s = ghost_set g s' * ghost_set g (Setminus s s'))%pred.
Proof.
  intros.
  apply ghost_op.
  split.
  - constructor; intros ? X; inv X.
    inv H1; contradiction.
  - extensionality; apply prop_ext; split; intro X.
    + destruct (Hdec x); [left | right; constructor]; auto.
    + destruct X. apply H; auto. inv H0; auto.
Qed.

Corollary ghost_set_remove : forall g a s,
  In s a -> (ghost_set g s = ghost_set g (Singleton a) * ghost_set g (Subtract s a))%pred.
Proof.
  intros; apply ghost_set_subset.
  { intro b; destruct (eq_dec a b); [left; subst; constructor | right; intros X; inv X; contradiction]. }
  intros ? X; inv X; auto.
Qed.

Definition iname := nat.

Class invG := { g_inv : gname; g_en : gname; g_dis : gname }.

Context {inv_names : invG}.

Definition master_list {A} g (l : list (option A)) := ghost_master1(ORD := list_order A) l g.

(* Our ghost state construction makes it awkward to put agree inside other ghost state constructions.
   As a workaround, instead of having one ghost location with a map from indices to agrees,
   we have a map from indices to ghost locations, each with an agree. *)

#[global] Instance token_PCM : Ghost := exclusive_PCM unit.

Fixpoint iter_sepcon {A} (p : A -> mpred) l :=
  match l with
    | nil => emp
    | x :: xl => (p x * iter_sepcon p xl)%pred
  end.

Typeclasses eauto := 1.

#[global] Instance Inhabitant_mpred : Inhabitant mpred := emp.

Definition wsat : mpred := (EX I : list mpred, EX lg : list gname, EX lb : list (option bool),
  !!(length lg = length I /\ length lb = length I) &&
  master_list g_inv (map (fun i => match Znth i lb with Some _ => Some (Znth i lg)
                                   | None => None end) (upto (length I))) *
  ghost_list g_dis (map (fun o => match o with Some true => Some (Some tt) | _ => None end) lb) *
  ghost_set g_en (fun i : iname => nth i lb None = Some false) *
  iter_sepcon (fun i => match Znth i lb with
                        | Some true => agree (Znth i lg) (Znth i I) * |> Znth i I
                        | Some false => agree (Znth i lg) (Znth i I)
                        | _ => emp end) (upto (length I)))%pred.

(* This is what's called ownI in Iris; we could build another layer with namespaces. *)
Definition invariant (i : iname) P : mpred := (EX g : gname,
  ghost_snap(ORD := list_order _) (list_singleton i g) g_inv * agree g P)%pred.

Lemma nth_singleton : forall {A} n (a : A) d, nth n (list_singleton n a) d = Some a.
Proof.
  intros; unfold list_singleton.
  rewrite app_nth2; rewrite repeat_length; auto.
  rewrite Nat.sub_diag; auto.
Qed.

Lemma list_join_singleton_inv : forall {P : Ghost} n a b l,
  list_join (list_singleton n a) (list_singleton n b) l ->
  exists c, join a b c /\ l = list_singleton n c.
Proof.
  induction n; inversion 1; subst.
  - inv H5.
    inv H6; eauto.
  - edestruct IHn as (c & ? & ?); eauto; subst.
    inv H5; eauto.
Qed.

Lemma singleton_join_self : forall {P: Ghost} k (a : G), join a a a ->
  join (list_singleton k a) (list_singleton k a) (list_singleton k a).
Proof.
  intros.
  induction k; repeat constructor; auto.
Qed.

Lemma invariant_dup : forall i P, (invariant i P = invariant i P * invariant i P)%pred.
Proof.
  intros; unfold invariant; apply pred_ext.
  - apply exp_left; intro g.
    rewrite exp_sepcon1; apply exp_right with g.
    rewrite exp_sepcon2; apply exp_right with g.
    rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- sepcon_assoc.
    erewrite ghost_snap_join.
    erewrite sepcon_assoc, <- agree_dup; apply derives_refl.
    { apply (singleton_join_self(P := discrete_PCM _)).
      constructor; auto. }
  - rewrite exp_sepcon1; apply exp_left; intro g1.
    rewrite exp_sepcon2; apply exp_left; intro g2.
    erewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- sepcon_assoc.
    rewrite ghost_snap_join'.
    rewrite !exp_sepcon1; apply exp_left; intro l.
    rewrite !sepcon_andp_prop1; apply prop_andp_left; intro H.
    apply (list_join_singleton_inv(P := discrete_PCM _)) in H as (g & H & ?); subst.
    inv H.
    erewrite sepcon_assoc, <- agree_dup.
    apply exp_right with g; apply derives_refl.
Qed.

(* up *)
Lemma Zlength_eq : forall {A B} (l1 : list A) (l2 : list B),
  Zlength l1 = Zlength l2 <-> length l1 = length l2.
Proof.
  intros; rewrite !Zlength_correct.
  split; [apply Nat2Z.inj|].
  intro; apply Z2Nat.inj; try lia.
Qed.

#[global] Instance list_Perm {P : Ghost} : Perm_alg (list (option G)).
Proof.
  apply list_PCM.
Qed.

(* up *)
Lemma nth_upto : forall m n d, (n < m)%nat -> nth n (upto m) d = Z.of_nat n.
Proof.
  intros.
  erewrite nth_indep by (rewrite upto_length; auto).
  erewrite nth_Znth', Znth_upto; auto.
  split; [lia|].
  apply Nat2Z.inj_lt; auto.
Qed.

Lemma nth_repeat : forall {A} n m (a : A), nth n (repeat a m) a = a.
Proof.
  induction n; destruct m; simpl; auto.
Qed.

Lemma list_incl_singleton : forall {A} n (a : A) l,
  list_incl (list_singleton n a) l <-> nth n l None = Some a.
Proof.
  unfold list_incl; split.
  - intros [? Hnth].
    apply Hnth.
    rewrite nth_singleton; auto.
  - intros; split.
    + rewrite singleton_length.
      destruct (lt_dec n (length l)); [lia|].
      erewrite nth_overflow in H by lia; discriminate.
    + intros ??.
      unfold list_singleton.
      destruct (lt_dec n0 n).
      * erewrite app_nth1 by (rewrite repeat_length; auto).
        rewrite nth_repeat; discriminate.
      * rewrite app_nth2; rewrite repeat_length; try lia.
        destruct (eq_dec n0 n); [|erewrite nth_overflow by (simpl; lia); discriminate].
        subst; rewrite Nat.sub_diag; simpl.
        intro X; inv X; auto.
Qed.

Lemma seq_app : forall a b c, seq a (b + c) = seq a b ++ seq (a + b) c.
Proof.
  intros ??; revert a; induction b; simpl; intros; auto.
  rewrite IHb; do 3 f_equal; lia.
Qed.

Lemma filter_ext_in : forall {A} (f g : A -> bool) l, (forall x, List.In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  induction l; auto; simpl; intros.
  rewrite -> H by auto.
  rewrite IHl; auto.
Qed.

Lemma filter_none : forall {A} (f : A -> bool) l, (forall x, List.In x l -> f x = false) -> filter f l = [].
Proof.
  induction l; auto; simpl; intros.
  rewrite H; auto.
Qed.

Ltac view_shift H := eapply derives_trans; [apply sepcon_derives, derives_refl; apply H
  | eapply derives_trans; [apply bupd_frame_r | eapply derives_trans, bupd_trans; apply bupd_mono]].

Lemma iter_sepcon_app:
  forall {B} p (l1 l2 : list B), (iter_sepcon p (l1 ++ l2) = iter_sepcon p l1 * iter_sepcon p l2)%pred.
Proof.
  induction l1; intros; simpl. rewrite emp_sepcon; auto. rewrite IHl1. rewrite sepcon_assoc. auto.
Qed.

Lemma iter_sepcon_func_strong: forall {A} (l : list A) P Q, (forall x, List.In x l -> P x = Q x) -> iter_sepcon P l = iter_sepcon Q l.
Proof.
  intros. induction l.
  + reflexivity.
  + simpl.
    f_equal.
    - apply H.
      simpl; auto.
    - apply IHl.
      intros; apply H.
      simpl; auto.
Qed.

Lemma iter_sepcon_emp': forall {B} p (l : list B), (forall x, List.In x l -> p x = emp) -> iter_sepcon p l = emp.
Proof.
  induction l; intros; simpl; auto.
  rewrite H, IHl, sepcon_emp; simpl; auto.
  intros; apply H; simpl; auto.
Qed.

Lemma wsat_alloc_dep : forall P, wsat * (ALL i, |> P i) |-- |==> wsat * EX i : _, invariant i (P i).
Proof.
  intros; unfold wsat.
  rewrite !exp_sepcon1; apply exp_left; intro l.
  rewrite !exp_sepcon1; apply exp_left; intro lg.
  rewrite !exp_sepcon1; apply exp_left; intro lb.
  rewrite !sepcon_andp_prop1; apply prop_andp_left; intros [].
  rewrite (sepcon_comm _ (ghost_list _ _)), !sepcon_assoc.
  view_shift (ghost_update_ND(RA := list_PCM token_PCM) g_dis (map
     (fun o => match o with Some true => Some (Some tt) | _ => None end) lb)
     (fun l => exists i, l =
      map (fun o => match o with Some true => Some (Some tt) | _ => None end)
          ((lb ++ repeat None i) ++ [Some true]))).
  { intros ? (? & ? & _).
    exists (map (fun o => match o with Some true => Some (Some tt) | _ => None end)
      ((lb ++ repeat None (length x - length lb)) ++ [Some true])).
    split; [eauto|].
    exists (x ++ [Some (Some tt)]); split; simpl; auto.
    erewrite !map_app, own.map_repeat; simpl.
    pose proof (list_join_length _ _ _ H1) as Hlen.
    rewrite map_length in Hlen.
    apply join_comm in H1.
    pose proof (list_join_length _ _ _ H1) as Hlen'.
    apply (join_comm(Perm_alg := list_Perm)), (list_join_over c).
    { erewrite app_length, map_length, repeat_length, Nat.add_comm, Nat.sub_add; auto. }
    apply (join_comm(Perm_alg := list_Perm)), (list_join_filler(P := token_PCM));
      [|rewrite map_length; auto].
    apply join_comm in H1; auto. }
  rewrite exp_sepcon1; apply exp_left; intro.
  rewrite !sepcon_andp_prop1; apply prop_andp_left; intros [i ?]; subst.
  eapply derives_trans with (emp * _)%pred; [rewrite emp_sepcon; apply derives_refl|].
  set (P' := P (length lg + i)%nat).
  view_shift (ghost_alloc(RA := unit_PCM) tt (pred_of P')); [simpl; auto|].
  rewrite !exp_sepcon1; apply exp_left; intro g.
  replace (own(RA := unit_PCM) g tt (pred_of P')) with (agree g P') by reflexivity.
  rewrite agree_dup.
  assert (Zlength lg = Zlength l) as Hlg by (apply Zlength_eq; auto).
  assert (Zlength lb = Zlength l) as Hlb by (apply Zlength_eq; auto).
  rewrite <- !sepcon_assoc, (sepcon_comm _ (master_list _ _)), !sepcon_assoc.
  view_shift (master_update(ORD := list_order _) ((map (fun i0 : Z =>
      match Znth i0 lb with Some _ => Some (Znth i0 lg) | None => None end) (upto (Datatypes.length l))))
        (map (fun j => match Znth j ((lb ++ repeat None i) ++ [Some true]) with
                       | Some _ => Some (Znth j ((lg ++ repeat O i) ++ [g]))
                       | None => None
                       end) (upto (length ((l ++ repeat emp i) ++ [P']))))).
  { rewrite <- !app_assoc, app_length, upto_app, map_app.
    split.
    { erewrite app_length, !map_length; lia. }
    intros ?? Hn.
    erewrite app_nth, map_length.
    if_tac; [|erewrite nth_overflow in Hn by (rewrite map_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in * by auto.
    erewrite upto_length in *.
    assert (Z.of_nat n < Zlength l).
    { rewrite Zlength_correct; apply Nat2Z.inj_lt; auto. }
    erewrite nth_upto in * by auto.
    erewrite !app_Znth1 by lia; auto. }
  view_shift (make_snap(ORD := list_order gname)).
  rewrite !sepcon_assoc.
  view_shift (ghost_snap_forget(ORD := list_order _) (list_singleton (length lg + i) g)).
  { apply list_incl_singleton.
    erewrite app_length, upto_app, map_app, app_nth2; erewrite map_length, upto_length, app_length,
      repeat_length; try lia.
    replace (_ - _)%nat with O by lia; simpl.
    rewrite Nat2Z.inj_add, Z.add_0_r.
    rewrite !app_Znth2; erewrite !Zlength_app, !coqlib4.Zlength_repeat, <- Zlength_correct; try lia.
    replace (_ - _) with 0 by lia; replace (_ - _) with 0 by lia; auto. }
  eapply derives_trans, bupd_intro.
  apply exp_right with ((l ++ repeat emp i) ++ [P']).
  rewrite exp_sepcon1; apply exp_right with ((lg ++ repeat O i) ++ [g]).
  rewrite exp_sepcon1; apply exp_right with ((lb ++ repeat None i) ++ [Some true]).
  erewrite !(app_length (_ ++ _)); simpl.
  erewrite prop_true_andp by (erewrite !app_length, !repeat_length; lia).
  erewrite upto_app, iter_sepcon_app; simpl.
  erewrite Z.add_0_r, <- Zlength_correct, !app_Znth2; erewrite !Zlength_app, !coqlib4.Zlength_repeat; try lia.
  erewrite Hlg, Hlb, Zminus_diag, !Znth_0_cons.
  rewrite sepcon_comm, !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
  rewrite <- sepcon_assoc, sepcon_comm, sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
  rewrite sepcon_assoc; apply sepcon_derives.
  { match goal with |-?P |-- ?Q => replace P with Q; [apply derives_refl|] end.
    f_equal. extensionality; apply prop_ext; split; intro X.
    - rewrite !app_nth, nth_repeat in X.
      repeat destruct (lt_dec _ _); auto; try discriminate.
      destruct (x - _)%nat; [|destruct n0]; inv X.
    - destruct (lt_dec x (length lb)).
      rewrite !app_nth, app_length.
      destruct (lt_dec _ _); [|lia].
      destruct (lt_dec _ _); [auto | lia].
      { rewrite nth_overflow in X by lia; discriminate. } }
  erewrite app_length, upto_app, iter_sepcon_app.
  rewrite sepcon_assoc; apply sepcon_derives.
  - eapply derives_trans with (_ * emp)%pred; [rewrite sepcon_emp; apply derives_refl|].
    apply sepcon_derives.
    + erewrite iter_sepcon_func_strong; auto.
      intros ??%In_upto.
      rewrite <- Zlength_correct in *.
      rewrite <- !app_assoc, !app_Znth1 by (rewrite ?Zlength_app; lia); auto.
    + rewrite iter_sepcon_emp'; auto.
      intros ? Hin.
      eapply in_map_iff in Hin as (? & ? & Hin%In_upto); subst.
      rewrite <- Zlength_correct, coqlib4.Zlength_repeat in Hin.
      rewrite <- Zlength_correct, <- app_assoc, app_Znth2 by lia.
      erewrite app_Znth1 by (rewrite coqlib4.Zlength_repeat; lia).
      unfold Znth; destruct (Z_lt_dec _ _); auto.
      rewrite nth_repeat; auto.
  - unfold invariant.
    rewrite emp_sepcon, !exp_sepcon2; apply exp_right with (length lg + i)%nat.
    rewrite !exp_sepcon2; apply exp_right with g.
    rewrite <- !sepcon_assoc, sepcon_comm, !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    apply sepcon_derives, derives_refl.
    eapply allp_left, derives_refl.
Qed.

Lemma wsat_alloc : forall P, wsat * |> P |-- |==> wsat * EX i : _, invariant i P.
Proof.
  intros; eapply derives_trans, wsat_alloc_dep.
  apply sepcon_derives; [apply derives_refl|].
  apply allp_right; auto.
Qed.

(* request an iname with a particular property *)
Lemma wsat_alloc_strong : forall P Pi (Hfresh : forall n, exists i, (n <= i)%nat /\ Pi i),
  wsat * |> P |-- |==> wsat * EX i : _, !!(Pi i) && invariant i P.
Proof.
  intros; unfold wsat.
  rewrite !exp_sepcon1; apply exp_left; intro l.
  rewrite !exp_sepcon1; apply exp_left; intro lg.
  rewrite !exp_sepcon1; apply exp_left; intro lb.
  rewrite !sepcon_andp_prop1; apply prop_andp_left; intros [].
  rewrite (sepcon_comm _ (ghost_list _ _)), !sepcon_assoc.
  view_shift (ghost_update_ND(RA := list_PCM token_PCM) g_dis (map
     (fun o => match o with Some true => Some (Some tt) | _ => None end) lb)
     (fun l => exists i, Pi (length lg + i)%nat /\ l =
      map (fun o => match o with Some true => Some (Some tt) | _ => None end)
          ((lb ++ repeat None i) ++ [Some true]))).
  { intros ? (? & ? & _).
    destruct (Hfresh (length x)) as (i & ? & ?).
    exists (map (fun o => match o with Some true => Some (Some tt) | _ => None end)
      ((lb ++ repeat None (i - length lb)) ++ [Some true])).
    pose proof (list_join_length _ _ _ H1) as Hlen.
    rewrite map_length in Hlen.
    split.
    { exists (i - length lg)%nat; rewrite H, H0; split; auto.
      rewrite Nat.add_comm, Nat.sub_add; auto; lia. }
    exists (x ++ repeat None (i - length x) ++ [Some (Some tt)]); split; simpl; auto.
    erewrite !map_app, own.map_repeat; simpl.
    apply join_comm in H1.
    rewrite app_assoc; apply (join_comm(Perm_alg := list_Perm)), (list_join_over c).
    { apply list_join_length in H1.
      rewrite app_length, map_length, repeat_length, Nat.add_comm, Nat.sub_add; auto; lia. }
    replace (i - length lb)%nat with ((length x - length lb) + (i - length x))%nat by lia.
    rewrite repeat_app, app_assoc; apply (list_join_over c).
    { apply list_join_length in H1.
      rewrite app_length, map_length, repeat_length; lia. }
    apply (join_comm(Perm_alg := list_Perm)), (list_join_filler(P := token_PCM));
      [|rewrite map_length; auto].
    apply join_comm in H1; auto. }
  rewrite exp_sepcon1; apply exp_left; intro.
  rewrite !sepcon_andp_prop1; apply prop_andp_left; intros [i []]; subst.
  eapply derives_trans with (emp * _)%pred; [rewrite emp_sepcon; apply derives_refl|].
  view_shift (ghost_alloc(RA := unit_PCM) tt (pred_of P)); [simpl; auto|].
  rewrite !exp_sepcon1; apply exp_left; intro g.
  replace (own(RA := unit_PCM) g tt (pred_of P)) with (agree g P) by reflexivity.
  rewrite agree_dup.
  assert (Zlength lg = Zlength l) as Hlg by (apply Zlength_eq; auto).
  assert (Zlength lb = Zlength l) as Hlb by (apply Zlength_eq; auto).
  rewrite <- !sepcon_assoc, (sepcon_comm _ (master_list _ _)), !sepcon_assoc.
  view_shift (master_update(ORD := list_order _) ((map (fun i0 : Z =>
      match Znth i0 lb with Some _ => Some (Znth i0 lg) | None => None end) (upto (Datatypes.length l))))
        (map (fun j => match Znth j ((lb ++ repeat None i) ++ [Some true]) with
                       | Some _ => Some (Znth j ((lg ++ repeat O i) ++ [g]))
                       | None => None
                       end) (upto (length ((l ++ repeat emp i) ++ [P]))))).
  { rewrite <- !app_assoc, app_length, upto_app, map_app.
    split.
    { erewrite app_length, !map_length; lia. }
    intros ?? Hn.
    erewrite app_nth, map_length.
    if_tac; [|erewrite nth_overflow in Hn by (rewrite map_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in * by auto.
    erewrite upto_length in *.
    assert (Z.of_nat n < Zlength l).
    { rewrite Zlength_correct; apply Nat2Z.inj_lt; auto. }
    erewrite nth_upto in * by auto.
    erewrite !app_Znth1 by lia; auto. }
  view_shift (make_snap(ORD := list_order gname)).
  rewrite !sepcon_assoc.
  view_shift (ghost_snap_forget(ORD := list_order _) (list_singleton (length lg + i) g)).
  { apply list_incl_singleton.
    erewrite app_length, upto_app, map_app, app_nth2; erewrite map_length, upto_length, app_length,
      repeat_length; try lia.
    replace (_ - _)%nat with O by lia; simpl.
    rewrite Nat2Z.inj_add, Z.add_0_r.
    rewrite !app_Znth2; erewrite !Zlength_app, !coqlib4.Zlength_repeat, <- Zlength_correct; try lia.
    replace (_ - _) with 0 by lia; replace (_ - _) with 0 by lia; auto. }
  eapply derives_trans, bupd_intro.
  apply exp_right with ((l ++ repeat emp i) ++ [P]).
  rewrite exp_sepcon1; apply exp_right with ((lg ++ repeat O i) ++ [g]).
  rewrite exp_sepcon1; apply exp_right with ((lb ++ repeat None i) ++ [Some true]).
  erewrite !(app_length (_ ++ _)); simpl.
  erewrite prop_true_andp by (erewrite !app_length, !repeat_length; lia).
  erewrite upto_app, iter_sepcon_app; simpl.
  erewrite Z.add_0_r, <- Zlength_correct, !app_Znth2; erewrite !Zlength_app, !coqlib4.Zlength_repeat; try lia.
  erewrite Hlg, Hlb, Zminus_diag, !Znth_0_cons.
  rewrite sepcon_comm, !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
  rewrite <- sepcon_assoc, sepcon_comm, sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
  rewrite sepcon_assoc; apply sepcon_derives.
  { match goal with |-?P |-- ?Q => replace P with Q; [apply derives_refl|] end.
    f_equal. extensionality; apply prop_ext; split; intro X.
    - rewrite !app_nth, nth_repeat in X.
      repeat destruct (lt_dec _ _); auto; try discriminate.
      destruct (x - _)%nat; [|destruct n0]; inv X.
    - destruct (lt_dec x (length lb)).
      rewrite !app_nth, app_length.
      destruct (lt_dec _ _); [|lia].
      destruct (lt_dec _ _); [auto | lia].
      { rewrite nth_overflow in X by lia; discriminate. } }
  erewrite app_length, upto_app, iter_sepcon_app.
  rewrite sepcon_assoc; apply sepcon_derives.
  - eapply derives_trans with (_ * emp)%pred; [rewrite sepcon_emp; apply derives_refl|].
    apply sepcon_derives.
    + erewrite iter_sepcon_func_strong; auto.
      intros ??%In_upto.
      rewrite <- Zlength_correct in *.
      rewrite <- !app_assoc, !app_Znth1 by (rewrite ?Zlength_app; lia); auto.
    + rewrite iter_sepcon_emp'; auto.
      intros ? Hin.
      eapply in_map_iff in Hin as (? & ? & Hin%In_upto); subst.
      rewrite <- Zlength_correct, coqlib4.Zlength_repeat in Hin.
      rewrite <- Zlength_correct, <- app_assoc, app_Znth2 by lia.
      erewrite app_Znth1 by (rewrite coqlib4.Zlength_repeat; lia).
      unfold Znth; destruct (Z_lt_dec _ _); auto.
      rewrite nth_repeat; auto.
  - unfold invariant.
    rewrite emp_sepcon, !exp_sepcon2; apply exp_right with (length lg + i)%nat.
    rewrite prop_true_andp by auto.
    rewrite !exp_sepcon2; apply exp_right with g.
    rewrite <- !sepcon_assoc, sepcon_comm, !sepcon_assoc; apply derives_refl.
Qed.

Lemma iter_sepcon_Znth: forall {A} {d : Inhabitant A} f (l : list A) i, 0 <= i < Zlength l ->
  iter_sepcon f l = (f (Znth i l) * iter_sepcon f (remove_Znth i l))%pred.
Proof.
  intros; unfold remove_Znth.
  transitivity (iter_sepcon f (sublist 0 (Zlength l) l)); [rewrite sublist_same; auto|].
  rewrite sublist_split with (mid := i) by lia.
  rewrite (sublist_next i) by lia.
  rewrite !iter_sepcon_app; simpl.
  rewrite <- !sepcon_assoc, (sepcon_comm (f _)); reflexivity.
Qed.

Lemma map_replace_nth:
  forall {A B} (f: A -> B) n R X, map f (replace_nth n R X) =
       replace_nth n (map f R) (f X).
Proof.
  intros.
  revert R; induction n; destruct R; simpl; auto.
  f_equal; auto.
Qed.

Lemma wsat_open : forall i P,
  (wsat * invariant i P * ghost_set g_en (Singleton i) |--
  |==> wsat * |> P * ghost_list g_dis (list_singleton i (Some tt))).
Proof.
  intros; unfold wsat, invariant.
  rewrite !exp_sepcon1; apply exp_left; intros l.
  rewrite !exp_sepcon1; apply exp_left; intros lg.
  rewrite !exp_sepcon1; apply exp_left; intros lb.
  rewrite !sepcon_andp_prop1; apply prop_andp_left; intros [].
  rewrite !exp_sepcon2, exp_sepcon1; apply exp_left; intros g.
  eapply derives_trans, (prop_andp_left (i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat).
  { rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
    unfold master_list; rewrite snap_master_join1.
    rewrite !sepcon_andp_prop1; apply andp_derives, derives_refl.
    apply prop_derives; intros Hincl.
    apply list_incl_singleton in Hincl.
    destruct (lt_dec i (length lg));
      [|rewrite nth_overflow in Hincl by (rewrite map_length, upto_length; lia); discriminate].
    rewrite nth_map' with (d' := 0) in Hincl by (rewrite upto_length; lia).
    rewrite nth_upto in Hincl by lia.
    destruct (Znth (Z.of_nat i) lb); inversion Hincl; eauto. }
  intros (? & ? & b & Hi).
  eapply derives_trans, bupd_intro.
  assert (nth i lb None = Some b) as Hi'.
  { rewrite <- nth_Znth, Nat2Z.id in Hi; auto.
    rewrite Zlength_correct; lia. }
  destruct b.
  erewrite ghost_list_nth with (n := i) by (rewrite nth_map' with (d' := None), Hi'; eauto; lia).
  rewrite (iter_sepcon_Znth _ _ (Z.of_nat i))
    by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
  rewrite Znth_upto, Hi by lia.
  rewrite (sepcon_assoc (agree _ _)), (sepcon_comm (agree _ _)), <- !sepcon_assoc, sepcon_comm, <- !sepcon_assoc, sepcon_assoc.
  subst; eapply derives_trans; [apply sepcon_derives, agree_join; apply derives_refl|].
  apply exp_right with l.
  rewrite !exp_sepcon1; apply exp_right with lg.
  rewrite !exp_sepcon1; apply exp_right with (replace_nth i lb (Some false)).
  rewrite prop_true_andp.
  rewrite (sepcon_comm _ (ghost_master1 _ _)), !sepcon_assoc; apply sepcon_derives.
  { erewrite map_ext; [apply derives_refl|].
    intros; simpl.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try lia.
    rewrite Hi; auto. }
  rewrite sepcon_comm, (sepcon_comm (ghost_list _ _)), !sepcon_assoc; apply sepcon_derives.
  { rewrite map_replace_nth; auto. }
  rewrite <- !sepcon_assoc, sepcon_comm, <- !sepcon_assoc.
  rewrite ghost_set_join, !sepcon_andp_prop1; apply prop_andp_left; intros.
  rewrite !sepcon_assoc; apply sepcon_derives.
  { match goal with |- ghost_set _ ?A |-- ghost_set _ ?B =>
      replace B with A end.
    apply derives_refl.
    extensionality; apply prop_ext; split; intro Hin.
    + inv Hin.
      * inv H3. rewrite nth_replace_nth; auto; lia.
      * destruct (eq_dec x i); [subst; rewrite nth_replace_nth | rewrite nth_replace_nth']; auto; lia.
    +
      destruct (eq_dec x i); [subst; constructor 1; constructor|].
      rewrite nth_replace_nth' in Hin; auto; constructor 2; auto. }
  rewrite <- !sepcon_assoc; apply sepcon_derives, derives_refl.
  rewrite sepcon_comm, (sepcon_comm _ (iter_sepcon _ _)), <- !sepcon_assoc.
  rewrite sepcon_assoc; apply sepcon_derives.
  { rewrite (iter_sepcon_Znth _ (upto _) (Z.of_nat i))
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    rewrite Znth_upto, Znth_replace_nth by lia.
    apply sepcon_derives; [apply derives_refl|].
    erewrite iter_sepcon_func_strong; auto.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; lia.
 }
  { rewrite sepcon_comm, wand_sepcon_adjoint; apply derives_refl. }
  { rewrite replace_nth_length; split; auto. }
  { rewrite !sepcon_assoc, (sepcon_comm (ghost_set _ _)), <- !sepcon_assoc, sepcon_assoc.
    eapply derives_trans, FF_derives.
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl|] | rewrite sepcon_comm, FF_sepcon; apply derives_refl].
    rewrite ghost_set_join; apply prop_andp_left; intros X.
    inv X. contradiction (H3 i). constructor; auto; constructor. }
Qed.

(* up *)
Lemma replace_nth_same' : forall {A} n l (a d : A), nth n l d = a -> replace_nth n l a = l.
Proof.
  intros; subst; apply replace_nth_same.
Qed.

Lemma wsat_close : forall i P,
  (wsat * invariant i P * |> P * ghost_list g_dis (list_singleton i (Some tt)) |--
  |==> wsat * ghost_set g_en (Singleton i)).
Proof.
  intros; unfold wsat, invariant.
  rewrite !exp_sepcon1; apply exp_left; intros l.
  rewrite !exp_sepcon1; apply exp_left; intros lg.
  rewrite !exp_sepcon1; apply exp_left; intros lb.
  rewrite !sepcon_andp_prop1; apply prop_andp_left; intros [].
  rewrite !exp_sepcon2, !exp_sepcon1; apply exp_left; intros g.
  eapply derives_trans, (prop_andp_left (i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat).
  { rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
    unfold master_list; rewrite snap_master_join1.
    rewrite !sepcon_andp_prop1; apply andp_derives, derives_refl.
    apply prop_derives; intros Hincl.
    apply list_incl_singleton in Hincl.
    destruct (lt_dec i (length lg));
      [|rewrite nth_overflow in Hincl by (rewrite map_length, upto_length; lia); discriminate].
    rewrite nth_map' with (d' := 0) in Hincl by (rewrite upto_length; lia).
    rewrite nth_upto in Hincl by lia.
    destruct (Znth (Z.of_nat i) lb); inversion Hincl; eauto. }
  intros (? & ? & b & Hi).
  eapply derives_trans, bupd_intro.
  assert (nth i lb None = Some b) as Hi'.
  { rewrite <- nth_Znth, Nat2Z.id in Hi; auto.
    rewrite Zlength_correct; lia. }
  destruct b.
  { rewrite (sepcon_comm (ghost_master1 _ _)), sepcon_comm, <- !sepcon_assoc.
    rewrite 4sepcon_assoc; eapply derives_trans, FF_derives.
    eapply derives_trans; [apply sepcon_derives, derives_refl | rewrite FF_sepcon; apply derives_refl].
    eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid_2|].
    apply prop_andp_left; intros (? & J & ?).
    apply list_join_nth with (n := i) in J.
    erewrite nth_singleton, nth_map' with (d' := None) in J by lia.
    rewrite Hi' in J; inv J.
    inv H7.
    inv H5. }
  rewrite ghost_set_remove with (a := i) by auto.
  apply exp_right with l.
  rewrite exp_sepcon1; apply exp_right with lg.
  rewrite exp_sepcon1; apply exp_right with (replace_nth i lb (Some true)).
  rewrite replace_nth_length, prop_true_andp by auto.
  rewrite !sepcon_assoc; apply sepcon_derives.
  { erewrite map_ext; [apply derives_refl|].
    intros.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try lia.
    rewrite Hi; auto. }
  rewrite sepcon_comm, sepcon_assoc, sepcon_comm, <- !sepcon_assoc; apply sepcon_derives, derives_refl.
  rewrite !sepcon_assoc, (sepcon_comm (ghost_list _ _) (_ * _)%pred), <- !sepcon_assoc, sepcon_assoc.
  apply sepcon_derives.
  rewrite !sepcon_assoc; apply sepcon_derives.
  { match goal with |- ghost_set _ ?A |-- ghost_set _ ?B =>
      replace B with A end; [apply derives_refl|].
    extensionality; apply prop_ext; split; intro Hin.
    + inv Hin.
      destruct (eq_dec x i); [subst; contradiction H4; constructor|].
      rewrite nth_replace_nth'; auto.
    +
      destruct (eq_dec x i); [subst; rewrite nth_replace_nth in Hin by lia; discriminate|].
      rewrite nth_replace_nth' in Hin by auto; constructor; auto.
      intros X; inv X; contradiction. }
  { rewrite (iter_sepcon_Znth _ _ (Z.of_nat i))
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    rewrite (iter_sepcon_Znth _ (upto _) (Z.of_nat i))
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    rewrite !Znth_upto, !Znth_replace_nth by lia.
    rewrite Hi.
    rewrite (sepcon_comm _ (|> P)%pred), <- !sepcon_assoc, sepcon_comm, <- !sepcon_assoc, sepcon_assoc.
    subst; eapply derives_trans; [apply sepcon_derives, derives_refl; apply agree_join2|].
    rewrite (sepcon_comm _ (agree _ _)), !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    rewrite <- sepcon_assoc, sepcon_comm, <- sepcon_assoc; apply sepcon_derives.
    + rewrite sepcon_comm, wand_sepcon_adjoint; apply derives_refl.
    + erewrite iter_sepcon_func_strong; eauto.
      unfold remove_Znth; intros ? Hin.
      rewrite Znth_replace_nth'; auto.
      intro; subst.
      apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; lia. }
  { unfold ghost_list. erewrite <- ghost_op; [apply derives_refl|].
    rewrite map_replace_nth.
    apply (list_join_singleton(P := token_PCM)).
    { rewrite map_length; lia. }
    rewrite nth_map' with (d' := None) by lia.
    rewrite Hi'; constructor. }
Qed.

Lemma invariant_dealloc : forall i P, invariant i P |-- emp.
Proof.
  intros; unfold invariant.
  apply exp_left; intro g.
  rewrite <- (emp_sepcon emp).
  apply sepcon_derives; apply ghost_dealloc.
Qed.

Lemma ghost_is_pred_nonexpansive : forall g H, nonexpansive (fun P => ghost_is (singleton g
  (existT (fun RA : Ghost => {a : @G RA | valid a}) unit_PCM
           (exist (fun a : G => valid a) (tt : @G unit_PCM) H),
        pred_of P))).
Proof.
  unfold nonexpansive.
  intros ??????; split; intros ?????; simpl in *;
    match goal with H : join_sub ?a ?b |- join_sub ?c ?b =>
      assert (a = c) as <-; auto end; simpl;
    rewrite !ghost_fmap_singleton; do 2 f_equal; simpl; f_equal;
    extensionality; apply pred_ext; intros ? []; split; auto;
    eapply H0; try apply necR_refl; auto; apply necR_level in H2; apply ext_level in H3; lia.
Qed.

Lemma agree_nonexpansive : forall g, nonexpansive (agree g).
Proof.
  intros; unfold agree, own.
  apply exists_nonexpansive; intros.
  unfold Own.
  apply conj_nonexpansive; [apply const_nonexpansive|].
  apply ghost_is_pred_nonexpansive.
Qed.

Lemma invariant_nonexpansive : forall N, nonexpansive (invariant N).
Proof.
  intros; unfold invariant.
  apply exists_nonexpansive; intros.
  apply sepcon_nonexpansive.
  - apply const_nonexpansive.
  - apply agree_nonexpansive.
Qed.

Lemma ghost_is_pred_nonexpansive2 : forall g H f,
    nonexpansive f ->
    nonexpansive (fun P => ghost_is (singleton g
  (existT (fun RA : Ghost => {a : @G RA | valid a}) unit_PCM
           (exist (fun a : G => valid a) (tt : @G unit_PCM) H),
        pred_of (f P)))).
Proof.
  unfold nonexpansive.
  intros ??????; split; intros ?????; specialize (H0 _ _ _ H1);
  simpl in *; match goal with H : join_sub ?a ?b |- join_sub ?c ?b =>
      assert (a = c) as <-; auto end; simpl;
    rewrite !ghost_fmap_singleton; do 2 f_equal; simpl; f_equal;
    extensionality; apply pred_ext; intros ? []; split; auto;
    eapply H0; try apply necR_refl; auto; apply necR_level in H3; apply ext_level in H4; lia.
Qed.

Lemma agree_nonexpansive2 : forall g f,
    nonexpansive f -> nonexpansive (fun a => agree g (f a)).
Proof.
  intros; unfold agree, own.
  apply exists_nonexpansive; intros.
  unfold Own.
  apply conj_nonexpansive; [apply const_nonexpansive|].
  now apply ghost_is_pred_nonexpansive2.
Qed.

Lemma invariant_nonexpansive2 : forall N f,
    nonexpansive f -> nonexpansive (fun a => invariant N (f a)).
Proof.
  intros; unfold invariant.
  apply exists_nonexpansive; intros.
  apply sepcon_nonexpansive.
  - apply const_nonexpansive.
  - now apply agree_nonexpansive2.
Qed.

(* Consider putting rules for invariants and fancy updates in msl (a la ghost_seplog), and proofs
   in veric (a la own). *)

Lemma ghost_set_empty : forall g s,
  (ghost_set g s = ghost_set g s * ghost_set g (Empty_set))%pred.
Proof.
  intros.
  apply ghost_op.
  hnf; split.
  - constructor.
    intros ? X; inv X.
    inv H0.
  - extensionality; apply prop_ext; split; intro X; [left | inv X]; auto.
    inv H.
Qed.

Lemma wsat_empty_eq : (wsat = wsat * ghost_set g_en (Empty_set))%pred.
Proof.
  unfold wsat.
  repeat (rewrite exp_sepcon1; f_equal; extensionality).
  rewrite !sepcon_andp_prop1; f_equal.
  rewrite !sepcon_assoc; f_equal; f_equal.
  rewrite !(sepcon_comm (ghost_set _ _)), sepcon_assoc; f_equal.
  rewrite sepcon_comm; apply ghost_set_empty.
Qed.

End Invariants.

Lemma make_wsat : emp |-- |==> EX inv_names : invG, wsat.
Proof.
  unfold wsat.
  eapply derives_trans with (Q := (_ * emp)%pred); [rewrite sepcon_emp; apply (ghost_alloc(RA := snap_PCM(ORD := list_order gname)) (Tsh, nil) NoneP); simpl; auto|].
  eapply derives_trans; [apply bupd_frame_r | eapply derives_trans, bupd_trans; apply bupd_mono].
  rewrite exp_sepcon1; apply exp_left; intro g_inv.
  eapply derives_trans; [eapply sepcon_derives with (q' := (|==> _ * emp)%pred); [apply derives_refl |
    rewrite sepcon_emp; apply (ghost_alloc(RA := list_PCM (exclusive_PCM unit)) nil NoneP); simpl; auto]|].
  eapply derives_trans; [apply bupd_frame_l | eapply derives_trans, bupd_trans; apply bupd_mono].
  rewrite exp_sepcon1, exp_sepcon2; apply exp_left; intro g_dis.
  rewrite <- sepcon_assoc.
  eapply derives_trans; [eapply sepcon_derives with (q' := (|==> _ * emp)%pred); [apply derives_refl |
    rewrite sepcon_emp; apply (ghost_alloc(RA := set_PCM) Ensembles.Empty_set NoneP); simpl; auto]|].
  eapply derives_trans; [apply bupd_frame_l | eapply derives_trans, bupd_trans; apply bupd_mono].
  rewrite exp_sepcon1, !exp_sepcon2; apply exp_left; intro g_en.
  rewrite <- sepcon_assoc.
  eapply derives_trans, bupd_intro.
  apply exp_right with {| g_inv := g_inv; g_dis := g_dis; g_en := g_en |}, exp_right with nil, exp_right with nil, exp_right with nil; simpl.
  rewrite !sepcon_andp_prop1; apply andp_right.
  - hnf; intros; simpl; auto.
  - repeat apply sepcon_derives; auto.
    replace (fun i : iname => match i with
                                     | 0%nat | _ => None
                                     end = Some false) with (@Ensembles.Empty_set nat); auto.
    extensionality; apply prop_ext; split; intro H.
    + inv H.
    + hnf in H.
      destruct x; inv H.
Qed.
