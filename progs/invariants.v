From stdpp Require Export coPset.
Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Import List.

(* Where should this sit? *)

Definition cored : mpred := own.cored.

Lemma cored_dup : forall P, P && cored |-- (P && cored) * (P && cored).
Proof.
  apply own.cored_dup.
Qed.

Lemma cored_duplicable : cored = cored * cored.
Proof.
  apply own.cored_duplicable.
Qed.

Lemma own_cored: forall {RA: Ghost} g a pp, join a a a -> own g a pp |-- cored.
Proof.
  intros; apply own.own_cored; auto.
Qed.

Require Import VST.veric.bi.
Require Import VST.msl.sepalg.

Lemma cored_emp: (cored |-- |==> emp)%I.
Proof.
  apply own.cored_emp.
Qed.

Lemma emp_cored : (emp |-- cored)%I.
Proof.
  apply own.emp_cored.
Qed.

Section Invariants.

Instance unit_PCM : Ghost := { valid a := True; Join_G a b c := True }.
Proof. auto. Defined.

Definition pred_of (P : mpred) := SomeP rmaps.Mpred (fun _ => P).

Definition agree g (P : mpred) := own(RA := unit_PCM) g tt (pred_of P).

Lemma agree_dup : forall g P, agree g P = agree g P * agree g P.
Proof.
  intros; apply own_op; constructor.
Qed.

Lemma agree_join : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P1.
Proof.
  intros.
  change (predicates_hered.derives (agree g P1 * agree g P2) ((|> P1 -* |> P2) * agree g P1)).
  intros ? (? & ? & ? & H1 & H2).
  do 3 eexists; [apply core_unit|].
  pose proof (ghost_of_join _ _ _ H) as J.
  change (agree g P1) with (own.own(RA := unit_PCM) g tt (pred_of P1)) in H1.
  destruct H1 as (? & Hid & H1).
  change (agree g P2) with (own.own(RA := unit_PCM) g tt (pred_of P2)) in H2.
  destruct H2 as (? & ? & H2).
  erewrite H1, H2, !own.ghost_fmap_singleton in J.
  apply own.singleton_join_inv in J as ([] & J & Jg).
  inv J; simpl in *.
  inv H4.
  apply SomeP_inj in H5.
  destruct (join_level _ _ _ H) as [Hl1 Hl2]; erewrite Hl1, Hl2 in *.
  assert (approx (level a) P1 = approx (level a) P2) as Heq.
  { apply (@equal_f _ _ (fun _ : list Type => approx (level a) P1) (fun _ : list Type => approx (level a) P2));
      auto.
    apply nil. }
  split.
  - intros ??? Hl J HP1 ? Ha'.
    pose proof (level_core a).
    pose proof (necR_level _ _ Hl).
    apply nec_identity in Hl; [|apply core_identity].
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
    + simpl; erewrite Jg, own.ghost_fmap_singleton; simpl.
      repeat f_equal; auto.
      inv H3; f_equal.
      destruct c0; apply exist_ext; auto.
Qed.

Lemma agree_join2 : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P2.
Proof.
  intros.
  change (predicates_hered.derives (agree g P1 * agree g P2) ((|> P1 -* |> P2) * agree g P2)).
  intros ? (? & ? & ? & H1 & H2).
  do 3 eexists; [apply core_unit|].
  pose proof (ghost_of_join _ _ _ H) as J.
  change (agree g P1) with (own.own(RA := unit_PCM) g tt (pred_of P1)) in H1.
  destruct H1 as (? & Hid & H1).
  change (agree g P2) with (own.own(RA := unit_PCM) g tt (pred_of P2)) in H2.
  destruct H2 as (? & ? & H2).
  erewrite H1, H2, !own.ghost_fmap_singleton in J.
  apply own.singleton_join_inv in J as ([] & J & Jg).
  inv J; simpl in *.
  inv H4.
  apply SomeP_inj in H5.
  destruct (join_level _ _ _ H) as [Hl1 Hl2]; erewrite Hl1, Hl2 in *.
  assert (approx (level a) P1 = approx (level a) P2) as Heq.
  { apply (@equal_f _ _ (fun _ : list Type => approx (level a) P1) (fun _ : list Type => approx (level a) P2));
      auto.
    apply nil. }
  split.
  - intros ??? Hl J HP1 ? Ha'.
    pose proof (level_core a).
    pose proof (necR_level _ _ Hl).
    apply nec_identity in Hl; [|apply core_identity].
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
    + simpl; erewrite Jg, own.ghost_fmap_singleton; simpl.
      repeat f_equal; auto.
      inv H3; f_equal.
      destruct c0; apply exist_ext; auto.
Qed.

Inductive list_join {P : Ghost} : Join (list (option G)) :=
  | list_join_nil_l m: list_join nil m m
  | list_join_nil_r m: list_join m nil m
  | list_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> list_join m1 m2 m3 ->
      list_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
Existing Instance list_join.

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

Instance list_PCM (P : Ghost) : Ghost := { valid a := True; Join_G := list_join }.
Proof.
  - exists (fun _ => nil); auto; constructor.
  - constructor.
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
  - auto.
Defined.

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

(* up *)
Lemma replace_nth_length : forall {A} n l (a : A),
  length (replace_nth n l a) = length l.
Proof.
  induction n; destruct l; simpl; intros; try lia.
  erewrite IHn by lia; auto.
Qed.

(* up *)
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
    erewrite app_nth2, minus_diag in Hjoin by lia; simpl in Hjoin.
    erewrite replace_nth_app, if_false, minus_diag by lia; simpl.
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
  intros; rewrite <- nth_Znth.
  apply nth_replace_nth; auto.
Qed.

Lemma Znth_replace_nth' : forall {A} {d : Inhabitant A} n m l (a : A), m <> Z.of_nat n ->
  Znth m (replace_nth n l a) = Znth m l.
Proof.
  intros.
  destruct (zlt m 0); [rewrite !Znth_underflow; auto|].
  rewrite <- (Z2Nat.id m) by lia.
  rewrite <- !nth_Znth; apply nth_replace_nth'.
  intro; contradiction H; subst.
  erewrite Z2Nat.id by lia; auto.
Qed.

Lemma ghost_list_nth : forall {P : Ghost} g n l (a : G) (Ha : nth n l None = Some a),
  ghost_list g l = ghost_list g (list_singleton n a) * ghost_list g (replace_nth n l None).
Proof.
  intros; apply own_op.
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
  length l3 = Max.max (length l1) (length l2).
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

Instance list_order A : @PCM_order (list_PCM (discrete_PCM A)) list_incl.
Proof.
  constructor.
  - repeat intro; split; auto.
  - repeat intro.
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
               destruct (Max.max_spec (length (removelast a)) (length b)) as [[? Hmax] | [? Hmax]];
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
                  { subst; rewrite minus_diag; simpl.
                    erewrite nth_error_replace_nth by (simpl in *; lia).
                    destruct (nth_error b (length (removelast a))) eqn: Hb; setoid_rewrite Hb; constructor.
                    destruct o; constructor.
                    destruct H0 as [_ Hc].
                    erewrite nth_error_nth in Hb by auto.
                    inv Hb.
                    apply Hc in H7.
                    destruct H as [_ Hc'].
                    specialize (Hc' (length (removelast a))).
                    erewrite app_nth2, minus_diag in Hc' by auto.
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
               erewrite app_nth2, minus_diag; auto.
         -- exists c'; split; auto.
            erewrite (app_removelast_last None), Ha by auto.
            apply list_join_filler with (n0 := 1%nat); auto; simpl in *; lia.
  - split.
    + split; [eapply list_join_length; eauto|].
      intros ?? Hnth.
      apply list_join_nth with (n0 := n) in H.
      rewrite Hnth in H; inv H; auto.
      inv H3; auto.
    + split; [apply join_comm in H; eapply list_join_length; eauto|].
      intros ?? Hnth.
      apply list_join_nth with (n0 := n) in H.
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

Notation union := base.union.

Instance set_PCM : Ghost := { valid := fun _ : coPset => True;
  Join_G a b c := a ## b /\ c = union a b }.
Proof.
  - exists (fun _ => empty); auto.
    intro; split; set_solver.
  - constructor.
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
  - auto.
Defined.

Definition ghost_set g s := own(RA := set_PCM) g s NoneP.

Lemma ghost_set_join : forall g (s1 s2 : coPset),
  ghost_set g s1 * ghost_set g s2 = !!(s1 ## s2) && ghost_set g (union s1 s2).
Proof.
  intros.
  setoid_rewrite own_op_gen.
  - instantiate (1 := union s1 s2).
    unfold ghost_set; apply pred_ext.
    + Intros; entailer!.
      destruct H as (? & [] & ?); auto.
    + Intros; entailer!.
      eexists; repeat (split; auto).
  - intros (? & H & ?); inv H; split; auto.
Qed.

Lemma ghost_set_subset : forall g (s s' : coPset),
  subseteq s' s -> ghost_set g s = ghost_set g s' * ghost_set g (difference s s').
Proof.
  intros.
  apply own_op.
  split.
  - set_solver.
  - apply union_difference_L; auto.
Qed.

Corollary ghost_set_remove : forall g a (s : coPset),
  elem_of a s -> ghost_set g s = ghost_set g (base.singleton a) * ghost_set g (difference s (base.singleton a)).
Proof.
  intros; apply ghost_set_subset.
  set_solver.
Qed.

Definition iname := nat.

Class invG := { g_inv : gname; g_en : gname; g_dis : gname }.

Context {inv_names : invG}.

Definition master_list {A} g (l : list (option A)) := ghost_master1(ORD := list_order A) l g.

(* up *)
Instance Inhabitant_option {A} : Inhabitant (option A) := None.

(* Our ghost state construction makes it awkward to put agree inside other ghost state constructions.
   As a workaround, instead of having one ghost location with a map from indices to agrees,
   we have a map from indices to ghost locations, each with an agree. *)

Instance token_PCM : Ghost := exclusive_PCM unit.

Definition wsat : mpred := EX I : list mpred, EX lg : list gname, EX lb : list (option bool),
  !!(length lg = length I /\ length lb = length I) &&
  master_list g_inv (map (fun i => match Znth i lb with Some _ => Some (Znth i lg)
                                   | None => None end) (upto (length I))) *
  ghost_list g_dis (map (fun o => match o with Some true => Some (Some tt) | _ => None end) lb) *
  ghost_set g_en (list_to_set (map (fun i => Pos.of_nat (S i)) (filter (fun i => decide (nth i lb None = Some false)) (seq 0 (length lb))))) *
  iter_sepcon (fun i => match Znth i lb with
                        | Some true => agree (Znth i lg) (Znth i I) * |> Znth i I
                        | Some false => agree (Znth i lg) (Znth i I)
                        | _ => emp%I end) (upto (length I)).

(* This is what's called ownI in Iris; we could build another layer with namespaces. *)
Definition invariant (i : iname) P : mpred := EX g : gname,
  ghost_snap(ORD := list_order _) (list_singleton i g) g_inv * agree g P.

Lemma nth_singleton : forall {A} n (a : A) d, nth n (list_singleton n a) d = Some a.
Proof.
  intros; unfold list_singleton.
  rewrite app_nth2; rewrite repeat_length; auto.
  rewrite minus_diag; auto.
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
  rewrite <- (replace_nth_same k (list_singleton k a) None) at 3.
  rewrite nth_singleton.
  apply list_join_singleton.
  + rewrite singleton_length; auto.
  + rewrite nth_singleton; repeat constructor; auto.
Qed.

Lemma invariant_dup : forall i P, invariant i P = invariant i P * invariant i P.
Proof.
  intros; unfold invariant; apply pred_ext.
  - Intros g; Exists g g.
    rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- sepcon_assoc.
    erewrite ghost_snap_join.
    erewrite sepcon_assoc, <- agree_dup; apply derives_refl.
    { apply (singleton_join_self(P := discrete_PCM _)).
      constructor; auto. }
  - Intros g1 g2.
    erewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- sepcon_assoc.
    rewrite ghost_snap_join'; Intros l.
    apply (list_join_singleton_inv(P := discrete_PCM _)) in H as (g & H & ?); subst.
    inv H.
    erewrite sepcon_assoc, <- agree_dup.
    Exists g; apply derives_refl.
Qed.

(* up *)
Lemma Zlength_eq : forall {A B} (l1 : list A) (l2 : list B),
  Zlength l1 = Zlength l2 <-> length l1 = length l2.
Proof.
  intros; rewrite !Zlength_correct.
  split; [apply Nat2Z.inj|].
  intro; apply Z2Nat.inj; try lia.
  rewrite !Nat2Z.id; auto.
Qed.

Instance list_Perm {P : Ghost} : Perm_alg (list (option G)).
Proof.
  apply list_PCM.
Qed.

(* up *)
Lemma nth_upto : forall m n d, (n < m)%nat -> nth n (upto m) d = Z.of_nat n.
Proof.
  intros.
  erewrite nth_indep by (rewrite upto_length; auto).
  erewrite nth_Znth, Znth_upto; auto.
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
        subst; rewrite minus_diag; simpl.
        intro X; inv X; auto.
Qed.

Lemma seq_app : forall a b c, seq a (b + c) = seq a b ++ seq (a + b) c.
Proof.
  intros ??; revert a; induction b; simpl; intros; auto.
  rewrite IHb; do 3 f_equal; omega.
Qed.

Lemma filter_ext_in : forall {A} (f g : A -> bool) l, (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  induction l; auto; simpl; intros.
  rewrite -> H by auto.
  rewrite IHl; auto.
Qed.

Lemma filter_none : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  induction l; auto; simpl; intros.
  rewrite H; auto.
Qed.

Lemma wsat_alloc : forall P, (wsat * |> P |-- |==> wsat * EX i : _, invariant i P)%I.
Proof.
  intros; iIntros "[wsat P]".
  unfold wsat.
  iDestruct "wsat" as (l lg lb) "((((% & inv) & dis) & en) & I)".
  iMod (own_alloc(RA := unit_PCM) tt (pred_of P) with "[$]") as (g) "agree"; first (simpl; auto).
  replace (own(RA := unit_PCM) g () (pred_of P)) with (agree g P) by reflexivity.
  rewrite agree_dup.
  iDestruct "agree" as "[agree1 agree2]".
  iMod (own_update_ND(RA := list_PCM token_PCM) _ _ (fun l => exists i, l =
      map (fun o => match o with Some true => Some (Some tt) | _ => None end)
          ((lb ++ repeat None i) ++ [Some true])) with "dis") as (disb) "[% dis]".
  { intros ? (? & ? & _).
    exists (map (fun o => match o with Some true => Some (Some tt) | _ => None end)
      ((lb ++ repeat None (length x - length lb)) ++ [Some true])).
    split; [eauto|].
    exists (x ++ [Some (Some tt)]); split; simpl; auto.
    erewrite !map_app, own.map_repeat; simpl.
    pose proof (list_join_length _ _ _ H0) as Hlen.
    rewrite map_length in Hlen.
    apply join_comm in H0.
    pose proof (list_join_length _ _ _ H0) as Hlen'.
    apply (join_comm(Perm_alg := list_Perm)), (list_join_over c).
    { erewrite app_length, map_length, repeat_length, le_plus_minus_r; auto. }
    apply (join_comm(Perm_alg := list_Perm)), (list_join_filler(P := token_PCM));
      [|rewrite map_length; auto].
    apply join_comm in H0; auto. }
  destruct H0 as [i ?]; subst.
  destruct H.
  assert (Zlength lg = Zlength l) as Hlg by (apply Zlength_eq; auto).
  assert (Zlength lb = Zlength l) as Hlb by (apply Zlength_eq; auto).
  iMod (master_update(ORD := list_order _) _
        (map (fun j => match Znth j ((lb ++ repeat None i) ++ [Some true]) with
                       | Some _ => Some (Znth j ((lg ++ repeat O i) ++ [g]))
                       | None => None
                       end) (upto (length ((l ++ repeat emp%I i) ++ [P])))) with "inv") as "inv".
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
  iMod (make_snap(ORD := list_order _) with "inv") as "[snap inv]".
  iMod (ghost_snap_forget(ORD := list_order _) (list_singleton (length lg + i) g) with "snap") as "snap".
  { apply list_incl_singleton.
    erewrite app_length, upto_app, map_app, app_nth2; erewrite map_length, upto_length, app_length,
      repeat_length; try lia.
    replace (_ - _)%nat with O by lia; simpl.
    erewrite Nat2Z.inj_add, Z.add_0_r.
    rewrite !app_Znth2; erewrite !Zlength_app, !Zlength_repeat, <- Zlength_correct; try lia.
    replace (_ - _) with 0 by lia; replace (_ - _) with 0 by lia; auto. }
  iModIntro; iSplitR "agree2 snap".
  - iExists ((l ++ repeat emp%I i) ++ [P]), ((lg ++ repeat O i) ++ [g]),
         ((lb ++ repeat None i) ++ [Some true]).
    erewrite !(app_length (_ ++ _)); simpl.
    erewrite upto_app, iter_sepcon_app; simpl.
    erewrite Z.add_0_r, <- Zlength_correct, !app_Znth2; erewrite !Zlength_app, !Zlength_repeat; try lia.
    erewrite Hlg, Hlb, Zminus_diag, !Znth_0_cons.
    erewrite prop_true_andp by (erewrite !app_length, !repeat_length; lia).
    iFrame.
    iSplitL "en".
    + rewrite app_length -plus_assoc seq_app filter_app.
      rewrite (filter_none _ (seq _ (_ + 1))).
      rewrite app_nil_r.
      erewrite filter_ext_in; auto.
      * intros ??%in_seq; simpl.
        rewrite <- app_assoc, app_nth1 by lia; auto.
      * intros ??%in_seq; simpl.
        rewrite <- app_assoc, app_nth2 by lia.
        destruct (lt_dec (x - length lb) i); [rewrite app_nth1 | rewrite app_nth2];
          rewrite ?repeat_length; try lia.
        -- rewrite nth_repeat; auto.
        -- destruct (x - length lb - i)%nat; auto; simpl.
          destruct n0; auto.
    + erewrite app_length, upto_app, iter_sepcon_app.
      rewrite <- sepcon_emp at 1; iDestruct "I" as "[I emp]".
      iSplitL "I".
      * erewrite iter_sepcon_func_strong; auto.
        intros ??%In_upto.
        rewrite <- Zlength_correct in *.
        rewrite <- !app_assoc, !app_Znth1 by (rewrite ?Zlength_app; lia); auto.
      * rewrite iter_sepcon_emp'; auto.
        intros ? Hin.
        eapply in_map_iff in Hin as (? & ? & Hin%In_upto); subst.
        rewrite <- Zlength_correct, Zlength_repeat in Hin.
        rewrite <- Zlength_correct, <- app_assoc, app_Znth2 by lia.
        erewrite app_Znth1, Znth_repeat'; auto; try lia.
        rewrite Zlength_repeat; lia.
  - iExists (length l + i)%nat; unfold invariant.
    iExists g; rewrite H; iFrame.
Qed.

Lemma list_to_set_eq : forall (l1 l2 : list positive), (forall x, elem_of x l1 <-> elem_of x l2) ->
  (list_to_set l1 : coPset) = list_to_set l2.
Proof.
  intros.
  apply coPset_leibniz, elem_of_equiv; intros.
  rewrite !elem_of_list_to_set; auto.
Qed.

Lemma wsat_open : forall i P,
  (wsat * invariant i P * ghost_set g_en (base.singleton (Pos.of_nat (S i))) |--
  |==> wsat * |> P * ghost_list g_dis (list_singleton i (Some tt)))%I.
Proof.
  intros; unfold wsat, invariant.
  iIntros "((H & inv1) & en1)". iDestruct "H" as (l lg lb) "((((% & inv) & dis) & en) & I)". iDestruct "inv1" as (g) "[snap agree]".
  iAssert ( !! (i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat) as %Hi.
  { iCombine "snap" "inv" as "inv"; unfold master_list; erewrite snap_master_join1.
    iDestruct "inv" as "[% inv]".
    apply list_incl_singleton in H0.
    destruct (lt_dec i (length lg));
      [|erewrite nth_overflow in H0 by (erewrite map_length, upto_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in H0 by (rewrite upto_length; lia).
    erewrite nth_upto in H0 by lia.
    destruct (Znth (Z.of_nat i) lb); inv H0; iPureIntro; eauto. }
  iMod (@own_dealloc (snap_PCM(ORD := list_order _)) with "snap").
  iModIntro.
  destruct Hi as (? & ? & b & Hi).
  assert (nth i lb None = Some b) as Hi' by (rewrite <- nth_Znth in Hi; auto).
  destruct b.
  erewrite ghost_list_nth with (n := i) by (erewrite nth_map' with (d' := None), Hi'; eauto; lia).
  iDestruct "dis" as "[token dis]".
  erewrite iter_sepcon_Znth with (i0 := Z.of_nat i)
    by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
  erewrite Znth_upto, Hi by lia.
  iDestruct "I" as "((agree' & HP) & I)".
  subst; iDestruct (agree_join with "[agree agree']") as "[imp agree]"; first iFrame.
  iSplitR "token"; last auto.
  iSplitR "HP imp"; last (iApply "imp"; auto).
  iExists l, lg, (replace_nth i lb (Some false)).
  rewrite replace_nth_length prop_true_andp; last auto.
  iSplitR "I agree".
  iSplitR "en en1".
  iSplitR "dis".
  - erewrite map_ext; eauto.
    intros; simpl.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try lia.
    rewrite Hi; auto.
  - rewrite map_replace_nth; auto.
  - iCombine "en en1" as "en"; erewrite ghost_set_join.
    iDestruct "en" as "[% en]".
    erewrite coPset_leibniz; auto; split.
    + intros Hin%elem_of_union; rewrite -> elem_of_list_to_set, elem_of_list_In, in_map_iff in *; destruct Hin as [Hin | Hin].
      * destruct Hin as (x' & ? & Hin); subst.
        apply filter_In in Hin as [Hin ?].
        do 2 eexists; eauto; apply filter_In; split; auto.
        destruct (decide (x' = i)); [subst; rewrite nth_replace_nth | rewrite nth_replace_nth']; auto; lia.
      * apply elem_of_singleton in Hin; subst.
        do 2 eexists; eauto; apply filter_In.
        split; [|rewrite nth_replace_nth; auto; lia].
        apply in_seq; lia.
    + intros Hin; rewrite elem_of_union; rewrite -> elem_of_list_to_set, elem_of_list_In, in_map_iff in *.
      destruct Hin as (x' & ? & Hin); subst.
      destruct (decide (x' = i)); [subst; rewrite elem_of_singleton; auto|].
      left; do 2 eexists; eauto.
      apply filter_In in Hin as [Hin ?]; rewrite filter_In; split; auto.
      erewrite nth_replace_nth' in H2; auto.
  - erewrite iter_sepcon_Znth with (i0 := Z.of_nat i)(l0 := upto _)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite Znth_upto, Znth_replace_nth by lia; iFrame.
    erewrite iter_sepcon_func_strong; auto.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; lia.
  - iCombine "en en1" as "en"; erewrite ghost_set_join.
    iDestruct "en" as "[% en]".
    rewrite -> elem_of_disjoint in H2.
    contradiction (H2 (Pos.of_nat (S i))).
    + rewrite -> elem_of_list_to_set, elem_of_list_In, in_map_iff.
      do 2 eexists; eauto.
      rewrite filter_In; split; [|rewrite Hi'; auto].
      apply in_seq; lia.
    + apply elem_of_singleton; auto.
Qed.

(* up *)
Lemma replace_nth_same' : forall {A} n l (a d : A), nth n l d = a -> replace_nth n l a = l.
Proof.
  intros; subst; apply replace_nth_same.
Qed.

Lemma wsat_close : forall i P,
  (wsat * invariant i P * |> P * ghost_list g_dis (list_singleton i (Some tt)) |--
  |==> wsat * ghost_set g_en (base.singleton (Pos.of_nat (S i))))%I.
Proof.
  intros; unfold wsat, invariant.
  iIntros "(((H & inv1) & HP) & dis1)". iDestruct "H" as (l lg lb) "((((% & inv) & dis) & en) & I)". iDestruct "inv1" as (g) "[snap agree]".
  iAssert ( !!(i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat) as %Hi.
  { iCombine "snap inv" as "inv"; unfold master_list; erewrite snap_master_join1.
    iDestruct "inv" as "[% inv]".
    apply list_incl_singleton in H0.
    destruct (lt_dec i (length lg));
      [|erewrite nth_overflow in H0 by (erewrite map_length, upto_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in H0 by (rewrite upto_length; lia).
    erewrite nth_upto in H0 by lia.
    destruct (Znth (Z.of_nat i) lb); inv H0; eauto. }
  iMod (@own_dealloc (snap_PCM(ORD := list_order _)) with "snap").
  iModIntro.
  destruct Hi as (? & ? & b & Hi).
  assert (nth i lb None = Some b) as Hi' by (rewrite <- nth_Znth in Hi; auto).
  destruct b.
  { iCombine "dis dis1" as "dis".
    iDestruct (own_valid_2(RA := list_PCM _) with "dis") as %H2.
    destruct H2 as (? & J & _).
    apply list_join_nth with (n := i) in J.
    erewrite nth_singleton, nth_map' with (d' := None) in J by lia.
    rewrite Hi' in J; inv J.
    inv H5.
    inv H3. }
  erewrite ghost_set_remove with (a := Pos.of_nat (S i)).
  iDestruct "en" as "[$ en]".
  iExists l, lg, (replace_nth i lb (Some true)).
  rewrite replace_nth_length prop_true_andp; last auto.
  iSplitR "I agree HP".
  iSplitR "en".
  iSplitR "dis dis1".
  - erewrite map_ext; eauto.
    intros.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try lia.
    rewrite Hi; auto.
  - iCombine "dis1 dis" as "dis"; setoid_rewrite <- own_op; auto.
    rewrite map_replace_nth.
    apply (list_join_singleton(P := token_PCM)).
    { rewrite map_length; lia. }
    erewrite nth_map' with (d' := None) by lia.
    rewrite Hi'; constructor.
  - erewrite coPset_leibniz; auto; split.
    + rewrite -> elem_of_difference, !elem_of_list_to_set, !elem_of_list_In, !in_map_iff.
      intros ((? & ? & Hin) & Hout); subst.
      do 2 eexists; eauto.
      rewrite -> filter_In in *; destruct Hin; split; auto.
      rewrite nth_replace_nth'; auto.
      intro; subst; contradiction Hout; apply elem_of_singleton; auto.
    + rewrite -> elem_of_difference, !elem_of_list_to_set, !elem_of_list_In, !in_map_iff.
      intros (x' & ? & Hin) ; subst.
      rewrite -> filter_In in *; destruct Hin as [? Hin].
      destruct (decide (x' = i)); [subst; erewrite nth_replace_nth in Hin by lia; discriminate|].
      erewrite nth_replace_nth' in Hin by auto.
      split; [|rewrite elem_of_singleton; auto].
      do 2 eexists; eauto.
      rewrite filter_In; split; auto.
      intros X%Nat2Pos.inj; congruence.
  - erewrite iter_sepcon_Znth with (i0 := Z.of_nat i)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite iter_sepcon_Znth with (i0 := Z.of_nat i)(l0 := upto _)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite !Znth_upto, !Znth_replace_nth by lia.
    rewrite Hi.
    iDestruct "I" as "[agree' I]".
    subst; iDestruct (agree_join2 with "[agree' agree]") as "[imp agree]"; first iFrame.
    iPoseProof ("imp" with "HP") as "?"; iFrame.
    erewrite iter_sepcon_func_strong; eauto.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; lia.
  - rewrite -> elem_of_list_to_set, elem_of_list_In, in_map_iff.
    do 2 eexists; eauto.
    rewrite filter_In; split; [|rewrite Hi'; auto].
    apply in_seq; lia.
Qed.

Lemma invariant_dealloc : forall i P, (invariant i P |-- |==> emp)%I.
Proof.
  intros; unfold invariant.
  Intro g.
  rewrite <- (emp_sepcon emp%I).
  eapply derives_trans, bupd_sepcon.
  apply sepcon_derives; apply own_dealloc.
Qed.

Lemma invariant_super_non_expansive : forall n N P,
  approx n (invariant N P) = approx n (invariant N (approx n P)).
Proof.
  intros; unfold invariant.
  rewrite !approx_exp; f_equal; extensionality g.
  rewrite !approx_sepcon; f_equal.
  apply own.own_super_non_expansive.
Qed.

Lemma invariant_cored : forall i P, invariant i P |-- cored.
Proof.
  intros; unfold invariant.
  apply exp_left; intro g.
  rewrite cored_duplicable.
  apply sepcon_derives; apply own_cored; hnf; auto; simpl.
  split; auto.
  rewrite !eq_dec_refl.
  apply (singleton_join_self(P := discrete_PCM _)).
  constructor; auto.
Qed.

(* Consider putting rules for invariants and fancy updates in msl (a la ghost_seplog), and proofs
   in veric (a la own). *)

Lemma ghost_set_empty : forall g s,
  ghost_set g s = ghost_set g s * ghost_set g empty.
Proof.
  intros.
  apply own_op.
  hnf; set_solver.
Qed.

Lemma wsat_empty_eq : wsat = wsat * ghost_set g_en empty.
Proof.
  unfold wsat.
  repeat (rewrite exp_sepcon1; f_equal; extensionality).
  erewrite ghost_set_empty at 1.
  apply pred_ext; entailer!.
Qed.

End Invariants.

Lemma make_wsat : (emp |-- |==> EX inv_names : invG, wsat)%I.
Proof.
  unfold wsat.
  iIntros.
  iMod (own_alloc(RA := snap_PCM(ORD := list_order gname)) (Tsh, nil) NoneP with "[$]") as (g_inv) "inv"; first (simpl; auto).
  iMod (own_alloc(RA := list_PCM (exclusive_PCM unit)) nil NoneP with "[$]") as (g_dis) "dis"; first (simpl; auto).
  iMod (own_alloc(RA := set_PCM) empty NoneP with "[$]") as (g_en) "en"; first (simpl; auto).
  iModIntro.
  iExists {| g_inv := g_inv; g_dis := g_dis; g_en := g_en |}.
  iExists nil, nil, nil; simpl; iFrame; auto.
Qed.
