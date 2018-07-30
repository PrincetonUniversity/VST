Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Import Ensembles.

(* Where should this sit? *)

Arguments In {_} _ _.
Arguments Included {_} _ _.
Arguments Singleton {_} _.
Arguments Union {_} _ _.
Arguments Add {_} _ _.
Arguments Intersection {_} _ _.
Arguments Complement {_} _.
Arguments Setminus {_} _ _.
Arguments Subtract {_} _ _.
Arguments Disjoint {_} _ _.
Arguments Same_set {_} _ _.

Lemma Included_Full : forall {A} E, Included E (Full_set A).
Proof.
  repeat intro; constructor.
Qed.
Hint Resolve Included_Full.

Notation cored := own.cored.

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

Lemma cored_emp: cored |-- |==> emp.
Proof.
  apply own.cored_emp.
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
  rewrite H1, H2, !own.ghost_fmap_singleton in J.
  apply own.singleton_join_inv in J as ([] & J & Jg).
  inv J; simpl in *.
  inv H4.
  apply SomeP_inj in H5.
  destruct (join_level _ _ _ H) as [Hl1 Hl2]; rewrite Hl1, Hl2 in *.
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
    { split; auto; omega. }
    rewrite Heq in HP1'; destruct HP1'; auto.
  - exists I; split.
    + intro l; simpl.
      apply (resource_at_join _ _ _ l) in H.
      apply Hid in H as <-; auto.
    + simpl; rewrite Jg, own.ghost_fmap_singleton; simpl.
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
  rewrite H1, H2, !own.ghost_fmap_singleton in J.
  apply own.singleton_join_inv in J as ([] & J & Jg).
  inv J; simpl in *.
  inv H4.
  apply SomeP_inj in H5.
  destruct (join_level _ _ _ H) as [Hl1 Hl2]; rewrite Hl1, Hl2 in *.
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
    { split; auto; omega. }
    rewrite Heq in HP1'; destruct HP1'; auto.
  - exists I; split.
    + intro l; simpl.
      apply (resource_at_join _ _ _ l) in H.
      apply Hid in H as <-; auto.
    + simpl; rewrite Jg, own.ghost_fmap_singleton; simpl.
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
  if_tac; [rewrite app_nth1 | rewrite app_nth2]; auto; omega.
Qed.

(* up *)
Lemma replace_nth_length : forall {A} n l (a : A),
  length (replace_nth n l a) = length l.
Proof.
  induction n; destruct l; simpl; intros; try omega.
  rewrite IHn by omega; auto.
Qed.

(* up *)
Lemma replace_nth_app : forall {A} n l1 l2 (a : A),
  replace_nth n (l1 ++ l2) a = if lt_dec n (length l1) then replace_nth n l1 a ++ l2
  else l1 ++ replace_nth (n - length l1) l2 a.
Proof.
  induction n; destruct l1; auto; simpl; intros.
  rewrite IHn.
  if_tac; if_tac; auto; omega.
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
  destruct l; simpl; [omega|].
  repeat constructor.
  apply IHn; omega.
Qed.

Lemma list_join_over : forall {P : Ghost} l l1 l2 l1', (length l <= length l1)%nat ->
  list_join l l1 l1' -> list_join l (l1 ++ l2) (l1' ++ l2).
Proof.
  induction 2; simpl in *.
  - constructor.
  - destruct m; [constructor | simpl in *; omega].
  - constructor; auto.
    apply IHlist_join; omega.
Qed.

Lemma singleton_length : forall {A} n (a : A), length (list_singleton n a) = S n.
Proof.
  intros; unfold list_singleton.
  rewrite app_length, repeat_length; simpl; omega.
Qed.

Lemma list_join_singleton : forall {P : Ghost} n a c l
  (Hn : (n < length l)%nat) (Hjoin: join (Some a) (nth n l None) (Some c)),
  list_join (list_singleton n a) l (replace_nth n l (Some c)).
Proof.
  induction l using rev_ind; simpl; intros; try omega.
  rewrite app_length in Hn; simpl in Hn.
  destruct (eq_dec n (length l)).
  - subst.
    rewrite app_nth2, minus_diag in Hjoin by omega; simpl in Hjoin.
    rewrite replace_nth_app, if_false, minus_diag by omega; simpl.
    apply list_join_app; try (rewrite repeat_length; auto).
    + apply list_join_None; auto.
    + repeat constructor; auto.
  - assert (n < length l)%nat by omega.
    rewrite app_nth1 in Hjoin by auto.
    rewrite replace_nth_app, if_true by auto.
    apply list_join_over, IHl; auto.
    rewrite singleton_length; omega.
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
  induction n; destruct l; auto; simpl; intros; try omega.
  apply IHn; omega.
Qed.

Lemma nth_replace_nth' : forall {A} n m l a (d : A), m <> n ->
  nth m (replace_nth n l a) d = nth m l d.
Proof.
  induction n; destruct l; auto; destruct m; auto; simpl; intros; try omega.
  apply IHn; omega.
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
  rewrite <- (Z2Nat.id m) by omega.
  rewrite <- !nth_Znth; apply nth_replace_nth'.
  intro; contradiction H; subst.
  rewrite Z2Nat.id by omega; auto.
Qed.

Lemma ghost_list_nth : forall {P : Ghost} g n l (a : G) (Ha : nth n l None = Some a),
  ghost_list g l = ghost_list g (list_singleton n a) * ghost_list g (replace_nth n l None).
Proof.
  intros; apply own_op.
  rewrite <- (replace_nth_same n l None) at 2.
  destruct (lt_dec n (length l)); [|rewrite nth_overflow in Ha by omega; discriminate].
  exploit (list_join_singleton n a a (replace_nth n l None)).
  { rewrite replace_nth_length; auto. }
  { rewrite nth_replace_nth by auto; constructor. }
  rewrite replace_nth_replace_nth, Ha; auto.
Qed.

Lemma list_join_length : forall {P : Ghost} l1 l2 l3, list_join l1 l2 l3 ->
  (length l1 <= length l3)%nat.
Proof.
  induction 1; auto; simpl; omega.
Qed.

Lemma list_join_filler : forall {P : Ghost} l1 l2 l3 n, list_join l1 l2 l3 ->
  (n <= length l3 - length l1)%nat -> list_join (l1 ++ repeat None n) l2 l3.
Proof.
  induction 1; simpl; intros.
  - apply list_join_None; omega.
  - destruct n; [|omega].
    rewrite app_nil_r; constructor.
  - constructor; auto.
Qed.

Lemma list_join_nth : forall {P : Ghost} l1 l2 l3 n, list_join l1 l2 l3 ->
  join (nth n l1 None) (nth n l2 None) (nth n l3 None).
Proof.
  intros; revert n.
  induction H; intro.
  - rewrite nth_overflow by (simpl; omega); constructor.
  - rewrite (nth_overflow []) by (simpl; omega); constructor.
  - destruct n; simpl; auto.
Qed.

Lemma list_join_max : forall {P : Ghost} l1 l2 l3, list_join l1 l2 l3 ->
  length l3 = Max.max (length l1) (length l2).
Proof.
  induction 1; simpl; auto.
  rewrite Nat.max_l; auto; omega.
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
  induction n; destruct l; auto; simpl; intros; try omega.
  apply IHn; omega.
Qed.

Lemma nth_error_replace_nth' : forall {A} n m l (a : A), m <> n ->
  nth_error (replace_nth n l a) m = nth_error l m.
Proof.
  induction n; destruct l; auto; destruct m; auto; simpl; intros; try omega.
  apply IHn; omega.
Qed.

Instance list_order A : @PCM_order (list_PCM (discrete_PCM A)) list_incl.
Proof.
  constructor.
  - repeat intro; split; auto.
  - repeat intro.
    destruct H, H0; split; auto; omega.
  - intro a.
    remember (length a) as n.
    revert dependent a; induction n; intros.
    + destruct a; inv Heqn.
      exists b; split; auto.
      change [] with (core b); apply core_unit.
    + assert (a <> []) by (intro; subst; discriminate).
      rewrite (app_removelast_last None) in H, Heqn by auto.
      rewrite app_length in Heqn; simpl in Heqn.
      rewrite Nat.add_1_r in Heqn; inv Heqn.
      specialize (IHn _ eq_refl).
      destruct (IHn b c) as (c' & ? & ?); auto.
      { destruct H as [Hlen H].
        split.
        { rewrite app_length in Hlen; simpl in *; omega. }
        intros ?? Hnth.
        specialize (H n a0).
        rewrite app_nth in H.
        if_tac in H; auto.
        rewrite nth_overflow in Hnth; [discriminate|].
        apply not_lt; auto. }
      pose proof (list_join_length _ _ _ H2).
      pose proof (list_join_length _ _ _ (join_comm H2)).
      destruct (eq_dec (length (removelast a)) (length c')).
      * exists (c' ++ [last a None]); split.
        -- rewrite (app_removelast_last None) at 1 by auto.
           apply join_comm, list_join_over; try omega.
           apply join_comm in H2; auto.
        -- split.
            { destruct H.
              rewrite app_length in *; simpl in *; omega. }
            intros ?? Hnth.
            rewrite app_nth in Hnth.
            if_tac in Hnth; [apply H3; auto|].
            destruct (n - length c')%nat eqn: Hminus; [|destruct n0; discriminate].
            simpl in Hnth.
            apply H.
            rewrite app_nth2 by omega.
            replace (_ - _)%nat with O by omega; auto.
       * destruct (last a None) eqn: Ha.
         -- exists (replace_nth (length (removelast a)) c' (Some g)).
            split.
            ++ apply list_join_alt; intro.
               pose proof (list_join_max _ _ _ H2) as Hlen.
               destruct (Max.max_spec (length (removelast a)) (length b)) as [[? Hmax] | [? Hmax]];
                 setoid_rewrite Hmax in Hlen; try omega.
               hnf in H2; rewrite list_join_alt in H2.
               specialize (H2 n0).
               rewrite (app_removelast_last None) at 1 by auto.
               rewrite Ha.
               destruct (lt_dec n0 (length (removelast a))).
               ** rewrite nth_error_app1 by auto.
                  rewrite nth_error_replace_nth' by omega; auto.
               ** rewrite nth_error_app2 by omega.
                  destruct (eq_dec n0 (length (removelast a))).
                  { subst; rewrite minus_diag; simpl.
                    rewrite nth_error_replace_nth by (simpl in *; omega).
                    destruct (nth_error b (length (removelast a))) eqn: Hb; setoid_rewrite Hb; constructor.
                    destruct o; constructor.
                    destruct H0 as [_ Hc].
                    erewrite nth_error_nth in Hb by auto.
                    inv Hb.
                    apply Hc in H7.
                    destruct H as [_ Hc'].
                    specialize (Hc' (length (removelast a))).
                    rewrite app_nth2, minus_diag in Hc' by auto.
                    setoid_rewrite Hc' in H7; [|reflexivity].
                    inv H7; constructor; auto. }
                  { destruct (_ - _)%nat eqn: Hminus; [omega | simpl].
                    rewrite nth_error_nil, nth_error_replace_nth' by (simpl in *; omega).
                    destruct (nth_error_length n0 (removelast a)) as [_ Hnone].
                    setoid_rewrite Hnone in H2; [auto | omega]. }
            ++ destruct H3.
               split.
               { rewrite replace_nth_length; auto. }
               intros ?? Hnth.
               destruct (eq_dec n0 (length (removelast a)));
                 [|rewrite nth_replace_nth' in Hnth; auto].
               subst; rewrite nth_replace_nth in Hnth by (simpl in *; omega).
               inv Hnth.
               apply H.
               rewrite app_nth2, minus_diag; auto.
         -- exists c'; split; auto.
            rewrite (app_removelast_last None), Ha by auto.
            apply list_join_filler with (n0 := 1%nat); auto; simpl in *; omega.
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
      simpl in *; omega.
    + destruct H as [? Hnth].
      destruct b; constructor.
      * destruct o; [|constructor].
        specialize (Hnth O _ eq_refl); simpl in Hnth.
        subst; repeat constructor.
      * apply IHa.
        split; [simpl in *; omega|].
        intros.
        apply (Hnth (S n)); auto.
Qed.

Instance set_PCM A : Ghost := { valid := fun _ : Ensemble A => True;
   Join_G a b c := Disjoint a b /\ c = Union a b }.
Proof.
  - exists (fun _ => Empty_set _); auto.
    intro; split.
    + constructor; intros ??.
      inv H; contradiction.
    + apply Extensionality_Ensembles; split.
      * repeat intro.
        constructor 2; auto.
      * repeat intro.
        inv H; auto; contradiction.
  - constructor.
    + intros.
      inv H; inv H0; auto.
    + intros.
      inv H; inv H0.
      eexists; split; [split; eauto | split].
      * constructor.
        intros ? Hin; inv Hin.
        inv H.
        apply (H3 x); constructor; auto.
        constructor 2; auto.
      * constructor.
        intros ? Hin; inv Hin.
        inv H2.
        -- inv H1.
           apply (H2 x); constructor; auto.
        -- inv H.
           apply (H2 x); repeat constructor; auto.
      * apply Extensionality_Ensembles; split.
        -- repeat intro.
           inv H0; [|repeat constructor 2; auto].
           inv H2; [constructor 1 | constructor 2; constructor 1]; auto.
        -- repeat intro.
           inv H0; [repeat constructor 1; auto|].
           inv H2; [constructor 1; constructor 2 | constructor 2]; auto.
    + intros.
      inv H.
      split.
      * inv H0; constructor.
        intros ? Hin; inv Hin.
        apply (H x); constructor; auto.
      * apply Extensionality_Ensembles; split;
          repeat intro; inv H; try solve [constructor 1; auto]; try solve [constructor 2; auto].
    + intros.
      inv H; inv H0.
      rewrite H2.
      apply Extensionality_Ensembles; split.
      * intros ? Hin.
        inv Hin; [|constructor 1; constructor 2; auto].
        inv H0; [repeat constructor 1; auto | constructor 2; auto].
      * intros ? Hin.
        inv Hin; auto.
        constructor 1; constructor 2; auto.
  - auto.
Defined.

Definition ghost_set {A} g s := own(RA := set_PCM A) g s NoneP.

Lemma ghost_set_join : forall {A} g (s1 s2 : Ensemble A),
  ghost_set g s1 * ghost_set g s2 = !!(Disjoint s1 s2) && ghost_set g (Union s1 s2).
Proof.
  intros.
  setoid_rewrite own_op_gen.
  - instantiate (1 := Union s1 s2).
    unfold ghost_set; apply pred_ext.
    + Intros; entailer!.
      destruct H as (? & H & ?); inv H; auto.
    + Intros; entailer!.
      eexists; repeat (split; auto).
  - intros (? & H & ?); inv H; split; auto.
Qed.

Lemma ghost_set_subset : forall {A} g (s s' : Ensemble A)
  (Hdec : forall a, In s' a \/ ~In s' a),
  Included s' s -> ghost_set g s = ghost_set g s' * ghost_set g (Setminus s s').
Proof.
  intros.
  apply own_op.
  split.
  - constructor; intros ? Hin.
    inv Hin.
    inv H1; contradiction.
  - apply Extensionality_Ensembles; split; intros ? Hin.
    + destruct (Hdec x).
      * constructor 1; auto.
      * constructor 2; constructor; auto.
    + inv Hin; auto.
      inv H0; auto.
Qed.

Corollary ghost_set_remove : forall {A} g a (s : Ensemble A) (Hdec : forall b, b = a \/ b <> a),
  In s a -> ghost_set g s = ghost_set g (Singleton a) * ghost_set g (Subtract s a).
Proof.
  intros; apply ghost_set_subset.
  - intro x; destruct (Hdec x).
    + subst; left; constructor.
    + right; intro Hin; inv Hin; contradiction.
  - intros ? Hin.
    inv Hin; auto.
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
  ghost_set g_en (fun i : iname => nth i lb None = Some false) *
  iter_sepcon (fun i => match Znth i lb with
                        | Some true => agree (Znth i lg) (Znth i I) * |> Znth i I
                        | Some false => agree (Znth i lg) (Znth i I)
                        | _ => emp end) (upto (length I)).

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
    rewrite sepcon_assoc, <- agree_dup; apply derives_refl.
    { apply (singleton_join_self(P := discrete_PCM _)).
      constructor; auto. }
  - Intros g1 g2.
    rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- sepcon_assoc.
    rewrite ghost_snap_join'; Intros l.
    apply (list_join_singleton_inv(P := discrete_PCM _)) in H as (g & H & ?); subst.
    inv H.
    rewrite sepcon_assoc, <- agree_dup.
    Exists g; apply derives_refl.
Qed.

(* up *)
Lemma Zlength_eq : forall {A B} (l1 : list A) (l2 : list B),
  Zlength l1 = Zlength l2 <-> length l1 = length l2.
Proof.
  intros; rewrite !Zlength_correct.
  split; [apply Nat2Z.inj|].
  intro; apply Z2Nat.inj; try omega.
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
  rewrite nth_Znth, Znth_upto; auto.
  split; [omega|].
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
      destruct (lt_dec n (length l)); [omega|].
      rewrite nth_overflow in H by omega; discriminate.
    + intros ??.
      unfold list_singleton.
      destruct (lt_dec n0 n).
      * rewrite app_nth1 by (rewrite repeat_length; auto).
        rewrite nth_repeat; discriminate.
      * rewrite app_nth2; rewrite repeat_length; try omega.
        destruct (eq_dec n0 n); [|rewrite nth_overflow by (simpl; omega); discriminate].
        subst; rewrite minus_diag; simpl.
        intro X; inv X; auto.
Qed.

Lemma wsat_alloc : forall P, wsat * |> P |-- |==> wsat * EX i : _, invariant i P.
Proof.
  intro; unfold wsat.
  Intros I lg lb.
  rewrite <- emp_sepcon at 1; eapply derives_trans; [apply sepcon_derives, derives_refl|].
  { apply (own_alloc(RA := unit_PCM) tt (pred_of P)); simpl; auto. }
  eapply derives_trans; [apply bupd_frame_r|].
  eapply derives_trans, bupd_trans; apply bupd_mono.
  Intro g.
  fold (agree g P).
  rewrite agree_dup.
  eapply derives_trans.
  { rewrite sepcon_comm, 3sepcon_assoc.
    rewrite (sepcon_comm (master_list _ _)), sepcon_assoc.
    apply sepcon_derives, derives_refl.
    apply own_update_ND with (B := fun l => exists i, l =
      map (fun o => match o with Some true => Some (Some tt) | _ => None end)
          ((lb ++ repeat None i) ++ [Some true])).
    intros ? (? & ? & _).
    exists (map (fun o => match o with Some true => Some (Some tt) | _ => None end)
      ((lb ++ repeat None (length x - length lb)) ++ [Some true])).
    split; [eauto|].
    exists (x ++ [Some (Some tt)]); split; simpl; auto.
    rewrite !map_app, own.map_repeat; simpl.
    pose proof (list_join_length _ _ _ H1) as Hlen.
    rewrite map_length in Hlen.
    apply join_comm in H1.
    pose proof (list_join_length _ _ _ H1) as Hlen'.
    apply (join_comm(Perm_alg := list_Perm)), (list_join_over c).
    { rewrite app_length, map_length, repeat_length, le_plus_minus_r; auto. }
    apply (join_comm(Perm_alg := list_Perm)), (list_join_filler(P := token_PCM));
      [|rewrite map_length; auto].
    apply join_comm in H1; auto. }
  eapply derives_trans; [apply bupd_frame_r|].
  eapply derives_trans, bupd_trans; apply bupd_mono.
  Intros lb'.
  destruct H1 as [i ?]; subst.
  assert (Zlength lg = Zlength I) as Hlg by (apply Zlength_eq; auto).
  assert (Zlength lb = Zlength I) as Hlb by (apply Zlength_eq; auto).
  eapply derives_trans.
  { rewrite sepcon_comm, !sepcon_assoc.
    apply sepcon_derives, derives_refl.
    eapply derives_trans.
    - apply (master_update(ORD := list_order _) _
        (map (fun j => match Znth j ((lb ++ repeat None i) ++ [Some true]) with
                       | Some _ => Some (Znth j ((lg ++ repeat O i) ++ [g]))
                       | None => None
                       end) (upto (length ((I ++ repeat emp i) ++ [P]))))).
      rewrite <- !app_assoc, app_length, upto_app, map_app.
      split.
      { rewrite app_length, !map_length; omega. }
      intros ?? Hn.
      rewrite app_nth, map_length.
      if_tac; [|rewrite nth_overflow in Hn by (rewrite map_length; omega); discriminate].
      rewrite nth_map' with (d' := 0) in * by auto.
      rewrite upto_length in *.
      assert (Z.of_nat n < Zlength I).
      { rewrite Zlength_correct; apply Nat2Z.inj_lt; auto. }
      rewrite nth_upto in * by auto.
      rewrite !app_Znth1 by omega; auto.
    - eapply derives_trans, bupd_trans.
      apply bupd_mono, make_snap. }
  eapply derives_trans; [apply bupd_frame_r|].
  eapply derives_trans, bupd_trans; apply bupd_mono.
  eapply derives_trans.
  { rewrite !sepcon_assoc; apply sepcon_derives, derives_refl.
    apply ghost_snap_forget with (v1 := list_singleton (length lg + i) g).
    apply list_incl_singleton.
    rewrite app_length, upto_app, map_app, app_nth2; rewrite map_length, upto_length, app_length,
      repeat_length; try omega.
    replace (_ - _)%nat with O by omega; simpl.
    rewrite Nat2Z.inj_add, Z.add_0_r.
    rewrite !app_Znth2; rewrite !Zlength_app, !Zlength_repeat, <- Zlength_correct; try omega.
    replace (_ - _) with 0 by omega; replace (_ - _) with 0 by omega; auto. }
  eapply derives_trans; [apply bupd_frame_r|].
  apply bupd_mono.
  Exists ((I ++ repeat emp i) ++ [P]) ((lg ++ repeat O i) ++ [g])
         ((lb ++ repeat None i) ++ [Some true]) (length I + i)%nat.
  rewrite !(app_length (_ ++ _)), !H; simpl.
  rewrite upto_app, iter_sepcon_app; simpl.
  rewrite Z.add_0_r, <- Zlength_correct, !app_Znth2; rewrite !Zlength_app, !Zlength_repeat; try omega.
  rewrite Hlg, Hlb, Zminus_diag, !Znth_0_cons.
  unfold invariant, master_list, ghost_master1, ghost_list.
  Exists g; entailer!.
  { rewrite !app_length, !repeat_length; omega. }
  rewrite !sepcon_assoc, sepcon_comm, !sepcon_assoc; repeat apply sepcon_derives; try apply derives_refl.
  - apply derives_refl'; f_equal; apply Extensionality_Ensembles.
    split; intro; unfold In.
    + intro Hx; rewrite <- app_assoc, app_nth.
      if_tac; auto.
      rewrite nth_overflow in Hx by omega; discriminate.
    + rewrite <- app_assoc, !app_nth.
      if_tac; auto.
      if_tac.
      * pose proof (nth_In _ None H2) as Hin.
        apply repeat_spec in Hin as ->; discriminate.
      * destruct (_ - _ - _)%nat; simpl; try discriminate.
        destruct n; discriminate.
  - rewrite app_length, upto_app, iter_sepcon_app.
    rewrite <- sepcon_emp at 1; apply sepcon_derives.
    + apply derives_refl', iter_sepcon_func_strong.
      intros ??%In_upto.
      rewrite <- Zlength_correct in *.
      rewrite <- !app_assoc, !app_Znth1 by (rewrite ?Zlength_app; omega); auto.
    + apply derives_refl'; symmetry; apply iter_sepcon_emp'.
      intros ? Hin.
      eapply in_map_iff in Hin as (? & ? & Hin%In_upto); subst.
      rewrite <- Zlength_correct, Zlength_repeat in Hin.
      rewrite <- Zlength_correct, <- app_assoc, app_Znth2 by omega.
      rewrite app_Znth1, Znth_repeat'; auto; try omega.
      rewrite Zlength_repeat; omega.
Qed.

Lemma wsat_open : forall i P,
  wsat * invariant i P * ghost_set g_en (Singleton i) |--
  |==> wsat * |> P * ghost_list g_dis (list_singleton i (Some tt)).
Proof.
  intros; unfold wsat, invariant.
  Intros I lg lb g.
  rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)).
  assert_PROP (i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat as Hi.
  { rewrite <- !sepcon_assoc.
    unfold master_list; rewrite snap_master_join1; Intros.
    apply list_incl_singleton in H1.
    destruct (lt_dec i (length lg));
      [|rewrite nth_overflow in H1 by (rewrite map_length, upto_length; omega); discriminate].
    rewrite nth_map' with (d' := 0) in H1 by (rewrite upto_length; omega).
    rewrite nth_upto in H1 by omega.
    destruct (Znth (Z.of_nat i) lb); inv H1; entailer!; eauto. }
  rewrite !sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply own_dealloc|].
  eapply derives_trans; [apply bupd_frame_r | apply bupd_mono].
  Exists I lg (replace_nth i lb (Some false)).
  destruct Hi as (? & ? & b & Hi).
  rewrite replace_nth_length; entailer!.
  assert (nth i lb None = Some b) as Hi' by (rewrite <- nth_Znth in Hi; auto).
  destruct b.
  erewrite ghost_list_nth with (n := i) by (rewrite nth_map' with (d' := None), Hi'; eauto; omega).
  cancel.
  rewrite iter_sepcon_Znth with (i0 := Z.of_nat i)
    by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; omega).
  rewrite Znth_upto, Hi by omega.
  rewrite (sepcon_comm _ (agree _ _)), <- !sepcon_assoc, (sepcon_comm _ (agree _ _)).
  rewrite <- !sepcon_assoc, 5sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply agree_join|].
  rewrite <- !sepcon_assoc, (sepcon_comm _ (|> _)).
  rewrite <- !sepcon_assoc, 5sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
  cancel.
  rewrite !sepcon_assoc, (sepcon_comm (iter_sepcon _ _)), sepcon_comm.
  rewrite !sepcon_assoc; apply sepcon_derives, sepcon_derives;
    [| | rewrite <- sepcon_assoc; apply sepcon_derives].
  - erewrite map_ext; [apply derives_refl|].
    intros; simpl.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try omega.
    rewrite Hi; auto.
  - rewrite map_replace_nth; apply derives_refl.
  - rewrite ghost_set_join; Intros.
    apply derives_refl'; f_equal.
    apply Extensionality_Ensembles; split.
    + intros ? Hin; unfold In.
      inv Hin.
      * destruct (eq_dec x i); [subst; rewrite nth_replace_nth | rewrite nth_replace_nth'];
          auto; omega.
      * inv H3.
        rewrite nth_replace_nth; auto; omega.
    + intros ? Hin; unfold In in Hin.
      destruct (eq_dec x i); [subst; constructor 2; constructor|].
      rewrite nth_replace_nth' in Hin by auto.
      constructor 1; auto.
  - rewrite iter_sepcon_Znth with (i0 := Z.of_nat i)(l := upto _)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; omega).
    rewrite Znth_upto, Znth_replace_nth by omega; cancel.
    apply derives_refl', iter_sepcon_func_strong.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; omega.
  - rewrite sepcon_comm, <- !sepcon_assoc, (sepcon_comm _ (ghost_set _ _)).
    rewrite <- !sepcon_assoc, ghost_set_join; Intros.
    inv H2.
    contradiction (H3 i).
    repeat constructor; auto.
Qed.

(* up *)
Lemma replace_nth_same' : forall {A} n l (a d : A), nth n l d = a -> replace_nth n l a = l.
Proof.
  intros; subst; apply replace_nth_same.
Qed.

Lemma wsat_close : forall i P,
  wsat * invariant i P * |> P * ghost_list g_dis (list_singleton i (Some tt)) |--
  |==> wsat * ghost_set g_en (Singleton i).
Proof.
  intros; unfold wsat, invariant.
  Intros I lg lb g.
  rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)).
  assert_PROP (i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat as Hi.
  { rewrite <- !sepcon_assoc.
    unfold master_list; rewrite snap_master_join1; Intros.
    apply list_incl_singleton in H1.
    destruct (lt_dec i (length lg));
      [|rewrite nth_overflow in H1 by (rewrite map_length, upto_length; omega); discriminate].
    rewrite nth_map' with (d' := 0) in H1 by (rewrite upto_length; omega).
    rewrite nth_upto in H1 by omega.
    destruct (Znth (Z.of_nat i) lb); inv H1; entailer!; eauto. }
  rewrite !sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply own_dealloc|].
  eapply derives_trans; [apply bupd_frame_r | apply bupd_mono].
  Exists I lg (replace_nth i lb (Some true)).
  destruct Hi as (? & ? & b & Hi).
  rewrite replace_nth_length; entailer!.
  assert (nth i lb None = Some b) as Hi' by (rewrite <- nth_Znth in Hi; auto).
  destruct b.
  { rewrite (sepcon_comm _ (ghost_list _ _)), (sepcon_comm _ (ghost_list _ _)), <- !sepcon_assoc.
    rewrite 4sepcon_assoc; eapply derives_trans.
    { apply sepcon_derives, derives_refl.
      apply prop_and_same_derives, own_valid_2. }
    Intros.
    destruct H2 as (? & J & _).
    apply list_join_nth with (n := i) in J.
    rewrite nth_singleton, nth_map' with (d' := None) in J by omega.
    rewrite Hi' in J; inv J.
    inv H5.
    inv H6. }
  rewrite ghost_set_remove with (a := i); auto; [|intro; omega].
  cancel.
  rewrite 5sepcon_assoc, (sepcon_comm (ghost_list _ _)).
  rewrite !sepcon_assoc; apply sepcon_derives;
    [|rewrite (sepcon_comm _ (_ * iter_sepcon _ _)), !sepcon_assoc; apply sepcon_derives;
      [|rewrite <- !sepcon_assoc, sepcon_assoc; apply sepcon_derives]].
  - erewrite map_ext; [apply derives_refl|].
    intros.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try omega.
    rewrite Hi; auto.
  - apply derives_refl'; f_equal.
    apply Extensionality_Ensembles; split.
    + intros ? Hin; unfold In.
      inv Hin.
      rewrite nth_replace_nth'; auto.
      intro; subst; contradiction H3; constructor.
    + intros ? Hin; unfold In in Hin.
      destruct (eq_dec x i); [subst; rewrite nth_replace_nth in Hin by omega; discriminate|].
      rewrite nth_replace_nth' in Hin by auto.
      constructor; auto.
      intro Hx; inv Hx; contradiction.
  - rewrite iter_sepcon_Znth with (i0 := Z.of_nat i)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; omega).
    rewrite iter_sepcon_Znth with (i0 := Z.of_nat i)(l := upto _)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; omega).
    rewrite !Znth_upto, !Znth_replace_nth by omega.
    rewrite Hi.
    sep_apply (agree_join2 (Znth (Z.of_nat i) lg) P (Znth (Z.of_nat i) I)).
    sep_apply (modus_ponens_wand (|> P) (|> Znth (Z.of_nat i) I)); cancel.
    apply derives_refl', iter_sepcon_func_strong.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; omega.
  - apply derives_refl'; symmetry; apply own_op.
    rewrite map_replace_nth.
    apply (list_join_singleton(P := token_PCM)).
    { rewrite map_length; omega. }
    rewrite nth_map' with (d' := None) by omega.
    rewrite Hi'; constructor.
Qed.

Lemma invariant_dealloc : forall i P, invariant i P |-- |==> emp.
Proof.
  intros; unfold invariant.
  Intro g.
  rewrite <- (emp_sepcon emp).
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
  Intro g; rewrite cored_duplicable.
  apply sepcon_derives; apply own_cored; hnf; auto; simpl.
  split; auto.
  rewrite !eq_dec_refl.
  apply (singleton_join_self(P := discrete_PCM _)).
  constructor; auto.
Qed.

(* Consider putting rules for invariants and fancy updates in msl (a la ghost_seplog), and proofs
   in veric (a la own). *)

Lemma Setminus_self : forall {A} s, Setminus s s = Empty_set A.
Proof.
  intros; apply Extensionality_Ensembles; split; intros ? X; inv X; contradiction.
Qed.

Lemma Included_self : forall {A} s, @Included A s s.
Proof.
  repeat intro; auto.
Qed.

Lemma ghost_set_empty : forall {A} g (s : Ensemble A),
  ghost_set g s = ghost_set g s * ghost_set g (Empty_set A).
Proof.
  intros.
  apply own_op.
  split.
  - constructor; intros ? X; inv X.
    inv H0.
  - apply Extensionality_Ensembles; split; intros ? X.
    + constructor 1; auto.
    + inv X; auto.
      inv H.
Qed.

Lemma wsat_empty_eq : wsat = wsat * ghost_set g_en (Empty_set iname).
Proof.
  unfold wsat.
  repeat (rewrite exp_sepcon1; f_equal; extensionality).
  rewrite ghost_set_empty at 1.
  apply pred_ext; entailer!.
Qed.

End Invariants.

Lemma make_wsat : emp |-- |==> EX inv_names : invG, wsat.
Proof.
  unfold wsat.
  rewrite <- 2emp_sepcon at 1.
  eapply derives_trans; [apply sepcon_derives, sepcon_derives|].
  - apply (own_alloc(RA := snap_PCM(ORD := list_order gname)) (Tsh, nil)), I.
  - apply (own_alloc(RA := list_PCM (exclusive_PCM unit)) nil), I.
  - apply (own_alloc(RA := set_PCM iname) (Empty_set _)), I.
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply bupd_sepcon]|].
    eapply derives_trans; [apply bupd_sepcon|].
    apply bupd_mono.
    Intros g_inv g_dis g_en.
    Exists {| g_inv := g_inv; g_dis := g_dis; g_en := g_en |}.
    Exists (@nil mpred) (@nil gname) (@nil (option bool)); simpl; entailer!.
    apply sepcon_derives; [apply sepcon_derives|].
    + apply derives_refl.
    + apply derives_refl.
    + apply derives_refl'; unfold ghost_set; f_equal.
      apply Extensionality_Ensembles; split.
      * intros ? X; inv X.
      * intros ? X.
        destruct x; inv X.
Qed.
