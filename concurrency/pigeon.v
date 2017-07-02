Require Import Omega.

Lemma pigeon:
  forall (n m: nat) (f: nat->option nat),
     (forall i, i < n ->
      exists j, j < m /\ f i = Some j) ->
    (forall i i' j j',
          f i = Some j -> f i' = Some j' ->
          i<>i' -> j<>j') ->
    m>=n.
Proof.
 induction n; intros.
 omega.
 assert (exists last, f n = Some last /\ last<m).
 destruct (H n) as [last [? ?]]. omega. exists last; auto.
 destruct H1 as [last [? H9]].
 destruct m.
 destruct (H 0). omega. destruct H2. omega.
 assert ( (exists i, f i = Some m) \/ ~ (exists i, f i = Some m)).
  admit.
 destruct H2.
 destruct H2 as [i ?].
 pose (g x := if x=?i then Some last else if x=?n then Some m else f x).
 specialize (IHn m g).
 assert (m >= n); [ | omega].
 apply IHn.
 intros. unfold g.
 pose proof (Nat.eqb_spec i0 i). inversion H4; clear H4; subst.
 clear H5.
 exists last; split; auto.
 assert (last <> m). apply (H0 _ _ _ _ H1 H2). omega.
 omega.
 clear H5.
 pose proof (Nat.eqb_spec i0 n). inversion H4; clear H4; subst. clear H5.
 omega.
 clear H5.
 generalize (H i0); intros.
 destruct H4 as [j [? ?]]. omega.
 exists j; split; auto.
 assert (j <> m); [ | omega].
 apply (H0 _ _ _ _ H5 H2); auto.
 intros.
 unfold g in H3, H4.
 pose proof (Nat.eqb_spec i0 i). inversion H6; clear H6; subst; clear H7.
 rewrite <- beq_nat_refl in H3. inversion H3; clear H3; subst.
 assert (E := Nat.eqb_spec i' i). inversion E; clear E; subst.
 omega.
 rewrite <- H3 in H4.
 assert (E := Nat.eqb_spec i' n). inversion E; clear E; subst.
 rewrite <- beq_nat_refl in H4. inversion H4; clear H4; subst j'.
 eapply H0; try eassumption.
 rewrite <- H7 in H4.
 eapply H0; try eassumption. omega.
 assert (E := Nat.eqb_spec i' i). inversion E; clear E; subst.
 rewrite <- beq_nat_refl in H4. inversion H4; clear H4; subst j'.
 assert (E := Nat.eqb_spec i0 i). inversion E; clear E; subst.
 rewrite <- H4 in H3. omega.
 rewrite <- H4 in H3.
 assert (E := Nat.eqb_spec i0 n). inversion E; clear E; subst; rewrite <- H10 in H3.
 inversion H3; clear H3; subst.
 eapply H0; try eassumption. omega.
 clear H10 H4 H6 H8.
 eapply H0; try eassumption.
 rewrite <- H6 in H4.
 assert (E := Nat.eqb_spec i0 i). inversion E; clear E; subst; try omega.
 rewrite <- H10 in H3.
 clear H6 H11 H10.
 assert (E := Nat.eqb_spec i0 n). inversion E; clear E; subst; rewrite <- H6 in H3.
 inversion H3; clear H3; subst j.
 assert (E := Nat.eqb_spec i' n). inversion E; clear E; subst; rewrite <- H3 in H4.
 omega.
 eapply H0; try eassumption. omega.
 assert (E := Nat.eqb_spec i' n). inversion E; clear E; subst; rewrite <- H11 in H4.
 inversion H4; clear H4; subst j'.
 eapply H0; try eassumption.
 eapply H0; try eassumption.
 assert (m >= n); [ | omega].
 apply (IHn m f).
 intros.
 destruct (H i). omega. destruct H4; exists x; split; auto.
 assert (x<>m). contradict H2.
 exists i; subst; auto.
 omega.
 intros.
 apply (H0 _ _ _ _ H3 H4). auto.
Qed.
 intros.

 omega.
 apply H.



 omega.

 omega.
 omega.
 eapply H0; try eassumption. omega.

 rewrite <- H6 in

 omega.


 omega.

 inversion H4; clear H4; subst j'.

 clear H6 H11 H10.


 rewrite <- H10 in H3.



 omega.



 omega.


 omega.

 eapply H0; try eassumption. omega.

 rewrite <- H4 in H3. omega.

 rewrite <- beq_nat_refl in H4. inversion H4; clear H4; subst j'.


 eapply H0; try eassumption. omega.

 rewrite
 eapply H0; try eassumption. omega.

 omega.
 omega.

 SearchAbout (_ =? _).
 clear H7.


 apply (H0 _ _ _ _ H3
 intro; subst j'.
admit. omega.

 assert (j <= S m) by admit.
 omega.

 [ | omega].
 omega.

 exists m. split; auto

 destruct (H n).
 omega.

 SearchAbout (_ =? _).
 red. red.
 simpl.

