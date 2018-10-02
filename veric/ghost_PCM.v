Require Export VST.msl.msl_standard.
Require Export VST.veric.base.
Require Export VST.veric.shares.
Require Import VST.msl.ghost.

Section Reference.
(* One common kind of PCM is one in which a central authority has a reference copy, and clients pass around
   partial knowledge. When a client recovers all pieces, it can gain full knowledge. *)
(* This is related to the snapshot PCM, but the snapshots aren't duplicable. *)

Lemma join_Bot : forall a b, sepalg.join a b Share.bot -> a = Share.bot /\ b = Share.bot.
Proof.
  intros ?? (? & ?).
  apply lub_bot_e; auto.
Qed.

Global Instance pos_PCM (P : Ghost) : Ghost := { G := option (share * G);
  valid a := match a with Some (sh, _) => sh <> Share.bot | _ => True end;
  Join_G a b c := match a, b, c with
  | Some (sha, a'), Some (shb, b'), Some (shc, c') =>
      sha <> Share.bot /\ shb <> Share.bot /\ sepalg.join sha shb shc /\ join a' b' c'
  | Some (sh, a), None, Some c' | None, Some (sh, a), Some c' => c' = (sh, a)
  | None, None, None => True
  | _, _, _ => False
  end }.
Proof.
  2: constructor.
  - exists (fun _ => None); auto.
    intros [[]|]; constructor.
  - intros [[]|] [[]|] [[]|] [[]|]; unfold join; simpl; auto; try contradiction; try congruence.
    intros (? & ? & ? & ?) (? & ? & ? & ?); f_equal; f_equal; eapply join_eq; eauto.
  - intros [[]|] [[]|] [[]|] [[]|] [[]|]; try contradiction; unfold join; simpl;
      intros; decompose [and] H; decompose [and] H0;
      repeat match goal with H : (_, _) = (_, _) |- _ => inv H end;
      try solve [eexists (Some _); split; auto; simpl; auto]; try solve [exists None; split; auto].
    + destruct (join_assoc H2 H6) as (sh' & ? & ?), (join_assoc H5 H9) as (a' & ? & ?).
      exists (Some (sh', a')); repeat (split; auto).
      intro; subst.
      apply join_Bot in H8 as []; auto.
    + exists (Some (s2, g2)); auto.
  - intros [[]|] [[]|] [[]|]; try contradiction; unfold join; auto.
    intros (? & ? & ? & ?); split; auto; split; auto; split; apply join_comm; auto.
  - intros [[]|] [[]|] [[]|] [[]|]; try contradiction; auto.
    intros (? & ? & ? & ?) (? & ? & ? & ?); f_equal; f_equal; eapply join_positivity; eauto.
  - intros [[]|] [[]|] [[]|]; try contradiction; auto.
    + intros []; auto.
    + unfold join; simpl; congruence.
Defined.

Definition completable {P : Ghost} (a: @G (pos_PCM P)) r := exists x, join a x (Some (Tsh, r)).

Global Instance ref_PCM (P : Ghost) : Ghost :=
{ valid a := valid (fst a) /\ match snd a with Some r => completable (fst a) r | None => True end;
  Join_G a b c := @Join_G (pos_PCM P) (fst a) (fst b) (fst c) /\
    @psepalg.Join_lower _ (psepalg.Join_discrete _) (snd a) (snd b) (snd c) }.
Proof.
  - apply sepalg_generators.Sep_prod.
    + apply @Sep_G.
    + apply psepalg.Sep_option.
  - apply sepalg_generators.Perm_prod.
    + apply @Perm_G.
    + apply psepalg.Perm_option.
  - intros ??? [? J] []; split; [eapply join_valid; eauto|].
    destruct a, b, c; simpl in *; inv J; auto.
    + destruct o1; auto.
      destruct H1.
      destruct (join_assoc H H1) as (? & ? & ?); eexists; eauto.
    + inv H2.
Defined.

End Reference.

Instance exclusive_PCM A : Ghost := { valid a := True; Join_G := Join_lower (Join_discrete A) }.
Proof. auto. Defined.

Definition ext_PCM Z : Ghost := ref_PCM (exclusive_PCM Z).

Lemma valid_ext : forall {Z} (ora : Z), @valid (ext_PCM _) (Some (Tsh, Some ora), None).
Proof.
  intros; simpl; split; auto.
  apply Share.nontrivial.
Qed.

Definition ext_ghost {Z} (ora : Z) : {g : ghost.Ghost & {a : ghost.G | ghost.valid a}} :=
  existT _ (ext_PCM _) (exist _ _ (valid_ext ora)).

Lemma valid_ext_ref : forall {Z} (ora : Z), @valid (ext_PCM _) (None, Some (Some ora)).
Proof.
  intros; simpl; split; auto.
  eexists (Some (_, _)); constructor.
Qed.

Definition ext_ref {Z} (ora : Z) : {g : ghost.Ghost & {a : ghost.G | ghost.valid a}} :=
  existT _ (ext_PCM _) (exist _ _ (valid_ext_ref ora)).