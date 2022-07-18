Require Import VST.floyd.proofauto.
Import Share.
Import sepalg.

(*

Definition shave (sh: share) : share * share :=
  (fst (split (glb sh Lsh)),
   lub (snd (split (glb sh Lsh))) (glb sh Rsh)).

Definition cleave: share -> share * share := slice.cleave.

Lemma shave_join:
   forall sh,  join (fst (shave sh)) (snd (shave sh)) sh.
Proof.
intros.
unfold shave.
split.
simpl.
-
rewrite distrib1.
destruct (split (glb sh Lsh)) eqn:?H.
simpl.
rewrite (split_disjoint _ _ _ H).
rewrite lub_commute, lub_bot.
rewrite <- glb_assoc.
rewrite glb_commute.
apply sub_glb_bot with Lsh.
2: apply glb_Rsh_Lsh.
exists (lub t1 (glb (comp sh) Lsh)).
split.
rewrite distrib2.
rewrite <- glb_assoc.
rewrite (glb_assoc t0).
rewrite (distrib1 sh).
rewrite comp2.
rewrite lub_bot.
rewrite (glb_commute sh).
rewrite <- (glb_assoc t0).
apply split_disjoint in H. rewrite H.
rewrite (glb_commute bot), glb_bot.
rewrite (glb_commute bot), glb_bot.
auto.
rewrite lub_commute.
rewrite distrib2.
rewrite <- (lub_commute t0).
rewrite <- lub_assoc.
rewrite (split_together _ _ _ H).
rewrite distrib2.
rewrite (glb_commute sh), <- (lub_commute Lsh), lub_absorb.
rewrite (glb_commute (lub _ _)).
rewrite (distrib1 Lsh).
rewrite <- (glb_assoc Lsh Lsh).
rewrite glb_idem.
rewrite share_distrib2'.
rewrite lub_idem.
rewrite (lub_commute sh), glb_absorb.
rewrite comp1.
rewrite glb_top.
rewrite glb_absorb.
rewrite lub_assoc.
rewrite (lub_commute (glb _ _)).
rewrite distrib2.
rewrite comp1.
rewrite (glb_commute top), glb_top.
rewrite <- lub_assoc.
rewrite distrib1.
rewrite glb_idem.
rewrite lub_commute, lub_absorb.
auto.
-
destruct (split (glb sh Lsh)) eqn:?H.
simpl.
rewrite <- lub_assoc.
rewrite (split_together _ _ _ H).
rewrite share_distrib2'.
rewrite lub_Lsh_Rsh.
rewrite glb_top.
rewrite lub_idem.
rewrite (lub_commute Lsh).
rewrite glb_absorb.
rewrite glb_absorb.
auto.
Qed.

Lemma shave_writable:
 forall sh,   writable_share sh -> nonempty_share (fst (shave sh)) /\ writable_share (snd (shave sh)).
Proof.
intros.
unfold writable_share in H.
destruct H.
unfold shave.
rewrite glb_commute in H.
unfold writable_share.
destruct (split (glb sh Lsh)) eqn:?H.
simpl.
split3.
-
intro.
apply identity_share_bot in H2. subst t0.
pose proof (split_nontrivial _ _ _ H1).
spec H2; auto.
rewrite H2 in H.
apply H.
apply bot_identity.
-
clear H0.
rewrite distrib1.
rewrite (glb_commute sh).
rewrite <- glb_assoc.
rewrite glb_Lsh_Rsh.
rewrite (glb_commute bot), glb_bot.
rewrite lub_bot.
unfold nonempty_share, nonidentity in H|-*.
assert (t0 <> bot /\ t1 <> bot). {
  assert (glb sh Lsh <> bot).
     unfold nonempty_share, nonidentity in H.
     contradict H. rewrite H. apply bot_identity.
   pose proof (split_nontrivial _ _ _ H1).  
  intuition.
}
destruct H0.
pose proof (split_together _ _ _ H1).
pose proof (split_disjoint _ _ _ H1).
rewrite glb_commute.
clear H.
intro.
apply identity_share_bot in H.
clear H1.
assert (join t0 t1 (glb sh Lsh)) by (split; auto).
assert (join_sub (glb sh Lsh) Lsh).
apply leq_join_sub.
apply glb_lower2.
destruct H5.
destruct (join_assoc (join_comm H1) H5) as [y [? ?]].
assert (t1 <= Lsh).
apply leq_join_sub; eexists; eauto.
apply ord_spec1 in H8.
rewrite H in H8.
rewrite H8 in H2. apply H2; auto.
-
apply leq_join_sub.
apply leq_join_sub in H0.
apply ord_spec1 in H0.
rewrite glb_commute.
rewrite <- H0.
apply lub_upper2.
Qed.

Lemma cleave_join:
   forall sh,  join (fst (cleave sh)) (snd (cleave sh)) sh.
Proof.
apply slice.cleave_join.
Qed.

Lemma cleave_readable:
  forall sh, readable_share sh -> readable_share (fst (cleave sh)) /\ readable_share (snd (cleave sh)).
Proof.
intros.
unfold cleave.
split.
apply slice.cleave_readable1; auto.
apply slice.cleave_readable2; auto.
Qed.

Lemma cleave_nonempty:
  forall sh, nonempty_share sh -> nonempty_share (fst (cleave sh)) /\ nonempty_share (snd (cleave sh)).
Proof.
intros.
unfold cleave.
pose proof (slice.cleave_join sh).
unfold slice.cleave in *.
destruct (split (glb Lsh sh)) as [a b] eqn:H1.
destruct (split (glb Rsh sh)) as [c d] eqn:H2.
simpl in *.
pose proof (split_nontrivial _ _ _ H1).  
pose proof (split_nontrivial _ _ _ H2).
pose proof (comp_parts comp_Lsh_Rsh sh).
rewrite H5 in H.
unfold nonempty_share, nonidentity in H.
assert (~identity (glb Lsh sh) \/ ~identity (glb Rsh sh)).
apply Classical_Prop.not_and_or.
intros [? ?].
apply identity_share_bot in H6.
apply identity_share_bot in H7.
rewrite H6,H7 in H.
rewrite lub_idem in H.
apply H.
apply bot_identity.
clear H.
destruct H6.
-
assert (glb Lsh sh <> bot).
intro. rewrite H6 in H. apply H; apply bot_identity.
assert (a<>bot /\ b<>bot) by intuition.
destruct H7.
split; intro H9; apply identity_share_bot in H9; apply lub_bot_e in H9; intuition.
-
assert (glb Rsh sh <> bot).
intro. rewrite H6 in H. apply H; apply bot_identity.
assert (c<>bot /\ d<>bot) by intuition.
destruct H7.
split; intro H9; apply identity_share_bot in H9; apply lub_bot_e in H9; intuition.
Qed.
*)

Lemma join_Ews:
  join  Ews (snd (split Lsh)) Tsh.
Proof.
unfold Ews.
unfold extern_retainer.
destruct (split Lsh) as [a b] eqn:?H.
simpl.
split.
rewrite glb_commute, distrib1.
rewrite glb_commute.
destruct (split_join _ _ _ H). 
rewrite H0. rewrite lub_commute, lub_bot.
clear - H1.
pose proof (lub_upper2 a b).
rewrite H1 in H.
pose proof (glb_less_both H (ord_refl Rsh)).
rewrite glb_Lsh_Rsh in H0.
apply ord_antisym; auto.
apply bot_correct.
rewrite (lub_commute a).
rewrite lub_assoc.
destruct (split_join _ _ _ H). 
rewrite H1.
rewrite lub_commute.
apply lub_Lsh_Rsh.
Qed.

Lemma comp_Ews:
  comp(Ews) = snd(split Lsh).
Proof.
apply join_top_comp.
apply join_Ews.
Qed.

(*

Fixpoint nth_split_left (sh: share) (n: nat) :=
 match n with
 | O => sh
 | S n' => nth_split_left (fst (split sh)) n'
 end.

Lemma nth_split_left_S:
 forall sh n,
  nth_split_left sh (S n) = fst (split (nth_split_left sh n)).
Proof.
intros.
revert sh; induction n; intros.
reflexivity.
simpl in *.
rewrite IHn.
auto.
Qed.

Lemma leftmost_epsilon (sh: share) :
  {n | join_sub (nth_split_left Tsh n) sh} +
  {~ exists n, join_sub (nth_split_left Tsh n) sh}.
  (* Andrew is quite sure this is provable. *)
Abort.

Definition augment (sh: share) := 
  if leftmost_epsilon sh then lub sh (comp Ews) else sh.

Definition leftmost_eps (sh: share) :=
  exists n, join_sub (nth_split_left Tsh n) sh.

Lemma leftmost_epsilon_Ews:  
  leftmost_eps Ews.
Proof.
intros.
unfold Ews.
unfold extern_retainer.
unfold Lsh.
exists 2%nat.
simpl.
exists Rsh.
unfold Rsh, Tsh. 
split; auto.
rewrite glb_commute.
apply sub_glb_bot with (fst (split top)).
exists (snd (split (fst (split top)))).
apply split_join.
apply surjective_pairing.
rewrite glb_commute.
apply glb_split.
Qed.

Axiom split_rel:
  forall sh, split sh = (rel sh Lsh, rel sh Rsh).

Axiom rel_congruence2:
 forall x1 x2 a,
  join_sub x1 x2 -> join_sub (rel x1 a) (rel x2 a).

Lemma leftmost_epsilon_lub1:
 forall a b n,
    join_sub (nth_split_left Tsh n) a ->
    join_sub (nth_split_left Tsh n) (lub a b).
Proof.
intros.
eapply join_sub_trans; [apply H |].
apply leq_join_sub.
apply lub_upper1.
Qed.

Lemma leftmost_epsilon_lub2:
 forall a b n,
    join_sub (nth_split_left Tsh n) b ->
    join_sub (nth_split_left Tsh n) (lub a b).
intros.
eapply join_sub_trans; [apply H |].
apply leq_join_sub.
apply lub_upper2.
Qed.

Lemma leftmost_epsilon_rel:
 forall a b m n,
    join_sub (nth_split_left Tsh m) a ->
    join_sub (nth_split_left Tsh n) b ->
    join_sub (nth_split_left Tsh (m+n)) (rel a b).
Proof.
Abort.

Lemma leftmost_epsilon_glb:
 forall a b n,
    join_sub (nth_split_left Tsh n) a ->
    join_sub (nth_split_left Tsh n) b ->
    join_sub (nth_split_left Tsh n) (glb a b).
Proof.
intros.
apply leq_join_sub in H.
apply leq_join_sub in H0.
apply leq_join_sub.
apply glb_greatest; auto.
Qed.

Lemma leftmost_epsilon_up:
 forall a (n m: nat),
    (n <= m)%nat -> 
    join_sub (nth_split_left Tsh n) a ->
    join_sub (nth_split_left Tsh m) a.
Proof.
intros.
Abort.

Lemma leftmost_epsilon_Lsh:
    join_sub (nth_split_left Tsh 1) Lsh.
Proof.
apply join_sub_refl.
Qed.

Lemma not_leftmost_epsilon_lub:
  forall a b, 
   ~ (exists n, join_sub (nth_split_left Tsh n) a) ->
   ~ (exists n, join_sub (nth_split_left Tsh n) b) ->
   ~ (exists n, join_sub (nth_split_left Tsh n) (lub a b)).
Proof.
Abort.

Lemma not_leftmost_epsilon_rel1:
  forall a b, 
   ~ (exists n, join_sub (nth_split_left Tsh n) a) ->
   ~ (exists n, join_sub (nth_split_left Tsh n) (rel a b)).
Proof.
intros.
contradict H.
destruct H as [n H].
exists n.
Abort.

Lemma not_leftmost_epsilon_rel2:
  forall a b, 
   ~ (exists n, join_sub (nth_split_left Tsh n) b) ->
   ~ (exists n, join_sub (nth_split_left Tsh n) (rel a b)).
Proof.
intros.
contradict H.
destruct H as [n H].
exists n.
Abort.

Lemma not_leftmost_epsilon_glb1:
  forall a b, 
   ~ (exists n, join_sub (nth_split_left Tsh n) a) ->
   ~ (exists n, join_sub (nth_split_left Tsh n) (glb a b)).
Proof.
intros.
contradict H.
destruct H as [n H].
exists n.
eapply join_sub_trans.
eassumption.
apply leq_join_sub.
apply glb_lower1.
Qed.

Lemma not_leftmost_epsilon_glb2:
  forall a b, 
   ~ (exists n, join_sub (nth_split_left Tsh n) b) ->
   ~ (exists n, join_sub (nth_split_left Tsh n) (glb a b)).
Proof.
intros.
contradict H.
destruct H as [n H].
exists n.
eapply join_sub_trans.
eassumption.
apply leq_join_sub.
apply glb_lower2.
Qed.

Lemma not_leftmost_epsilon_Rsh:
   ~ (exists n, join_sub (nth_split_left Tsh n) Rsh).
Proof.
intros [n H].
Abort.

Lemma shave_leftmost_epsilon1:
  forall sh, leftmost_eps sh -> 
     leftmost_eps (fst (shave sh)).
Proof.
intros.
unfold shave.
rewrite !split_rel.
simpl.
destruct H.
exists ((1+x)+(1+x))%nat.
apply leftmost_epsilon_rel.
apply leftmost_epsilon_glb.
eapply leftmost_epsilon_up; [ |apply H]; lia.
eapply leftmost_epsilon_up; [ |apply leftmost_epsilon_Lsh]; lia.
eapply leftmost_epsilon_up; [ |apply leftmost_epsilon_Lsh]; lia.
Qed.

Lemma shave_leftmost_epsilon2:
  forall sh, ~ leftmost_eps (snd (shave sh)).
Proof.
intros.
unfold shave; simpl.
rewrite !split_rel; simpl.
apply not_leftmost_epsilon_lub.
apply not_leftmost_epsilon_rel2.
apply not_leftmost_epsilon_Rsh.
apply not_leftmost_epsilon_glb2.
apply not_leftmost_epsilon_Rsh.
Qed.

Lemma shave_leftmost_epsilon:
  forall sh, leftmost_eps sh -> 
     leftmost_eps (fst (shave sh)) /\  ~ leftmost_eps (snd (shave sh)).
Proof.
intros.
split.
apply shave_leftmost_epsilon1; auto.
apply shave_leftmost_epsilon2.
Qed.

Lemma cleave_leftmost_epsilon:
  forall sh, leftmost_eps sh -> 
     leftmost_eps (fst (cleave sh)) /\  ~ leftmost_eps (snd (cleave sh)).
Proof.
intros.
unfold cleave, slice.cleave.
simpl.
rewrite !split_rel; simpl.
split.
-
destruct H.
exists (1 + x + (1 + x))%nat.
apply leftmost_epsilon_lub1.
apply leftmost_epsilon_rel.
apply leftmost_epsilon_glb.
eapply leftmost_epsilon_up;  [  | apply leftmost_epsilon_Lsh].
lia.
eapply leftmost_epsilon_up;  [  | apply H].
lia.
eapply leftmost_epsilon_up;  [  | apply leftmost_epsilon_Lsh].
lia.
-
unfold leftmost_eps.
apply not_leftmost_epsilon_lub.
apply not_leftmost_epsilon_rel2.
apply not_leftmost_epsilon_Rsh.
apply not_leftmost_epsilon_rel2.
apply not_leftmost_epsilon_Rsh.
Qed.

Lemma augment_Ews:  augment Ews = Tsh.
Proof.
  unfold augment.
  destruct (leftmost_epsilon Ews).
  rewrite comp1; auto.
  pose leftmost_epsilon_Ews; unfold leftmost_eps in *; contradiction.
Qed.

*)

Lemma nonidentity_comp_Ews:
  nonidentity (comp Ews).
Proof.
  rewrite comp_Ews.
  assert (nonidentity Lsh).
  { replace Lsh with (fst (split top)) by auto.
    assert (split top = (fst (split top), snd (split top))) as Htop 
        by apply surjective_pairing.
    pose (split_nontrivial' _ _ _ Htop).
    pose top_share_nonidentity.
    unfold nonidentity in *; unfold not in *; auto.
  }
  assert (split Lsh = (fst (split Lsh), snd (split Lsh))) as HLsh 
      by apply surjective_pairing.
  pose (split_nontrivial' _ _ _ HLsh). 
  unfold nonidentity in *; unfold not in *; auto.
Qed.

(*

(* Toy version of malloc_token, without large/small distinction, without 
   the waste part of the header, and Int size rather than data type and Ptrofs. 
   In the full development we'll have both n and s, with s>0 because small 
   chunks are nonempty *)

Definition maybe_sliver_leftmost (sh: share) :=
  if leftmost_epsilon sh then (comp Ews) else bot.  

Definition compEwsL := rel (comp Ews) Lsh.
Definition compEwsR := rel (comp Ews) Rsh.

(* The R relation *)
Inductive tokChunk : share -> share -> Prop :=
  | mkTokChunk: forall sh sh' a b: share, 
    join (rel extern_retainer a) (rel Rsh b) sh ->
    lub (rel compEwsL a) (rel compEwsR b) = sh' -> tokChunk sh sh'.

Lemma tokChunk_disj:
  forall a b, glb (rel compEwsL a) (rel compEwsR b) = bot.
Proof.
intros.
apply ord_antisym.
2: apply bot_correct.
eapply ord_trans with (glb compEwsL compEwsR).
apply glb_greatest.
eapply ord_trans; [ apply glb_lower1 | apply leq_join_sub; apply rel_leq].
eapply ord_trans; [ apply glb_lower2 | apply leq_join_sub; apply rel_leq].
unfold compEwsL, compEwsR.
rewrite <- rel_preserves_glb.
rewrite glb_Lsh_Rsh.
rewrite rel_bot1.
apply ord_refl.
Qed.

Lemma tokChunk_Ews: tokChunk Ews (comp Ews).
Proof.
apply mkTokChunk with Tsh Tsh.
rewrite !rel_top1.
split; auto.
unfold extern_retainer.
rewrite split_rel; simpl.
apply ord_antisym.
2: apply bot_correct.
eapply ord_trans with (glb Lsh Rsh).
apply glb_less_both.
apply leq_join_sub.
apply rel_leq.
apply ord_refl.
rewrite glb_Lsh_Rsh.
apply ord_refl.
rewrite !rel_top1.
unfold compEwsL, compEwsR.
rewrite <- rel_preserves_lub.
rewrite lub_Lsh_Rsh.
rewrite !rel_top1.
auto.
Qed.

Lemma tokChunk_bot: forall sh, tokChunk sh bot -> sh = bot.
Proof.
intros.
inv H.
assert (ET: Ews <> top). {
 clear.
 intro.
 pose proof (join_Ews). rewrite H in H0.
 apply join_top_comp in H0.
 rewrite <- comp_bot, comp_inv in H0.
 destruct (split Lsh) eqn:?.  simpl in *. subst t1.
 apply split_nontrivial in Heqp.
 apply Lsh_bot_neq; auto.
 auto.
}
apply lub_bot_e in H1.
destruct H1.
rewrite <- (rel_bot1 compEwsR) in H1.
apply rel_inj_l in H1. subst.
rewrite <- (rel_bot1 compEwsL) in H.
apply rel_inj_l in H. subst.
rewrite !rel_bot1 in H0.
destruct H0.
rewrite lub_bot in H0. subst; auto.
clear - ET; intro.
unfold compEwsL in H.
rewrite <- (rel_bot2 Lsh) in H.
apply rel_inj_r in H.
pose proof (join_Ews).
rewrite <- comp_Ews in H0.
rewrite H in H0.
apply join_unit2_e in H0; auto.
apply Lsh_bot_neq.
clear - ET.
unfold compEwsR.
intro.
rewrite <- (rel_bot2 Rsh) in H.
apply rel_inj_r in H.
assert (comp (comp Ews) = comp bot) by congruence.
rewrite comp_inv in H0.
rewrite comp_bot in H0.
contradiction.
clear.
intro.
unfold Rsh in H.
destruct (split top) eqn:?H.
simpl in *; subst.
apply split_nontrivial in H0; auto.
apply nontrivial; auto.
Qed.


Lemma tokChunk_fun: 
forall sh a b,
    join (rel extern_retainer a) (rel Rsh b) sh ->
    a = fst(split(fst(split(glb sh extern_retainer)))) /\
    b = snd(split(glb sh Rsh)).
Proof.
intros.
inv H.
Abort.

Lemma tokChunk_functional:
forall sh sh' sh'', tokChunk sh sh' -> tokChunk sh sh'' -> sh' = sh''.
Proof.
intros.
inv H; inv H0.
pose proof (tokChunk_fun _ _ _ H1) as [Ha Hb].
pose proof (tokChunk_fun _ _ _ H) as [Ha0 Hb0].
subst; reflexivity.
Qed.

Lemma tokChunk_shave: forall sh sh' sh1 sh2,
    tokChunk sh sh' -> (sh1,sh2) = shave sh -> 
    exists sh1' sh2', join sh1' sh2' sh' /\ tokChunk sh1 sh1' /\ tokChunk sh2 sh2'.
Abort.

Lemma tokChunk_cleave: forall sh sh' sh1 sh2,
    tokChunk sh sh' -> (sh1,sh2) = shave sh -> 
    exists sh1' sh2', join sh1' sh2' sh' /\ tokChunk sh1 sh1' /\ tokChunk sh2 sh2'.
Abort.

*)


