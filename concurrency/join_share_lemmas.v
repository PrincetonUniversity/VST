
Require Import compcert.common.Memory.
From veric Require Import shares juicy_mem.
Require Import msl.msl_standard.
Require Import msl.Coqlib2.

  Lemma perm_of_glb_not_Freeable: forall sh,
      ~ perm_of_sh (Share.glb Share.Rsh sh) = Some Freeable.
  Proof.
   intros.
   unfold perm_of_sh.
   if_tac.
   rewrite if_false by apply glb_Rsh_not_top.
   congruence.
   if_tac. congruence.
   if_tac. congruence. congruence.
  Qed.

  Lemma writable_not_join_readable:
    forall sh1 sh2,
      joins sh1 sh2 ->
      writable_share sh1 ->
      ~ readable_share sh2.
  Proof.
    intros.
    intro.
    unfold readable_share, writable_share in *.
    destruct H0. destruct H.
    destruct (join_assoc (join_comm H0) H) as [? [? _]].
    unfold nonempty_share in H1. clear - H1 H2.
    destruct H2 as [H2 _]. rewrite H2 in H1.
    apply H1. apply bot_identity.
 Qed.

  Lemma writable_not_join_writable :
    forall sh1 sh2,
      joins sh1 sh2 ->
      writable_share sh1 ->
      ~ writable_share sh2.
   Proof.
     intros. intro.
      SearchAbout writable_share joins.
    pose proof (writable_not_join_readable _ _ H H0).
    apply H2. auto.
   Qed.

  Lemma only_bot_joins_top:
    forall sh, joins Share.top sh -> sh = Share.bot.
  Proof.
    intros. destruct H. destruct H.
    rewrite Share.glb_commute in H. rewrite Share.glb_top in H. auto.
  Qed.

  Lemma glb_Rsh_not_top:
    forall sh, ~ Share.glb Share.Rsh sh = Share.top.
  Proof.
    intros. apply glb_Rsh_not_top.
  Qed.

  Lemma writable_right:
    forall sh,  writable_share (Share.glb Share.Rsh sh) ->
           writable_share sh.
  Proof.
     intros.
     unfold writable_share in *.
     apply leq_join_sub in H.
     apply leq_join_sub.
     eapply Share.ord_trans; try eassumption.
     rewrite Share.glb_commute.
     apply Share.glb_lower1.
  Qed.

Lemma join_readable_unreadable:
  forall sh1 sh2 sh3,
    join sh1 sh2 sh3 ->
    ~ shares.writable_share sh1 ->
    ~ shares.readable_share sh2 ->
    ~ shares.writable_share sh3.
Proof.
 intros.
 contradict H0.
 unfold writable_share in *.
 destruct H0.
(*
 apply leq_join_sub in H0. apply leq_join_sub.
 destruct (join_comp_parts comp_Lsh_Rsh H).

 destruct H.
 subst sh3. rename H into G.
 apply not_readable_Rsh_part in H1.
 destruct H0.
 destruct H.
 exists (Share.glb Share.Lsh sh1).
 split.
 rewrite <- Share.glb_assoc.
 rewrite (Share.glb_commute Share.Rsh).
 rewrite glb_Lsh_Rsh.
 rewrite Share.glb_commute, Share.glb_bot; auto.
 clear dependent x.
 rewrite Share.distrib2.
 rewrite (Share.lub_commute Share.Rsh).
 rewrite lub_Lsh_Rsh.
 rewrite Share.glb_commute, Share.glb_top.
 
 
 auto.

 
 

 apply leq_join_sub in H0. apply leq_join_sub.
 pose proof (comp_parts comp_Lsh_Rsh sh2).
 rewrite H1 in H. rewrite Share.lub_bot in H.
 rewrite H in H0.
 rewrite Share.distrib2 in H0.
 rewrite Share.distrib1 in H0.
 rewrite (Share.glb_commute _ sh2) in H0.
 rewrite Share.distrib1 in H0.
 rewrite (Share.glb_commute sh2 sh1) in H0.
 rewrite G in H0. 
 rewrite (Share.lub_commute Share.bot) in H0.
 rewrite Share.lub_bot in H0.
 rewrite (Share.glb_commute _ sh1) in H0.
 rewrite Share.distrib1 in H0.
 rewrite Share.glb_idem in H0.
 rewrite Share.lub_absorb in H0.
 apply Share.ord_spec2 in H0. 
 rewrite Share.distrib2 in H0.
 rewrite (Share.lub_commute sh1) in H0.
 SearchAbout (Share.lub _ (Share.glb _ _) ). 
rewrite Share.distrib1 in H0.

 
 Search (Share.lub _ (Share.glb _ _) = _).
 
 rewrite <- Share.distrib2 in H0.
 rewrite (Share.distrib1 _ _ sh2) in H0.
 

 eapply Share.ord_trans; try apply H0.
 eapply Share.ord_trans; try apply Share.glb_lower1.
 
 Search Share.Ord Share.glb.
(* apply Share.ord_spec2.*)
 apply Share.ord_spec2 in H0. 
 apply Share.ord_spec2 in H0.
 rewrite (Share.lub_commute sh1) in H0.
 rewrite <- Share.lub_assoc in H0.
 pattern sh2 at 1 in H0; rewrite H in H0.
 rewrite Share.distrib2 in H0.
 rewrite (Share.lub_commute Share.Rsh) in H0.
 rewrite lub_Lsh_Rsh in H0.
 rewrite (Share.glb_commute Share.top) in H0.
 rewrite Share.glb_top in H0.
 rewrite Share.lub_assoc in H0.
*)
Admitted.

Lemma readable_glb:
   forall sh,
     shares.readable_share sh ->
     shares.readable_share (Share.glb Share.Rsh sh).
 Proof.
   intros.
   unfold readable_share in *. rewrite glb_twice. auto.
 Qed.

 Lemma unreadable_glb:
   forall sh,
     ~shares.readable_share sh ->
     ~shares.readable_share (Share.glb Share.Rsh sh).
 Proof.
   intros.
   unfold readable_share in *. rewrite glb_twice. auto.
 Qed.

 