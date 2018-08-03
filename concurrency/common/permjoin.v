Require Import VST.msl.Coqlib2.
Require Import VST.msl.sepalg.
Require Import VST.msl.shares.
Require Import VST.msl.pshares.
Require Import VST.veric.coqlib4.
Require Import VST.veric.shares.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_ops.
Require Import VST.concurrency.common.permjoin_def.
Require Import FunInd.
Import Memtype.

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

Lemma join_bot_bot_eq sh :
  sepalg.join Share.bot Share.bot sh ->
  sh = Share.bot.
Proof.
  intros j.
  apply (join_eq j  (z' := Share.bot) (join_bot_eq Share.bot)).
Qed.

Lemma join_to_bot_l {sh1 sh2} :
  sepalg.join sh1 sh2 Share.bot ->
  sh1 = Share.bot.
Proof.
  intros [H H'].
  apply shares.lub_bot_e in H'.
  apply H'.
Qed.

Lemma join_to_bot_r {sh1 sh2} :
  sepalg.join sh1 sh2 Share.bot ->
  sh2 = Share.bot.
Proof.
  intros [H H'].
  apply shares.lub_bot_e in H'.
  apply H'.
Qed.

Lemma join_top_l {sh2 sh3} :
  sepalg.join Share.top sh2 sh3 ->
  sh2 = Share.bot.
Proof.
  intros [H H'].
  rewrite Share.glb_commute in H.
  rewrite Share.glb_top in H.
  auto.
Qed.

Lemma join_top {sh2 sh3} :
  sepalg.join Share.top sh2 sh3 ->
  sh3 = Share.top.
Proof.
  intros [H H'].
  rewrite Share.lub_commute in H'.
  rewrite Share.lub_top in H'.
  auto.
Qed.

Lemma join_pfullshare {sh2 sh3 : pshare} : ~sepalg.join pfullshare sh2 sh3.
Proof.
  intros [H H'].
  unfold pfullshare in *.
  unfold fullshare in *.
  simpl in *.
  rewrite Share.glb_commute in H.
  rewrite Share.glb_top in H.
  destruct sh2.
  simpl in *.
  subst.
  destruct (shares.not_nonunit_bot Share.bot).
  tauto.
Qed.

Lemma join_with_bot_r sh1 sh2 : join sh1 Share.bot sh2 -> sh1 = sh2.
Proof.
  intros [H H'].
  rewrite Share.lub_bot in H'.
  auto.
Qed.

Lemma join_with_bot_l sh1 sh2 : join Share.bot sh1 sh2 -> sh1 = sh2.
  intros [H H'].
  rewrite Share.lub_commute in H'.
  rewrite Share.lub_bot in H'.
  auto.
Qed.

Lemma join_top_r sh1 sh3 : join sh1 Share.top sh3 -> sh1 = Share.bot.
Proof.
  intros [H H'].
  rewrite Share.glb_top in H.
  auto.
Qed.

Lemma join_pshare_top_l (p1 p2 p3 : pshare) :
  @join pshare _ p1 p2 p3 ->
  pshare_sh p1 <> Share.top.
Proof.
  destruct p1; simpl in *.
  intros [H H'] ->.
  simpl in *.
  destruct p2 as [x n0]; simpl in *.
  rewrite Share.glb_commute in H.
  rewrite Share.glb_top in H.
  subst x.
  simpl in *.
  subst.
  destruct (shares.not_nonunit_bot Share.bot).
  tauto.
Qed.

Lemma join_pshare_top_r (p1 p2 p3 : pshare) :
  @join pshare _ p1 p2 p3 ->
  pshare_sh p2 <> Share.top.
Proof.
  intros j.
  apply join_comm in j.
  apply join_pshare_top_l in j; auto.
Qed.

(*Got this ltac from permission.v maybe should factor*)
Ltac if_simpl:=
  repeat match goal with
         | [ H: ?X = true |- context[if ?X then _ else _] ] => rewrite H; simpl 
         | [ H: ?X = false |- context[if ?X then _ else _] ] => rewrite H; simpl 
         | [ H: ?X = left _ |- context[match ?X with left _ => _ | right _ => _ end] ]=>
           rewrite H; simpl 
         | [ H: ?X = right _ |- context[match ?X with left _ => _ | right _ => _ end] ]=>
           rewrite H; simpl 
         end.
Lemma top_aint_bot:
  eq_dec Share.top Share.bot = right Share.nontrivial.
  destruct (eq_dec Share.top Share.bot).
  - exfalso; apply Share.nontrivial; auto.
  - f_equal. apply proof_irr.
Qed.

  
Ltac common_contradictions:=
  match goal with
  | [H: Share.glb _ _ = Share.top |- _ ] =>
    exfalso;
    eapply shares.glb_Rsh_not_top; eassumption
    | [ H: Share.bot = Share.top |- _ ] => exfalso; apply Share.nontrivial; symmetry; assumption
    | [ H: Share.top = Share.bot |- _ ] => exfalso; apply Share.nontrivial; assumption
    | [ H: ~ shares.readable_share Share.top |- _ ] => pose proof shares.readable_share_top; contradiction
    | [ H: ~ shares.writable_share Share.top |- _ ] => pose proof shares.writable_share_top; contradiction
    | [ H: shares.readable_share Share.bot |- _ ] => pose proof shares.bot_unreadable; contradiction        
    | [ H: shares.writable_share Share.bot |- _ ] => apply shares.writable_readable in H; pose proof shares.bot_unreadable; contradiction
    | [ H: shares.writable_share ?sh, H0: ~ shares.readable_share ?sh   |- _ ] =>
      exfalso; apply H0; eapply shares.writable_readable; assumption
    | _ => contradiction 
    end.
  
  Ltac join_share_contradictions_oneside:=
    match goal with
    | [ H: @join Share.t _ Share.top _ _ |- _ ] =>
      pose proof (join_top_l H); first [common_contradictions | subst]
    | [ H: @join Share.t _ Share.bot _ _ |- _ ] =>
      pose proof (join_with_bot_l _ _ H); first [common_contradictions | subst]
    | [ H: @join Share.t _ _ _ Share.bot |- _ ] =>
      pose proof (join_to_bot_l H); pose proof (join_to_bot_r H);
      first [common_contradictions | subst]
    | [ H1: ~ shares.readable_share ?sh1,
        H2: ~ shares.readable_share ?sh2,
            H: join ?sh1 ?sh2 _ |- _ ] =>
      pose proof (shares.join_unreadable_shares H H1 H2);
      first [common_contradictions | subst]
    | [ H1: ~ shares.writable_share ?sh1,
        H2: ~ shares.readable_share ?sh2,
            H: join ?sh1 ?sh2 _ |- _ ] =>
      pose proof (join_readable_unreadable _ _ _ H H1 H2);
      first [common_contradictions | subst]
    | [ H1: shares.writable_share ?sh1,
        H2: shares.writable_share ?sh2,
            H: join ?sh1 ?sh2 _ |- _ ] =>
      exfalso; eapply shares.join_writable_readable;
      try eapply shares.writable_readable; eassumption
    | [ H1: shares.writable_share ?sh1,
            H: join ?sh1 _ _ |- _ ] =>
      pose proof (shares.join_writable1 H H1);
      first [common_contradictions | subst]
    | [ H1: shares.readable_share ?sh1,
            H: join ?sh1 ?sh2 _ |- _ ] =>
      pose proof (shares.join_readable1 H H1);
      common_contradictions
    end.
  Ltac join_share_contradictions:=
    try join_share_contradictions_oneside;
    match goal with
    | [ H: @join Share.t _ _ _ _ |- _ ] =>
      apply join_comm in H; join_share_contradictions_oneside
    end; try contradiction.

Lemma join_permjoin r1 r2 r3 :
  join r1 r2 r3 ->
  permjoin (perm_of_res r1) (perm_of_res r2) (perm_of_res r3).
Proof.
  intros.
  inversion H; subst;
    try (destruct k);
    try constructor;
  functional induction (perm_of_sh sh1) using perm_of_sh_ind;
    simpl; if_simpl;
    repeat match goal with
           | [  |- context [eq_dec Share.top Share.bot] ] => rewrite top_aint_bot 
           end;
  functional induction (perm_of_sh sh2) using perm_of_sh_ind;
    simpl; if_simpl;
    repeat match goal with
           | [  |- context [eq_dec Share.top Share.bot] ] => rewrite top_aint_bot 
           end;
  functional induction (perm_of_sh sh3) using perm_of_sh_ind;
  simpl; if_simpl;
    repeat match goal with
           | [  |- context [eq_dec Share.top Share.bot] ] => rewrite top_aint_bot 
           end;
    try (do 2 join_share_contradictions);
    unfold perm_of_sh; if_simpl; 
    try econstructor.
    contradiction (join_readable_unreadable RJ _x _x2); apply writable_share_top.
    contradiction (join_readable_unreadable RJ _x _x2).
    contradiction (join_readable_unreadable (join_comm RJ) _x2 _x0); apply writable_share_top.
    contradiction (join_readable_unreadable (join_comm RJ) _x2 _x0).
Qed.

Lemma join_permjoin_lock
  : forall r1 r2 r3 ,
    sepalg.join r1 r2 r3 ->
    permjoin_def.permjoin
      (perm_of_res_lock r1)
      (perm_of_res_lock r2)
      (perm_of_res_lock r3).
Proof.
 intros.
 inversion H; clear H; subst; simpl; try constructor;
 repeat match goal with
 | [ H: join ?sh _ _ , H1: shares.readable_share ?sh  |- _ ] =>
   apply readable_glb in H1
 | [ H: join ?sh _ _ , H1: ~ shares.readable_share ?sh  |- _ ] =>
   apply unreadable_glb in H1
 | [ H: join _ ?sh _ , H1: shares.readable_share ?sh  |- _ ] =>
   apply readable_glb in H1
 | [ H: join _ ?sh _ , H1: ~ shares.readable_share ?sh  |- _ ] =>
   apply unreadable_glb in H1
 | [ H: join _ _ ?sh , H1: shares.readable_share ?sh  |- _ ] =>
   apply readable_glb in H1
 | [ H: join _ _ ?sh , H1: ~ shares.readable_share ?sh  |- _ ] =>
   apply unreadable_glb in H1
 end;
 match goal with
   | [ H: join _ _ _ |- _ ] => eapply compcert_rmaps.join_glb_Rsh in H 
 end;
   try (destruct k);
    try constructor;
  functional induction (perm_of_sh  (Share.glb Share.Rsh sh1)) using perm_of_sh_ind;
    simpl; if_simpl;
  functional induction (perm_of_sh  (Share.glb Share.Rsh sh2)) using perm_of_sh_ind;
    simpl; if_simpl;
  functional induction (perm_of_sh  (Share.glb Share.Rsh sh3)) using perm_of_sh_ind;
  simpl; if_simpl;
    repeat match goal with
           | [  |- context [eq_dec Share.top Share.bot] ] => rewrite top_aint_bot 
           end;
    try (unfold perm_of_sh; if_simpl; econstructor);
    try (do 2 join_share_contradictions);
  try eapply permjoin_None_l;
  try eapply permjoin_None_r;
  forget (Share.glb Share.Rsh sh1) as s1;
  forget (Share.glb Share.Rsh sh2) as s2;
  forget (Share.glb Share.Rsh sh3) as s3;
  clear e e0 e1 e2 e3 e4 e5; subst;
  try contradiction (join_readable_unreadable RJ _x _x2).
  apply join_unit1_e in RJ; auto; subst; contradiction.
  contradiction (join_readable_unreadable (join_comm RJ) _x2 _x0).
Qed.
