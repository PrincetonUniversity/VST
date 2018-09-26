Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.semantics.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.Clight_new.
Require compcert.cfrontend.Clight.
Module CC := Clight.
Require VST.veric.Clight_core.
Module CC' := Clight_core.
Section GE.
Variable ge : genv.
Definition CCstep s1 s2 := 
  Clight_core.at_external s1 = None /\
  Clight.step ge (Clight.function_entry2 ge) s1 Events.E0 s2.

Fixpoint strip_skip' (k: CC.cont) : CC.cont :=
 match k with
 | CC.Kseq Sskip k' => strip_skip' k'
 | _ => k
 end.

Inductive match_cont:  cont -> CC.cont -> Prop :=
  | match_cont_nil: match_cont nil CC.Kstop
  | match_cont_seq: forall s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq s :: k) (CC.Kseq s k')
  | match_cont_loop1: forall e3 s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq Scontinue :: Kloop1 s e3 :: k) (CC.Kloop1 s e3 k')
  | match_cont_loop2: forall e3 s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kloop2 s e3 :: k) (CC.Kloop2 s e3 k')
  | match_cont_switch: forall k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kswitch :: k) (CC.Kswitch k')
  | match_cont_call: forall lid fd f ve te k k'
         (CUR: match current_function k with Some f' => f'=f | _ => True end),
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq (Sreturn None) :: Kcall lid fd ve te :: k) (CC.Kcall lid f ve te k').

Inductive star: state -> state -> Prop :=
  | star_refl: forall s,
      star s s
  | star_step: forall s1 s2 s3,
      CCstep s1 s2 -> star s2 s3 -> star s1 s3.

Lemma star_one:
  forall s1 s2, CCstep s1 s2 -> star s1 s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl.
Qed.

Lemma star_two:
  forall s1 s2 s3,
  CCstep s1 s2 -> CCstep s2 s3 ->
  star s1 s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto.
Qed.

Lemma star_trans:
  forall {s1 s2}, star s1 s2 ->
  forall {s3}, star s2 s3 -> star s1 s3.
Proof.
  induction 1; intros; auto.
  eapply star_step; eauto.
Qed.


Inductive plus: state -> state -> Prop :=
  | plus_left: forall s1 s2 s3,
      CCstep s1 s2 -> star s2 s3 -> plus s1 s3.

Lemma plus_one:
  forall s1 s2, CCstep s1 s2 -> plus s1 s2.
Proof.
  intros. eapply plus_left; eauto. apply star_refl.
Qed.

Lemma plus_two:
  forall s1 s2 s3, CCstep s1 s2 -> CCstep s2 s3 -> plus s1 s3.
Proof.
  intros. eapply plus_left; eauto. apply star_one; auto.
Qed.

Lemma plus_star: forall s1 s2, plus s1 s2 -> star s1 s2.
Proof.
  intros. inv H. eapply star_step; eauto.
Qed.

Lemma plus_trans: forall {s1 s2 s3},
   plus s1 s2 -> plus s2 s3 -> plus s1 s3.
Proof.
 intros.
  inv H. eapply plus_left. eauto.
  apply @star_trans with (s2:=s2); eauto.
  apply plus_star. auto.
Qed.

Lemma star_plus_trans: forall {s1 s2 s3},
   star s1 s2 -> plus s2 s3 -> plus s1 s3.
Proof.
 intros. inv H. auto. eapply plus_left; eauto.
 eapply star_trans; eauto. apply plus_star; auto.
Qed.

Lemma plus_star_trans: forall {s1 s2 s3},
   plus s1 s2 -> star s2 s3 -> plus s1 s3.
Proof.
 intros.
 inv H. eapply plus_left; eauto. eapply star_trans; eauto.
Qed.


Lemma exec_skips:
 forall {s0 k s k'}
   (H1: match_cont (Kseq s0 :: k) (strip_skip' (CC.Kseq s k')))
   f ve te m,
   match s0 with Sskip => False | Scontinue => False | Sloop _ _ => False
            | Sifthenelse _ _ _ => False | Sreturn _ => False
            | _ => True end ->
   exists k2, strip_skip' (CC.Kseq s k') = CC.Kseq s0 k2 /\
     star (CC.State f s k' ve te m) (CC.State f s0 k2 ve te m).
Proof.
 intros.
 remember (CC.Kseq s k') as k0.
 revert k s k' H1 Heqk0; induction k0; intros; inv Heqk0.
 assert ({s1=Sskip}+{s1<>Sskip}) by (destruct s1; try (left; congruence); right; congruence).
 destruct H0. subst s1.
 destruct k'; try solve [inv H1].
 specialize (IHk0 _ s k' H1 (eq_refl _)).
 destruct IHk0 as [k2 [? ?]].
 exists k2. split; simpl; auto.
 econstructor 2. split;[reflexivity|]. constructor. auto.
 inv H1; contradiction. simpl in *. inv H1. contradiction.
  replace (strip_skip' (CC.Kseq s1 k')) with (CC.Kseq s1 k')  in *
     by (destruct s1; try congruence; auto).
 inv H1.
 exists k'; split; auto.
 constructor 1.
Qed.

Lemma strip_skip_not:
  forall s k, s<>Sskip -> strip_skip (Kseq s :: k) = (Kseq s :: k).
Proof.
 destruct s; intros; auto. congruence.
Qed.
Lemma strip_skip'_not:
  forall s k, s<>Sskip -> strip_skip' (CC.Kseq s k) = (CC.Kseq s k).
Proof.
 destruct s; intros; auto. congruence.
Qed.

Lemma dec_skip: forall s, {s=Sskip}+{s<>Sskip}.
Proof.
 destruct s; try (left; congruence); right; congruence.
Qed.

Lemma dec_continue: forall s, {s=Scontinue}+{s<>Scontinue}.
Proof.
 destruct s; try (left; congruence); right; congruence.
Qed.


Lemma strip_step:
  forall ge ve te k m st' m',
     cl_step ge (State ve te (strip_skip k)) m st' m' <->
    cl_step ge (State ve te k) m st' m'.
Proof.
intros.
 induction k; intros; split; simpl; intros; try destruct IHk; auto.
 destruct a; try destruct s; auto.
  constructor; auto.
 destruct a; try destruct s; auto.
 inv H. auto.
Qed.

Lemma continue_cont_skip:
  forall k, continue_cont k = continue_cont (strip_skip k).
Proof.
 induction k; simpl; intros; auto.
 destruct a; auto. destruct s; auto.
Qed.

Lemma break_cont_skip:
    forall k, break_cont (strip_skip k) = break_cont k.
Proof. induction k; try destruct a; simpl; auto; destruct s; simpl; auto.
Qed.

Lemma continue_cont_is:
 forall k, match (continue_cont k) with nil => True | Kseq e3 :: Kloop2 s e3' :: _ => e3=e3' | _ => False end.
Proof.
 induction k; simpl; auto; try contradiction.
  destruct a; auto.
Qed.

Lemma match_cont_strip:
   forall s k k', match_cont (strip_skip k) (strip_skip' k') ->
           match_cont (strip_skip (Kseq s :: k)) (strip_skip' (CC.Kseq s k')).
 Proof.
 intros.  destruct (dec_skip s). subst. simpl; auto.
  rewrite strip_skip_not by auto. rewrite strip_skip'_not by auto.
  constructor; auto.
 Qed.

Lemma exec_skips':
  forall f s k' s0 k0' ve te m,
        strip_skip' (CC.Kseq s k') = CC.Kseq s0 k0' ->
        star (CC.State f s k' ve te m) (CC.State f s0 k0' ve te m).
Proof.
 intros.
 destruct (dec_skip s). subst. simpl in *.
 induction k'; try solve [inv H].
 destruct (dec_skip s). subst. simpl in *.
 econstructor 2; eauto. split;[reflexivity|]. constructor. auto. rewrite strip_skip'_not in * by auto.
 inv H. econstructor 2; eauto. split;[reflexivity|]. constructor. constructor 1. auto.
 rewrite strip_skip'_not in H by auto. inv H. constructor 1.
Qed.

Lemma break_strip:
 forall f ve te m k,
     star (CC.State f Sbreak k ve te m) (CC.State f Sbreak (strip_skip' k) ve te m).
 Proof. induction k; try solve [constructor 1].
    destruct (dec_skip s). subst. simpl.
     econstructor 2. split;[reflexivity|]. constructor. eauto. auto.
  rewrite strip_skip'_not; auto. constructor 1.
Qed.


Lemma strip_skip'_loop2:
  forall f ve te m a3 s k1 k, CC.Kloop2 a3 s k1 = strip_skip' k ->
  star (CC.State f Sskip k ve te m) (CC.State f Sskip (CC.Kloop2 a3 s k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. eapply star_trans; try apply IHk; auto. apply star_one.
 split;[reflexivity|]. constructor. auto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. constructor 1. simpl in H. inv H. constructor 1.
Qed.

Lemma call_strip: forall k, call_cont (strip_skip k) = call_cont k.
Proof.
 induction k; simpl; intros; auto. destruct a; simpl; auto. destruct s; simpl; auto.
Qed.

Lemma strip_call: forall k, strip_skip (call_cont k) = call_cont k.
Proof.
 induction k; simpl; intros; auto. destruct a; simpl; auto.
Qed.

Lemma call_strip': forall k, CC.call_cont (strip_skip' k) = CC.call_cont k.
Proof.
 induction k; simpl; intros; auto. destruct s; simpl; auto.
Qed.

Lemma strip_call': forall k, strip_skip' (CC.call_cont k) = CC.call_cont k.
Proof.
 induction k; simpl; intros; auto.
Qed.

Lemma strip_skip'_loop1:
  forall f ve te m a3 s k1 k, CC.Kloop1 a3 s k1 = strip_skip' k ->
  star (CC.State f Sskip k ve te m) (CC.State f Sskip (CC.Kloop1 a3 s k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. eapply star_trans; try apply IHk; auto. apply star_one.
 split;[reflexivity|]. constructor. auto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. constructor 1. simpl in H. inv H. constructor 1.
Qed.


Lemma strip_skip'_call:
  forall f ve te m lid f' ve' te' k1 k, CC.Kcall lid f' ve' te' k1 = strip_skip' k ->
  star (CC.State f Sskip k ve te m) (CC.State f Sskip (CC.Kcall lid f' ve' te' k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s). subst. eapply star_trans; try apply IHk; auto. apply star_one.
 split;[reflexivity|]. constructor. auto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. constructor 1. simpl in H. inv H. constructor 1.
Qed.

Lemma match_cont_call_strip:
 forall k k',
    call_cont k <> nil ->
    match_cont (strip_skip k) (strip_skip' k') ->
   match_cont (Kseq (Sreturn None) :: call_cont k) (CC.call_cont k').
Proof.
 intros.
 rewrite <- call_strip in *. rewrite <- call_strip'.
 forget (strip_skip k) as k1. forget (strip_skip' k') as k1'.
 revert H; induction H0; simpl; intros; try rewrite call_strip in *; try rewrite call_strip' in *; auto.
 congruence.
 constructor; auto.
Qed.

Lemma match_cont_strip1:
  forall k k', match_cont k k' -> match_cont (strip_skip k) (strip_skip' k').
 Proof. induction 1; try solve [constructor; auto].
 apply match_cont_strip. auto.
Qed.

Lemma match_find_label_None:
  forall lbl s1 k0 k0',      match_cont (strip_skip k0)  (strip_skip' k0') ->
     find_label lbl s1 k0 = None -> CC.find_label lbl s1 k0' = None
 with match_find_ls_None:
   forall lbl ls k0 k0',  match_cont (strip_skip k0)  (strip_skip' k0') ->
     find_label_ls lbl ls k0 = None -> CC.find_label_ls lbl ls k0' = None.
Proof. induction s1; intros; simpl in *; auto.
 revert H0; case_eq (find_label lbl s1_1 (Kseq s1_2 :: k0)); intros. inv H1.
 erewrite IHs1_1; eauto. apply match_cont_strip. auto.
 revert H0; case_eq (find_label lbl s1_1 k0); intros. inv H1.
 erewrite IHs1_1; eauto.
 revert H0; case_eq (find_label lbl s1_1 (Kseq Scontinue :: Kloop1 s1_1 s1_2 :: k0)); intros. inv H1.
 erewrite IHs1_1; eauto. erewrite IHs1_2; eauto. simpl. constructor. auto.
 simpl. constructor; auto.
 eapply match_find_ls_None; eauto. constructor. auto.
 if_tac. subst. inv H0. eapply match_find_label_None; eauto.
 induction ls; intros; simpl in *; auto.
 revert H0; case_eq (find_label lbl s (Kseq (seq_of_labeled_statement ls) :: k0)); intros.
 inv H1.
 erewrite match_find_label_None; eauto. apply match_cont_strip. auto.
Qed.

Lemma match_find_label: forall lbl k' s1 k0 k0',
     match_cont (strip_skip k0) (strip_skip' k0') ->
     (find_label lbl s1 k0 = Some k' ->
      exists s2 : statement, exists k2' : CC.cont,
       CC.find_label lbl s1 k0' = Some (s2, k2') /\
       match_cont k' (CC.Kseq s2 k2'))
 with match_find_label_ls: forall lbl k' s1 k0 k0',
     match_cont (strip_skip k0) (strip_skip' k0') ->
     (find_label_ls lbl s1 k0 = Some k' ->
      exists s2 : statement, exists k2' : CC.cont,
       CC.find_label_ls lbl s1 k0' = Some (s2, k2') /\
       match_cont k' (CC.Kseq s2 k2')).
Proof.
 induction s1; intros; simpl in *; intuition; try discriminate.
 revert H0; case_eq (find_label lbl s1_1 (Kseq s1_2 :: k0)); intros.
 inv H1.
 destruct (IHs1_1 (Kseq s1_2 :: k0) (CC.Kseq s1_2 k0')) as [s2 [k2' [? ?]]]; clear IHs1_1.
 apply match_cont_strip. auto. auto.
 exists s2; exists k2'; split; auto. rewrite H1; auto.
  destruct (IHs1_2 k0 k0') as [s2 [k2' [? ?]]]; clear IHs1_1 IHs1_2; auto.
 exists s2, k2'; split; auto.
 erewrite match_find_label_None; eauto.
  apply match_cont_strip. auto.
 revert H0; case_eq (find_label lbl s1_1 k0); intros. inv H1.
 destruct (IHs1_1 k0 k0') as [s2 [k2' [? ?]]]; clear IHs1_1; auto.
 exists s2, k2'; split; auto.
 rewrite H1. auto.
  destruct (IHs1_2 k0 k0') as [s2 [k2' [? ?]]]; clear IHs1_1 IHs1_2; auto.
 exists s2, k2'; split; auto.
 erewrite match_find_label_None; eauto.
 revert H0; case_eq (find_label lbl s1_1 (Kseq Scontinue :: Kloop1 s1_1 s1_2 :: k0)); intros.
 inv H1.
 destruct (IHs1_1 (Kseq Scontinue :: Kloop1 s1_1 s1_2 :: k0) (CC.Kloop1 s1_1 s1_2 k0')) as [s2 [k2' [? ?]]]; clear IHs1_1; auto.
 simpl. constructor; auto.
 exists s2, k2'; split; auto. rewrite H1. auto.
 destruct (IHs1_2 (Kloop2 s1_1 s1_2 :: k0) (CC.Kloop2 s1_1 s1_2 k0')) as [s2 [k2' [? ?]]]; clear IHs1_1; auto.
 constructor; auto.
 exists s2, k2'; split; auto.
 erewrite match_find_label_None; eauto.  simpl. constructor; auto.
 destruct (match_find_label_ls lbl k' l (Kswitch :: k0) (CC.Kswitch k0')) as [s2 [k2' [? ?]]]; auto.
 constructor; auto.
 exists s2, k2'; split; auto.
 if_tac. subst l.
 exists s1, k0'; split; auto. inv H0; constructor; auto.
 destruct (IHs1 k0 k0') as [s2 [k2' [? ?]]]; auto.
 exists s2, k2'; split; auto.

 clear match_find_label_ls.
 induction s1; intros. simpl in *.
 inv H0.
 simpl in H0.
 destruct (find_label lbl s (Kseq (seq_of_labeled_statement s1) :: k0))
   eqn:?; auto.
 *
  destruct (match_find_label lbl k' s (Kseq (seq_of_labeled_statement s1) :: k0) (CC.Kseq (seq_of_labeled_statement s1)  k0')) as [s2 [k2' [? ?]]]; auto.
  apply match_cont_strip. auto.
  inv H0.
  auto.
  inv H0.
 exists s2, k2'; split; auto.
 simpl.
 rewrite H1. auto.
 *
  simpl.
 destruct (IHs1 _ _ H H0) as [s3 [k3' [? ?]]].
 exists s3, k3'; split; auto.
 erewrite match_find_label_None; try eassumption.
 apply match_cont_strip. auto.
Qed.

Lemma current_function_strip: forall k, current_function (strip_skip k) = current_function k.
Proof.
 induction k; try destruct a; try destruct s; simpl; auto.
Qed.

 Lemma current_function_call_cont:
   forall k, current_function (call_cont k) = current_function k.
 Proof. induction k; try destruct a; simpl; auto. Qed.

 Lemma current_function_find_label:
  forall lbl f s k k', current_function k = Some f ->
              find_label lbl s k = Some k' ->
              current_function k' = Some f
 with current_function_find_label_ls:
  forall lbl f s k k', current_function k = Some f ->
              find_label_ls lbl s k = Some k' ->
              current_function k' = Some f.
 Proof.
   induction s; simpl; intros; try discriminate.
   revert H0; case_eq (find_label lbl s1 (Kseq s2 :: k)); intros. inv H1.
   eapply IHs1; [ | eauto]. simpl; auto.
   eapply IHs2; [ | eauto]. simpl; auto.
 revert H0; case_eq (find_label lbl s1 k); intros. inv H1.
   eapply IHs1; [ | eauto]. simpl; auto.
   eapply IHs2; [ | eauto]. simpl; auto.
 revert H0; case_eq (find_label lbl s1 (Kseq Scontinue :: Kloop1 s1 s2 :: k)); intros. inv H1.
   eapply IHs1; [ | eauto]. simpl; auto.
   eapply IHs2; [ | eauto]. simpl; auto.
  eapply current_function_find_label_ls; [ | eauto]. simpl; auto.
  if_tac in H0. inv H0. simpl. auto.
   eapply IHs; [ | eauto]. simpl; auto.

   induction s; simpl; intros; try discriminate.
  revert H0; case_eq (find_label lbl s (Kseq (seq_of_labeled_statement s0) :: k)); intros.
 inv H1.
  eapply current_function_find_label; [ | eauto]. simpl; auto.
   eapply IHs; [ | eauto]. simpl; auto.
 Qed.

Lemma step_continue_strip:
  forall f k ve te m,
           star (CC.State f Scontinue k ve te m)
               (CC.State f Scontinue (strip_skip' k) ve te m).
Proof.
intros.
induction k; simpl; try constructor 1.
destruct (dec_skip s).
subst.
eapply star_trans.
  apply @star_one. split;[reflexivity|]. apply CC.step_continue_seq.
  apply IHk.
auto.
destruct s; try congruence; constructor 1.
Qed.

(*Similar constructors as CC.State, but without all the mem's*)
Inductive match_states: forall (qm: corestate) (st: CC'.CC_core), Prop :=
 | match_states_seq: forall f ve te s k k'
      (CUR: match current_function k with Some f' => f'=f | _ => True end),
      match_cont (strip_skip k) (strip_skip' (CC.Kseq s k')) ->
      match_states (State ve te k) (CC'.CC_core_State f s k' ve te)
 | match_states_ext: forall k f ef tyargs tyres cc args lid ve te k'
      (CUR: match current_function k with Some f' => f'=f | _ => True end),
      match_cont (strip_skip k) (strip_skip' k') ->
      match_states (ExtCall ef args lid ve te k)
           (CC'.CC_core_Callstate (External ef tyargs tyres cc) args (CC.Kcall lid f ve te k')).

Lemma Clightnew_Clight_sim_eq_noOrder_SSplusConclusion:
forall (c1 : corestate) (m : mem) (c1' : corestate) (m' : mem),
corestep (cl_core_sem ge) c1 m c1' m' ->
forall (c2 : CC'.CC_core),
 match_states c1 c2 ->
exists c2' : CC'.CC_core,
    plus (CC'.CC_core_to_CC_state c2 m) (CC'.CC_core_to_CC_state c2' m') /\
    match_states c1' c2'.
Proof.
intros.
simpl in H.
(* inv H.
rename H1 into H.*)
revert c2 H0. induction H; intros.

* (* step_assign *)
inv H4.
simpl strip_skip in H9.
destruct (exec_skips H9 f ve te m) as [k2 [? ?]]; simpl; auto.
exists (CC'.CC_core_State f Sskip k2 ve te); split.
    eapply star_plus_trans. eassumption.
          apply plus_one. split;[reflexivity|]. econstructor; eauto.
    constructor. apply CUR.  rewrite  H4 in H9.  inv H9.  simpl in *. apply H7.

*  (* step_set *)
inv H0.
destruct (exec_skips H5 f ve te m) as [k2 [? ?]]; simpl; auto.
exists (CC'.CC_core_State f Sskip k2 ve (PTree.set id v te)); split.
  eapply star_plus_trans. eassumption. apply plus_one.
  split;[reflexivity|]. econstructor; eauto.
  rewrite H0 in H5. inv H5; constructor; auto.

* (* step_call_internal *)
inv H7.
 destruct (exec_skips H12 f0 ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H7 in *. inv H12. simpl in CUR.
  exists (CC'.CC_core_State f (fn_body f) (CC.Kcall optid f0 ve te k2) ve' le').
  split.
  + eapply star_plus_trans. apply H8.
               eapply plus_two. split;[reflexivity|]. econstructor; eauto.
               split;[reflexivity|]. econstructor; eauto.
               apply list_norepet_app in H4. destruct H4 as [? [? ?]].
               econstructor; auto.
  + constructor.
     simpl; auto.
     apply match_cont_strip. simpl. constructor; auto.

* (* step_call_external *)
inv H3.
 destruct (exec_skips H8 f ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H3 in *. inv H8. simpl in CUR.
  exists (CC'.CC_core_Callstate (External ef tyargs tyres cc) vargs (CC.Kcall optid f ve te k2)).
  split.
  + eapply star_plus_trans. eassumption. eapply plus_one.
    split;[reflexivity|]. econstructor; eauto.
  + econstructor; eauto.

* (* step_seq *)
 inv H0.
 destruct (exec_skips H5 f ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H0 in *. inv H5.
 destruct (IHcl_step (CC'.CC_core_State f s1 (CC.Kseq s2 k2) ve te))
                as [st2 [? ?]]; clear  IHcl_step.
 repeat constructor; auto.
 apply match_cont_strip.  apply match_cont_strip.  auto.
 exists st2; split; auto.
 eapply star_plus_trans; [ eassumption | ].
 eapply plus_trans. apply @plus_one.
 split;[reflexivity|]. constructor. eassumption.

* (* step_skip *)
 inv H0.
 simpl strip_skip in H5.
 remember (strip_skip k) as k0.
 destruct k0.
 elimtype False; clear - H Heqk0.
 revert H; induction k; intros. inv H.
 forget (a::k) as k';  clear - Heqk0 H.
 remember (State ve te k') as s.
 revert ve te k' Heqs Heqk0; induction H; intros; inv Heqs; simpl in *; try congruence.
 eapply IHcl_step. reflexivity. auto.
 remember (strip_skip' (CC.Kseq s k')) as k0'.
 destruct k0'; inv H5;
  try solve [rewrite <- strip_step in H; rewrite <- Heqk0 in H; inv H].
 +
 assert (s0<>Sskip).
 clear- Heqk0; intro; subst.
 revert Heqk0; induction k; simpl; intros. inv Heqk0. destruct a; try solve [inv Heqk0]; auto. destruct s; inv Heqk0; auto.
 destruct (IHcl_step (CC'.CC_core_State f s k' ve te))
                 as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. rewrite <- Heqk0'.
 constructor 2; auto.
 exists st2; split; auto.
 +
 destruct (IHcl_step (CC'.CC_core_State f Sskip (CC.Kloop1 s0 s1 k0') ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. simpl. rewrite <- Heqk0. constructor. auto.
  exists st2; split; auto.
 inv H0.
 eapply plus_star_trans; try apply H4.
 clear - H3 Heqk0'.
 destruct s; inv Heqk0'.
 rewrite H0 in H3.
 eapply star_plus_trans; [ | apply plus_one; eauto ].
 rewrite <- H0;
 apply strip_skip'_loop1; auto.
 +
 destruct (IHcl_step (CC'.CC_core_State f Sskip (CC.Kloop2 s0 s1 k0') ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
 destruct (dec_skip s). subst.
 econstructor; eauto. rewrite <- Heqk0. constructor. auto.
 rewrite strip_skip'_not in Heqk0' by auto. inv Heqk0'.
  exists st2; split; auto.
  destruct s; inv Heqk0'.
 eapply star_plus_trans; try apply H0.
 clear - H4; revert H4; induction k'; intros; inv H4.
 destruct (dec_skip s). subst.
 specialize (IHk' H0). econstructor 2.
 split;[reflexivity|]. constructor. apply IHk'. auto.
 replace (CC.Kloop2 s0 s1 k0') with (CC.Kseq s k') by  (destruct s; auto; congruence).
 constructor 1.
 constructor 1.
 +
 destruct s; inv Heqk0'.
 destruct (IHcl_step (CC'.CC_core_State f Sskip (CC.Kcall o f0 e t k0') ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. constructor; auto.
  exists st2; split; auto.
  inv H0.
 eapply plus_star_trans; [ | apply H5].
 destruct H4 as [H4' H4].
 inv H4.
 eapply star_plus_trans; [eapply strip_skip'_call; eauto | ].
 apply plus_one. split;[reflexivity|]. constructor; auto.

* (* step_continue *)
 inv H0.
 simpl strip_skip in H5.
 inv H5.
 +
 change (CC.Kseq Scontinue k'0 = strip_skip' (CC.Kseq s k')) in H3.
 symmetry in H3.
 rewrite continue_cont_skip in *.
 simpl in CUR.
 rewrite <- current_function_strip in CUR.
 forget (strip_skip k) as k0. clear k. rename k0 into k.
 generalize (continue_cont_is k); case_eq (continue_cont k); intros; try contradiction.
 rewrite H0 in H; inv H.
 destruct c; try contradiction. destruct l; try contradiction. destruct c; try contradiction.
 subst s0.

 assert (star (CC.State f s k' ve te m)
              (CC.State f Scontinue k'0 ve te m)).
 clear - H3.
 destruct (dec_skip s). subst. simpl in H3.
 eapply exec_skips'; auto.
 rewrite strip_skip'_not in H3 by auto. inv H3. constructor.
 assert (star (CC.State f Scontinue k'0 ve te m)
              (CC.State f Scontinue (strip_skip' k'0) ve te m)).
clear.
  induction k'0; try solve [constructor 1].
 destruct (dec_skip s). subst.  simpl in *. econstructor 2.
 split;[reflexivity|]. constructor. eassumption. auto.
  rewrite strip_skip'_not; auto. constructor 1.
 generalize (star_trans H2 H4); clear H2 H4; intro.
 clear H3.
 forget (strip_skip' k'0) as k0'; clear k'0.
 assert (precontinue_cont k = Kloop1 s1 s2 :: l).
 revert H0; clear; induction k; simpl; try congruence.  destruct a; try congruence; auto.
 assert (exists k1',
               star (CC.State f Scontinue k0' ve te m)
                    (CC.State f Scontinue k1' ve te m) /\
               match_cont (Kseq Scontinue :: Kloop1 s1 s2 :: l) k1'). {
   clear - H1 H0.
   revert H0; induction H1; simpl; intros; try congruence.
   destruct IHmatch_cont as [k1' [? ?]].
   rewrite <- continue_cont_skip; auto.
   econstructor. split; [ | eassumption].
   eapply star_trans; try apply H.
   clear.
   eapply star_trans. apply star_one.
   split;[reflexivity|].
   apply CC.step_continue_seq.
   apply step_continue_strip.
   inv H0.
   econstructor; split. constructor 1.  constructor.  auto.
   destruct IHmatch_cont as [k1' [? ?]].
   rewrite <- continue_cont_skip; auto.
   econstructor. split; [ | eassumption].
   eapply star_trans; try apply H.
   eapply star_trans. apply star_one.
   split;[reflexivity|].
   apply CC.step_continue_switch.
   apply step_continue_strip.
 }
 destruct H4 as [k1' [? ?]].
 generalize (star_trans H2 H4); clear H2 H4; intro H2.
 rewrite H0 in *.
 assert (CUR': match current_function l with
      | Some f' => f' = f
      | None => True
      end). {
   clear - CUR H0. revert CUR H0; induction k; simpl; intros.
   inv H0.
   destruct a; try discriminate; auto.
   apply IHk. auto. auto. inv H0. auto.
   apply IHk; auto.
 }
 clear H1 CUR k H0 H3.
 inv H5. inv H4. simpl in *.
 destruct (IHcl_step (CC'.CC_core_State f s2 (CC.Kloop2 s1 s2 k'0) ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. apply match_cont_strip. constructor. auto.
 exists st2; split; auto.
 eapply star_plus_trans; [apply H2 | ].
 eapply star_plus_trans; [ | apply H0].
 apply star_one. split;[reflexivity|]. constructor. auto.
 +
   change (CC.Kloop1 s0 e3 k'0 = strip_skip' (CC.Kseq s k')) in H1.
 destruct (dec_skip s); [ | destruct s; try congruence; inv H1].
 subst s.
 simpl in H.
 simpl in H1.
 simpl in *.
 assert (star (CC.State f Sskip k' ve te m)
             (CC.State f Sskip (CC.Kloop1 s0 e3 k'0) ve te m)).
 rewrite H1; clear.
 induction k'; intros; try solve [constructor 1].
  destruct (dec_skip s). subst. simpl in *. econstructor 2.
  split;[reflexivity|]. constructor.
  apply IHk'. auto.
 rewrite strip_skip'_not; auto. constructor 1.
 forget (CC.State f Sskip k' ve te m) as st1.
 clear k' H1.
 assert (plus st1 (CC.State f e3 (CC.Kloop2 s0 e3 k'0) ve te m)).
 eapply star_plus_trans; try apply H0.
 econstructor. split;[reflexivity|]. constructor. auto. constructor 1.
 clear H0.
 destruct (IHcl_step (CC'.CC_core_State f e3 (CC.Kloop2  s0 e3 k'0) ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. apply match_cont_strip; constructor; auto.
 exists st2; split; auto.
 eapply plus_trans; eauto.

* (* step_break *)
 inv H0. simpl strip_skip in H5.
(***)
 inv H5.
 change (CC.Kseq Sbreak k'0 = strip_skip' (CC.Kseq s k')) in H3.
 symmetry in H3.
 rewrite <- break_cont_skip in *.
 simpl in CUR.
 rewrite <- current_function_strip in CUR.
 forget (strip_skip k) as k0. clear k. rename k0 into k.
 simpl.
 pose proof (exec_skips' f s k' Sbreak k'0 ve te m H3).
 forget (CC.State f s k' ve te m) as st1.
 clear k' H3. 
 pose proof (break_strip f ve te m k'0).
 pose proof (star_trans H0 H2); clear H0 H2.
 forget (strip_skip' k'0) as k0'; clear k'0.
 assert (X:exists k1',
             plus (CC.State f Sbreak k0' ve te m)
                       (CC.State f Sskip k1' ve te m)
               /\ match_cont (strip_skip (break_cont k)) (strip_skip' k1')). {
       clear - H H1. rename H1 into H2.
       revert H; induction H2; intros; try solve [inv H].
            rewrite break_cont_skip in *. simpl in H.
               destruct (IHmatch_cont H) as [k1' [? ?]]; clear IHmatch_cont. simpl.
               exists k1'; split; auto.
               eapply star_plus_trans; try eassumption.
               econstructor 2. split;[reflexivity|]. constructor.
              apply break_strip.

            simpl  in *. exists k'; split. econstructor.
               split;[reflexivity|].  eapply CC.step_break_loop1. constructor 1. auto.

            simpl  in *. exists k'; split. econstructor.
               split;[reflexivity|].  eapply CC.step_break_loop2. constructor 1. auto.

            simpl in *. exists k'; split.
                  econstructor. split;[reflexivity|]. eapply CC.step_skip_break_switch. auto.
                  constructor 1; auto.
                  auto.
  }

 destruct X as [k1' [? ?]].
 destruct (IHcl_step (CC'.CC_core_State f Sskip k1' ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
       constructor; auto.
       clear - H CUR.
       revert CUR; induction  k; intros. apply I.
       destruct a; simpl in *; auto. apply IHk; auto.
 exists st2; split; auto.
 simpl in H4.
 eapply star_plus_trans; [ | eassumption].
 eapply star_trans; [eassumption | apply plus_star; eassumption].
* (* step_ifthenelse *)
 inv H1. simpl strip_skip in H6.
 inv H6.
 change (CC.Kseq (Sifthenelse a s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H4.
 assert (star (CC.State f s k' ve te m) (CC.State f (Sifthenelse a s1 s2) k'0 ve te m)). {
     clear - H4.
     revert H4; induction k'; intros; try solve [ destruct s; inv H4; constructor 1].
     destruct (dec_skip s). subst s.
     destruct (dec_skip s0). subst s0. simpl in *.
     eapply star_trans; try apply IHk'; eauto. apply star_one.
       split;[reflexivity|]. constructor. auto.
      change (strip_skip' (CC.Kseq Sskip (CC.Kseq s0 k'))) with
               (strip_skip' (CC.Kseq s0 k')) in H4.
      rewrite strip_skip'_not in H4 by auto.
      inv H4. apply star_one.
     split;[reflexivity|]. constructor. rewrite strip_skip'_not in * by auto.
      inv H4. constructor 1.
 }
 exists (CC'.CC_core_State f (if b then s1 else s2) k'0 ve te); split; auto.
 eapply star_plus_trans; try apply H1.
 apply plus_one. split;[reflexivity|]. econstructor; eauto. auto. constructor; auto.
 apply match_cont_strip; auto.

* (* step_loop *)
 inv H0. inv H4.
 change (CC.Kseq (Sloop s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H2.
 generalize (exec_skips' f _ _ _ _ ve te m (@eq_sym _ _ _ H2)); intro.
 exists ( (CC'.CC_core_State f s1 (CC.Kloop1 s1 s2 k'0) ve te)); split.
 eapply star_plus_trans; try apply H.
 apply plus_one. split;[reflexivity|]. eapply CC.step_loop; eauto.
 constructor; auto. apply match_cont_strip; constructor; auto.

* (* step_loop2 *)
  inv H0. inv H4.
 destruct s0; inv H3.
 generalize (strip_skip'_loop2 f ve te m _ _ _ _ H1); intro.
 exists (CC'.CC_core_State f s (CC.Kloop1 s a3 k'0) ve te); split.
 + eapply star_plus_trans; try apply H.
               econstructor. split;[reflexivity|].
                            eapply CC.step_skip_loop2; eauto.
                            apply star_one. split;[reflexivity|]. eapply CC.step_loop; eauto.
 + constructor; auto. apply match_cont_strip. constructor. auto.

* (* step_return *) {
 inv H3.
  remember (strip_skip' (CC.Kseq s k'0)) as k3. simpl in CUR, H8.
 inv H8.
 * (*first case*)
 generalize (exec_skips' f0 _ _ _ _ ve te m (@eq_sym _ _ _ H4)); intro H99.
 assert (f0=f).
   simpl in CUR; clear - CUR H.
   revert H CUR; induction k; intros. inv H. simpl in *. destruct a; auto. inv CUR; auto. inv H; auto.
 subst f.
 generalize (match_cont_call_strip k k'1); intro.
 spec H3; [congruence |]. spec H3; [auto |].
 generalize H3; rewrite H; intro.
 inv H5.
  +  elimtype False; clear - H10.
         revert H10; induction k'1; simpl; intros; congruence.
  + destruct optexp;  [destruct H1 as [v [? ?]] | ]; (destruct optid; destruct H2 as [H2 H2'];
               try solve [contradiction H2; auto]; subst te'' ).
    -   eexists (CC'.CC_core_State f Sskip k'2 ve' (PTree.set i v' te')).
                split.
                     apply (star_plus_trans H99). (*with (s2:=CC.State f0 (Sreturn (Some e)) k'1 ve te m).  apply H99. *)
                     eapply @plus_trans with (s2:=CC.Returnstate v' (CC.call_cont k'1) m').
                                         eapply plus_one. split;[reflexivity|]. simpl. econstructor; eauto.
                                         eapply plus_one. split;[reflexivity|]. simpl. rewrite <- H13.
                                         eapply CC.step_returnstate.
                    constructor; auto.
    -   eexists (CC'.CC_core_State f Sskip k'2 ve' te').
                split.
                     eapply (star_plus_trans H99). (* with (s2:=CC.State f0 (Sreturn (Some e)) k'1 ve te m). apply H99. *)
                          eapply @plus_trans with (s2:=CC.Returnstate v' (CC.call_cont k'1) m').
                                         eapply plus_one. split;[reflexivity|]. simpl. econstructor; eauto.
                                         eapply plus_one. split;[reflexivity|]. simpl. rewrite <- H13. eapply CC.step_returnstate.
                    constructor; auto.
    -   eexists (CC'.CC_core_State f Sskip k'2 ve' (CC.set_opttemp (Some i) Vundef te')).
                split.
                     eapply (star_plus_trans H99).  (*with (s2:=CC.State f0 (Sreturn None) k'1 ve te m).  apply H99. *)
                          eapply @plus_trans with (s2:=CC.Returnstate Vundef (CC.call_cont k'1) m').
                                         eapply plus_one. split;[reflexivity|]. simpl. econstructor; eauto.
                                         eapply plus_one. split;[reflexivity|]. simpl. rewrite <- H13.
                apply CC.step_returnstate. subst.
                 simpl. constructor 1. auto. simpl.  auto.
   - eexists (CC'.CC_core_State f Sskip k'2 ve' te').
                split.
                     eapply (star_plus_trans H99).
                          eapply @plus_trans with (s2:=CC.Returnstate Vundef (CC.call_cont k'1) m').
                                         eapply plus_one. split;[reflexivity|]. simpl. econstructor; eauto.
                                         eapply plus_one. split;[reflexivity|]. simpl. rewrite <- H13.
                apply CC.step_returnstate. subst.
                 simpl. constructor 1. auto. simpl.  auto.
 * (*second case*)
 destruct optid; destruct H2 as [_ H2]; subst te''.
  + simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR.
    destruct s; inv H4.
    assert (star (CC.State f Sskip k'0 ve te m)
                 (CC.State f Sskip (CC.Kcall (Some i) f1 ve' te' k'1) ve te m)).
     clear - H1.
     revert H1; induction k'0; intros; try solve [inv H1].
           destruct (dec_skip s). subst s. simpl in H1.
               eapply star_trans; try apply IHk'0; auto. 
               apply star_one. split;[reflexivity|]. constructor; auto.
          rewrite strip_skip'_not in H1 by auto. rewrite <- H1. constructor 1.
          simpl in H1. inv H1. constructor 1.
 (econstructor; split; [eapply star_plus_trans; [ apply H  | eapply plus_two ] | ]).
     split;[reflexivity|]. eapply CC.step_skip_call; simpl; eauto.
     assert (X: CCstep (CC.Returnstate Vundef (CC.Kcall (Some i) f1 ve' te' k'1) m')
                       (CC'.CC_core_to_CC_state (CC'.CC_core_State f1 Sskip k'1 ve'  (CC.set_opttemp (Some i) Vundef te')) m')).
           split;[reflexivity|]. econstructor; eauto.
       apply X.
    auto.
    econstructor; eauto.
 +
   simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR.
 destruct s; inv H4.
 assert (star (CC.State f Sskip k'0 ve te m)
             (CC.State f Sskip (CC.Kcall None f1 ve' te' k'1) ve te m)).
     clear - H1.
     revert H1; induction k'0; intros; try solve [inv H1].
           destruct (dec_skip s). subst s. simpl in H1.
               eapply star_trans; try apply IHk'0; auto.
          apply star_one. split;[reflexivity|]. constructor; auto.
          rewrite strip_skip'_not in H1 by auto. rewrite <- H1. constructor 1.
          simpl in H1. inv H1. constructor 1.
 (econstructor; split; [eapply star_plus_trans; [ apply H  | eapply plus_two ] | ]).
     split;[reflexivity|]. eapply CC.step_skip_call; simpl; eauto.
     assert (X: CCstep (CC.Returnstate Vundef (CC.Kcall None f1 ve' te' k'1) m')
                       (CC'.CC_core_to_CC_state (CC'.CC_core_State f1 Sskip k'1 ve' te') m')).
            split;[reflexivity|]. econstructor; eauto.
       apply X.
    auto.
    econstructor; eauto.
}

* (* step_switch *)
 inv H1. simpl strip_skip in H6.
 remember (CC.Kseq s k') as k0'.
 inv H6.
 evar (c2': CC'.CC_core).
 exists c2'; split.
 2:{ constructor; eauto. apply match_cont_strip. simpl.
                    instantiate (1:= CC.Kswitch k'0). constructor. auto.
   }
     generalize (exec_skips' f _ _ _ _ ve te m (@eq_sym _ _ _ H4)); intro H99.
        eapply star_plus_trans; try apply H99.
        unfold c2'. apply plus_one. split;[reflexivity|]. simpl. econstructor; eauto.

* (* step_label *)
 inv H0.  remember (CC.Kseq s0 k') as k0'. inv H5.
 destruct (IHcl_step (CC'.CC_core_State f s k'0 ve te)) as [st2 [? ?]]; clear IHcl_step.
 constructor; auto. apply match_cont_strip. auto.
 exists st2; split; auto.
   eapply star_plus_trans; try eassumption.
   generalize (exec_skips' f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
     eapply star_trans; try apply H99.
     apply star_one. split;[reflexivity|]. constructor.

* (* step_goto *)
 inv H0. remember (CC.Kseq s k'0) as k0'. inv H5.
  generalize (match_cont_call_strip k k'1); intro.
 spec H0.
 clear - CUR. apply (call_cont_nonnil _ _ CUR).
 specialize (H0 H1).
  rewrite <- strip_call' in H0.
 change (Kseq (Sreturn None) :: call_cont k) with (strip_skip (Kseq (Sreturn None) :: call_cont k)) in H0.
 destruct (match_find_label _ _ _ _ _ H0 H) as [s2 [k2' [? ?]]].
 exists (CC'.CC_core_State f s2 k2' ve te); split.
    simpl in CUR0. inversion2 CUR CUR0.
     generalize (exec_skips' f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
     eapply star_plus_trans; try apply H99.
         apply plus_one. split;[reflexivity|]. constructor; auto.
         constructor; auto.
   clear - CUR H. forget (fn_body f) as s.
       rewrite <- current_function_call_cont in CUR.
       change (current_function (Kseq (Sreturn None) :: call_cont k) = Some f) in CUR.
        forget (Kseq (Sreturn None) :: call_cont k) as k0. clear - CUR H.
        rewrite (current_function_find_label _ _ _ _ _ CUR H). auto.
 apply match_cont_strip1. auto.
Qed.

End GE.

Definition coresem_extract_cenv {M} {core} (CS: @CoreSemantics core M)
                         (cenv: composite_env) :
            @CoreSemantics core M :=
  Build_CoreSemantics _ _
             (CS.(initial_core))
             (CS.(semantics.at_external))
             (CS.(semantics.after_external))
             CS.(halted)
            (CS.(corestep) )
            (CS.(corestep_not_halted) )
            CS.(corestep_not_at_external).

Require Import VST.sepcomp.step_lemmas.

Definition genv_symb_injective {F V} (ge: Genv.t F V) : extspec.injective_PTree block.
Proof.
exists (Genv.genv_symb ge).
hnf; intros.
eapply Genv.genv_vars_inj; eauto.
Defined.
