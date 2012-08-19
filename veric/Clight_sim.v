Require Import veric.base.
Require Import veric.Clight_lemmas.
Require Import veric.forward_simulations.
Require Import veric.forward_simulations_proofs.
Require Import veric.Clight_new.
Require compcert.Clight_sem.
Module CC := Clight_sem.

(* Don't need this proof here, but it's a shame to delete it. *)
Lemma cc_step_fun: forall ge s1 s2 s2',
   CC.step ge s1 nil s2 -> CC.step ge s1 nil s2' -> s2=s2'.
Proof.
 intros.
 inv H; inv H0;
 repeat match goal with
  | H: _ \/ _  |- _ => destruct H; try discriminate
  end;
 try contradiction;
  repeat fun_tac; auto; try congruence.
  inversion2 H18 H5. 
  fun_tac. auto.
  rename H9 into H0. rename H1 into H.
  clear - H H0.
  hnf in H,H0.
  destruct ef; try congruence; inv H; inv H0; try congruence.
  inv H7; inv H1; congruence.
  inv H1; inv H8; congruence.
  inv H3; inv H2; congruence.
  inv H2; inv H4; congruence.
Qed.

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
  | match_cont_while'' : forall (a : expr) (s : statement) (k : cont)
                          (k' : CC.cont),
                        match_cont (strip_skip k) (strip_skip' k') ->
                        match_cont (Kseq Scontinue :: Kfor2 a Sskip s ::  k) (CC.Kwhile a s k')
  | match_cont_while': forall a s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
           match_cont (Kseq (Sfor' a Sskip s) :: k) (CC.Kseq (Swhile a s) k')
  | match_cont_while: forall e s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kfor3 e Sskip s :: k) (CC.Kwhile e s k')
  | match_cont_dowhile': forall e s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
           match_cont (Kfor3 e Sskip s :: k) (CC.Kdowhile e s k')
  | match_cont_dowhile: forall e s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
         match_cont (Kseq Scontinue :: Kfor2 e Sskip s :: k) (CC.Kdowhile e s k')
  | match_cont_for2: forall e2 e3 s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq Scontinue :: Kfor2 e2 e3 s :: k) (CC.Kfor2 e2 e3 s k')
  | match_cont_for3: forall e2 e3 s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kfor3 e2 e3 s :: k) (CC.Kfor3 e2 e3 s k')
  | match_cont_switch: forall k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kswitch :: k) (CC.Kswitch k')
  | match_cont_call: forall lid fd f ve te k k'
         (CUR: current_function k = Some f),
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq (Sreturn None) :: Kcall lid fd ve te :: k) (CC.Kcall lid f ve te k').

Inductive match_states: forall (qm: corestate * mem) (st: CC.state), Prop :=
 | match_states_seq: forall f ve te s k k' m
      (CUR: current_function k = Some f),
      match_cont (strip_skip k) (strip_skip' (CC.Kseq s k')) ->
      match_states (State ve te k, m) (CC.State f s k' ve te m)
 | match_states_ext: forall k f ef tyargs tyres args lid ve te m k'
      (CUR: current_function k = Some f),
      match_cont (strip_skip k) (strip_skip' k') ->
      match_states (ExtCall ef (signature_of_type tyargs tyres) args lid ve te k, m) 
           (CC.Callstate (External ef tyargs tyres) args (CC.Kcall lid f ve te k') m).

Lemma exec_skips:
 forall {s0 k s k'} 
   (H1: match_cont (Kseq s0 :: k) (strip_skip' (CC.Kseq s k')))
   ge f ve te m,
   match s0 with Sskip => False | Scontinue => False | Sfor' _ _ _ => False 
            | Sifthenelse _ _ _ => False | Sreturn _ => False 
            | _ => True end ->
   exists k2, strip_skip' (CC.Kseq s k') = CC.Kseq s0 k2 /\
     Smallstep.star CC.step ge (CC.State f s k' ve te m) Events.E0 
              (CC.State f s0 k2 ve te m).
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
 econstructor 2. constructor. eauto. auto.
 inv H1; contradiction. simpl in *. inv H1. contradiction.
 simpl in H1. inv H1. contradiction.
 simpl in H1. inv H1. contradiction.
  replace (strip_skip' (CC.Kseq s1 k')) with (CC.Kseq s1 k')  in *
     by (destruct s1; try congruence; auto).
 inv H1.
 exists k'; split; auto.
 constructor 1.
 contradiction.
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
 forall k, match (continue_cont k) with nil => True | Kseq e3 :: Kfor3 e2 e3' s :: _ => e3=e3' | _ => False end.
Proof.
 induction k; simpl; auto; try contradiction.
  destruct a; auto.
Qed.

Inductive step' ge : (corestate * mem) -> Events.trace -> (corestate * mem) -> Prop :=
 mk_step': forall q m q' m', cl_step ge q m q' m' -> step' ge (q,m) Events.E0 (q',m').

Module SS := compcert.Smallstep.
Definition ef_exit := EF_external exit_syscall_number (mksignature nil None).

Inductive initial_state (p: program): (corestate * mem) -> Prop :=
(*
  | initial_state_intro: forall b (f: fundef) m0 ve te,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s ->
      initial_state p (State ve te (Kfun f nil None  :: Kfun (External ef_exit Tnil Tvoid) nil None :: nil), m0).
*)
  .  (* fixme *)

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: (corestate * mem) -> int -> Prop :=
(*
  | final_state_intro: forall r ve te m,
      final_state (State ve te 
                          (Kfun (External ef_exit Tnil Tvoid) nil None :: nil), m) r
*)
 . (* fixme *)

Definition semantics (p: program) :=
  SS.Semantics step' (initial_state p) final_state (Genv.globalenv p).

Lemma match_cont_strip:
   forall s k k', match_cont (strip_skip k) (strip_skip' k') ->
           match_cont (strip_skip (Kseq s :: k)) (strip_skip' (CC.Kseq s k')).
 Proof.
 intros.  destruct (dec_skip s). subst. simpl; auto. 
  rewrite strip_skip_not by auto. rewrite strip_skip'_not by auto.
  constructor; auto.
 Qed.

Lemma exec_skips':
  forall ge f s k' s0 k0' ve te m,
        strip_skip' (CC.Kseq s k') = CC.Kseq s0 k0' ->
        Smallstep.star CC.step ge (CC.State f s k' ve te m) Events.E0
                                   (CC.State f s0 k0' ve te m).
Proof.
 intros.
 destruct (dec_skip s). subst. simpl in *.
 induction k'; try solve [inv H]. 
 destruct (dec_skip s). subst. simpl in *.
 econstructor 2; eauto. constructor. auto. rewrite strip_skip'_not in * by auto.
 inv H. econstructor 2; eauto. constructor. constructor 1. auto.
 rewrite strip_skip'_not in H by auto. inv H. constructor 1.
Qed.

Lemma break_strip:
 forall ge f ve te m k,
     SS.star CC.step ge (CC.State f Sbreak k ve te m) nil (CC.State f Sbreak (strip_skip' k) ve te m).
 Proof. induction k; try solve [constructor 1].
    destruct (dec_skip s). subst. simpl. 
     econstructor 2. constructor. eauto. auto.
  rewrite strip_skip'_not; auto. constructor 1.
Qed.

Lemma plus_trans: forall ge s1 s2 s3, 
   SS.plus CC.step ge s1 Events.E0 s2 -> SS.plus CC.step ge s2 Events.E0 s3 -> SS.plus CC.step ge s1 Events.E0 s3.
Proof.
 intros. eapply SS.plus_trans; eauto.
Qed.

Lemma star_plus_trans: forall ge s1 s2 s3, 
   SS.star CC.step ge s1 Events.E0 s2 -> SS.plus CC.step ge s2 Events.E0 s3 -> SS.plus CC.step ge s1 Events.E0 s3.
Proof.
 intros. eapply SS.star_plus_trans; eauto.
Qed. 

Lemma plus_star_trans: forall ge s1 s2 s3, 
   SS.plus CC.step ge s1 Events.E0 s2 -> SS.star CC.step ge s2 Events.E0 s3 -> SS.plus CC.step ge s1 Events.E0 s3.
Proof.
 intros. eapply SS.plus_star_trans; eauto.
Qed.

Lemma star_trans: forall ge s1 s2 s3, 
   SS.star CC.step ge s1 Events.E0 s2 -> SS.star CC.step ge s2 Events.E0 s3 -> SS.star CC.step ge s1 Events.E0 s3.
Proof.
 intros. eapply SS.star_trans; eauto.
Qed.

Lemma strip_skip'_while:
  forall ge f ve te m a s k1 k, CC.Kwhile a s k1 = strip_skip' k ->
  SS.star CC.step ge (CC.State f Sskip k ve te m) Events.E0 (CC.State f Sskip (CC.Kwhile a s k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. eapply SS.star_trans; try apply IHk; auto. apply SS.star_one. constructor. auto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. constructor 1. simpl in H. inv H. constructor 1.
Qed.

Lemma strip_skip'_dowhile:
  forall ge f ve te m a s k1 k, CC.Kdowhile a s k1 = strip_skip' k ->
  SS.star CC.step ge (CC.State f Sskip k ve te m) Events.E0 (CC.State f Sskip (CC.Kdowhile a s k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. eapply SS.star_trans; try apply IHk; auto. apply SS.star_one. constructor. auto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. constructor 1. simpl in H. inv H. constructor 1.
Qed.

Lemma strip_skip'_for3:
  forall ge f ve te m a2 a3 s k1 k, CC.Kfor3 a2 a3 s k1 = strip_skip' k ->
  SS.star CC.step ge (CC.State f Sskip k ve te m) Events.E0 (CC.State f Sskip (CC.Kfor3 a2 a3 s k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. eapply SS.star_trans; try apply IHk; auto. apply SS.star_one. constructor. auto.
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


Lemma strip_skip'_for2:
  forall ge f ve te m a2 a3 s k1 k, CC.Kfor2 a2 a3 s k1 = strip_skip' k ->
  SS.star CC.step ge (CC.State f Sskip k ve te m) Events.E0 (CC.State f Sskip (CC.Kfor2 a2 a3 s k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. eapply SS.star_trans; try apply IHk; auto. apply SS.star_one. constructor. auto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. constructor 1. simpl in H. inv H. constructor 1.
Qed.


Lemma strip_skip'_call:
  forall ge f ve te m lid f' ve' te' k1 k, CC.Kcall lid f' ve' te' k1 = strip_skip' k ->
  SS.star CC.step ge (CC.State f Sskip k ve te m) Events.E0 (CC.State f Sskip (CC.Kcall lid f' ve' te' k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s). subst. eapply SS.star_trans; try apply IHk; auto. apply SS.star_one. constructor. auto.
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
 revert H0; case_eq (find_label lbl s1_1 (Kseq s1_2 :: k0)); intros.
 inv H1. erewrite IHs1_1; eauto. apply match_cont_strip. auto.
 revert H0; case_eq (find_label lbl s1_1 k0); intros. inv H1.
 erewrite IHs1_1; eauto.  erewrite IHs1; eauto. simpl; constructor; auto.
 erewrite IHs1; eauto. constructor. auto.
 revert H0; case_eq (find_label lbl s1_2 (Kseq Scontinue :: Kfor2 e s1_1 s1_2 :: k0)); intros. inv H1.
 erewrite IHs1_2; eauto. erewrite IHs1_1; eauto. constructor. auto.
 simpl. constructor; auto.
 eapply match_find_ls_None; eauto. constructor. auto.
 if_tac. subst. inv H0. eapply match_find_label_None; eauto.
 induction ls; intros; simpl in *.
 eapply match_find_label_None; eauto.
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
  destruct (IHs1 (Kseq Scontinue :: Kfor2 e Sskip s1 :: k0) (CC.Kwhile e s1 k0')) as [s2 [k2' [? ?]]]; clear IHs1; auto.
 constructor; auto.
 exists s2, k2'; split; auto.
  destruct (IHs1 (Kseq Scontinue :: Kfor2 e Sskip s1 :: k0) (CC.Kdowhile e s1 k0')) as [s2 [k2' [? ?]]]; clear IHs1; auto.
 constructor; auto.
 exists s2, k2'; split; auto.
 revert H0; case_eq (find_label lbl s1_2 (Kseq Scontinue :: Kfor2 e s1_1 s1_2 :: k0)); intros.
 inv H1.
  destruct (IHs1_2 (Kseq Scontinue :: Kfor2 e s1_1 s1_2 :: k0) (CC.Kfor2 e s1_1 s1_2 k0')) as [s2 [k2' [? ?]]]; clear IHs1_1; auto.
 simpl. constructor; auto.
 exists s2, k2'; split; auto. rewrite H1. auto.
 destruct (IHs1_1 (Kfor3 e s1_1 s1_2 :: k0) (CC.Kfor3 e s1_1 s1_2 k0')) as [s2 [k2' [? ?]]]; clear IHs1_1; auto.
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
 
 induction s1; intros. simpl in *.
 eauto.
 simpl in *.
 revert H0; case_eq (find_label lbl s (Kseq (seq_of_labeled_statement s1) :: k0)); intros.
 inv H1.
destruct (match_find_label lbl k' s (Kseq (seq_of_labeled_statement s1) :: k0) (CC.Kseq (seq_of_labeled_statement s1)  k0')) as [s2 [k2' [? ?]]]; auto.
apply match_cont_strip. auto.
 exists s2, k2'; split; auto.
 rewrite H1. auto.
 erewrite match_find_label_None; eauto.
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
   eapply IHs; [ | eauto]. simpl; auto.
   eapply IHs; [ | eauto]. simpl; auto.
 revert H0; case_eq (find_label lbl s2 (Kseq Scontinue :: Kfor2 e s1 s2 :: k)); intros. inv H1.
   eapply IHs2; [ | eauto]. simpl; auto.
   eapply IHs1; [ | eauto]. simpl; auto.
  eapply current_function_find_label_ls; [ | eauto]. simpl; auto.
  if_tac in H0. inv H0. simpl. auto.
   eapply IHs; [ | eauto]. simpl; auto.
   induction s; simpl; intros; try discriminate.
  eapply current_function_find_label; [ | eauto]. simpl; auto.
  revert H0; case_eq (find_label lbl s (Kseq (seq_of_labeled_statement s0) :: k)); intros.
 inv H1.
  eapply current_function_find_label; [ | eauto]. simpl; auto. 
   eapply IHs; [ | eauto]. simpl; auto.
 Qed.


Lemma step_continue_strip:
  forall ge f k ve te m, 
           SS.star CC.step ge (CC.State f Scontinue k ve te m) Events.E0
               (CC.State f Scontinue (strip_skip' k) ve te m).
Proof.
intros.
induction k; simpl; try constructor 1.
destruct (dec_skip s).
subst.
eapply star_trans.
apply SS.star_one; apply CC.step_continue_seq.
auto.
destruct s; try congruence; constructor 1.
Qed.

Lemma sim: forall p, SS.forward_simulation (semantics p) (CC.semantics p).
Proof.
intros. 
apply (SS.forward_simulation_plus) with match_states; auto.
admit.  (* initial states *)
admit.  (* final states *)

simpl. intros.
forget (Genv.globalenv p) as ge. clear p.
inv H.
rename H1 into H.
revert s2 H0; induction H; intros.

Focus 1. (* step_assign *)
inv H4.
simpl strip_skip in H10.
destruct (exec_skips H10 ge f ve te m) as [k2 [? ?]]; auto.
exists (CC.State f Sskip k2 ve te m'); split.
eapply star_plus_trans. eassumption. apply SS.plus_one. econstructor; eauto.
 assert (t=nil). inv H3; try congruence; reflexivity. subst t. auto.
constructor; auto.
rewrite H4 in H10. inv H10; auto. 

Focus 1. (* step_set *)
inv H0.
destruct (exec_skips H6 ge f ve te m) as [k2 [? ?]]; auto.
 exists (CC.State f Sskip k2 ve (PTree.set id v te) m).
split.
eapply star_plus_trans. eassumption. apply SS.plus_one. econstructor; eauto. auto.
rewrite H0 in H6. inv H6; constructor; auto.

Focus 1. (* step_call_internal *)
inv H7. 
 destruct (exec_skips H13 ge f0 ve te m) as [k2 [? ?]]; auto.
 rewrite H7 in *. inv H13. simpl in CUR. 
 econstructor; split. 
eapply star_plus_trans. eassumption. eapply SS.plus_two. econstructor; eauto.
 econstructor; eauto. auto.
 constructor. auto. apply match_cont_strip. simpl.
 constructor; auto.

Focus 1. (* step_call_external *)
inv H3. 
 destruct (exec_skips H9 ge f ve te m) as [k2 [? ?]]; auto.
 rewrite H3 in *. inv H9. simpl in CUR. 
 econstructor; split. 
eapply star_plus_trans. eassumption. eapply SS.plus_one. econstructor; eauto.
 econstructor; eauto.

Focus 1. (* step_seq *)
 inv H0.
 destruct (exec_skips H6 ge f ve te m) as [k2 [? ?]]; auto.
 rewrite H0 in *. inv H6.
 destruct (IHcl_step (CC.State f s1 (CC.Kseq s2 k2) ve te m))
                as [st2 [? ?]]; clear  IHcl_step.
 repeat constructor; auto.
 apply match_cont_strip.  apply match_cont_strip.  auto.
 exists st2; split; auto.
 eapply star_plus_trans; [ eassumption | ].
 eapply plus_trans. apply SS.plus_one. constructor. eassumption.

 Focus 1. (* step_skip *)
 inv H0.
 simpl strip_skip in H6.
 remember (strip_skip k) as k0.
 destruct k0.
 elimtype False; clear - H Heqk0.
 revert H; induction k; intros. inv H.
 forget (a::k) as k';  clear - Heqk0 H.
 remember (State ve te k') as s.
 revert ve te k' Heqs Heqk0; induction H; intros; inv Heqs; simpl in *; try congruence.
 eapply IHcl_step. reflexivity. auto.
 remember (strip_skip' (CC.Kseq s k')) as k0'.
 destruct k0'; inv H6;
  try solve [rewrite <- strip_step in H; rewrite <- Heqk0 in H; inv H].
 assert (s0<>Sskip).
 clear- Heqk0; intro; subst.
 revert Heqk0; induction k; simpl; intros. inv Heqk0. destruct a; try solve [inv Heqk0]; auto. destruct s; inv Heqk0; auto.
 destruct (IHcl_step (CC.State f s k' ve te m)) 
                 as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. rewrite <- Heqk0'.
 constructor 2; auto.
 exists st2; split; auto.

 rewrite <- strip_step in H; rewrite <- Heqk0 in H.
 generalize (exec_skips' ge f _ _ _ _ ve te m (@eq_sym _ _ _ Heqk0')); intro H99.
  destruct (IHcl_step (CC.State f (Swhile a s1) k0' ve te m))
                 as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. constructor. auto.
 exists st2; split; auto.
 eapply star_plus_trans; eassumption.

rewrite <- strip_step in H. rewrite <- Heqk0 in H.
  destruct (IHcl_step (CC.State f Sskip (CC.Kwhile e s0 k0') ve te m))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. simpl. rewrite <- Heqk0. constructor. auto.
 exists st2; split; auto.
 destruct s; inv Heqk0'. rewrite H4 in H0.
 eapply star_plus_trans; [ | eassumption  ].
 rename H4 into H3;  clear - H3.
 revert H3; induction k'; intros; inv H3.
 destruct (dec_skip s). subst.
 specialize (IHk' H0).
 econstructor. constructor. apply IHk'. auto.
 rewrite strip_skip'_not; auto.
  constructor 1.
 constructor 1.

  destruct (IHcl_step (CC.State f Sskip (CC.Kwhile e s0 k0') ve te m)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. simpl. rewrite <- Heqk0. constructor. auto.
 exists st2; split; auto.
 destruct s; inv Heqk0'. rewrite H4 in H0.
 eapply star_plus_trans; [ | eassumption  ].
 rename H4 into H3;  clear - H3.
 revert H3; induction k'; intros; inv H3.
 destruct (dec_skip s). subst.
 specialize (IHk' H0).
 econstructor. constructor. apply IHk'. auto.
 rewrite strip_skip'_not; auto.
  constructor 1.
 constructor 1.

  destruct (IHcl_step (CC.State f Sskip (CC.Kdowhile e s0 k0') ve te m)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. simpl. rewrite <- Heqk0. constructor.
 auto.
 exists st2; split; auto.
 destruct s; inv Heqk0'. rewrite H4 in H0.
 eapply star_plus_trans; [ | eassumption  ].
 rename H4 into H3;  clear - H3.
 revert H3; induction k'; intros; inv H3.
 destruct (dec_skip s). subst.
 specialize (IHk' H0).
 econstructor. constructor. apply IHk'. auto.
 rewrite strip_skip'_not; auto.
  constructor 1.
 constructor 1.

 destruct s; inv Heqk0'.
  destruct (IHcl_step (CC.State f Sskip (CC.Kdowhile e s0 k0') ve te m)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto.  rewrite <- Heqk0. constructor. auto.
 exists st2; split; auto.
 rewrite H2 in H0.
 eapply star_plus_trans; try apply H0.
 clear - H2.
 rewrite <- H2.
 apply strip_skip'_dowhile; auto.

  destruct (IHcl_step (CC.State f Sskip (CC.Kfor2 e s0 s1 k0') ve te m)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. simpl. rewrite <- Heqk0. constructor. auto.
  exists st2; split; auto.
 inv H0. destruct t1; inv H5. simpl in H0. subst t2.
 eapply plus_star_trans; try apply H4.
 clear - H3 Heqk0'.
 destruct s; inv Heqk0'.
 rewrite H0 in H3.
 eapply star_plus_trans; [ | apply SS.plus_one; eauto ].

 rewrite <- H0;
 apply strip_skip'_for2; auto.

 destruct (IHcl_step (CC.State f Sskip (CC.Kfor3 e s0 s1 k0') ve te m)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 destruct (dec_skip s). subst.
 econstructor; eauto. rewrite <- Heqk0. constructor. auto.
 rewrite strip_skip'_not in Heqk0' by auto. inv Heqk0'.
  exists st2; split; auto.
  destruct s; inv Heqk0'.
 eapply star_plus_trans; try apply H0.
 clear - H4; revert H4; induction k'; intros; inv H4.
 destruct (dec_skip s). subst.
 specialize (IHk' H0). econstructor 2. constructor. apply IHk'. auto.
 replace (CC.Kfor3 e s0 s1 k0') with (CC.Kseq s k') by  (destruct s; auto; congruence).
 constructor 1.
 constructor 1.

 destruct s; inv Heqk0'.
 destruct (IHcl_step (CC.State f Sskip (CC.Kcall o f0 e t k0') ve te m))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. constructor; auto.
  exists st2; split; auto.
  inv H0. destruct t1; inv H6. simpl in H0; subst t2.
 eapply plus_star_trans; [ | apply H5].
 inv H4.
 eapply star_plus_trans; [eapply strip_skip'_call; eauto | ].
 apply SS.plus_one. constructor; auto.

 Focus 1. (* step_continue *)
 inv H0.
 simpl strip_skip in H6.
 inv H6.
 Focus 1.  (* match_cont_seq: case 1 of 5 *)
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

 assert (SS.star CC.step ge (CC.State f s k' ve te m) Events.E0 
                             (CC.State f Scontinue k'0 ve te m)).
 clear - H3.
 destruct (dec_skip s). subst. simpl in H3.
 eapply exec_skips'; auto.
 rewrite strip_skip'_not in H3 by auto. inv H3. constructor.
 assert (SS.star CC.step ge (CC.State f Scontinue k'0 ve te m) Events.E0
                                 (CC.State f Scontinue (strip_skip' k'0) ve te m)).
clear.
  induction k'0; try solve [constructor 1].
 destruct (dec_skip s). subst.  simpl in *. econstructor 2. constructor. eassumption. auto.
  rewrite strip_skip'_not; auto. constructor 1.
 generalize (SS.star_trans H2 H4 (eq_refl _)); clear H2 H4; intro.
 clear H3.
 forget (strip_skip' k'0) as k0'; clear k'0.
 assert (precontinue_cont k = Kfor2 e s1 s2 :: l).
 revert H0; clear; induction k; simpl; try congruence.  destruct a; try congruence; auto.
 assert (exists k1', 
               Smallstep.star CC.step ge (CC.State f Scontinue k0' ve te m)
                  (Events.Eapp Events.E0 Events.E0)
                    (CC.State f Scontinue k1' ve te m) /\
               match_cont (Kseq Scontinue :: Kfor2 e s1 s2 :: l) k1').
 clear - H1 H0.
 revert H0; induction H1; simpl; intros; try congruence.
 destruct IHmatch_cont as [k1' [? ?]].
 rewrite <- continue_cont_skip; auto.
 econstructor. split; [ | eassumption].
 eapply star_trans; try apply H.
 clear.
 eapply star_trans. apply SS.star_one.
 apply CC.step_continue_seq.
 apply step_continue_strip.
 inv H0.
 econstructor; split. constructor 1.  constructor.  auto.
 destruct IHmatch_cont as [k1' [? ?]].
 rewrite <- continue_cont_skip; auto.
 econstructor. split; [ | eassumption].
 eapply star_trans; try apply H.
 eapply star_trans. apply SS.star_one.
 apply CC.step_continue_seq.
 apply step_continue_strip.
 inv H0.  econstructor; split. constructor 1.  constructor.  auto.
 inv H0.  econstructor; split. constructor 1.  constructor.  auto.
 destruct IHmatch_cont as [k1' [? ?]].
 rewrite <- continue_cont_skip; auto.
 econstructor. split; [ | eassumption].
 eapply star_trans; try apply H.
 eapply star_trans. apply SS.star_one.
 apply CC.step_continue_switch.
 apply step_continue_strip.

 destruct H4 as [k1' [? ?]].
 generalize (SS.star_trans H2 H4 (eq_refl _)); clear H2 H4; intro H2.
 rewrite H0 in *.
 assert (CUR': current_function l = Some f).
   clear - CUR H0. revert CUR H0; induction k; simpl; intros. inv CUR.
   destruct a; try discriminate; auto. inv H0. auto.
 clear H1 CUR k H0 H3.
 inv H5. inv H4. simpl in *.
 rename k'0 into l'.
 destruct (IHcl_step (CC.State f Sskip (CC.Kwhile e s2 l') ve te m))
                      as [st2 [? ?]]; clear  IHcl_step.
 repeat constructor; auto.
  exists st2; split; auto.
 eapply star_plus_trans; try apply H2.
 inv H0.
 destruct t1; inv H5. simpl in H0; subst t2.
 eapply plus_star_trans; try apply H4.
 inv H3. 2: inv H11.
 apply SS.plus_one.
 apply CC.step_skip_or_continue_while; auto.
 
 simpl in H2.
 inv H. inv H8.
 destruct (IHcl_step (CC.State f Sskip (CC.Kdowhile e s2 k'0) ve te m'))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. simpl. constructor.
 auto.
 exists st2; split; auto.
 eapply star_plus_trans; [apply H2 | ].
 inv H.
 econstructor; try apply H3.
 instantiate (1:=t1).
clear - H1.
 inv H1.
 eapply CC.step_skip_or_continue_dowhile_false; eauto.
 eapply CC.step_skip_or_continue_dowhile_true; eauto.
 inv H7. auto.

  simpl in H2.
 destruct (IHcl_step (CC.State f s1 (CC.Kfor3 e s1 s2 k'0) ve te m))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. apply match_cont_strip. constructor. auto.
 exists st2; split; auto.
 eapply star_plus_trans; [apply H2 | ].
 eapply star_plus_trans; [ | apply H0].
 apply SS.star_one. constructor. auto.
 
Focus 1.  (* case 2 of 4 *)
 change (CC.Kwhile a s0 k'0 = strip_skip' (CC.Kseq s k')) in H1.
 destruct (dec_skip s); [ | destruct s; try congruence; inv H1].
 subst s.
 simpl in *.
 assert (Smallstep.star CC.step ge (CC.State f Sskip k' ve te m) Events.E0
                   (CC.State f Sskip (CC.Kwhile a s0 k'0) ve te m)).
 rewrite H1; clear.
 induction k'; intros; try solve [constructor 1].
  destruct (dec_skip s). subst. simpl in *. econstructor 2. constructor.
  apply IHk'. auto.
 rewrite strip_skip'_not; auto. constructor 1.
 forget (CC.State f Sskip k' ve te m) as st1.
 clear k' H1.
  destruct (IHcl_step (CC.State f Sskip (CC.Kwhile a s0 k'0) ve te m))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. constructor; auto.
 exists st2; split; auto.
 eapply star_plus_trans; try apply H1.
 apply H0.

Focus 1.  (* case 3 of 4 *)
 change (CC.Kdowhile e s0 k'0 = strip_skip' (CC.Kseq s k')) in H1.
 destruct (dec_skip s); [ | destruct s; try congruence; inv H1].
 subst s.
 simpl in *.
 assert (Smallstep.star CC.step ge (CC.State f Sskip k' ve te m) Events.E0
                   (CC.State f Sskip (CC.Kdowhile e s0 k'0) ve te m)).
 rewrite H1; clear.
 induction k'; intros; try solve [constructor 1].
  destruct (dec_skip s). subst. simpl in *. econstructor 2. constructor.
  apply IHk'. auto.
 rewrite strip_skip'_not; auto. constructor 1.
 forget (CC.State f Sskip k' ve te m) as st1.
 clear k' H1.
  destruct (IHcl_step (CC.State f Sskip (CC.Kdowhile e s0 k'0) ve te m))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. constructor; auto.
 exists st2; split; auto.
 eapply star_plus_trans; try apply H1.
 apply H0.

Focus 1. (* case 4 of 4 *)
   change (CC.Kfor2 e2 e3 s0 k'0 = strip_skip' (CC.Kseq s k')) in H1.
 destruct (dec_skip s); [ | destruct s; try congruence; inv H1].
 subst s.
 simpl in H.
 simpl in H1.
 simpl in *.
 assert (Smallstep.star CC.step ge (CC.State f Sskip k' ve te m) Events.E0
                   (CC.State f Sskip (CC.Kfor2 e2 e3 s0 k'0) ve te m)).
 rewrite H1; clear.
 induction k'; intros; try solve [constructor 1].
  destruct (dec_skip s). subst. simpl in *. econstructor 2. constructor.
  apply IHk'. auto.
 rewrite strip_skip'_not; auto. constructor 1.
 forget (CC.State f Sskip k' ve te m) as st1.
 clear k' H1.
 assert (Smallstep.plus CC.step ge st1 Events.E0
                  (CC.State f e3 (CC.Kfor3 e2 e3 s0 k'0) ve te m)).
 eapply Smallstep.star_plus_trans; try apply H0.
 econstructor. constructor. auto. constructor 1. reflexivity. auto.
 clear H0.
 destruct (IHcl_step (CC.State f e3 (CC.Kfor3 e2 e3 s0 k'0) ve te m)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. apply match_cont_strip; constructor; auto.
 exists st2; split; auto.
 eapply plus_trans; eauto.

 (* step_break *)
 Focus 1.
 inv H0. simpl strip_skip in H6.
 destruct (dec_skip s). subst.  simpl strip_skip' in *.
 assert (exists k1', strip_skip' k' = CC.Kseq Sbreak k1').
 revert H6; clear. remember (strip_skip' k') as k0'. 
 revert k' Heqk0'; induction k0'; intros; try solve [inv H6].
  inv H6. eauto.
 destruct H0 as [k1' H0].
 assert (Smallstep.star CC.step ge (CC.State f Sskip k' ve te m) Events.E0
                           (CC.State f Sbreak k1' ve te m)).
 revert k1' H0; clear; induction k'; intros; try solve [inv H0].
  destruct (dec_skip s). subst.  simpl in *. specialize (IHk' _ H0).
  econstructor 2. constructor. eassumption. auto. 
 rewrite strip_skip'_not in H0 by auto. inv H0.
 econstructor 2. constructor. constructor 1. auto.
 forget (CC.State f Sskip k' ve te m) as st1.
 rewrite H0 in *.
 clear k' H0.
 inv H6.
 rewrite <- break_cont_skip in *.
 simpl in CUR. rewrite <- current_function_strip in CUR. 
 forget (strip_skip k) as k0.
 assert (Smallstep.star CC.step ge st1 Events.E0 (CC.State f Sbreak (strip_skip' k1') ve te m)).
 eapply Smallstep.star_trans; try apply H1; auto.
 2:  instantiate (1:=Events.E0); auto.
 clear.
 induction k1'; try destruct s; try solve [constructor 1].
 simpl. econstructor 2; eauto. constructor. auto.
 forget (strip_skip' k1') as k0'. clear k1' H1.

assert (exists k1',
             Smallstep.plus CC.step ge (CC.State f Sbreak k0' ve te m) Events.E0 
                       (CC.State f Sskip k1' ve te m)
          /\ match_cont (strip_skip (break_cont k0)) (strip_skip' k1')).
 clear - H H2.
 revert H; induction H2; intros; try solve [inv H].
  rewrite break_cont_skip in *. simpl in H.
 destruct (IHmatch_cont H) as [k1' [? ?]]; clear IHmatch_cont. simpl.
 exists k1'; split; auto.
 eapply Smallstep.star_plus_trans; try eassumption.  2:  instantiate (1:=Events.E0); auto.
 econstructor 2. constructor.  2:  instantiate (1:=Events.E0); auto.
 apply break_strip.

 simpl  in *. exists k'; split.
 apply SS.plus_one.
 eapply CC.step_break_while.
 auto.

  rewrite break_cont_skip in *. simpl in H.
 destruct (IHmatch_cont H) as [k1' [? ?]]; clear IHmatch_cont. simpl.
 exists k1'; split; auto.
 eapply Smallstep.star_plus_trans; try eassumption.  2:  instantiate (1:=Events.E0); auto.
 econstructor 2. constructor.  2:  instantiate (1:=Events.E0); auto.
 apply break_strip.

 simpl  in *. exists k'; split.
 apply SS.plus_one.
 eapply CC.step_break_dowhile.
 auto.

 simpl  in *. exists k'; split. econstructor.
 eapply CC.step_break_for2. constructor 1. auto.
 auto.
 simpl in *. exists k'; split. econstructor. eapply CC.step_skip_break_switch. auto.
 constructor 1; auto. auto. auto.

 destruct H1 as [k1' [? ?]].
 destruct (IHcl_step (CC.State f Sskip k1' ve te m))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto.
 clear - H CUR. revert CUR; induction  k0; intros. inv CUR.
  destruct a; simpl in *; auto. inv H. inv H.
 exists st2; split; auto.
 eapply star_plus_trans; try apply H5.
 eapply star_trans; try apply H0.
 apply SS.plus_star; apply H1.  auto.
 rewrite strip_skip'_not in H6 by auto.
 inv H6. clear n.
 admit.  (* probably similar to the previous case *)

 Focus 1.  (* step_ifthenelse *)
 inv H1. simpl strip_skip in H7.
 inv H7. 
 change (CC.Kseq (Sifthenelse a s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H4.
 assert (SS.star CC.step ge (CC.State f s k' ve te m) nil (CC.State f (Sifthenelse a s1 s2) k'0 ve te m)).
 clear - H4.
 revert H4; induction k'; intros; try solve [ destruct s; inv H4; constructor 1].
  destruct (dec_skip s). subst s.
  destruct (dec_skip s0). subst s0. simpl in *.
 eapply SS.star_trans; try apply IHk'; eauto. apply SS.star_one. constructor. auto.
 change (strip_skip' (CC.Kseq Sskip (CC.Kseq s0 k'))) with 
               (strip_skip' (CC.Kseq s0 k')) in H4.
 rewrite strip_skip'_not in H4 by auto.
 inv H4. apply SS.star_one. constructor. rewrite strip_skip'_not in * by auto.
 inv H4. constructor 1.
 exists (CC.State f (if b then s1 else s2) k'0 ve te m); split; auto.
 eapply star_plus_trans; try apply H1. 
 apply SS.plus_one. econstructor; eauto. auto. constructor; auto.
 apply match_cont_strip; auto.

 Focus 1. (* step_while *)
 inv H0.  simpl strip_skip in H6.
 inv H6.
 change (CC.Kseq (Swhile a s) k'0 = strip_skip' (CC.Kseq s0 k')) in H3.
 destruct (IHcl_step (CC.State f (Swhile a s) k'0 ve te m)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 repeat constructor; auto.
 exists st2; split; auto.
 eapply star_plus_trans.
 eapply exec_skips'; eauto.
 auto. 

 Focus 1. (* step_dowhile *)
 inv H0. inv H6.
 change (CC.Kseq (Sdowhile a s) k'0 = strip_skip' (CC.Kseq s0 k')) in H3.
  destruct (IHcl_step (CC.State f s (CC.Kdowhile  a s k'0) ve te m)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. 
 destruct (dec_skip s). subst. simpl.
 repeat constructor; auto.
 rewrite strip_skip'_not by auto.  rewrite strip_skip_not by auto.
  repeat constructor; auto.
 exists st2; split; auto.
 eapply star_plus_trans.
  eapply exec_skips'; eauto.
 econstructor. constructor. apply Smallstep.plus_star. apply H0. auto.

 Focus 1. (* step_for *)
 inv H1. inv H7.
 change (CC.Kseq (Sfor' a2 a3 s) k'0 = strip_skip' (CC.Kseq s0 k')) in H4.
  generalize (exec_skips' ge f _ _ _ _ ve te m (@eq_sym _ _ _ H4)); intro.
 destruct b.
 econstructor; split.
 eapply star_plus_trans; try apply H1.
 apply SS.plus_one. eapply CC.step_for_true; eauto.
 constructor; auto. apply match_cont_strip; constructor; auto.
 econstructor; split.
 eapply star_plus_trans; try apply H1.
 apply SS.plus_one. eapply CC.step_for_false; eauto.
 constructor; auto.

  change (CC.Kseq (Swhile a2 s) k'0 = strip_skip' (CC.Kseq s0 k')) in H6.
  generalize (exec_skips' ge f _ _ _ _ ve te m (@eq_sym _ _ _ H6)); intro.
 destruct b.
 exists (CC.State f s (CC.Kwhile a2 s k'0) ve te m); split; auto.
 eapply star_plus_trans; try eassumption.
 apply SS.plus_one. eapply CC.step_while_true; eauto.
 constructor; auto; apply match_cont_strip; simpl; apply match_cont_while''; auto.
 exists (CC.State f Sskip k'0 ve te m); split; auto.
 eapply star_plus_trans; try eassumption.
 apply SS.plus_one. eapply CC.step_while_false; eauto.
 constructor; auto.

 Focus 1. (* step_for3 *)
  inv H1. inv H7.
 destruct s0; inv H6.
 generalize (strip_skip'_while ge f ve te m _ _ _ _ H3); intro.
 exists (if b then (CC.State f s (CC.Kwhile a2 s k'0) ve te m)
                   else (CC.State f Sskip k'0 ve te m)); split.
 eapply star_plus_trans; try apply H1.
 destruct b.
 econstructor.  eapply CC.step_skip_or_continue_while; eauto.
 apply SS.star_one. eapply CC.step_while_true; eauto. auto.
  econstructor.  eapply CC.step_skip_or_continue_while; eauto.
 apply SS.star_one. eapply CC.step_while_false; eauto. auto.
 destruct b. constructor; auto. apply match_cont_strip. constructor. auto.
 constructor; auto. simpl. auto.

 destruct s0; inv H6.
 generalize (strip_skip'_dowhile ge f ve te m _ _ _ _ H3); intro.
 exists (if b then (CC.State f s (CC.Kdowhile a2 s k'0) ve te m)
                   else (CC.State f Sskip k'0 ve te m)); split.
 eapply star_plus_trans; try apply H1.
 destruct b.
 econstructor.  eapply CC.step_skip_or_continue_dowhile_true; eauto.
 apply SS.star_one. eapply CC.step_dowhile; eauto. auto.
 apply SS.plus_one.  eapply CC.step_skip_or_continue_dowhile_false; eauto.
 destruct b. constructor; auto. apply match_cont_strip. constructor. auto.
 constructor; auto. simpl. auto.

 destruct s0; inv H6.
 generalize (strip_skip'_for3 ge f ve te m _ _ _ _ _ H3); intro.
 exists (if b then (CC.State f s (CC.Kfor2 a2 a3 s k'0) ve te m)
                   else (CC.State f Sskip k'0 ve te m)); split.
 eapply star_plus_trans; try apply H1.
 destruct b.
 econstructor.  eapply CC.step_skip_for3; eauto.
 apply SS.star_one. eapply CC.step_for_true; eauto. auto.
 econstructor.  eapply CC.step_skip_for3; eauto.
 apply SS.star_one. eapply CC.step_for_false; eauto. auto.
 destruct b. constructor; auto. apply match_cont_strip. constructor. auto.
 constructor; auto. simpl. auto.

 Focus 1. (* step_return *)
 inv H3.
  remember (strip_skip' (CC.Kseq s k'0)) as k3. simpl in CUR, H9.
 inv H9.
 generalize (exec_skips' ge f0 _ _ _ _ ve te m (@eq_sym _ _ _ H4)); intro H99.
 assert (f0=f).
 simpl in CUR; clear - CUR H.
 revert H CUR; induction k; intros. inv H. simpl in *. destruct a; auto. inv CUR; auto. inv H; auto.
 subst f.
 generalize (match_cont_call_strip k k'1); intro.
 spec H3; [congruence |]. spec H3; [auto |].
 generalize H3; rewrite H; intro. inv H5.
 elimtype False; clear - H10.
 revert H10; induction k'1; simpl; intros; congruence.
 destruct optexp;  [destruct H1 as [v [? ?]] | ]; (destruct optid; destruct H2 as [H2 H2']; 
   try solve [contradiction H2; auto]; subst te'' );
 try (econstructor; split; [eapply star_plus_trans; [ apply H99  | eapply SS.plus_two ] | ]).
 econstructor; eauto. rewrite <- H13.
 eapply CC.step_returnstate_some. auto. constructor; auto.
 econstructor; eauto. rewrite <- H13.
 eapply CC.step_returnstate_none. auto.
 econstructor; eauto.
 econstructor; eauto. rewrite <- H13.  eapply CC.step_returnstate_none. auto. 
 subst; econstructor; auto.
 destruct optid. destruct H2. congruence.
 destruct H2; subst te''.
 simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR.
 destruct s; inv H4.
 assert (SS.star CC.step ge (CC.State f Sskip k'0 ve te m) nil
                         (CC.State f Sskip (CC.Kcall None f1 ve' te' k'1) ve te m)).
 clear H1; rename H3 into H1.
 clear - H1. revert H1; induction k'0; intros; try solve [inv H1].
 destruct (dec_skip s). subst s. simpl in H1. 
 eapply star_trans; try apply IHk'0; auto. apply SS.star_one. constructor; auto.
 rewrite strip_skip'_not in H1 by auto. rewrite <- H1. constructor 1.
 simpl in H1. inv H1. constructor 1.
 (econstructor; split; [eapply star_plus_trans; [ apply H  | eapply SS.plus_two ] | ]).
 eapply CC.step_skip_call; simpl; eauto.
 econstructor; eauto. auto.
 econstructor; eauto.
 
 Focus 1. (* step_switch *)
 inv H0. simpl strip_skip in H6.
 remember (CC.Kseq s k') as k0'.
 inv H6.
 evar (s2: CC.state).
 exists s2; split.
 Focus 2.
 constructor; eauto. apply match_cont_strip. simpl.
 instantiate (1:= CC.Kswitch k'0). constructor. auto.
 generalize (exec_skips' ge f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
 eapply star_plus_trans; try apply H99.
 unfold s2. apply SS.plus_one. constructor; auto.

 Focus 1. (* step_label *)
 inv H0.  remember (CC.Kseq s0 k') as k0'. inv H6.
 destruct (IHcl_step (CC.State f s k'0 ve te m)) as [st2 [? ?]]; clear IHcl_step.
 constructor; auto. apply match_cont_strip. auto.
 exists st2; split; auto.
 eapply star_plus_trans; try eassumption.
  generalize (exec_skips' ge f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
 eapply star_trans; try apply H99.
 apply SS.star_one. constructor.
 
 Focus 1. (* step_goto *)
 inv H0. remember (CC.Kseq s k'0) as k0'. inv H6.
  generalize (match_cont_call_strip k k'1); intro.
 spec H0.
 clear - CUR. admit. (* easy *)
 specialize (H0 H1).
  rewrite <- strip_call' in H0.
 change (Kseq (Sreturn None) :: call_cont k) with (strip_skip (Kseq (Sreturn None) :: call_cont k)) in H0.
 destruct (match_find_label _ _ _ _ _ H0 H) as [s2 [k2' [? ?]]].
 exists (CC.State f s2 k2' ve te m); split.
 simpl in CUR0. inversion2 CUR CUR0.
 generalize (exec_skips' ge f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
 eapply star_plus_trans; try apply H99.
 apply SS.plus_one. constructor; auto.
 constructor; auto.
 clear - CUR H. forget (fn_body f) as s.
 rewrite <- current_function_call_cont in CUR.
 change (current_function (Kseq (Sreturn None) :: call_cont k) = Some f) in CUR.
 forget (Kseq (Sreturn None) :: call_cont k) as k0. clear - CUR H.
 eapply current_function_find_label; eauto.
 apply match_cont_strip1. auto.
Qed.
