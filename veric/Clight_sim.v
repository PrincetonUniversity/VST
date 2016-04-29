Require Import sepcomp.mem_lemmas.
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.simulations.
Require Import sepcomp.simulations_lemmas.
(*Require Import sepcomp.compiler_correctness.*)

Require Import veric.base.
Require Import veric.Clight_lemmas.
Require Import veric.Clight_new.
Require compcert.cfrontend.Clight.
Module CC := Clight.

Definition CCstep ge := Clight.step ge (Clight.function_entry2 ge).

Lemma cc_step_fun: forall ge s1 s2 s2',
   CCstep ge s1 nil s2 -> CCstep ge s1 nil s2' -> s2=s2'.
Proof.
 intros.
 inv H; inv H0;
 repeat match goal with
  | H: _ \/ _  |- _ => destruct H; try discriminate
  end;
 try contradiction;
  repeat fun_tac; auto; try congruence.
  inversion2 H5 H18; fun_tac; congruence.
  destruct (Events.external_call_determ _ _ _ _ _ _ _ _ _ _ H14 H2)
    as [? [? ?]]; subst; auto.
  inv H1; inv H6.
  inversion2 H9 H4.
  pose proof (alloc_variables_fun H8 H3). inv H4.
  auto.
  destruct (Events.external_call_determ _ _ _ _ _ _ _ _ _ _ H10 H1).
  destruct H0; subst; auto.
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
         (CUR: current_function k = Some f),
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq (Sreturn None) :: Kcall lid fd ve te :: k) (CC.Kcall lid f ve te k').

(*LENB: NOT NEEDED UNTIL MUCH LATER (SEE BELOW), AND THEN ONLY FOR CORES NOT STATES
Inductive match_states: forall (qm: corestate * mem) (st: CC.state), Prop :=
 | match_states_seq: forall f ve te s k k' m
      (CUR: current_function k = Some f),
      match_cont (strip_skip k) (strip_skip' (CC.Kseq s k')) ->
      match_states (State ve te k, m) (CC.State f s k' ve te m)
 | match_states_ext: forall k f ef tyargs tyres args lid ve te m k'
      (CUR: current_function k = Some f),
      match_cont (strip_skip k) (strip_skip' k') ->
      match_states (ExtCall ef (signature_of_type tyargs tyres) args lid ve te k, m) 
           (CC.Callstate (External ef tyargs tyres) args (CC.Kcall lid f ve te k') m).*)

Lemma exec_skips:
 forall {s0 k s k'} 
   (H1: match_cont (Kseq s0 :: k) (strip_skip' (CC.Kseq s k')))
   ge f ve te m,
   match s0 with Sskip => False | Scontinue => False | Sloop _ _ => False 
            | Sifthenelse _ _ _ => False | Sreturn _ => False 
            | _ => True end ->
   exists k2, strip_skip' (CC.Kseq s k') = CC.Kseq s0 k2 /\
     Smallstep.star CCstep ge (CC.State f s k' ve te m) Events.E0 
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

Inductive step' ge : (corestate * mem) -> Events.trace -> (corestate * mem) -> Prop :=
 mk_step': forall q m q' m', cl_step ge q m q' m' -> step' ge (q,m) Events.E0 (q',m').

(*Module SS := compcert.Smallstep.*)
Definition ef_exit := EF_external "__exit" (mksignature nil None cc_default).

Inductive initial_state (p: program): (corestate * mem) -> Prop :=
(*
  | initial_state_intro: forall b (f: fundef) m0 ve te,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s ->
      initial_state p (State ve te (Kfun f nil None  :: Kfun (EXternal ef_exit Tnil Tvoid) nil None :: nil), m0).
*)
  .  (* fixme *)

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: (corestate * mem) -> int -> Prop :=
(*
  | final_state_intro: forall r ve te m,
      final_state (State ve te 
                          (Kfun (EXternal ef_exit Tnil Tvoid) nil None :: nil), m) r
*)
 . (* fixme *)

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
        Smallstep.star CCstep ge (CC.State f s k' ve te m) Events.E0
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
     Smallstep.star CCstep ge (CC.State f Sbreak k ve te m) nil (CC.State f Sbreak (strip_skip' k) ve te m).
 Proof. induction k; try solve [constructor 1].
    destruct (dec_skip s). subst. simpl. 
     econstructor 2. constructor. eauto. auto.
  rewrite strip_skip'_not; auto. constructor 1.
Qed.

Lemma plus_trans: forall ge s1 s2 s3, 
   Smallstep.plus CCstep ge s1 Events.E0 s2 -> Smallstep.plus CCstep ge s2 Events.E0 s3 -> Smallstep.plus CCstep ge s1 Events.E0 s3.
Proof.
 intros. eapply Smallstep.plus_trans; eauto.
Qed.

Lemma star_plus_trans: forall ge s1 s2 s3, 
   Smallstep.star CCstep ge s1 Events.E0 s2 -> Smallstep.plus CCstep ge s2 Events.E0 s3 -> Smallstep.plus CCstep ge s1 Events.E0 s3.
Proof.
 intros. eapply Smallstep.star_plus_trans; eauto.
Qed. 

Lemma plus_star_trans: forall ge s1 s2 s3, 
   Smallstep.plus CCstep ge s1 Events.E0 s2 -> Smallstep.star CCstep ge s2 Events.E0 s3 -> Smallstep.plus CCstep ge s1 Events.E0 s3.
Proof.
 intros. eapply Smallstep.plus_star_trans; eauto.
Qed.

Lemma star_trans: forall ge s1 s2 s3, 
   Smallstep.star CCstep ge s1 Events.E0 s2 -> Smallstep.star CCstep ge s2 Events.E0 s3 -> Smallstep.star CCstep ge s1 Events.E0 s3.
Proof.
 intros. eapply Smallstep.star_trans; eauto.
Qed.

Lemma strip_skip'_loop2:
  forall ge f ve te m a3 s k1 k, CC.Kloop2 a3 s k1 = strip_skip' k ->
  Smallstep.star CCstep ge (CC.State f Sskip k ve te m) Events.E0 (CC.State f Sskip (CC.Kloop2 a3 s k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. eapply Smallstep.star_trans; try apply IHk; auto. apply Smallstep.star_one. constructor. auto.
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
  forall ge f ve te m a3 s k1 k, CC.Kloop1 a3 s k1 = strip_skip' k ->
  Smallstep.star CCstep ge (CC.State f Sskip k ve te m) Events.E0 (CC.State f Sskip (CC.Kloop1 a3 s k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. eapply Smallstep.star_trans; try apply IHk; auto. apply Smallstep.star_one. constructor. auto.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. constructor 1. simpl in H. inv H. constructor 1.
Qed.


Lemma strip_skip'_call:
  forall ge f ve te m lid f' ve' te' k1 k, CC.Kcall lid f' ve' te' k1 = strip_skip' k ->
  Smallstep.star CCstep ge (CC.State f Sskip k ve te m) Events.E0 (CC.State f Sskip (CC.Kcall lid f' ve' te' k1) ve te m).
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s). subst. eapply Smallstep.star_trans; try apply IHk; auto. apply Smallstep.star_one. constructor. auto.
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
  forall ge f k ve te m, 
           Smallstep.star CCstep ge (CC.State f Scontinue k ve te m) Events.E0
               (CC.State f Scontinue (strip_skip' k) ve te m).
Proof.
intros.
induction k; simpl; try constructor 1.
destruct (dec_skip s).
subst.
eapply Smallstep.star_trans.
  apply Smallstep.star_one. apply CC.step_continue_seq.
  apply IHk.
auto.
destruct s; try congruence; constructor 1.
Qed.

(*Similar constructors as CC.State, but without all the mem's*)
Inductive CC_core : Type :=
    CC_core_State : function ->
            statement -> CC.cont -> env -> temp_env -> CC_core
  | CC_core_Callstate : fundef -> list val -> CC.cont -> CC_core
  | CC_core_Returnstate : val -> CC.cont -> CC_core.

Definition CC_core_to_CC_state (c:CC_core) (m:mem) : CC.state :=
  match c with
     CC_core_State f st k e te => CC.State f st k e te m
  |  CC_core_Callstate fd args k => CC.Callstate fd args k m
  | CC_core_Returnstate v k => CC.Returnstate v k m
 end. 
Definition CC_state_to_CC_core (c:CC.state): CC_core * mem :=
  match c with
     CC.State f st k e te m => (CC_core_State f st k e te, m)
  |  CC.Callstate fd args k m => (CC_core_Callstate fd args k, m)
  | CC.Returnstate v k m => (CC_core_Returnstate v k, m)
 end.

Lemma  CC_core_CC_state_1: forall c m, 
   CC_state_to_CC_core  (CC_core_to_CC_state c m) = (c,m).
  Proof. intros. destruct c; auto. Qed.

Lemma  CC_core_CC_state_2: forall s c m, 
   CC_state_to_CC_core  s = (c,m) -> s= CC_core_to_CC_state c m.
  Proof. intros. destruct s; simpl in *.
      destruct c; simpl in *; inv H; trivial. 
      destruct c; simpl in *; inv H; trivial. 
      destruct c; simpl in *; inv H; trivial. 
  Qed.

Lemma  CC_core_CC_state_3: forall s c m, 
   s= CC_core_to_CC_state c m -> CC_state_to_CC_core  s = (c,m).
  Proof. intros. subst. apply CC_core_CC_state_1. Qed.  

Lemma  CC_core_CC_state_4: forall s, exists c, exists m, s =  CC_core_to_CC_state c m.
  Proof. intros. destruct s. 
             exists (CC_core_State f s k e le). exists m; reflexivity.
             exists (CC_core_Callstate fd args k). exists m; reflexivity.
             exists (CC_core_Returnstate res k). exists m; reflexivity.
  Qed.

Lemma CC_core_to_CC_state_inj: forall c m c' m',
     CC_core_to_CC_state c m = CC_core_to_CC_state c' m' -> (c',m')=(c,m).
  Proof. intros. 
       apply  CC_core_CC_state_3 in H. rewrite  CC_core_CC_state_1 in H.  inv H. trivial.
  Qed.

(*HERE'S THE ADAPTATION OF THE EARLER MATCH_STATE_RLEATION, COMMENTED OUT ABOVE*)
Inductive match_states: forall (qm: corestate) (st: CC_core), Prop :=
 | match_states_seq: forall f ve te s k k' 
      (CUR: current_function k = Some f),
      match_cont (strip_skip k) (strip_skip' (CC.Kseq s k')) ->
      match_states (State ve te k) (CC_core_State f s k' ve te)
 | match_states_ext: forall k f ef tyargs tyres args lid ve te k'
      (CUR: current_function k = Some f),
      match_cont (strip_skip k) (strip_skip' k') ->
      match_states (ExtCall ef (signature_of_type tyargs tyres cc_default) args lid ve te k) 
           (CC_core_Callstate (External ef tyargs tyres cc_default) args (CC.Kcall lid f ve te k')).

Lemma Clightnew_Clight_sim_eq_noOrder_SSplusConclusion:
forall (cenv: composite_env) 
     p (c1 : corestate) (m : mem) (c1' : corestate) (m' : mem),
corestep cl_core_sem (Build_genv (Genv.globalenv p) cenv) c1 m c1' m' ->
forall (c2 : CC_core),
 match_states c1 c2 ->
exists c2' : CC_core,
    Smallstep.plus CCstep (Build_genv (Genv.globalenv p) cenv) (CC_core_to_CC_state c2 m) Events.E0 (CC_core_to_CC_state c2' m') /\
    match_states c1' c2'.
Proof.
intros.
forget (Genv.globalenv p) as ge. clear p.
simpl in H.
(* inv H.
rename H1 into H.*)
revert c2 H0. induction H; intros.

Focus 1. (* step_assign *)
inv H4.
simpl strip_skip in H9. 
destruct (exec_skips H9 (Build_genv ge cenv) f ve te m) as [k2 [? ?]]; simpl; auto.
exists (CC_core_State f Sskip k2 ve te); split. 
    eapply Smallstep.star_plus_trans. eassumption.
          apply Smallstep.plus_one. econstructor; eauto. reflexivity.
    constructor. apply CUR.  rewrite  H4 in H9.  inv H9.  simpl in *. apply H7.

Focus 1. (* step_set *)
inv H0.
destruct (exec_skips H5 (Build_genv ge cenv) f ve te m) as [k2 [? ?]]; simpl; auto.
exists (CC_core_State f Sskip k2 ve (PTree.set id v te)); split. 
  eapply Smallstep.star_plus_trans. eassumption. apply Smallstep.plus_one. econstructor; eauto. auto.
  rewrite H0 in H5. inv H5; constructor; auto.

Focus 1. (* step_call_internal *)
inv H7. 
 destruct (exec_skips H12 (Build_genv ge cenv) f0 ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H7 in *. inv H12. simpl in CUR.
  (* econstructor; split. -- introduction of CC_core destroys potential for automation/econstructor
         here - need to instanitate manually.*)
  exists (CC_core_State f (fn_body f) (CC.Kcall optid f0 ve te k2) ve' le').
  split.
  (*a*) eapply star_plus_trans. apply H8. 
               eapply Smallstep.plus_two. econstructor; eauto. 
              econstructor; eauto. 
               apply list_norepet_app in H4. destruct H4 as [? [? ?]].
               econstructor; auto. reflexivity.
  (*b*) constructor.
              auto.
             apply match_cont_strip. simpl. constructor; auto.

Focus 1. (* step_call_external *)
inv H3. 
 destruct (exec_skips H8 (Build_genv ge cenv) f ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H3 in *. inv H8. simpl in CUR. 
 (*econstructor; split.  -- again, we need to instantiate manually*)
  exists (CC_core_Callstate (External ef tyargs tyres cc_default) vargs (CC.Kcall optid f ve te k2)).
  split.
   (*a*) eapply star_plus_trans. eassumption. eapply Smallstep.plus_one. econstructor; eauto.
   (*b*) econstructor; eauto.

Focus 1. (* step_seq *)
 inv H0.
 destruct (exec_skips H5 (Build_genv ge cenv) f ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H0 in *. inv H5.
 destruct (IHcl_step (CC_core_State f s1 (CC.Kseq s2 k2) ve te))
                as [st2 [? ?]]; clear  IHcl_step.
 repeat constructor; auto.
 apply match_cont_strip.  apply match_cont_strip.  auto.
 exists st2; split; auto.
 eapply star_plus_trans; [ eassumption | ].
 eapply plus_trans. apply Smallstep.plus_one. constructor. eassumption.

 Focus 1. (* step_skip *)
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
 assert (s0<>Sskip).
 clear- Heqk0; intro; subst.
 revert Heqk0; induction k; simpl; intros. inv Heqk0. destruct a; try solve [inv Heqk0]; auto. destruct s; inv Heqk0; auto.
 destruct (IHcl_step (CC_core_State f s k' ve te)) 
                 as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. rewrite <- Heqk0'.
 constructor 2; auto.
 exists st2; split; auto.

  destruct (IHcl_step (CC_core_State f Sskip (CC.Kloop1 s0 s1 k0') ve te)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. simpl. rewrite <- Heqk0. constructor. auto.
  exists st2; split; auto.
 inv H0. destruct t1; inv H5. simpl in H0. subst t2.
 eapply plus_star_trans; try apply H4.
 clear - H3 Heqk0'.
 destruct s; inv Heqk0'.
 rewrite H0 in H3.
 eapply star_plus_trans; [ | apply Smallstep.plus_one; eauto ].
 rewrite <- H0;
 apply strip_skip'_loop1; auto.

 destruct (IHcl_step (CC_core_State f Sskip (CC.Kloop2 s0 s1 k0') ve te)) 
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
 replace (CC.Kloop2 s0 s1 k0') with (CC.Kseq s k') by  (destruct s; auto; congruence).
 constructor 1.
 constructor 1.

 destruct s; inv Heqk0'.
 destruct (IHcl_step (CC_core_State f Sskip (CC.Kcall o f0 e t k0') ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. constructor; auto.
  exists st2; split; auto.
  inv H0. destruct t1; inv H6. simpl in H0; subst t2.
 eapply plus_star_trans; [ | apply H5].
 inv H4.
 eapply star_plus_trans; [eapply strip_skip'_call; eauto | ].
 apply Smallstep.plus_one. constructor; auto.

 Focus 1. (* step_continue *)
 inv H0.
 simpl strip_skip in H5.
 inv H5.
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

 assert (Smallstep.star CCstep (Build_genv ge cenv) (CC.State f s k' ve te m) Events.E0 
                             (CC.State f Scontinue k'0 ve te m)).
 clear - H3.
 destruct (dec_skip s). subst. simpl in H3.
 eapply exec_skips'; auto.
 rewrite strip_skip'_not in H3 by auto. inv H3. constructor.
 assert (Smallstep.star CCstep (Build_genv ge cenv) (CC.State f Scontinue k'0 ve te m) Events.E0
                                 (CC.State f Scontinue (strip_skip' k'0) ve te m)).
clear.
  induction k'0; try solve [constructor 1].
 destruct (dec_skip s). subst.  simpl in *. econstructor 2. constructor. eassumption. auto.
  rewrite strip_skip'_not; auto. constructor 1.
 generalize (Smallstep.star_trans H2 H4 (eq_refl _)); clear H2 H4; intro.
 clear H3.
 forget (strip_skip' k'0) as k0'; clear k'0.
 assert (precontinue_cont k = Kloop1 s1 s2 :: l).
 revert H0; clear; induction k; simpl; try congruence.  destruct a; try congruence; auto.
 assert (exists k1', 
               Smallstep.star CCstep (Build_genv ge cenv) (CC.State f Scontinue k0' ve te m)
                  (Events.Eapp Events.E0 Events.E0)
                    (CC.State f Scontinue k1' ve te m) /\
               match_cont (Kseq Scontinue :: Kloop1 s1 s2 :: l) k1').
 clear - H1 H0.
 revert H0; induction H1; simpl; intros; try congruence.
 destruct IHmatch_cont as [k1' [? ?]].
 rewrite <- continue_cont_skip; auto.
 econstructor. split; [ | eassumption].
 eapply star_trans; try apply H.
 clear.
 eapply star_trans. apply Smallstep.star_one.
 apply CC.step_continue_seq.
 apply step_continue_strip.
 inv H0.
 econstructor; split. constructor 1.  constructor.  auto.
 destruct IHmatch_cont as [k1' [? ?]].
 rewrite <- continue_cont_skip; auto.
 econstructor. split; [ | eassumption].
 eapply star_trans; try apply H.
 eapply star_trans. apply Smallstep.star_one.
 apply CC.step_continue_switch.
 apply step_continue_strip.

 destruct H4 as [k1' [? ?]].
 generalize (Smallstep.star_trans H2 H4 (eq_refl _)); clear H2 H4; intro H2.
 rewrite H0 in *.
 assert (CUR': current_function l = Some f).
   clear - CUR H0. revert CUR H0; induction k; simpl; intros. inv CUR.
   destruct a; try discriminate; auto. inv H0. auto.
 clear H1 CUR k H0 H3.
 inv H5. inv H4. simpl in *.
 destruct (IHcl_step (CC_core_State f s2 (CC.Kloop2 s1 s2 k'0) ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. apply match_cont_strip. constructor. auto.
 exists st2; split; auto.
 eapply star_plus_trans; [apply H2 | ].
 eapply star_plus_trans; [ | apply H0].
 apply Smallstep.star_one. constructor. auto.
 
Focus 1. (* case x of y *)
   change (CC.Kloop1 s0 e3 k'0 = strip_skip' (CC.Kseq s k')) in H1.
 destruct (dec_skip s); [ | destruct s; try congruence; inv H1].
 subst s.
 simpl in H.
 simpl in H1.
 simpl in *.
 assert (Smallstep.star CCstep (Build_genv ge cenv) (CC.State f Sskip k' ve te m) Events.E0
                   (CC.State f Sskip (CC.Kloop1 s0 e3 k'0) ve te m)).
 rewrite H1; clear.
 induction k'; intros; try solve [constructor 1].
  destruct (dec_skip s). subst. simpl in *. econstructor 2. constructor.
  apply IHk'. auto.
 rewrite strip_skip'_not; auto. constructor 1.
 forget (CC.State f Sskip k' ve te m) as st1.
 clear k' H1.
 assert (Smallstep.plus CCstep (Build_genv ge cenv) st1 Events.E0
                  (CC.State f e3 (CC.Kloop2 s0 e3 k'0) ve te m)).
 eapply Smallstep.star_plus_trans; try apply H0.
 econstructor. constructor. auto. constructor 1. reflexivity. auto.
 clear H0.
 destruct (IHcl_step (CC_core_State f e3 (CC.Kloop2  s0 e3 k'0) ve te)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. apply match_cont_strip; constructor; auto.
 exists st2; split; auto.
 eapply plus_trans; eauto.

 (* step_break *)
 Focus 1.
 inv H0. simpl strip_skip in H5.
 destruct (dec_skip s).
 (*s=skip*)
 subst.  simpl strip_skip' in *.
 assert (exists k1', strip_skip' k' = CC.Kseq Sbreak k1').
     revert H5; clear. remember (strip_skip' k') as k0'.   
     revert k' Heqk0'; induction k0'; intros; try solve [inv H5].
        inv H5. eauto.
 destruct H0 as [k1' H0].
 assert (Smallstep.star CCstep (Build_genv ge cenv) (CC.State f Sskip k' ve te m) Events.E0
                           (CC.State f Sbreak k1' ve te m)).
       revert k1' H0; clear; induction k'; intros; try solve [inv H0].
        destruct (dec_skip s). subst.  simpl in *. specialize (IHk' _ H0).
            econstructor 2. constructor. eassumption. auto. 
      rewrite strip_skip'_not in H0 by auto. inv H0.
         econstructor 2. constructor. constructor 1. auto.
 simpl.
 forget (CC.State f Sskip k' ve te m) as st1.
 rewrite H0 in *.
 clear k' H0.
 inv H5.
 rewrite <- break_cont_skip in *.
 simpl in CUR. rewrite <- current_function_strip in CUR. 
 forget (strip_skip k) as k0.
 assert (Smallstep.star CCstep (Build_genv ge cenv) st1 Events.E0 (CC.State f Sbreak (strip_skip' k1') ve te m)).
      eapply Smallstep.star_trans; try apply H1; auto.
      2:  instantiate (1:=Events.E0); auto.
      clear.
      induction k1'; try destruct s; try solve [constructor 1].
         simpl. econstructor 2; eauto. constructor. auto.
 forget (strip_skip' k1') as k0'. clear k1' H1.
 assert (X:exists k1',
             Smallstep.plus CCstep (Build_genv ge cenv) (CC.State f Sbreak k0' ve te m) Events.E0 
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

            simpl  in *. exists k'; split. econstructor.
                 eapply CC.step_break_loop1. constructor 1. auto.
                 auto.

            simpl in *. exists k'; split.
                  econstructor. eapply CC.step_skip_break_switch. auto.
                  constructor 1; auto.
                  auto.
                  auto.

 destruct X as [k1' [? ?]].
 destruct (IHcl_step (CC_core_State f Sskip k1' ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
       constructor; auto.
       clear - H CUR.
       revert CUR; induction  k0; intros. inv CUR.
       destruct a; simpl in *; auto. inv H. inv H.
 exists st2; split; auto.
 eapply star_plus_trans; try apply H5.
      eapply star_trans; try apply H0.
      apply Smallstep.plus_star; apply H1.
      auto.

(*s<>skip*)
 rewrite strip_skip'_not in H5 by auto.
 inv H5. clear n.
 
 admit. (*probably similar to the previous case -- means similar so s=skip*)

 Focus 1.  (* step_ifthenelse *)
 inv H1. simpl strip_skip in H6.
 inv H6. 
 change (CC.Kseq (Sifthenelse a s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H4.
 assert (Smallstep.star CCstep (Build_genv ge cenv) (CC.State f s k' ve te m) nil (CC.State f (Sifthenelse a s1 s2) k'0 ve te m)).
     clear - H4.
     revert H4; induction k'; intros; try solve [ destruct s; inv H4; constructor 1].
     destruct (dec_skip s). subst s.
     destruct (dec_skip s0). subst s0. simpl in *.
     eapply Smallstep.star_trans; try apply IHk'; eauto. apply Smallstep.star_one. constructor. auto.
      change (strip_skip' (CC.Kseq Sskip (CC.Kseq s0 k'))) with 
               (strip_skip' (CC.Kseq s0 k')) in H4.
      rewrite strip_skip'_not in H4 by auto.
      inv H4. apply Smallstep.star_one. constructor. rewrite strip_skip'_not in * by auto.
      inv H4. constructor 1.
 exists (CC_core_State f (if b then s1 else s2) k'0 ve te); split; auto.
 eapply star_plus_trans; try apply H1. 
 apply Smallstep.plus_one. econstructor; eauto. auto. constructor; auto.
 apply match_cont_strip; auto.

 Focus 1. (* step_loop *)
 inv H0. inv H4.
 change (CC.Kseq (Sloop s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H2.
 generalize (exec_skips' (Build_genv ge cenv) f _ _ _ _ ve te m (@eq_sym _ _ _ H2)); intro.
 exists ( (CC_core_State f s1 (CC.Kloop1 s1 s2 k'0) ve te)); split.
 eapply star_plus_trans; try apply H.
 apply Smallstep.plus_one. eapply CC.step_loop; eauto.
 constructor; auto. apply match_cont_strip; constructor; auto.

 Focus 1. (* step_loop2 *) {
  inv H0. inv H4.
 destruct s0; inv H3.
 generalize (strip_skip'_loop2 (Build_genv ge cenv) f ve te m _ _ _ _ H1); intro.
 exists (CC_core_State f s (CC.Kloop1 s a3 k'0) ve te); split.
 * eapply star_plus_trans; try apply H.
               econstructor.
                            eapply CC.step_skip_loop2; eauto.
                            apply Smallstep.star_one. eapply CC.step_loop; eauto.
                            auto.
 * constructor; auto. apply match_cont_strip. constructor. auto.
} Unfocus.

 Focus 1. (* step_return *) {
 inv H3.
  remember (strip_skip' (CC.Kseq s k'0)) as k3. simpl in CUR, H8.
 inv H8.
 * (*first case*)
 generalize (exec_skips' (Build_genv ge cenv) f0 _ _ _ _ ve te m (@eq_sym _ _ _ H4)); intro H99.
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
    -   eexists (CC_core_State f Sskip k'2 ve' (PTree.set i v' te')).
                split. 
                     apply (star_plus_trans _ _ _ _ H99). (*with (s2:=CC.State f0 (Sreturn (Some e)) k'1 ve te m).  apply H99. *)
                     eapply plus_trans with (s2:=CC.Returnstate v' (CC.call_cont k'1) m').
                                         eapply Smallstep.plus_one. simpl. econstructor; eauto.
                                         eapply Smallstep.plus_one. simpl. rewrite <- H13. 
                                         eapply CC.step_returnstate.
                    constructor; auto.
    -   eexists (CC_core_State f Sskip k'2 ve' te').
                split. 
                     eapply (star_plus_trans _ _ _ _ H99). (* with (s2:=CC.State f0 (Sreturn (Some e)) k'1 ve te m). apply H99. *)
                          eapply plus_trans with (s2:=CC.Returnstate v' (CC.call_cont k'1) m').
                                         eapply Smallstep.plus_one. simpl. econstructor; eauto.
                                         eapply Smallstep.plus_one. simpl. rewrite <- H13. eapply CC.step_returnstate.
                    constructor; auto.
    -   eexists (CC_core_State f Sskip k'2 ve' (CC.set_opttemp (Some i) Vundef te')).
                split.
                     eapply (star_plus_trans _ _ _ _ H99).  (*with (s2:=CC.State f0 (Sreturn None) k'1 ve te m).  apply H99. *)
                          eapply plus_trans with (s2:=CC.Returnstate Vundef (CC.call_cont k'1) m').
                                         eapply Smallstep.plus_one. simpl. econstructor; eauto.
                                         eapply Smallstep.plus_one. simpl. rewrite <- H13.
                apply CC.step_returnstate. subst.
                 simpl. constructor 1. auto. simpl.  auto.
   - eexists (CC_core_State f Sskip k'2 ve' te').
                split.
                     eapply (star_plus_trans _ _ _ _ H99).  
                          eapply plus_trans with (s2:=CC.Returnstate Vundef (CC.call_cont k'1) m').
                                         eapply Smallstep.plus_one. simpl. econstructor; eauto.
                                         eapply Smallstep.plus_one. simpl. rewrite <- H13.
                apply CC.step_returnstate. subst.
                 simpl. constructor 1. auto. simpl.  auto.
 * (*second case*)
 destruct optid; destruct H2 as [_ H2]; subst te''.
  + simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR.
    destruct s; inv H4.
    assert (Smallstep.star CCstep (Build_genv ge cenv) (CC.State f Sskip k'0 ve te m) nil
                         (CC.State f Sskip (CC.Kcall (Some i) f1 ve' te' k'1) ve te m)).
     clear - H1.
     revert H1; induction k'0; intros; try solve [inv H1].
           destruct (dec_skip s). subst s. simpl in H1. 
               eapply star_trans; try apply IHk'0; auto. apply Smallstep.star_one. constructor; auto.
          rewrite strip_skip'_not in H1 by auto. rewrite <- H1. constructor 1.
          simpl in H1. inv H1. constructor 1.
 (econstructor; split; [eapply star_plus_trans; [ apply H  | eapply Smallstep.plus_two ] | ]).
     eapply CC.step_skip_call; simpl; eauto.
     assert (X: CCstep (Build_genv ge cenv) (CC.Returnstate Vundef (CC.Kcall (Some i) f1 ve' te' k'1) m') 
                                      Events.E0
                                     (CC_core_to_CC_state (CC_core_State f1 Sskip k'1 ve'  (CC.set_opttemp (Some i) Vundef te')) m')).
            econstructor; eauto.
       apply X.
    auto.
    econstructor; eauto.
 +
   simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR.
 destruct s; inv H4.
 assert (Smallstep.star CCstep (Build_genv ge cenv) (CC.State f Sskip k'0 ve te m) nil
                         (CC.State f Sskip (CC.Kcall None f1 ve' te' k'1) ve te m)).
     clear - H1.
     revert H1; induction k'0; intros; try solve [inv H1].
           destruct (dec_skip s). subst s. simpl in H1. 
               eapply star_trans; try apply IHk'0; auto. apply Smallstep.star_one. constructor; auto.
          rewrite strip_skip'_not in H1 by auto. rewrite <- H1. constructor 1.
          simpl in H1. inv H1. constructor 1.
 (econstructor; split; [eapply star_plus_trans; [ apply H  | eapply Smallstep.plus_two ] | ]).
     eapply CC.step_skip_call; simpl; eauto.
     assert (X: CCstep (Build_genv ge cenv) (CC.Returnstate Vundef (CC.Kcall None f1 ve' te' k'1) m') 
                                      Events.E0
                                     (CC_core_to_CC_state (CC_core_State f1 Sskip k'1 ve' te') m')).
            econstructor; eauto.
       apply X.
    auto.
    econstructor; eauto.
} Unfocus.
 
 Focus 1. (* step_switch *)
 inv H1. simpl strip_skip in H6.
 remember (CC.Kseq s k') as k0'.
 inv H6.
 evar (c2': CC_core).
 exists c2'; split.
     Focus 2. constructor; eauto. apply match_cont_strip. simpl.
                    instantiate (1:= CC.Kswitch k'0). constructor. auto.
     generalize (exec_skips' (Build_genv ge cenv) f _ _ _ _ ve te m (@eq_sym _ _ _ H4)); intro H99.
        eapply star_plus_trans; try apply H99.
        unfold c2'. apply Smallstep.plus_one. simpl. econstructor; eauto.

 Focus 1. (* step_label *)
 inv H0.  remember (CC.Kseq s0 k') as k0'. inv H5.
 destruct (IHcl_step (CC_core_State f s k'0 ve te)) as [st2 [? ?]]; clear IHcl_step.
 constructor; auto. apply match_cont_strip. auto.
 exists st2; split; auto.
   eapply star_plus_trans; try eassumption.
   generalize (exec_skips' (Build_genv ge cenv) f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
     eapply star_trans; try apply H99.
     apply Smallstep.star_one. constructor.
 
 Focus 1. (* step_goto *)
 inv H0. remember (CC.Kseq s k'0) as k0'. inv H5.
  generalize (match_cont_call_strip k k'1); intro.
 spec H0.
 clear - CUR. apply (call_cont_nonnil _ _ CUR).
 specialize (H0 H1).
  rewrite <- strip_call' in H0.
 change (Kseq (Sreturn None) :: call_cont k) with (strip_skip (Kseq (Sreturn None) :: call_cont k)) in H0.
 destruct (match_find_label _ _ _ _ _ H0 H) as [s2 [k2' [? ?]]].
 exists (CC_core_State f s2 k2' ve te); split.
    simpl in CUR0. inversion2 CUR CUR0.
     generalize (exec_skips' (Build_genv ge cenv) f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
     eapply star_plus_trans; try apply H99.
         apply Smallstep.plus_one. constructor; auto.
         constructor; auto.
   clear - CUR H. forget (fn_body f) as s.
       rewrite <- current_function_call_cont in CUR.
       change (current_function (Kseq (Sreturn None) :: call_cont k) = Some f) in CUR.
        forget (Kseq (Sreturn None) :: call_cont k) as k0. clear - CUR H.
        eapply current_function_find_label; eauto.
 apply match_cont_strip1. auto.
Admitted.

Definition CC_at_external (c: CC_core) : option (external_function * signature * list val) :=
  match c with
  | CC_core_State _ _ _ _ _ => None
  | CC_core_Callstate fd args k => 
    match fd with
      Internal _ => None
      | External ef tps tp cc => 
          match tp with 
          | Tvoid => Some (ef, mksignature (typlist_of_typelist tps) None cc, args)
          | _ => Some (ef, mksignature (typlist_of_typelist tps) (Some (typ_of_type tp)) cc, args)
          end
    end
  | CC_core_Returnstate _ _ => None
 end.


Definition CC_after_external (rv: option val) (c: CC_core) : option CC_core :=
  match c with
     CC_core_Callstate fd vargs (CC.Kcall optid f e lenv k) =>
        match fd with
          Internal _ => None
        | External ef tps tp cc =>
            match rv, optid with
              Some v, _ => Some(CC_core_State f Sskip k e (set_opttemp optid v lenv))
            |   None, None    => Some(CC_core_State f Sskip k e lenv)
            | _ , _ => None
            end
        end
   | _ => None
  end.

(*Earlier definition:
  Parameter mkAfterExtCore: external_function -> typelist -> type -> val -> list val -> CC.cont -> option CC_core.
(*something like the following (cf Clight_sem.v) seems reasonable  - but need ge and memories...
Definition mkAfterExtCore ge (ef:external_function) (targs: typelist) (tres: type)
                                (vres: val) (vargs: list val) (k: CC.cont) (c: CC_core ) :Prop :=
    match c with   CC_core_Returnstate vres' k'  => exists m, exists m', exists tr,
                     external_call ef  ge vargs m tr vres m' /\ vres = vres' /\ k=k'
                  | _ => False
    end.
*)

Definition CC_after_external (rv: option val) (c: CC_core) : option CC_core :=
  match rv, c with
   | Some v, CC_core_Callstate fd vargs k =>
                     match fd with
                         Internal _ => None
                       | External ef tps tp => mkAfterExtCore ef tps tp v vargs k
                     end
(*MAY NEED ANOTHER CASE HERE FOR Tvoid*)
  | _, _ => None
  end.
*)


Parameter main_function:function. (*IS THIS WHAT THE FIRST ARGUMENT OF CC_core_state is about, ie current function?*)
Parameter myStatement:statement.
Definition CC_initial_core (ge: genv) (v: val) (args: list val) : option CC_core := 
  let tl := typed_params 2%positive (length args)
   in Some (CC_core_State main_function myStatement
                           (CC.Kseq (Scall None 
                                  (Etempvar 1%positive (Tfunction (type_of_params tl) Tvoid cc_default))
                                  (map (fun x => Etempvar (fst x) (snd x)) tl))
                              (CC.Kseq (Sloop Sskip Sskip) CC.Kstop)) (*IS THE FORMATION OF THE CONT HERE CORRECT? WAS A cont list*)
                          empty_env (temp_bindings 1%positive (v::args))).

Definition CC_step (ge: genv) (q:CC_core) (m:mem) (q': CC_core) (m': mem) : Prop :=
  match q with 
      CC_core_Callstate (External _ _ _ _) _ _ => False 
   | _ => CCstep ge (CC_core_to_CC_state q m) (Events.E0)(CC_core_to_CC_state q' m')
  end.

Lemma CC_corestep_not_at_external: forall (ge : genv) (m : mem) (q : CC_core) (m' : mem)
  (q' : CC_core), CC_step ge q m q' m' -> CC_at_external q = None.
  Proof. intros.
     destruct q; simpl in *; trivial.
       destruct f; trivial. contradiction.
  Qed.

Definition CC_safely_halted (q:CC_core) : option val := None. (*Same cheat as in Clight_new/Clight_newSim*)

Lemma CC_corestep_not_halted :
       forall ge m q m' q', CC_step ge q m q' m' -> CC_safely_halted q = None.
  Proof. intros; trivial. Qed.

 Lemma CC_at_external_halted_excl :
       forall q, CC_at_external q = None \/ CC_safely_halted q = None.
   Proof. intros. right; trivial. Qed.

 Lemma CC_after_at_external_excl : forall retv(q q' : CC_core),
  CC_after_external retv q = Some q' -> CC_at_external q' = None.
  Proof. intros.
    destruct q; simpl in *; try inv H.
    destruct c; inv H1.
    destruct f; inv H0; simpl in *.
    destruct retv; inv H1; simpl. trivial.
    destruct o; inv H0; trivial.
  Qed.

Definition CC_core_sem : CoreSemantics genv CC_core mem.
 apply (Build_CoreSemantics _ _ _ (*_*) (*cl_init_mem*)
                CC_initial_core CC_at_external CC_after_external CC_safely_halted CC_step).
       apply CC_corestep_not_at_external.
       apply CC_corestep_not_halted.
       apply CC_at_external_halted_excl.
  Defined.

Lemma CC_step_to_CCstep: forall ge q m q' m',
   CC_step ge q m q' m' -> CCstep ge (CC_core_to_CC_state q m) nil  (CC_core_to_CC_state q' m').
  Proof. intros.
       destruct q; simpl in *. apply H.
          destruct f; try contradiction. apply H.
        apply H. 
  Qed. 

Definition isExternalCallState (c:CC.state) :=
  match c with CC.Callstate (External _ _ _ _ ) _ _ _  => True
                      | _ => False
  end.

Lemma CCstep_to_CC_step_1: forall ge c m c' m',
              CCstep ge (CC_core_to_CC_state c m) Events.E0 (CC_core_to_CC_state c' m') ->
              CC_at_external c = None -> CC_step ge c m c' m'.
   Proof. intros.
      destruct c; try apply H.
      destruct f; try apply H. 
      destruct t0; try solve [inv H0].
   Qed.

  Lemma CC_atExternal_isExternal: forall s,
         (exists z, CC_at_external (fst (CC_state_to_CC_core s)) = Some z) = isExternalCallState s.
  Proof. intros. apply prop_ext.
     destruct s; simpl. 
        split; intros; try contradiction. destruct H. inv H.
        destruct fd; simpl; intros.
        split; try contradiction.
        intros [z H1]. congruence.
        destruct t0; split; auto; intros; try solve[eexists; eauto].
        split; try solve[intros;elimtype False; auto|intros [? ?]; congruence].
  Qed.

Lemma step_to_CC_step: forall ge s s'  (H:CCstep ge s Events.E0 s') (Hs: ~ isExternalCallState s),
       exists c, exists m, exists c', exists m',
                  s = CC_core_to_CC_state c m /\  s' = CC_core_to_CC_state c' m' /\
                  CC_step ge c m c' m'.
  Proof. intros.
       destruct (CC_core_CC_state_4 s) as [c [m Hcm]]; subst.
       destruct (CC_core_CC_state_4 s') as [c' [m' Hcm']]; subst.
       eexists. exists m. eexists. exists m'. split. reflexivity. split. reflexivity.
        apply CCstep_to_CC_step_1.  apply H.
        remember (CC_at_external c) as b.
          destruct b; trivial; apply eq_sym in Heqb.
            exfalso. apply Hs. clear Hs.
            rewrite <- CC_atExternal_isExternal. exists p.
                 rewrite (CC_core_CC_state_3 _ c m); auto.
  Qed. 

Lemma CC_step_to_step: forall ge c m c' m',  CC_step ge c m c' m' ->
   CCstep ge (CC_core_to_CC_state c m) Events.E0 (CC_core_to_CC_state c' m').
  Proof. intros.
      destruct c; try  apply H.
      destruct f; try contradiction. apply H.
  Qed. 

Lemma CC_step_fun: forall ge m q m1 q1 m2 q2, 
    CC_step ge q m q1 m1 -> 
    CC_step ge q m q2 m2 -> 
    (q1,m1)=(q2,m2).
Proof.
intros. apply CC_step_to_step in H.  apply CC_step_to_step in H0.
  assert (Z:= cc_step_fun _ _ _ _ H H0).
  destruct q1; destruct q2; inv Z; trivial.
Qed.

Lemma exec_skips_CC:
 forall {s0 k s k'} 
   (H1: match_cont (Kseq s0 :: k) (strip_skip' (CC.Kseq s k')))
   ge f ve te m,
   match s0 with Sskip => False | Scontinue => False | Sloop _ _ => False 
            | Sifthenelse _ _ _ => False | Sreturn _ => False 
            | _ => True end ->
   exists k2, strip_skip' (CC.Kseq s k') = CC.Kseq s0 k2 /\
     corestep_star CC_core_sem ge  (CC_core_State f s k' ve te) m 
              (CC_core_State f s0 k2 ve te) m.
Proof.
 intros.
(*proof using  exec_skips is not expected to work since conversion CCstep to CC_step is only possible for nonAtexternal states
assert (ZZ:= exec_skips H1 ge f ve te m H). clear H.
  destruct ZZ as [k2 [K1 K2]].
 exists k2. split; trivial.*)

 remember (CC.Kseq s k') as k0.
 revert k s k' H1 Heqk0; induction k0; intros; inv Heqk0.
 assert ({s1=Sskip}+{s1<>Sskip}) by (destruct s1; try (left; congruence); right; congruence). 
 destruct H0.
 (*s1 = Sskip*)  subst s1.
      destruct k'; try solve [inv H1].
      (*1/3*) specialize (IHk0 _ s k' H1 (eq_refl _)).
                   destruct IHk0 as [k2 [? ?]].
                   exists k2. split; simpl; auto.
                   (*old proof. i.e used in exec_skips: econstructor 2. constructor. eauto. auto.*)
                   clear - H2. destruct H2 as [n Hn]. exists (S n). simpl.
                     eexists. eexists. split. Focus 2. apply Hn.
                                                          constructor.
     (*2/3*) inv H1; contradiction.
     (*3/3*) simpl in H1. inv H1. contradiction.
(*s1 <> Sskip*)
   replace (strip_skip' (CC.Kseq s1 k')) with (CC.Kseq s1 k')  in *
       by (destruct s1; try congruence; auto).
  clear - H H1.
   inv H1. exists k'; split; auto.  exists O. reflexivity.
Qed.

Lemma exec_skips'_CC:
  forall ge f s k' s0 k0' ve te m,
        strip_skip' (CC.Kseq s k') = CC.Kseq s0 k0' ->
        corestep_star CC_core_sem ge (CC_core_State f s k' ve te) m
                                   (CC_core_State f s0 k0' ve te) m.
Proof.
 intros.
 destruct (dec_skip s). subst. simpl in *.
 induction k'; try solve [inv H]. 
 destruct (dec_skip s). subst. simpl in *.
  eapply corestep_star_trans.
             Focus 2.  apply IHk'. apply H. 
       apply corestep_star_one. simpl. econstructor.
 rewrite strip_skip'_not in * by auto.
 inv H.  apply corestep_star_one. simpl. econstructor.
 rewrite strip_skip'_not in H by auto. inv H. exists O. simpl. reflexivity.
Qed.

Lemma strip_skip'_loop1_CC:
  forall ge f ve te m a3 s k1 k, CC.Kloop1 s a3 k1 = strip_skip' k ->
  corestep_star CC_core_sem ge (CC_core_State f Sskip k ve te) m
                                                         (CC_core_State f Sskip (CC.Kloop1 s a3 k1) ve te) m.
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0). subst. simpl in H.
     eapply corestep_star_trans; try apply (IHk H).
       apply corestep_star_one. simpl. constructor.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. apply corestep_star_zero.
 simpl in H. inv H. apply corestep_star_zero.
Qed.

Lemma strip_skip'_call_CC:
  forall ge f ve te m lid f' ve' te' k1 k, CC.Kcall lid f' ve' te' k1 = strip_skip' k ->
  corestep_star CC_core_sem ge (CC_core_State f Sskip k ve te) m
                                                          (CC_core_State f Sskip (CC.Kcall lid f' ve' te' k1) ve te) m.
Proof.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s). subst. simpl in H. 
     eapply corestep_star_trans; try apply (IHk H).
       apply corestep_star_one. simpl. constructor.
 rewrite strip_skip'_not in * by auto.
 rewrite <- H. apply corestep_star_zero.
 simpl in H. inv H. apply corestep_star_zero. 
Qed.

Lemma step_continue_strip_CC:
  forall ge f k ve te m, 
           corestep_star CC_core_sem ge (CC_core_State f Scontinue k ve te) m
               (CC_core_State f Scontinue (strip_skip' k) ve te) m.
Proof.
intros.
induction k; simpl; try apply corestep_star_zero.
destruct (dec_skip s).
(*s=skip*)
   subst.
   eapply corestep_star_trans.
         apply corestep_star_one. 
            assert (ZZ: corestep CC_core_sem ge (CC_core_State f Scontinue (CC.Kseq Sskip k) ve te) m (CC_core_State f Scontinue k ve te) m).
                    simpl. apply (CC.step_continue_seq ge (function_entry2 ge) f Sskip k ve te m).
            apply ZZ.
         assumption.
destruct s; try congruence; apply corestep_star_zero.
Qed.

Lemma step_continue_seq_CC: forall ge f s k e le m,
       corestep CC_core_sem ge (CC_core_State f Scontinue (CC.Kseq s k) e le) m
                                                      (CC_core_State f Scontinue k e le) m.
  Proof. intros.
    assert (Z:CCstep ge (CC.State f Scontinue (CC.Kseq s k) e le m) Events.E0  (CC.State f Scontinue k e le m) ).
           apply CC.step_continue_seq.
    apply step_to_CC_step in Z. 
                     destruct Z as [cc [mm [cc' [mm' [Heq1 [Heq2 Hstep]]]]]].
                         apply CC_core_CC_state_3 in Heq1. apply CC_core_CC_state_3 in Heq2. simpl in *.
                     inv Heq1. inv Heq2. apply Hstep.
                     auto.
  Qed. 

Lemma step_continue_switch_CC: forall ge f k e le m,
              corestep CC_core_sem ge (CC_core_State f Scontinue (CC.Kswitch k) e le) m
                                                             (CC_core_State f Scontinue k e le) m.
  Proof. intros.
    assert (Z:CCstep ge (CC.State f Scontinue (CC.Kswitch k) e le m) Events.E0  (CC.State f Scontinue k e le m) ).
           apply CC.step_continue_switch.
    apply step_to_CC_step in Z. 
                     destruct Z as [cc [mm [cc' [mm' [Heq1 [Heq2 Hstep]]]]]].
                         apply CC_core_CC_state_3 in Heq1. apply CC_core_CC_state_3 in Heq2. simpl in *.
                     inv Heq1. inv Heq2. apply Hstep.
                     auto.
  Qed. 

Lemma break_strip_CC: forall ge f ve te m k,
       corestep_star CC_core_sem ge (CC_core_State f Sbreak k ve te) m
                               (CC_core_State f Sbreak (strip_skip' k) ve te) m.
 Proof. induction k; try solve [apply corestep_star_zero].
    destruct (dec_skip s).
    (*s=skip*)  subst. simpl.
         eapply corestep_star_trans; try eassumption. eapply corestep_star_one. constructor. 
  rewrite strip_skip'_not; auto. apply corestep_star_zero.
Qed.

Lemma strip_skip'_loop2_CC:
  forall ge f ve te m a3 s k1 k, CC.Kloop2 s a3 k1 = strip_skip' k ->
  corestep_star CC_core_sem  ge (CC_core_State f Sskip k ve te) m 
                     (CC_core_State f Sskip (CC.Kloop2 s a3 k1) ve te) m.
Proof. intros.
 induction k; intros; try solve [inv H].
 destruct (dec_skip s0).
  (*s=skip*)  subst. eapply corestep_star_trans; try apply IHk; auto. apply corestep_star_one. constructor.
  (*s<>skip*) rewrite strip_skip'_not in * by auto.
         rewrite <- H. apply corestep_star_zero.

 simpl in H. inv H.  apply corestep_star_zero.
Qed.

Lemma Clightnew_Clight_sim_eq_noOrder:
forall cenv p (c1 : corestate) (m : mem) (c1' : corestate) (m' : mem),
corestep cl_core_sem (Build_genv (Genv.globalenv p) cenv) c1 m c1' m' ->
forall (c2 : CC_core),
 match_states c1 c2 ->
exists c2' : CC_core,
    corestep_plus CC_core_sem (Build_genv (Genv.globalenv p) cenv) c2 m c2' m' /\
    match_states c1' c2'.
Proof.
intros.
forget (Build_genv (Genv.globalenv p) cenv) as ge. clear p.
simpl in H.
(* inv H.
rename H1 into H.*)
revert c2 H0. induction H; intros.

Focus 1. (* step_assign *)
inv H4.
simpl strip_skip in H9. 
destruct (exec_skips_CC H9 ge f ve te m) as [k2 [? ?]]; simpl; auto.
exists (CC_core_State f Sskip k2 ve te); split. 
       eapply corestep_star_plus_trans. eassumption.
              eapply corestep_plus_one. econstructor; eauto.
constructor; auto.
rewrite H4 in H9. inv H9; auto.

Focus 1. (* step_set *)
inv H0.
destruct (exec_skips_CC H5 ge f ve te m) as [k2 [? ?]]; simpl; auto.
exists (CC_core_State f Sskip k2 ve (PTree.set id v te)); split. 
  eapply corestep_star_plus_trans. eassumption. apply corestep_plus_one. econstructor; eauto.
  rewrite H0 in H5. inv H5; constructor; auto.

Focus 1. (* step_call_internal *)
inv H7. 
 destruct (exec_skips_CC H12 ge f0 ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H7 in *. inv H12. simpl in CUR.
  (* econstructor; split. -- introduction of CC_core destroys potential for automation/econstructor
         here - need to instanitate manually.*)
  exists (CC_core_State f (fn_body f) (CC.Kcall optid f0 ve te k2) ve' le').
  split.
  (*a*) eapply corestep_star_plus_trans. apply H8. 
               apply corestep_plus_two with (c':=CC_core_Callstate (Internal f) vargs (CC.Kcall optid f0 ve te k2))(m':=m). 
                     simpl. econstructor; eauto.
              econstructor; eauto.
   (*b*)  simpl. apply list_norepet_app in H4; destruct H4 as [? [? ?]].
             econstructor; eauto. econstructor; eauto.
             apply match_cont_strip. simpl. constructor; auto.

Focus 1. (* step_call_external *)
inv H3. 
 destruct (exec_skips_CC H8 ge f ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H3 in *. inv H8. simpl in CUR. 
 (*econstructor; split.  -- again, we need to instantiate manually*)
  exists (CC_core_Callstate (External ef tyargs tyres cc_default) vargs (CC.Kcall optid f ve te k2)).
  split.
   (*a*) eapply corestep_star_plus_trans. eassumption. eapply corestep_plus_one. econstructor; eauto.
   (*b*) econstructor; eauto.

Focus 1. (* step_seq *)
 inv H0.
 destruct (exec_skips_CC H5 ge f ve te m) as [k2 [? ?]]; simpl; auto.
 rewrite H0 in *. inv H5.
 destruct (IHcl_step (CC_core_State f s1 (CC.Kseq s2 k2) ve te))
                as [st2 [? ?]]; clear  IHcl_step.
 repeat constructor; auto.
 apply match_cont_strip.  apply match_cont_strip.  auto.
 exists st2; split; auto.
 eapply corestep_star_plus_trans; [ eassumption | ]. simpl.
 apply corestep_plus_trans with (c2:=CC_core_State f s1 (CC.Kseq s2 k2) ve te)(m2:=m).
              apply corestep_plus_one. simpl. econstructor. eassumption.

 Focus 1. (* step_skip *)
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
 assert (s0<>Sskip).
 clear- Heqk0; intro; subst.
 revert Heqk0; induction k; simpl; intros. inv Heqk0. destruct a; try solve [inv Heqk0]; auto. destruct s; inv Heqk0; auto.
 destruct (IHcl_step (CC_core_State f s k' ve te)) 
                 as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. rewrite <- Heqk0'.
 constructor 2; auto.
 exists st2; split; auto.

  destruct (IHcl_step (CC_core_State f Sskip (CC.Kloop1 s0 s1 k0') ve te)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. simpl. rewrite <- Heqk0. constructor. auto.
  exists st2; split; auto.
  apply corestep_plus_split in H0. destruct H0 as [cc [mm [Hstep Hstar]]].
      eapply corestep_plus_star_trans; try apply Hstar.
          clear  - Hstep Heqk0'.
             destruct s; inv Heqk0'.
             eapply corestep_star_plus_trans.
                    apply (strip_skip'_loop1_CC _ _ _ _ _ _ _ _ _ H0).
                    eapply corestep_plus_one. apply Hstep.

 destruct (IHcl_step (CC_core_State f Sskip (CC.Kloop2 s0 s1 k0') ve te)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 destruct (dec_skip s). subst.
 econstructor; eauto. rewrite <- Heqk0. constructor. auto.
 rewrite strip_skip'_not in Heqk0' by auto. inv Heqk0'.
  exists st2; split; auto.
  destruct s; inv Heqk0'.
  eapply corestep_star_plus_trans; try apply H0.
  clear - H4; revert H4; induction k'; intros; inv H4.
  destruct (dec_skip s). subst.
  specialize (IHk' H0). 
       eapply corestep_star_trans; try apply IHk'. apply corestep_star_one. constructor.
 replace (CC.Kloop2 s0 s1 k0') with (CC.Kseq s k') by  (destruct s; auto; congruence).
    apply corestep_star_zero. 
 apply corestep_star_zero.

 destruct s; inv Heqk0'.
 destruct (IHcl_step (CC_core_State f Sskip (CC.Kcall o f0 e t k0') ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. rewrite <- Heqk0. constructor; auto.
  exists st2; split; auto.
  apply corestep_plus_split in H0. destruct H0 as [cc [mm [Hstep Hstar]]].
      eapply corestep_plus_star_trans; try apply Hstar.
          clear  - Hstep H2.
             eapply corestep_star_plus_trans.
                    eapply (strip_skip'_call_CC _ _ _ _ _ _ _ _ _ _ _ H2); try apply Hstep.
                    eapply corestep_plus_one. apply Hstep.

 Focus 1. (* step_continue *)
 inv H0.
 simpl strip_skip in H5.
 inv H5.
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

 assert (X1: corestep_star CC_core_sem ge (CC_core_State f s k' ve te) m
                             (CC_core_State f Scontinue k'0 ve te) m).
     clear - H3.
     destruct (dec_skip s).
     (*s=skip*) subst. simpl in H3.
           eapply exec_skips'_CC; auto.
     (*s<>skip*)
           rewrite strip_skip'_not in H3 by auto. inv H3. simpl. apply corestep_star_zero.
 assert (X2: corestep_star CC_core_sem ge (CC_core_State f Scontinue k'0 ve te) m
                                       (CC_core_State f Scontinue (strip_skip' k'0) ve te) m).
      clear.
      induction k'0; try solve [apply corestep_star_zero].
      destruct (dec_skip s).
      (*s=skip*)  subst.  simpl in *.
                            eapply corestep_star_trans; try apply IHk'0. clear IHk'0.
                            apply corestep_star_one. constructor.
      (*s<>skip*) 
           rewrite strip_skip'_not; auto.  apply corestep_star_zero.
 generalize (corestep_star_trans _ _ _ _ _ _ _ _ X1 X2); clear X1 X2; intro.
 clear H3.
 forget (strip_skip' k'0) as k0'; clear k'0.
 assert (precontinue_cont k = Kloop1 s1 s2 :: l).
 revert H0; clear; induction k; simpl; try congruence.  destruct a; try congruence; auto.
 assert (exists k1', 
               corestep_star CC_core_sem ge (CC_core_State f Scontinue k0' ve te) m
                    (CC_core_State f Scontinue k1' ve te) m /\
               match_cont (Kseq Scontinue :: Kloop1 s1 s2 :: l) k1').
     clear - H1 H0.
     revert H0; induction H1; simpl; intros; try congruence.
        destruct IHmatch_cont as [k1' [? ?]].
           rewrite <- continue_cont_skip; auto.
        econstructor. split; [ | eassumption].
           eapply corestep_star_trans; try apply H. 
             clear. 
             eapply corestep_star_trans.
                 eapply corestep_star_one. apply step_continue_seq_CC.
                 apply step_continue_strip_CC. 
(*       inv H0. econstructor; split. apply corestep_star_zero. constructor. auto. 
       destruct IHmatch_cont as [k1' [? ?]].
           rewrite <- continue_cont_skip; auto.
          econstructor. split; [ | eassumption].
            eapply corestep_star_trans; try apply H.
              eapply corestep_star_trans. 
                 eapply corestep_star_one. apply step_continue_seq_CC.
                 apply step_continue_strip_CC. *)
      inv H0.  econstructor; split. apply corestep_star_zero. constructor. auto.
      destruct IHmatch_cont as [k1' [? ?]].
          rewrite <- continue_cont_skip; auto.
          econstructor. split; [ | eassumption].
             eapply corestep_star_trans; try apply H.
              eapply corestep_star_trans. 
                 eapply corestep_star_one. apply step_continue_switch_CC. 
                 apply step_continue_strip_CC.
 destruct H4 as [k1' [StepStar Mtch]].
 generalize (corestep_star_trans _ _ _ _ _ _ _ _ H2 StepStar); clear H2 StepStar; intro H2.
 rewrite H0 in *.
 assert (CUR': current_function l = Some f).
   clear - CUR H0. revert CUR H0; induction k; simpl; intros. inv CUR.
   destruct a; try discriminate; auto. inv H0. auto.
 clear H1 CUR k H0 H3.
 inv Mtch.
     inv H4. simpl in *.
    destruct (IHcl_step (CC_core_State f s2 (CC.Kloop2 s1 s2 k'0) ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
    constructor; auto. apply match_cont_strip. constructor. auto.
    exists st2; split; auto.
    eapply corestep_star_plus_trans; [apply H2 | ].
    eapply corestep_star_plus_trans; [ | apply H0].
    eapply corestep_star_one. constructor. auto.

Focus 1.
   change (CC.Kloop1 s0 e3 k'0 = strip_skip' (CC.Kseq s k')) in H1.
 destruct (dec_skip s); [ | destruct s; try congruence; inv H1].
 subst s.
 simpl in H.
 simpl in H1.
 simpl in *.
 assert (X1: corestep_star CC_core_sem ge (CC_core_State f Sskip k' ve te) m
                   (CC_core_State f Sskip (CC.Kloop1 s0 e3 k'0) ve te) m).
     rewrite H1; clear.
     induction k'; intros; try solve [apply corestep_star_zero].
     destruct (dec_skip s).
     (*s=skip*)  subst. simpl in *. eapply corestep_star_trans; try apply IHk'.
                                        apply corestep_star_one. simpl. econstructor. 
    (*s <> skip*) rewrite strip_skip'_not; auto.  apply corestep_star_zero.  
 forget (CC_core_State f Sskip k' ve te) as st1.
 clear k' H1.
 assert (X2: corestep_star CC_core_sem ge st1 
                  m (CC_core_State f e3 (CC.Kloop2 s0 e3 k'0) ve te) m).
     eapply corestep_star_trans; try apply X1.
     eapply corestep_star_one. constructor. auto.
 clear X1.
 destruct (IHcl_step (CC_core_State f e3 (CC.Kloop2 s0 e3 k'0) ve te)) 
                      as [st2 [? ?]]; clear  IHcl_step.
 constructor; auto. apply match_cont_strip; constructor; auto.
 exists st2; split; auto.
 eapply corestep_star_plus_trans; eauto.

 (* step_break *)
 Focus 1.
 inv H0. simpl strip_skip in H5.
 destruct (dec_skip s).
 (*s=skip*)
      subst.  simpl strip_skip' in *.
      assert (exists k1', strip_skip' k' = CC.Kseq Sbreak k1').
           revert H5; clear. remember (strip_skip' k') as k0'.  
           revert k' Heqk0'; induction k0'; intros; try solve [inv H5].
           inv H5. eauto.
      destruct H0 as [k1' H0].
      assert (X: corestep_star CC_core_sem ge (CC_core_State f Sskip k' ve te) m
                           (CC_core_State f Sbreak k1' ve te) m).
          revert k1' H0; clear; induction k'; intros; try solve [inv H0].
          destruct (dec_skip s).
          (*s=skip*)  subst.  simpl in *. specialize (IHk' _ H0).
                  eapply corestep_star_trans; try apply IHk'. apply corestep_star_one. constructor.
          (* s <> skip*) rewrite strip_skip'_not in H0 by auto. inv H0.
                          apply corestep_star_one. constructor.
      simpl.
      forget (CC_core_State f Sskip k' ve te) as st1.
      rewrite H0 in *.
      clear k' H0.
      inv H5.
      rewrite <- break_cont_skip in *.
      simpl in CUR. rewrite <- current_function_strip in CUR.    
      forget (strip_skip k) as k0.
      assert (Y: corestep_star  CC_core_sem ge st1 m (CC_core_State f Sbreak (strip_skip' k1') ve te) m).
          eapply corestep_star_trans; try apply X; auto.
          clear.
          induction k1'; try destruct s; try solve [apply corestep_star_zero].
          simpl. eapply corestep_star_trans; eauto. apply corestep_star_one. constructor.
      forget (strip_skip' k1') as k0'. clear k1' X.

      assert (X: exists k1',
             corestep_plus CC_core_sem ge (CC_core_State f Sbreak k0' ve te) m
                       (CC_core_State f Sskip k1' ve te) m
             /\ match_cont (strip_skip (break_cont k0)) (strip_skip' k1')).
          clear - H H1.
          revert H; induction H1; intros; try solve [inv H].
          (*1/6*)
              rewrite break_cont_skip in *. simpl in H.
              destruct (IHmatch_cont H) as [k1' [? ?]]; clear IHmatch_cont. simpl.
              exists k1'; split; auto.
              eapply corestep_star_plus_trans; try eassumption.
                   eapply corestep_star_trans with (c2:=CC_core_State f Sbreak k' ve te)(m2:=m). 
                        apply corestep_star_one. simpl. constructor. 
                        apply break_strip_CC.  
         (*4/6*) simpl  in *. exists k'; split.
               apply corestep_plus_one. simpl. eapply CC.step_break_loop1. 
                auto.
         (*6/6*) simpl in *. exists k'; split.
                eapply corestep_plus_one. simpl. eapply CC.step_skip_break_switch. auto.
                assumption.
       destruct X as [k1' [? ?]].
       destruct (IHcl_step (CC_core_State f Sskip k1' ve te))
                      as [st2 [? ?]]; clear  IHcl_step.
         constructor; auto.
            clear - H CUR. revert CUR; induction  k0; intros. inv CUR.
            destruct a; simpl in *; auto. inv H. inv H.
       exists st2; split; auto.
       eapply corestep_star_plus_trans; try apply Y.
       eapply corestep_plus_trans. apply H0. apply H3.
   (*s<>skip*)
     rewrite strip_skip'_not in H5 by auto.
     inv H5. clear n.
     admit.  (* probably similar to the previous case *)

 Focus 1.  (* step_ifthenelse *)
 inv H1. simpl strip_skip in H6.
 inv H6. 
 change (CC.Kseq (Sifthenelse a s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H4.
 assert (X: corestep_star CC_core_sem ge (CC_core_State f s k' ve te) m (CC_core_State f (Sifthenelse a s1 s2) k'0 ve te) m).
     clear - H4.
     revert H4; induction k'; intros; try solve [ destruct s; inv H4; apply corestep_star_zero].
     destruct (dec_skip s).
      (*s=skip*) subst s.
          destruct (dec_skip s0).
          (*s0=skip*)  subst s0. simpl in *.
               eapply corestep_star_trans; try apply IHk'; eauto. apply corestep_star_one. constructor.
          (*s0 <> skip*) change (strip_skip' (CC.Kseq Sskip (CC.Kseq s0 k'))) with 
               (strip_skip' (CC.Kseq s0 k')) in H4.
               rewrite strip_skip'_not in H4 by auto.
               inv H4. apply corestep_star_one. constructor.
      (*s<>skip*)  rewrite strip_skip'_not in * by auto.
          inv H4.  apply corestep_star_zero.
 exists (CC_core_State f (if b then s1 else s2) k'0 ve te); split; auto.
   eapply corestep_star_plus_trans; try apply X.  
      apply corestep_plus_one. econstructor; eauto. 
 constructor; auto. apply match_cont_strip; auto.

 Focus 1. (* step_loop *)
 inv H0. inv H4.
 (*First case*)
 change (CC.Kseq (Sloop s1 s2) k'0 = strip_skip' (CC.Kseq s k')) in H2.
  generalize (exec_skips'_CC ge f _ _ _ _ ve te m (@eq_sym _ _ _ H2)); intro.
 exists ( (CC_core_State f s1 (CC.Kloop1 s1 s2 k'0) ve te)); split.
 eapply corestep_star_plus_trans; try apply H.
  apply corestep_plus_one. simpl. eapply CC.step_loop; eauto.
  (*b*) constructor; auto. apply match_cont_strip; constructor; auto.

 Focus 1. (* step_loop2 *)
  inv H0. inv H4.
 destruct s0; inv H3.
 generalize (strip_skip'_loop2_CC ge f ve te m _ _ _ _ H1); intro.
 exists (CC_core_State f s (CC.Kloop1 s a3 k'0) ve te); split.
 eapply corestep_star_plus_trans; try apply H.
 eapply corestep_plus_star_trans with (c2:=CC_core_State f (Sloop s a3) k'0 ve te)(m2:=m).
 apply corestep_plus_one. simpl.  eapply CC.step_skip_loop2; eauto.
 apply corestep_star_one. simpl. eapply CC.step_loop; eauto.
  constructor; auto. apply match_cont_strip. constructor. auto.

 Focus 1. (* step_return *)
 inv H3.
  remember (strip_skip' (CC.Kseq s k'0)) as k3. simpl in CUR, H8.
 inv H8.
 (*first case of two*)
 generalize (exec_skips'_CC ge f0 _ _ _ _ ve te m (@eq_sym _ _ _ H4)); intro H99.
 assert (f0=f).
   simpl in CUR; clear - CUR H.
   revert H CUR; induction k; intros. inv H. simpl in *. destruct a; auto. inv CUR; auto. inv H; auto.
 subst f.
 generalize (match_cont_call_strip k k'1); intro.
 spec H3; [congruence |]. spec H3; [auto |].
 generalize H3; rewrite H; intro.
 inv H5.
 (*1/2*)   elimtype False; clear - H10.
         revert H10; induction k'1; simpl; intros; congruence.
 (*2/2*) destruct optexp;  [destruct H1 as [v [? ?]] | ]; (destruct optid; destruct H2 as [H2 H2']; 
               try solve [contradiction H2; auto]; subst te'' );
               try (eapply corestep_star_trans; split; [eapply corestep_star_plus_trans; [ apply H99  | eapply corestep_plus_two ] | ]).
        (*The orignial proof resulted in 12 subcases here - now we have only 3 ;-) *)
           (*1/3*) 
                eexists (CC_core_State f Sskip k'2 ve' (PTree.set i v' te')).
                split. 
                     eapply (corestep_star_plus_trans _ _ _ _ _ _ _ _ H99). (* with (c2:=CC_core_State f0 (Sreturn (Some e)) k'1 ve te)(m2:=m).   apply H99. *)
                          eapply corestep_plus_trans with (c2:=CC_core_Returnstate v' (CC.call_cont k'1))(m2:=m').
                                         eapply corestep_plus_one. simpl. econstructor; eauto.
                                         eapply corestep_plus_one. simpl. rewrite <- H13. eapply CC.step_returnstate.
                    constructor; auto.
           (*2/3*) 
                eexists (CC_core_State f Sskip k'2 ve' te').
                split. 
                     eapply (corestep_star_plus_trans _ _ _ _ _ _ _ _ H99). (* with (c2:=CC_core_State f0 (Sreturn (Some e)) k'1 ve te)(m2:=m). apply H99. *)
                          eapply corestep_plus_trans with (c2:=CC_core_Returnstate v' (CC.call_cont k'1))(m2:=m').
                                         eapply corestep_plus_one. simpl. econstructor; eauto.
                                         eapply corestep_plus_one. simpl. rewrite <- H13. eapply CC.step_returnstate.
                    constructor; auto.
           (*3/3*) 
                eexists (CC_core_State f Sskip k'2 ve' (CC.set_opttemp (Some i) v' te')).
                split. 
                     eapply (corestep_star_plus_trans _ _ _ _ _ _ _ _ H99). (* with (c2:=CC_core_State f0 (Sreturn None) k'1 ve te)(m2:=m). apply H99. *)
                          eapply corestep_plus_trans with (c2:=CC_core_Returnstate v' (CC.call_cont k'1))(m2:=m').
                                         eapply corestep_plus_one. simpl. subst; econstructor; eauto.
                                         eapply corestep_plus_one. simpl. rewrite <- H13.
                      eapply CC.step_returnstate.
                      simpl.
                    constructor; auto.
            (* 4/3 *)
              eexists (CC_core_State f Sskip k'2 ve' te').
                split. 
                     eapply (corestep_star_plus_trans _ _ _ _ _ _ _ _ H99). (* with (c2:=CC_core_State f0 (Sreturn None) k'1 ve te)(m2:=m). apply H99. *)
                          eapply corestep_plus_trans with (c2:=CC_core_Returnstate v' (CC.call_cont k'1))(m2:=m').
                                         eapply corestep_plus_one. simpl. subst; econstructor; eauto.
                                         eapply corestep_plus_one. simpl. rewrite <- H13.
                      eapply CC.step_returnstate.
                      simpl.
                    constructor; auto.

 (*second case*)
 destruct optid. destruct H2.
   subst te''.
  simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR.
 destruct s; inv H4.
 assert (corestep_star CC_core_sem ge (CC_core_State f Sskip k'0 ve te) m
                         (CC_core_State f Sskip (CC.Kcall (Some i) f1 ve' te' k'1) ve te) m).
     revert H1; induction k'0; intros; try solve [inv H1].
           destruct (dec_skip s).
           (*s=skip*)  subst s. simpl in H1. 
               eapply corestep_star_trans; try apply IHk'0; auto. apply corestep_star_one. constructor; auto.
          (*s<>skip*)
              rewrite strip_skip'_not in H1 by auto. rewrite <- H1. apply corestep_star_zero.
          simpl in H1. inv H1.  apply corestep_star_zero.
 eexists (CC_core_State f1 Sskip k'1 ve' (CC.set_opttemp (Some i) Vundef te')).
     split. eapply corestep_star_plus_trans. apply H. clear H.
              eapply corestep_plus_trans with (c2:=CC_core_Returnstate Vundef (CC.Kcall (Some i) f1 ve' te' k'1))(m2:=m').
                  eapply corestep_plus_one. simpl. eapply CC.step_skip_call; simpl; eauto.
                  eapply corestep_plus_one. simpl.  econstructor; eauto.
     econstructor; eauto.
 destruct H2; subst te''.
 simpl in H. inv H. simpl in CUR. symmetry in CUR; inv CUR.
 destruct s; inv H4.
 assert (corestep_star CC_core_sem ge (CC_core_State f Sskip k'0 ve te) m
                         (CC_core_State f Sskip (CC.Kcall None f1 ve' te' k'1) ve te) m).
     clear - H1.
     revert H1; induction k'0; intros; try solve [inv H1].
           destruct (dec_skip s).
           (*s=skip*)  subst s. simpl in H1. 
               eapply corestep_star_trans; try apply IHk'0; auto. apply corestep_star_one. constructor; auto.
          (*s<>skip*)
              rewrite strip_skip'_not in H1 by auto. rewrite <- H1. apply corestep_star_zero.
          simpl in H1. inv H1.  apply corestep_star_zero.
 eexists (CC_core_State f1 Sskip k'1 ve' te').
     split. eapply corestep_star_plus_trans. apply H. clear H.
              eapply corestep_plus_trans with (c2:=CC_core_Returnstate Vundef (CC.Kcall None f1 ve' te' k'1))(m2:=m').
                  eapply corestep_plus_one. simpl. eapply CC.step_skip_call; simpl; eauto.
                  eapply corestep_plus_one. simpl.  econstructor; eauto.
     econstructor; eauto.
 
 Focus 1. (* step_switch *)
 rename H0 into Hn. rename H1 into H0.
 inv H0. simpl strip_skip in H5.
 remember (CC.Kseq s k') as k0'.
 inv H5.
 evar (c2': CC_core).
 exists c2'; split.
     Focus 2. constructor; eauto. apply match_cont_strip. simpl.
                    instantiate (1:= CC.Kswitch k'0). constructor. auto.
     generalize (exec_skips'_CC ge f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
        eapply corestep_star_plus_trans; try apply H99.
        unfold c2'. apply corestep_plus_one. simpl. econstructor; eauto.

 Focus 1. (* step_label *)
 inv H0.  remember (CC.Kseq s0 k') as k0'. inv H5.
 destruct (IHcl_step (CC_core_State f s k'0 ve te)) as [st2 [? ?]]; clear IHcl_step.
 constructor; auto. apply match_cont_strip. auto.
 exists st2; split; auto.
   eapply corestep_star_plus_trans; try eassumption.
   generalize (exec_skips'_CC ge f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
     eapply corestep_star_trans; try apply H99.
     apply corestep_star_one. constructor.
 
 Focus 1. (* step_goto *)
 inv H0. remember (CC.Kseq s k'0) as k0'. inv H5.
  generalize (match_cont_call_strip k k'1); intro.
 spec H0.
 clear - CUR. apply (call_cont_nonnil _ _ CUR).
 specialize (H0 H1).
  rewrite <- strip_call' in H0.
 change (Kseq (Sreturn None) :: call_cont k) with (strip_skip (Kseq (Sreturn None) :: call_cont k)) in H0.
 destruct (match_find_label _ _ _ _ _ H0 H) as [s2 [k2' [? ?]]].
 exists (CC_core_State f s2 k2' ve te); split.
    simpl in CUR0. inversion2 CUR CUR0.
     generalize (exec_skips'_CC ge f _ _ _ _ ve te m (@eq_sym _ _ _ H3)); intro H99.
     eapply corestep_star_plus_trans; try apply H99.
         apply corestep_plus_one. constructor; auto.
         constructor; auto.
   clear - CUR H. forget (fn_body f) as s.
       rewrite <- current_function_call_cont in CUR.
       change (current_function (Kseq (Sreturn None) :: call_cont k) = Some f) in CUR.
        forget (Kseq (Sreturn None) :: call_cont k) as k0. clear - CUR H.
        eapply current_function_find_label; eauto.
 apply match_cont_strip1. auto.
Admitted.

Definition MS (_:corestate)(c: corestate) (C: CC_core): Prop := match_states c C.

Definition coresem_extract_cenv {M} {core} (CS: CoreSemantics genv core M)
                         (cenv: composite_env) :
            CoreSemantics (Genv.t fundef type) core M :=
  Build_CoreSemantics _ _ _
             (fun ge => CS.(initial_core) (Build_genv ge cenv))
             CS.(at_external)
             CS.(after_external)
             CS.(halted)
            (fun ge => CS.(corestep) (Build_genv ge cenv))
            (fun ge => CS.(corestep_not_at_external) (Build_genv ge cenv))
            (fun ge => CS.(corestep_not_halted) (Build_genv ge cenv))
            CS.(at_external_halted_excl).

(*
Lemma Clightnew_Clight_sim_eq: forall cenv p ExternIdents entrypoints
               (ext_ok : CompilerCorrectness.entryPts_ok p p ExternIdents entrypoints)
(*               (IniHyp : forall x : mem, Genv.init_mem p = Some x <->
                                           initial_mem CC_core_sem (Genv.globalenv p) x p.(prog_vars))*),
              Forward_simulation_eq.Forward_simulation_equals (*_ _ _*)
                  (coresem_extract_cenv cl_core_sem cenv)
                  (coresem_extract_cenv CC_core_sem cenv)
                  (Build_genv (Genv.globalenv p) cenv)
                  (Build_genv (Genv.globalenv p) cenv)
                  entrypoints.
Proof.
  intros. 
  pose (bogus_measure := (fun x: corestate => O)).
  eapply eq_simulation_plus with (match_cores:=MS); try apply bogus_measure; unfold MS.
 (*genvs_domain_eq*)
    apply genvs_domain_eq_refl.
 (* initial states *)
      intros. unfold cl_core_sem, CC_core_sem; simpl. 
      unfold cl_initial_core, CC_initial_core; simpl.
     eexists. split. eexists. (*split. reflexivity. split. reflexivity.*)
       assert (v1=v2). unfold  CompilerCorrectness.entryPts_ok in ext_ok.
          admit. (*again some Genv/entrypojnts/ext_ok stuff*)
       subst. 
       (*econstructor. simpl.
          admit. (*Definition of CC_initial_core seems to be wrong here*)
         simpl. assert (myStatement = Sskip). admit. 
          rewrite H0. econstructor. simpl. constructor. simpl. constructor.*)
       admit. (* initial_core case needs fixing *)
 (* final states *)  
      intros. unfold cl_core_sem in H0. simpl in H0. unfold cl_halted  in H0. inv H0.
  (*at_external*)
     intros. inv H; subst; simpl in *. 
          inv H0. simpl in *. inv H2. simpl in *. congruence.
          unfold CC_at_external. destruct tyres;auto. simpl.
          admit. (*HOLE REGARDING ARGUMENT TYPES???*)
  (*after_external*) 
         intros. inv H1; simpl in *. 
          admit. (*HOLE REGARDING ARGUMENT TYPES???*)
          intros. destruct H0; subst. 
  (*simulation_diag*)
     intros. 
     (*1/2*) 
       apply (Clightnew_Clight_sim_eq_noOrder _ _ _ _ _ _ H
                     (CC_core_State f s k' ve te)).
          constructor; assumption.
   (*2/2*) inv H.
  Admitted.

Require Import sepcomp.simulations.

Theorem Clightnew_Clight_sim: forall cenv p ExternIdents entrypoints
         (ext_ok: CompilerCorrectness.entryPts_ok p p ExternIdents entrypoints)
        (*(IniHyp: forall x, Genv.init_mem p = Some x <-> initial_mem CC_core_sem (Genv.globalenv p) x p.(prog_defs))*),
        CompilerCorrectness.core_correctness
             (fun F C V Sem P => True)
              ExternIdents entrypoints _ _ _ _ _ _ 
                  (coresem_extract_cenv cl_core_sem cenv)
                  (coresem_extract_cenv CC_core_sem cenv)
               p p.
Proof.
intros.
econstructor.
  auto. (*simpl.  intros. exists m1; auto.*)
  apply ext_ok.
  eapply Clightnew_Clight_sim_eq; eauto.
  trivial.
  unfold CompilerCorrectness.GenvHyp; auto.
  trivial. (*apply IniHyp.*)
  trivial. (*apply IniHyp.*)
Qed.
*)

(*Before elimination of initial_mem from coresem, the theorem was like this:

Theorem Clightnew_Clight_sim: forall p ExternIdents entrypoints
         (ext_ok: CompilerCorrectness.entryPts_ok p p ExternIdents entrypoints)
        (IniHyp: forall x, Genv.init_mem p = Some x <-> initial_mem CC_core_sem (Genv.globalenv p) x p.(prog_defs)),
        CompilerCorrectness.core_correctness
             (fun F C V Sem P => (forall x, Genv.init_mem P = Some x <-> initial_mem Sem (Genv.globalenv P) x P.(prog_defs)))
              ExternIdents _ _ _ _ _ _  cl_core_sem CC_core_sem p p.
Proof.
intros.
econstructor.
  simpl.  intros. exists m1; auto.
  apply ext_ok.
  eapply Clightnew_Clight_sim_eq; eauto.
  trivial.
  unfold CompilerCorrectness.GenvHyp; auto.
  apply IniHyp.
  apply IniHyp.
Qed.
*)