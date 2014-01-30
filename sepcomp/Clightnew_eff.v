Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Export Maps.
Require Import Events.
Require Import Globalenvs.

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.

Require Import Cop. (*for sem_cast*)
Require Import Ctypes. (*for access_mode*)
Require Import Clight.
Require Import Clight_new.
Require Import Clightnew_coop.

Definition assign_loc_Effect (ty:type) (b: block) (ofs: int) v : (block -> Z -> bool)  :=
  match access_mode ty with
     By_value chunk => fun b' z' => eq_block b' b 
              && zle (Int.unsigned ofs) z' 
              && zlt z' ((Int.unsigned ofs) + Z.of_nat (length (encode_val chunk v)))
   | By_copy => fun b' z' => eq_block b' b 
              && zle (Int.unsigned ofs) z' 
              && zlt z' ((Int.unsigned ofs) + (sizeof ty))
   | _ => fun b' z' => false
  end.
  
Lemma assign_loc_Effect_Sound: forall a m loc ofs v m'
      (AL: assign_loc (typeof a) m loc ofs v m'),
     Mem.unchanged_on (fun b z => assign_loc_Effect (typeof a) 
                            loc ofs v b z = false) m m'.
Proof. intros. inv AL.
inv H0.
(*access_mode (typeof a) = By_value chunk*)
  split; intros.
  (*perm*)
    split; intros.
    eapply Mem.perm_store_1; eassumption.
    eapply Mem.perm_store_2; eassumption.
  (*memcontents*)
    rewrite (Mem.store_mem_contents _ _ _ _ _ _ H2).
    unfold assign_loc_Effect in H0; rewrite H in H0.
    destruct (eq_block b loc); subst; simpl in H0.
      rewrite PMap.gss. rewrite andb_false_iff in H0.
      apply Mem.setN_other. intros; intros N. subst.
      destruct H3.
      destruct (zle (Int.unsigned ofs) ofs0); simpl in *.
        destruct H0; try discriminate.
        destruct (zlt ofs0 (Int.unsigned ofs + Z.of_nat (length (encode_val chunk v)))); simpl in *. discriminate.
        omega.
      omega.
    rewrite PMap.gso; trivial.
(*access_mode (typeof a) = By_copy*)
  split; intros.
  (*perm*)
    split; intros.
    eapply Mem.perm_storebytes_1; eassumption.
    eapply Mem.perm_storebytes_2; eassumption.
  (*memcontents*)
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H4).
    unfold assign_loc_Effect in H5; rewrite H in H5.
    destruct (eq_block b loc); subst; simpl in H5.
      rewrite PMap.gss. rewrite andb_false_iff in H5.
      apply Mem.setN_other. intros; intros N. subst.
      destruct H7.
      destruct (zle (Int.unsigned ofs) ofs0); simpl in *.
        destruct H5; try discriminate.
        destruct (zlt ofs0 (Int.unsigned ofs + sizeof (typeof a))); simpl in *. discriminate.
        apply Mem.loadbytes_length in H3. rewrite H3 in H8.
          rewrite nat_of_Z_eq in H8. omega. 
          assert (ZZZ:= sizeof_pos (typeof a)). omega.
      omega.
    rewrite PMap.gso; trivial.
Qed.

Lemma alloc_variables_unchanged_on:
      forall P args env m e m' (H:alloc_variables env m args e m'),
      Mem.unchanged_on P m m'.
Proof. intros P args.
  induction args; simpl; intros; inv H.
    apply Mem.unchanged_on_refl.
  apply IHargs  in H7.
  specialize (alloc_forward _ _ _ _ _ H4). intros.
  eapply unchanged_on_trans;  try eassumption.
  eapply Mem.alloc_unchanged_on. eassumption.
Qed.

Section EFFSEM.
Inductive cln_effstep (ge:genv): (block -> Z -> bool) ->
            corestate -> mem -> corestate -> mem -> Prop :=

  | cln_effstep_assign: forall ve te k m a1 a2 loc ofs v2 v m',
     type_is_volatile (typeof a1) = false ->
      Clight.eval_lvalue ge ve te m a1 loc ofs ->
      Clight.eval_expr ge ve te m a2 v2 ->
      Cop.sem_cast v2 (typeof a2) (typeof a1) = Some v ->
      Clight.assign_loc (typeof a1) m loc ofs v m' ->
      cln_effstep ge (assign_loc_Effect (typeof a1) loc ofs v)
          (State ve te (Kseq (Sassign a1 a2):: k)) m 
          (State ve te k) m'

  | cln_effstep_set:   forall ve te k m id a v,
      Clight.eval_expr ge ve te m a v ->
      cln_effstep ge EmptyEffect 
          (State ve te (Kseq (Sset id a) :: k)) m
          (State ve (PTree.set id v te) k) m

  | cln_effstep_call_internal:   forall ve te k m optid a al tyargs tyres vf vargs f m1 ve' le',
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres ->
      Clight.eval_expr ge ve te m a vf ->
      Clight.eval_exprlist ge ve te m al tyargs vargs ->
      Genv.find_funct ge vf = Some (Internal f) ->
      type_of_function f = Tfunction tyargs tyres ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_temps)) ->
      forall (NRV: list_norepet (var_names f.(fn_vars))),
      Clight.alloc_variables empty_env m (f.(fn_vars)) ve' m1 ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some 
le' ->
      cln_effstep ge EmptyEffect 
           (State ve te (Kseq (Scall optid a al) :: k)) m
           (State ve' le' (Kseq f.(fn_body) :: Kseq (Sreturn None) :: Kcall optid f ve te :: k)) m1

  | cln_effstep_call_external:   forall ve te k m optid a al tyargs tyres vf vargs ef,
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres ->
      Clight.eval_expr ge ve te m a vf ->
      Clight.eval_exprlist ge ve te m al tyargs vargs ->
      Genv.find_funct ge vf = Some (External ef tyargs tyres) ->
      cln_effstep ge EmptyEffect 
           (State ve te (Kseq (Scall optid a al) :: k)) m
           (ExtCall ef (signature_of_type tyargs tyres) vargs optid ve te k) m

  | cln_effstep_seq: forall ve te k m s1 s2 st' m' E,
          cln_effstep ge E (State ve te (Kseq s1 :: Kseq s2 :: k)) m st' m' ->
          cln_effstep ge E (State ve te (Kseq (Ssequence s1 s2) :: k)) m st' m'

  | cln_effstep_skip: forall ve te k m st' m' E,
          cln_effstep ge E (State ve te k) m st' m' ->
          cln_effstep ge E (State ve te (Kseq Sskip :: k)) m st' m'

  | cln_effstep_continue: forall ve te k m st' m' E,
           cln_effstep ge E (State ve te (continue_cont k)) m st' m' ->
           cln_effstep ge E (State ve te (Kseq Scontinue :: k)) m st' m' 

  | cln_effstep_break: forall ve te k m st' m' E,
                   cln_effstep ge E (State ve te (break_cont k)) m st' m' ->
                   cln_effstep ge E (State ve te (Kseq Sbreak :: k)) m st' m'

  | cln_effstep_ifthenelse:  forall ve te k m a s1 s2 v1 b,
      Clight.eval_expr ge ve te m a v1 ->
      Cop.bool_val v1 (typeof a) = Some b ->
      cln_effstep ge EmptyEffect 
          (State ve te (Kseq (Sifthenelse a s1 s2) :: k)) m 
          (State ve te  (Kseq (if b then s1 else s2) :: k)) m

  | cln_effstep_for: forall ve te k m s1 s2,
      cln_effstep ge EmptyEffect 
          (State ve te (Kseq (Sloop s1 s2) :: k)) m 
          (State ve te (Kseq s1 :: Kseq Scontinue :: Kloop1 s1 s2 :: k)) m

  | cln_effstep_loop2: forall ve te k m a3 s,
      cln_effstep ge EmptyEffect 
          (State ve te (Kloop2 s a3 :: k)) m 
          (State ve te (Kseq s :: Kseq Scontinue :: Kloop1 s a3 :: k)) m

  | cln_effstep_return: forall f ve te optexp optid k m v' m' ve' te' te'' k',
      call_cont k = Kcall optid f ve' te' :: k' ->
      Mem.free_list m (Clight.blocks_of_env ve) = Some m' ->
      match optexp with None => True
                                  | Some a => exists v, Clight.eval_expr ge ve te m a v /\ Cop.sem_cast v (typeof a) f.(fn_return) = Some v' 
                            end ->
      match optid with None => f.(fn_return) = Tvoid /\ te''=te'
                                | Some id => optexp <> None /\ te'' = PTree.set id v' te'
      end ->
      cln_effstep ge (FreelistEffect m (Clight.blocks_of_env ve))
          (State ve te (Kseq (Sreturn optexp) :: k)) m
          (State ve' te'' k') m'

  | cln_effstep_switch: forall ve te k m a sl n,
      Clight.eval_expr ge ve te m a (Vint n) ->
      cln_effstep ge EmptyEffect 
          (State ve te (Kseq (Sswitch a sl) :: k)) m
          (State ve te (Kseq (seq_of_labeled_statement (select_switch n sl)) :: Kswitch :: k)) m

  | cln_effstep_label: forall ve te k m lbl s st' m' E,
       cln_effstep ge E (State ve te (Kseq s :: k)) m st' m' ->
       cln_effstep ge E (State ve te (Kseq (Slabel lbl s) :: k)) m st' m'

  | cln_effstep_goto: forall f ve te k m lbl k' 
                     (* make sure to take a step here, so that every loop ticks the clock *) 
      (CUR: current_function k = Some f),
      find_label lbl f.(fn_body) (Kseq (Sreturn None) :: (call_cont k)) = Some k' ->
      cln_effstep ge EmptyEffect 
          (State ve te (Kseq (Sgoto lbl) :: k)) m (State ve te k') m.
(*
  | cln_effstep_sub_val: forall E EE c m c' m',
      (forall b ofs, Mem.valid_block m b ->
                     E b ofs = true -> EE b ofs = true) ->
      cln_effstep ge E c m c' m' ->
      cln_effstep ge EE c m c' m'.*)

Lemma clightnew_effax1: forall (M : block -> Z -> bool) ge c m c' m'
      (H: cln_effstep ge M c m c' m'),
       corestep CLN_coop_sem ge c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m'.
Proof. 
intros.
  induction H.
  split. econstructor; try eassumption.
         eapply assign_loc_Effect_Sound; eassumption.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
    eapply alloc_variables_unchanged_on; eassumption.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  destruct IHcln_effstep. 
   split. econstructor; try eassumption.
          assumption.
  destruct IHcln_effstep. 
   split. econstructor; try eassumption.
          assumption.
  destruct IHcln_effstep. 
   split. econstructor; try eassumption.
          assumption.
  destruct IHcln_effstep. 
   split. econstructor; try eassumption.
          assumption.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply FreelistEffect_freelist; eassumption. 
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  destruct IHcln_effstep. 
   split. econstructor; try eassumption.
          assumption.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  (*effstep_sub_val
    destruct IHcln_effstep.
    split; trivial.
    eapply unchanged_on_validblock; try eassumption.
    intros; simpl. remember (E b ofs) as d.
    destruct d; trivial. apply eq_sym in Heqd.
    rewrite (H _ _ H3 Heqd) in H4. discriminate.*)
Qed.

Lemma clightnew_effax2: forall ge c m c' m',
      corestep CLN_coop_sem ge c m c' m' ->
      exists M, cln_effstep ge M c m c' m'.
Proof.
intros. induction H.
  eexists. eapply cln_effstep_assign; eassumption.
  eexists. eapply cln_effstep_set; eassumption.
  eexists. eapply cln_effstep_call_internal; eassumption.
  eexists. eapply cln_effstep_call_external; eassumption.
  destruct IHcl_step.
    eexists. eapply cln_effstep_seq; eassumption.
  destruct IHcl_step.
    eexists. eapply cln_effstep_skip; eassumption.
  destruct IHcl_step.
    eexists. eapply cln_effstep_continue; eassumption.
  destruct IHcl_step.
    eexists. eapply cln_effstep_break; eassumption.
  eexists. eapply cln_effstep_ifthenelse; eassumption.
  eexists. eapply cln_effstep_for; eassumption.
  eexists. eapply cln_effstep_loop2; eassumption.
  eexists. eapply cln_effstep_return; eassumption.
  eexists. eapply cln_effstep_switch; eassumption.
  destruct IHcl_step.
    eexists. eapply cln_effstep_label; eassumption.
  eexists. eapply cln_effstep_goto; eassumption.
Qed.

Lemma clightnew_effstep_valid: forall (M : block -> Z -> bool) g c m c' m',
      cln_effstep g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b.
Proof.
intros.
  induction H; try (solve [inv H0; auto]).

  inv H4; unfold assign_loc_Effect in H0; rewrite H5 in H0.
     destruct (eq_block b loc); subst; simpl in *; try discriminate.
     apply Mem.store_valid_access_3 in H6.
     eapply Mem.perm_valid_block. eapply H6. 
       destruct (zle (Int.unsigned ofs) z); simpl in *; try discriminate.
       destruct (zlt z (Int.unsigned ofs + Z.of_nat (length (encode_val chunk v)))); simpl in *; try discriminate.
       split. eassumption. rewrite encode_val_length in l0. rewrite <- size_chunk_conv in l0. trivial.

     destruct (eq_block b loc); subst; simpl in *; try discriminate.
     apply Mem.loadbytes_length in H9.
     eapply Mem.perm_valid_block with (ofs:=z). 
        eapply Mem.storebytes_range_perm. eassumption.
       destruct (zle (Int.unsigned ofs) z); simpl in *; try discriminate.
       destruct (zlt z (Int.unsigned ofs + sizeof (typeof a1))); simpl in *; try discriminate.
       split. eassumption. rewrite H9. rewrite nat_of_Z_eq. trivial. 
              specialize (sizeof_pos (typeof a1)). omega.

  eapply FreelistEffect_validblock; eassumption.
Qed.

Definition cln_eff_sem  
  :  @EffectSem Clight.genv corestate.
eapply Build_EffectSem with (sem := CLN_coop_sem)
         (effstep:=cln_effstep).
apply clightnew_effax1. 
apply clightnew_effax2. 
apply clightnew_effstep_valid.
(*apply cln_effstep_sub_val. *)
Defined.
End EFFSEM.