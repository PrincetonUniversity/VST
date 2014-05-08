Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Ctypes. (*for type and access_mode*)
Require Import mem_lemmas. (*needed for definition of valid_block_dec etc*)

Require Import Axioms.
Require Import StructuredInjections.
Require Import reach. 
Require Import effect_properties.
Require Import effect_simulations. 

Definition memcpy_Effect sz vargs m:=
       match vargs with 
          Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil =>
          fun b z => eq_block b b1 && zle (Int.unsigned ofs1) z &&
                     zlt z (Int.unsigned ofs1 + sz) && valid_block_dec m b
       | _ => fun b z => false
       end.
      
Lemma memcpy_Effect_unchOn: forall m bsrc osrc sz bytes bdst odst m'
        (LD: Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes)
        (ST: Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m')
        (SZ: sz >= 0),
    Mem.unchanged_on
      (fun b z=> memcpy_Effect sz (Vptr bdst odst :: Vptr bsrc osrc :: nil) 
                 m b z = false) m m'.
Proof. intros.
  split; intros.
    unfold Mem.perm. rewrite (Mem.storebytes_access _ _ _ _ _ ST). intuition.
  unfold memcpy_Effect in H.
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST).
    destruct (valid_block_dec m b); simpl in *. rewrite andb_true_r in H; clear v.
    destruct (eq_block b bdst); subst; simpl in *.
      rewrite PMap.gss. apply Mem.setN_other.
      intros. intros N; subst. 
        rewrite (Mem.loadbytes_length _ _ _ _ _ LD), nat_of_Z_eq in H1; trivial.
          destruct (zle (Int.unsigned odst) ofs); simpl in *.
            destruct (zlt ofs (Int.unsigned odst + sz)). inv H.
            omega. omega.
    clear H. rewrite PMap.gso; trivial.
  elim n. eapply Mem.perm_valid_block; eassumption.
Qed.

Lemma external_call_memcpy_unchOn:
    forall {F V:Type} (ge : Genv.t F V) m ty b1 ofs1 b2 ofs2 m' a tr vres,
    external_call (EF_memcpy (sizeof ty) a) ge 
                  (Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil) m tr vres m' -> 
    Mem.unchanged_on
      (fun b z=> memcpy_Effect (sizeof ty) (Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil) 
                 m b z = false) m m'.
Proof. intros. inv H.
  eapply memcpy_Effect_unchOn; try eassumption. omega.
Qed.
 
Lemma memcpy_Effect_validblock:
    forall {F V:Type} (ge : Genv.t F V) m sz vargs b z,
    memcpy_Effect sz vargs m b z = true ->
    Mem.valid_block m b.
Proof. intros.
 unfold memcpy_Effect in H.  
  destruct vargs; try discriminate.
  destruct v; try discriminate.
  destruct vargs; try discriminate.
  destruct v; try discriminate.
  destruct vargs; try discriminate.
  destruct (valid_block_dec m b); simpl in *. trivial. 
  rewrite andb_false_r in H. inv H. 
Qed.
                                                          
Definition BuiltinEffect  {F V: Type} (ge: Genv.t F V) (ef: external_function)
          (vargs:list val) (m:mem): block -> Z -> bool :=
  match ef with
    EF_memcpy sz a => memcpy_Effect sz vargs m
  | _ => fun b z => false
  end.

Lemma BuiltinEffect_unchOn:
    forall {F V:Type} ef (g : Genv.t F V) vargs m t vres m',
    external_call ef g vargs m t vres m' -> 
    Mem.unchanged_on
      (fun b z=> BuiltinEffect g ef vargs m b z = false) m m'.
Proof. intros.
  destruct ef.
    admit. (*case EF_external*)
    admit. (*case EF_builtin*)
    admit. (*case EF_vload*)
    admit. (*case EF_vstore*)
    admit. (*case EF_vload_global*)
    admit. (*case EF_vstore_global*)
    admit. (*case EF_malloc*)
    admit. (*case EF_free*)
    simpl. (*case EE_memcpy*)
           inv H. clear - H1 H6 H7.
           eapply memcpy_Effect_unchOn; try eassumption. omega.
    admit. (*case EF_annot1*)
    admit. (*case EF_annot2*)
    admit. (*case EF_inline_asm*)
Qed.

Lemma BuiltinEffect_valid_block:
    forall {F V:Type} ef (g : Genv.t F V) vargs m b z,
     BuiltinEffect g ef vargs m b z = true -> Mem.valid_block m b. 
Proof. intros. unfold BuiltinEffect in H. 
  destruct ef; try discriminate.
    eapply memcpy_Effect_validblock; eassumption.
Qed.

(*takes the role of external_call_mem_inject for builtins etc.
  Since inlinables write at most to vis, we use the
  Mem-Unchanged_on condition loc_out_of_reach, rather than
  local_out_of_reach as in external calls.*)
Lemma inlineable_extern_inject: forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) (GDE: genvs_domain_eq ge tge) 
          ef vargs m t vres m1 mu tm vargs'
       (WD: SM_wd mu) (SMV: sm_valid mu m tm) (RC: REACH_closed m (vis mu)),
       meminj_preserves_globals ge (as_inj mu) ->
       external_call ef ge vargs m t vres m1 ->
       Mem.inject (as_inj mu) m tm ->
       val_list_inject (restrict (as_inj mu) (vis mu)) vargs vargs' ->
       exists mu' vres' tm1,
         external_call ef tge vargs' tm t vres' tm1 /\
         val_inject (restrict (as_inj mu') (vis mu')) vres vres' /\
         Mem.inject (as_inj mu') m1 tm1 /\
         Mem.unchanged_on (loc_unmapped (restrict (as_inj mu) (vis mu))) m m1 /\
         Mem.unchanged_on (loc_out_of_reach (restrict (as_inj mu) (vis mu)) m) tm tm1 /\
         intern_incr mu mu' /\
         sm_inject_separated mu mu' m tm /\
         sm_locally_allocated mu mu' m tm m1 tm1 /\
         SM_wd mu' /\ sm_valid mu' m1 tm1 /\
         (REACH_closed m (vis mu) -> REACH_closed m1 (vis mu')).
Proof. intros.
destruct ef; simpl in H0.
    admit. (*case EF_external*)
    admit. (*case EF_builtin*)
    admit. (*case EF_vload*)
    admit. (*case EF_vstore*)
    admit. (*case EF_vload_global*)
    admit. (*case EF_vstore_global*)
    admit. (*case EF_malloc*)
    admit. (*case EF_free*)
  (*memcpy*)
     inv H0. 
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m bsrc (Int.unsigned osrc) (Int.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Int.unsigned odst) (Int.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega.
  assert (PSRC: Mem.perm m bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  inv H2. inv H12. inv H14. inv H15. inv H12.
  destruct (restrictD_Some _ _ _ _ _ H11).
  destruct (restrictD_Some _ _ _ _ _ H13).
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists mu; exists Vundef; exists m2'.
  split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto. 
  eapply Mem.aligned_area_inject with (m := m); eauto.
  eapply Mem.aligned_area_inject with (m := m); eauto.
  eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto.
  split. constructor.
  split. auto.
  split. eapply Mem.storebytes_unchanged_on; eauto.
         unfold loc_unmapped; intros. rewrite H11. congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto.
         unfold loc_out_of_reach; intros. red; intros.
         eapply (H16 _ _ H11). 
             apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
             eapply Mem.storebytes_range_perm; eauto.  
             erewrite list_forall2_length; eauto. 
             omega.
         (*destruct H16. specialize (H17 bdst delta).
         assert (local_of mu bdst = Some (b2, delta)).
           destruct (joinD_Some _ _ _ _ _ H0).
             destruct (extern_DomRng _ WD _ _ _ H18).
             rewrite (extBlocksTgt_locBlocksTgt _ WD _ H20) in H16. discriminate.
           eapply H18.
         destruct (H17 H18); clear H17.
           elim H19; clear H19.
             apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
             eapply Mem.storebytes_range_perm; eauto.  
             erewrite list_forall2_length; eauto. 
             omega.
         admit. *)(*need to restrict to replace_locals!*)
  split. apply intern_incr_refl.
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl.
       rewrite (storebytes_freshloc _ _ _ _ _ H10). clear. intuition.
       rewrite (storebytes_freshloc _ _ _ _ _ C). clear. intuition.
       rewrite (storebytes_freshloc _ _ _ _ _ H10). clear. intuition.
       rewrite (storebytes_freshloc _ _ _ _ _ C). clear. intuition.
  split; trivial. 
  split. split; intros.
       eapply storebytes_forward; try eassumption.
          eapply SMV; trivial.
       eapply storebytes_forward; try eassumption.
          eapply SMV; trivial.
  destruct (loadbytes_D _ _ _ _ _ H9); clear A C.
   clear RPSRC RPDST PSRC PDST H8 H11 H3 H5 H6 H7 EQ1 EQ2 B D.  
  intros. eapply REACH_Storebytes; try eassumption.
          intros. eapply H3. subst bytes.
          destruct (in_split _ _ H5) as [bts1 [bts2 Bytes]]; clear H5.
          specialize (getN_range _ _ _ _ _ _ Bytes). intros.
          apply getN_aux in Bytes. 
          eapply REACH_cons. instantiate(1:=bsrc).
            eapply REACH_nil. apply H14.
            Focus 2. apply eq_sym. eassumption. 
            eapply H15. clear - H5 H4. split. specialize (Zle_0_nat (length bts1)). intros. omega.
            apply inj_lt in H5. rewrite nat_of_Z_eq in H5; omega.
 
    admit. (*case EF_annot*)
    admit. (*case EFannot_val*)
    admit. (*case EF_inline*)
Qed.

Lemma BuiltinEffect_Propagate: forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) ef m vargs t vres m'
       (EC : external_call ef ge vargs m t vres m') mu m2 tvargs
       (ArgsInj : val_list_inject (restrict (as_inj mu) (vis mu)) vargs tvargs)
       (WD : SM_wd mu) (MINJ : Mem.inject (as_inj mu) m m2),
     forall b ofs, BuiltinEffect tge ef tvargs m2 b ofs = true ->
       visTgt mu b = true /\
       (locBlocksTgt mu b = false ->
        exists b1 delta1,
           foreign_of mu b1 = Some (b, delta1) /\
           BuiltinEffect ge ef vargs m b1 (ofs - delta1) = true /\
           Mem.perm m b1 (ofs - delta1) Max Nonempty).
Proof.
 intros. destruct ef; try inv H.
     (*memcpy*)
        simpl in EC. inv EC. 
        inv ArgsInj. inv H12. inv H10. inv H11. inv H14. 
        rewrite H1. unfold memcpy_Effect in H1.
        destruct (eq_block b b2); subst; simpl in *; try inv H1.
        destruct (zle (Int.unsigned (Int.add odst (Int.repr delta))) ofs); simpl in *; try inv H9. 
        destruct (zlt ofs (Int.unsigned (Int.add odst (Int.repr delta)) + sz)); simpl in *; try inv H1.
        destruct (valid_block_dec m2 b2); simpl in *; try inv H9.
        split. eapply visPropagateR; eassumption.
        intros. exists bdst, delta.
        destruct (restrictD_Some _ _ _ _ _ H12).
        exploit Mem.address_inject.
           eapply MINJ.
           eapply Mem.storebytes_range_perm. eassumption.
           split. apply Z.le_refl.
             rewrite (Mem.loadbytes_length _ _ _ _ _ H6).
               rewrite nat_of_Z_eq; omega.
           eassumption.
        intros UNSIG; rewrite UNSIG in *.
        assert (MP: Mem.perm m bdst (ofs - delta) Max Nonempty).
           eapply Mem.perm_implies.
             eapply Mem.perm_max. 
             eapply Mem.storebytes_range_perm. eassumption.
             rewrite (Mem.loadbytes_length _ _ _ _ _ H6).
             rewrite nat_of_Z_eq; omega.
           constructor. 
        rewrite (restrict_vis_foreign_local _ WD) in H12.
        destruct (joinD_Some _ _ _ _ _ H12) as [FRG | [FRG LOC]]; clear H12.
          split; trivial. split; trivial.
          destruct (eq_block bdst bdst); simpl. clear e.
            destruct (zle (Int.unsigned odst) (ofs - delta)); simpl.
              destruct (zlt (ofs - delta) (Int.unsigned odst + sz)); simpl.
                destruct (valid_block_dec m bdst); trivial.
                elim n. eapply Mem.perm_valid_block; eassumption.
              omega.
            omega.
          elim n; trivial.
        destruct (local_DomRng _ WD _ _ _ LOC).
          rewrite H13 in H1. discriminate.
  inv H8.
  inv H8.
Qed.
