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
Require Import effect_semantics. 
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
  
Definition free_Effect vargs m:=
       match vargs with 
          Vptr b1 lo :: nil =>
          match Mem.load Mint32 m b1 (Int.unsigned lo - 4)
          with Some (Vint sz) =>
            fun b z => eq_block b b1 && zlt 0 (Int.unsigned sz) &&
                     zle (Int.unsigned lo - 4) z &&
                     zlt z (Int.unsigned lo + Int.unsigned sz)
          | _ => fun b z => false
          end
       | _ => fun b z => false
       end.

Lemma free_Effect_unchOn: forall {F V : Type} (g : Genv.t F V)
        vargs m t vres m' (FR : external_call EF_free g vargs m t vres m'),
     Mem.unchanged_on (fun b z => free_Effect vargs m b z = false) m m'.
Proof. intros. inv FR. 
  eapply Mem.free_unchanged_on. eassumption.
  intros. unfold free_Effect. rewrite H.
    destruct (eq_block b b); simpl.
      clear e. destruct (zlt 0 (Int.unsigned sz)); simpl; try omega. 
      clear l. destruct (zlt 0 (Int.unsigned sz)); simpl; try omega.
      clear l. destruct (zle (Int.unsigned lo - 4) i); simpl; try omega.
      clear l. destruct (zlt i (Int.unsigned lo + Int.unsigned sz)); simpl; try omega.
      discriminate.
   elim n; trivial.
Qed.

Lemma freeEffect_valid_block vargs m: forall b z 
        (FR: free_Effect vargs m b z = true),
      Mem.valid_block m b.
Proof. intros.
  destruct vargs; inv FR.
  destruct v; inv H0.
  destruct vargs; inv H1.
  remember (Mem.load Mint32 m b0 (Int.unsigned i - 4)) as d.
  destruct d; apply eq_sym in Heqd.
    destruct v; inv H0.
    destruct (eq_block b b0); subst; simpl in *.
      apply Mem.load_valid_access in Heqd.
      eapply Mem.valid_access_valid_block.
      eapply Mem.valid_access_implies; try eassumption. constructor.
    inv H1.
  inv H0.
Qed.

Definition BuiltinEffect  {F V: Type} (ge: Genv.t F V) (ef: external_function)
          (vargs:list val) (m:mem): block -> Z -> bool :=
  match ef with
    EF_malloc => EmptyEffect
  | EF_free => free_Effect vargs m
  | EF_memcpy sz a => memcpy_Effect sz vargs m
  | _ => fun b z => false
  end.

Lemma malloc_Effect_unchOn: forall {F V : Type} (g : Genv.t F V)
         vargs m t vres m' (EF: external_call EF_malloc g vargs m t vres m'),
     Mem.unchanged_on
      (fun b z => BuiltinEffect g EF_malloc vargs m b z = false) m m'.
Proof. intros.
       simpl. inv EF.
       split; intros.
          unfold Mem.perm. rewrite (Mem.store_access _ _ _ _ _ _ H0).
          split; intros. 
            eapply Mem.perm_alloc_1; eassumption. 
            eapply Mem.perm_alloc_4; try eassumption.
              intros N. subst. eapply Mem.fresh_block_alloc; eassumption.
        rewrite <- (AllocContentsOther _ _ _ _ _ H). 
                rewrite (Mem.store_mem_contents _ _ _ _ _ _ H0).
                rewrite PMap.gso. trivial.
                intros N; subst. apply Mem.perm_valid_block in H2.
                    eapply Mem.fresh_block_alloc; eassumption.
              intros N; subst. apply Mem.perm_valid_block in H2.
                    eapply Mem.fresh_block_alloc; eassumption.
Qed.

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
    (*case EF_malloc*)
       eapply  malloc_Effect_unchOn; eassumption.
    (*case EF_free*)
       eapply free_Effect_unchOn; eassumption.
    (*case EE_memcpy*)
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
    eapply freeEffect_valid_block; eassumption.
    eapply memcpy_Effect_validblock; eassumption.
Qed.
Lemma REACH_Store: forall m chunk b i v m'
     (ST: Mem.store chunk m b i v = Some m')
     Roots (VISb: Roots b = true)
     (VISv : forall b', getBlocks (v :: nil) b' = true -> 
             Roots b' = true)
     (R: REACH_closed m Roots),
     REACH_closed m' Roots.
Proof. intros.
intros bb Hbb.
apply R. clear R.
rewrite REACHAX.
remember (Roots bb) as Rb. destruct Rb; apply eq_sym in HeqRb.
  eexists. eapply reach_nil; trivial. 
rewrite REACHAX in Hbb.
destruct Hbb as [L HL].
destruct (reachD'' _ _ _ _ HL) as [r [M [Rr [RCH HM]]]]; clear HL L.
destruct (eq_block r b); subst. 
(*we stored into the root of the access path to bb*)
  clear VISb.
  generalize dependent bb.
  induction M; simpl in *; intros.
  inv RCH. congruence. 
  inv RCH.    
  apply (Mem.perm_store_2 _ _ _ _ _ _ ST) in H2.
  remember (rev M) as rm.
  destruct rm; simpl in *. destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
        inv Hzz1.
        intuition. 
        assert (M= nil). destruct M; trivial. 
             assert (@length (block * Z) nil = length (rev (p :: M))). rewrite Heqrm; trivial.
             rewrite rev_length in H3. simpl in H3. inv H3.
        subst. simpl in *. clear H Heqrm H0 H1.
          specialize (Mem.loadbytes_store_same _ _ _ _ _ _ ST). intros LD.
          apply loadbytes_D in LD. destruct LD.

     rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST) in H4, H0. 
          apply Mem.store_valid_access_3 in ST. destruct ST as [RP ALGN].
          rewrite PMap.gss in H4.
          destruct (zlt zz i).
            rewrite Mem.setN_outside in H4.
            eexists. eapply reach_cons; try eassumption.
                     apply reach_nil. assumption.
            left; trivial. 
          destruct (zlt zz (i + Z.of_nat (length (encode_val chunk v)))).
          Focus 2.
            rewrite Mem.setN_outside in H4.
            eexists. eapply reach_cons; try eassumption.
                     apply reach_nil. assumption.
            right; trivial.
          rewrite encode_val_length in *. rewrite <- size_chunk_conv in *.
            rewrite PMap.gss in H0.
            remember ((Mem.setN (encode_val chunk v) i
          (Mem.mem_contents m) !! b)) as c. apply eq_sym in H0.
          specialize (getN_aux (nat_of_Z ((size_chunk chunk))) i c).
          assert (exists z, zz = i + z /\ z>=0 /\ z < size_chunk chunk).
            exists (zz - i). omega.
          destruct H1 as [z [Z1 [Z2 Z3]]]. clear g l. subst zz.
          rewrite <- (nat_of_Z_eq _ Z2) in H4.
          assert (SPLIT: exists vl1 u vl2,
                     encode_val chunk v = vl1 ++ u :: vl2 /\
                     length vl1 = nat_of_Z z).
            eapply list_split. rewrite encode_val_length.
                 rewrite size_chunk_conv in Z3.
            remember (size_chunk_nat chunk) as k. clear Heqk H2 H4 Hzz3.
            specialize (Z2Nat.inj_lt z (Z.of_nat k)); intros.
            rewrite Nat2Z.id in H1. apply H1. omega. omega.  assumption.
            
          destruct SPLIT as [B1 [u [B2 [EE LL]]]].
          rewrite EE in *. rewrite <- LL in H4.
          intros. apply H1 in H0. clear H1.
          rewrite <- H0 in H4. clear H0. subst u.
          destruct (encode_val_pointer_inv' _ _ _ _ _ _ _ EE).
          subst.
          rewrite VISv in HeqRb. discriminate.
             rewrite getBlocks_char. exists off; left. trivial.
  destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
    subst.
    remember (Roots b') as q.
    destruct q; apply eq_sym in Heqq.
      assert (b' = b). apply (Hzz3 _ z Heqq). left; trivial.
      subst. elim (Hzz2 z). apply in_or_app. right. left. trivial.
    destruct (eq_block b' b); try congruence.
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST) in H4.
        rewrite PMap.gso in H4; trivial.
        assert (Hb': exists L : list (block * Z),
            reach m (fun bb0 : block => Roots bb0 = true) L b').
          apply IHM; trivial. clear IHM.
          exists zz. intuition.
          eapply (Hzz2 zz0). apply in_or_app. left; trivial.
          eapply (Hzz3 _ zx H). right; trivial.
        destruct Hb' as [L HL].
          eexists. eapply reach_cons; try eassumption.  
(*we stored elsewhere*)
generalize dependent bb.
induction M; simpl in *; intros.
  inv RCH. congruence. 
  inv RCH.    
  apply (Mem.perm_store_2 _ _ _ _ _ _ ST) in H2.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST) in H4.
  remember (rev M) as rm.
  destruct rm; simpl in *. destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
        inv Hzz1.
        rewrite PMap.gso in H4; trivial.
        eexists. eapply reach_cons; try eassumption.
           apply reach_nil. assumption.
  destruct HM as [zz [Hzz1 [Hzz2 Hzz3]]].
    subst.
    remember (Roots b') as q.
    destruct q; apply eq_sym in Heqq.
      assert (b' = r). apply (Hzz3 _ z Heqq). left; trivial.
      subst. 
        rewrite PMap.gso in H4; trivial.
          eexists. eapply reach_cons; try eassumption.
           apply reach_nil. assumption.
    destruct (eq_block b' b); try congruence.
        rewrite PMap.gso in H4; trivial.
        assert (Hb': exists L : list (block * Z),
            reach m (fun bb0 : block => Roots bb0 = true) L b').
          apply IHM; trivial. clear IHM.
          exists zz. intuition.
          eapply (Hzz2 zz0). apply in_or_app. left; trivial.
          eapply (Hzz3 _ zx H). right; trivial.
        destruct Hb' as [L HL].
          eexists. eapply reach_cons; try eassumption.
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
    (*case EF_malloc*)
    inv H0. inv H2. inv H8. inv H6. 
    exploit alloc_parallel_intern; eauto. apply Zle_refl. apply Zle_refl. 
    intros [mu' [tm' [tb [TALLOC [INJ' [INC [AI1 [AI2 [SEP [LOCALLOC [WD' [SMV' RC']]]]]]]]]]]].
    exploit Mem.store_mapped_inject. eexact INJ'. eauto. eauto. 
    instantiate (1 := Vint n). auto.   
    intros [tm1 [ST' INJ1]].
    assert (visb': vis mu' b = true).
        apply sm_locally_allocatedChar in LOCALLOC.
        unfold vis. destruct LOCALLOC as [_ [_ [LOC _]]]. rewrite LOC.
        rewrite (freshloc_alloc _ _ _ _ _ H3).
        destruct (eq_block b b); subst; simpl. intuition. elim n0; trivial.
    exists mu'; exists (Vptr tb Int.zero); exists tm1; intuition.
      econstructor; eauto.
      econstructor. eapply restrictI_Some; eassumption.
      rewrite Int.add_zero. trivial.
    split; unfold loc_unmapped; intros. unfold Mem.perm. 
         rewrite (Mem.store_access _ _ _ _ _ _ H4).
         split; intros.
         eapply Mem.perm_alloc_1; eassumption.
         eapply Mem.perm_alloc_4; try eassumption.
         intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ H3 H5).
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ H4).
        apply Mem.perm_valid_block in H5.
        rewrite PMap.gso. 
          rewrite (AllocContentsOther1 _ _ _ _ _ H3). trivial. 
          intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ H3 H5).
        intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ H3 H5).
    split; unfold loc_out_of_reach; intros.
         unfold Mem.perm. 
         rewrite (Mem.store_access _ _ _ _ _ _ ST').
         split; intros.
         eapply Mem.perm_alloc_1; eassumption.
         eapply Mem.perm_alloc_4; try eassumption.
         intros N; subst. eapply (Mem.fresh_block_alloc _ _ _ _ _ TALLOC H5).
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST').
        apply Mem.perm_valid_block in H5.
        rewrite PMap.gso. 
          rewrite (AllocContentsOther1 _ _ _ _ _ TALLOC). trivial. 
          intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ TALLOC H5).
        intros N; subst; eapply (Mem.fresh_block_alloc _ _ _ _ _ TALLOC H5).
    rewrite sm_locally_allocatedChar.
      rewrite sm_locally_allocatedChar in LOCALLOC.
      destruct LOCALLOC as [LAC1 [LAC2 [LAC3 [LAC4 [LAC5 LOC6]]]]].
      rewrite LAC1, LAC2, LAC3, LAC4, LAC5, LOC6; clear LAC1 LAC2 LAC3 LAC4 LAC5 LOC6.
           repeat split; extensionality bb.
             rewrite (freshloc_alloc _ _ _ _ _ H3).
             rewrite <- (freshloc_trans m m'), (freshloc_alloc _ _ _ _ _ H3), (store_freshloc _ _ _ _ _ _ H4).
             rewrite orb_false_r. trivial.
             eapply alloc_forward; eassumption. eapply store_forward; eassumption.

             rewrite (freshloc_alloc _ _ _ _ _ TALLOC).
             rewrite <- (freshloc_trans tm tm'), (freshloc_alloc _ _ _ _ _ TALLOC), (store_freshloc _ _ _ _ _ _ ST').
             rewrite orb_false_r. trivial.
             eapply alloc_forward; eassumption. eapply store_forward; eassumption.

             rewrite (freshloc_alloc _ _ _ _ _ H3).
             rewrite <- (freshloc_trans m m'), (freshloc_alloc _ _ _ _ _ H3), (store_freshloc _ _ _ _ _ _ H4).
             rewrite orb_false_r. trivial.
             eapply alloc_forward; eassumption. eapply store_forward; eassumption.

             rewrite (freshloc_alloc _ _ _ _ _ TALLOC).
             rewrite <- (freshloc_trans tm tm'), (freshloc_alloc _ _ _ _ _ TALLOC), (store_freshloc _ _ _ _ _ _ ST').
             rewrite orb_false_r. trivial.
             eapply alloc_forward; eassumption. eapply store_forward; eassumption.

        split; intros; eapply store_forward; try eassumption.
          rewrite sm_locally_allocatedChar in LOCALLOC.
          destruct LOCALLOC as [LAC1 _]. unfold DOM in H2; rewrite LAC1 in H2; clear LAC1.
          rewrite (freshloc_alloc _ _ _ _ _ H3) in H2.
          destruct (eq_block b1 b); subst; simpl in *.
            eapply Mem.valid_new_block; eassumption.
          rewrite orb_false_r in H2. 
            eapply Mem.valid_block_alloc; try eassumption.
            eapply SMV; eassumption.

          rewrite sm_locally_allocatedChar in LOCALLOC.
          destruct LOCALLOC as [_ [LAC2 _]]. unfold RNG in H2; rewrite LAC2 in H2; clear LAC2.
          rewrite (freshloc_alloc _ _ _ _ _ TALLOC) in H2.
          destruct (eq_block b2 tb); subst; simpl in *.
            eapply Mem.valid_new_block; eassumption.
          rewrite orb_false_r in H2. 
            eapply Mem.valid_block_alloc; try eassumption.
            eapply SMV; eassumption.
      eapply (REACH_Store m'); try eassumption.
      intros. rewrite getBlocks_char in H5. destruct H5 as [zz [ZZ | ZZ]]; inv ZZ.
  (*case EF_free*)
    inv H0. inv H2. inv H9. inv H7.
    destruct (restrictD_Some _ _ _ _ _ H6) as [AIb VISb].
    exploit free_parallel_inject; try eassumption.
    intros [tm1 [TFR Inj1]].
    exploit (Mem.load_inject (as_inj mu) m); try eassumption.
    intros [v [TLD Vinj]]. inv Vinj.
    assert (Mem.range_perm m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
      eapply Mem.free_range_perm; eauto.
    exploit Mem.address_inject. eapply H1. 
      apply Mem.perm_implies with Freeable; auto with mem.
      apply H0. instantiate (1 := lo). omega.
      eassumption. 
    intro EQ.
    assert (Mem.range_perm tm b2 (Int.unsigned lo + delta - 4) (Int.unsigned lo + delta + Int.unsigned sz) Cur Freeable).
      red; intros. 
      replace ofs with ((ofs - delta) + delta) by omega.
      eapply Mem.perm_inject. eassumption. eassumption. eapply H0. omega.
(*    destruct (Mem.range_perm_free _ _ _ _ H2) as [m2' FREE].*)
    exists mu; eexists; exists tm1; split.
      simpl. econstructor.
       rewrite EQ. replace (Int.unsigned lo + delta - 4) with (Int.unsigned lo - 4 + delta) by omega.
       eauto. auto. 
      rewrite EQ. clear - TFR.
        assert (Int.unsigned lo + delta - 4 = Int.unsigned lo - 4 + delta). omega. rewrite H; clear H.
        assert (Int.unsigned lo + delta + Int.unsigned sz = Int.unsigned lo + Int.unsigned sz + delta). omega. rewrite H; clear H.
        assumption.
     intuition.  

     eapply Mem.free_unchanged_on; eauto. 
       unfold loc_unmapped; intros. congruence.

     eapply Mem.free_unchanged_on; eauto.   
       unfold loc_out_of_reach; intros. red; intros. eelim H8; eauto. 
       apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
       apply H0. omega.

     apply intern_incr_refl.
     apply sm_inject_separated_same_sminj.
     apply sm_locally_allocatedChar.
       repeat split; try extensionality bb; simpl.
       rewrite (freshloc_free _ _ _ _ _ H5). clear. intuition.
       rewrite (freshloc_free _ _ _ _ _ TFR). clear. intuition.
       rewrite (freshloc_free _ _ _ _ _ H5). clear. intuition.
       rewrite (freshloc_free _ _ _ _ _ TFR). clear. intuition.
     split; intros; eapply Mem.valid_block_free_1; try eassumption.
       eapply SMV; assumption. eapply SMV; assumption.
     eapply REACH_closed_free; eassumption.
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
  (*free*)
    simpl in EC. inv EC. 
    inv ArgsInj. inv H7. inv H5.
    rewrite H1. unfold free_Effect in H1.
    destruct (restrictD_Some _ _ _ _ _ H6) as [AIb VISb].
    exploit (Mem.load_inject (as_inj mu) m); try eassumption.
    intros [v [TLD Vinj]]. inv Vinj.
    assert (RP: Mem.range_perm m b0 (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
      eapply Mem.free_range_perm; eauto.
    exploit Mem.address_inject. eapply MINJ. 
      apply Mem.perm_implies with Freeable; auto with mem.
      apply RP. instantiate (1 := lo). omega.
      eassumption. 
    intro EQ.
    rewrite EQ in *.
    assert (Arith4: Int.unsigned lo - 4 + delta = Int.unsigned lo + delta - 4) by omega.
    rewrite Arith4, TLD in *.
    destruct (eq_block b b2); subst; simpl in *; try inv H1.
    rewrite H, H4.
    split. eapply visPropagateR; eassumption.
    intros. exists b0, delta.
    rewrite restrict_vis_foreign_local in H6; trivial.
    destruct (joinD_Some _ _ _ _ _ H6) as [FRG | [FRG LOC]]; clear H6.
    Focus 2. destruct (local_DomRng _ WD _ _ _ LOC). rewrite H5 in H1; discriminate.
    split; trivial.
    destruct (eq_block b0 b0); simpl in *.
    Focus 2. elim n; trivial. 
    clear e. 
        destruct (zlt 0 (Int.unsigned sz)); simpl in *; try inv H4.
        destruct (zle (Int.unsigned lo + delta - 4) ofs); simpl in *; try inv H5.
        destruct (zlt ofs (Int.unsigned lo + delta + Int.unsigned sz)); simpl in *; try inv H4.
        destruct (zle (Int.unsigned lo - 4) (ofs - delta)); simpl in *; try omega.
        split. destruct (zlt (ofs - delta) (Int.unsigned lo + Int.unsigned sz)); trivial.
                 omega. 
        eapply Mem.perm_implies. 
          eapply Mem.perm_max. eapply RP. split; trivial. omega.
          constructor. 
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
