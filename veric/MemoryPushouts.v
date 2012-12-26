Load loadpath.
Require Import veric.base.
Require Import Events.
Require Import veric.MemEvolve.

Lemma compose_meminjD_Some: forall j jj b b2 ofs2, 
       (compose_meminj j jj) b = Some(b2,ofs2) -> 
       exists b1, exists ofs1, exists ofs,
       j b = Some(b1,ofs1) /\ jj b1 = Some(b2,ofs) /\ ofs2=ofs1+ofs. 
Proof. unfold compose_meminj; intros.
       remember (j b) as z; destruct z; apply eq_sym in Heqz.
         destruct p. exists b0. exists z. 
         remember (jj b0) as zz. 
         destruct zz; apply eq_sym in Heqzz. 
           destruct p. inv H. exists z0. auto.
           inv H.
         inv H.
Qed. 

Lemma compose_meminj_inject_incr: forall j12 j12' j23 j23'
  (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23'),
  inject_incr (compose_meminj j12 j23) (compose_meminj j12' j23').
Proof.
  intros. intros b; intros. 
  apply compose_meminjD_Some in H. 
  destruct H as [b1 [ofs1 [ofs [Hb [Hb1 Hdelta]]]]]. 
  unfold compose_meminj.
  rewrite (InjIncr12 _ _ _ Hb).
  rewrite (InjIncr23 _ _ _ Hb1). subst. trivial.
Qed.

Lemma compose_meminj_inject_separated: forall j12 j12' j23 j23' m1 m2 m3
   (InjSep12 : inject_separated j12 j12' m1 m2)
   (InjSep23 : inject_separated j23 j23' m2 m3)
   (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23')
   (BV12: forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
   (BV23: forall b1 b2 ofs, j23 b1 = Some (b2,ofs) -> Mem.valid_block m2 b1 /\ Mem.valid_block m3 b2),
   inject_separated (compose_meminj j12 j23) (compose_meminj j12' j23') m1 m3.
Proof. intros.
  unfold compose_meminj; intros b; intros.
  remember (j12 b) as j12b.
  destruct j12b; inv H; apply eq_sym in Heqj12b. destruct p.
    rewrite (InjIncr12 _ _ _ Heqj12b) in H0.
    remember (j23 b0) as j23b0.
    destruct j23b0; inv H2; apply eq_sym in Heqj23b0. destruct p. inv H1.
    remember (j23' b0) as j23'b0.
    destruct j23'b0; inv H0; apply eq_sym in Heqj23'b0. destruct p. inv H1.
    destruct (InjSep23 _ _ _ Heqj23b0 Heqj23'b0).    
    split; trivial. exfalso. apply H. eapply BV12. apply Heqj12b.
  remember (j12' b) as j12'b.
  destruct j12'b; inv H0; apply eq_sym in Heqj12'b. destruct p.
    destruct (InjSep12 _ _ _ Heqj12b Heqj12'b). split; trivial.
    remember (j23' b0) as j23'b0.
    destruct j23'b0; inv H1; apply eq_sym in Heqj23'b0. destruct p. inv H3.
    remember (j23 b0) as j23b0.
    destruct j23b0; apply eq_sym in Heqj23b0. destruct p. rewrite (InjIncr23 _ _ _ Heqj23b0) in Heqj23'b0. inv Heqj23'b0.      
      exfalso. apply H0. eapply BV23. apply Heqj23b0.
    destruct (InjSep23 _ _ _ Heqj23b0 Heqj23'b0). assumption.    
Qed.

Lemma compose_meminj_inject_separated': forall j12 j12' j23 j23' m1 m2 m3
   (InjSep12 : inject_separated j12 j12' m1 m2)
   (InjSep23 : inject_separated j23 j23' m2 m3)
   (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23')
   (MInj12: Mem.inject j12 m1 m2)
   (MInj23: Mem.inject j23 m2 m3),
   inject_separated (compose_meminj j12 j23) (compose_meminj j12' j23') m1 m3.
Proof. intros.
  eapply compose_meminj_inject_separated; try eassumption.
  intros; split. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj12). apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj12).
  intros; split. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj23). apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj23).
Qed.

Lemma forall_lessdef_refl: forall vals,  Forall2 Val.lessdef vals vals.
Proof. induction vals; econstructor; trivial. Qed.

Lemma lessdef_hastype: forall v v' (V:Val.lessdef v v') T, Val.has_type v' T -> Val.has_type v T.
Proof. intros. inv V; simpl; trivial. Qed.

Lemma forall_lessdef_hastype: forall vals vals' (V:Forall2 Val.lessdef vals vals') Ts 
          (HTs: Forall2 Val.has_type vals' Ts), Forall2 Val.has_type vals Ts.
Proof.
  intros vals vals' V.
  induction V; simpl in *; intros.
       trivial.
  inv HTs. constructor. eapply  lessdef_hastype; eassumption. apply (IHV _ H4).
Qed.

Lemma valinject_hastype:  forall j v v' (V: (val_inject j) v v') T, Val.has_type v' T -> Val.has_type v T.
Proof. intros. inv V; simpl; trivial. Qed.

Lemma forall_valinject_hastype:  forall j vals vals' (V:  Forall2 (val_inject j) vals vals') 
                Ts (HTs: Forall2 Val.has_type vals' Ts), Forall2 Val.has_type vals Ts.
Proof.
  intros j vals vals' V.
  induction V; simpl in *; intros.
       trivial.
  inv HTs. constructor. eapply  valinject_hastype; eassumption. apply (IHV _ H4).
Qed.


Lemma forall_lessdef_trans: forall vals1 vals2 (V12: Forall2 Val.lessdef vals1 vals2) 
                                                               vals3  (V23: Forall2 Val.lessdef vals2 vals3) ,  Forall2 Val.lessdef vals1 vals3.
Proof. intros vals1 vals2 V12. 
   induction V12; intros; inv V23; econstructor.
   eapply Val.lessdef_trans; eauto.
          eapply IHV12; trivial.
Qed.

Lemma extends_loc_out_of_bounds: forall m1 m2 (Ext: Mem.extends m1 m2) b ofs,
                loc_out_of_bounds m2 b ofs -> loc_out_of_bounds m1 b ofs.
Proof. intros.
  inv Ext. inv mext_inj.
  intros N.  eapply H. apply (mi_perm _ b 0) in N. rewrite Zplus_0_r in N. assumption. reflexivity.
Qed.

Lemma extends_loc_out_of_reach: forall m1 m2 (Ext: Mem.extends m1 m2) b ofs j
               (Hj: loc_out_of_reach j m2 b ofs), loc_out_of_reach j m1 b ofs.
Proof. intros. unfold loc_out_of_reach in *. intros.
           intros N. eapply (Hj _ _ H). clear Hj H. inv Ext. inv mext_inj.
           specialize (mi_perm b0 _ 0 (ofs - delta) Max Nonempty (eq_refl _)). rewrite Zplus_0_r in mi_perm. apply (mi_perm N).
Qed.

Lemma valinject_lessdef: forall v1 v2 v3 j (V12:val_inject j v1 v2) (V23 : Val.lessdef v2 v3),val_inject j v1 v3.
Proof. intros. 
   inv V12; inv V23; try constructor.
    econstructor. eassumption. trivial.
Qed.

Lemma forall_valinject_lessdef: forall vals1 vals2 j (VInj12 : Forall2 (val_inject j) vals1 vals2) vals3 
                  (LD23 : Forall2 Val.lessdef vals2 vals3), Forall2 (val_inject j) vals1 vals3.
Proof. intros vals1 vals2 j VInj12.
   induction VInj12; intros; inv LD23. constructor.
     econstructor. eapply valinject_lessdef; eassumption.
          eapply (IHVInj12 _ H4).
Qed.

Lemma val_lessdef_inject_compose: forall v1 v2 (LD12 : Val.lessdef v1 v2) j v3
              (InjV23 : val_inject j v2 v3), val_inject j v1 v3.
Proof. intros. 
  apply val_inject_id in LD12.
  apply (val_inject_compose _ _ _ _ _ LD12) in InjV23.
  rewrite compose_idL in InjV23. assumption.
Qed. 

Lemma forall_val_lessdef_inject_compose: forall v1 v2 (LD12 : Forall2 Val.lessdef v1 v2) j v3
              (InjV23 : Forall2 (val_inject j) v2 v3), Forall2 (val_inject j) v1 v3.
Proof. intros v1 v2 H.
  induction H; intros; inv InjV23; econstructor.
       eapply val_lessdef_inject_compose; eassumption.
       apply (IHForall2 _ _ H5). 
Qed. 

Lemma inject_LOOR_LOOB: forall m1 m2 j (Minj12 : Mem.inject j m1 m2) m3 m3', 
  mem_unchanged_on (loc_out_of_reach j m1) m3 m3' -> mem_unchanged_on (loc_out_of_bounds m2) m3 m3'.
Proof. intros.
     split; intros; eapply H; trivial.
         intros b2; intros. unfold loc_out_of_bounds in H0. intros N. apply H0.
                          inv Minj12. inv mi_inj. apply (mi_perm _ _ _ _ _ _ H2) in N.
                         rewrite <- Zplus_comm in N. rewrite Zplus_minus in N.  apply N.
    intros. apply H0 in H2.
         intros b2; intros. unfold loc_out_of_bounds in H2. intros N. apply H2.
                          inv Minj12. inv mi_inj. apply (mi_perm _ _ _ _ _ _ H3) in N.
                         rewrite <- Zplus_comm in N. rewrite Zplus_minus in N.  apply N.
Qed.

Lemma forall_val_inject_compose: forall vals1 vals2 j1 (ValsInj12 : Forall2 (val_inject j1) vals1 vals2)
                vals3 j2 (ValsInj23 : Forall2 (val_inject j2) vals2 vals3),
              Forall2 (val_inject (compose_meminj j1 j2)) vals1 vals3.
Proof.
  intros vals1 vals2 j1 ValsInj12.
  induction ValsInj12; intros; inv ValsInj23; econstructor.
     eapply val_inject_compose; eassumption.
  apply (IHValsInj12 _ _ H4).
Qed.

Lemma val_inject_flat: forall m1 m2 j (Inj: Mem.inject j m1 m2) v1 v2 (V: val_inject j v1 v2),
                val_inject  (Mem.flat_inj (Mem.nextblock m1)) v1 v1.
Proof. intros.
  inv V; try constructor.
    apply val_inject_ptr with (delta:=0).
            unfold Mem.flat_inj. inv Inj.
            remember (zlt b1 (Mem.nextblock m1)).
            destruct s. trivial. assert (j b1 = None). apply mi_freeblocks. apply z. rewrite H in H0. inv H0.
            rewrite Int.add_zero. trivial.
Qed.

Lemma forall_val_inject_flat: forall m1 m2 j (Inj: Mem.inject j m1 m2) vals1 vals2
                (V: Forall2 (val_inject j) vals1 vals2),
                Forall2 (val_inject  (Mem.flat_inj (Mem.nextblock m1))) vals1 vals1.
Proof. intros.
  induction V; intros; try econstructor.
       eapply val_inject_flat; eassumption.
  apply IHV.
Qed.

Lemma extends_valvalid: forall m1 m2 (Ext: Mem.extends m1 m2) v,
        val_valid v m1 <-> val_valid v m2.
Proof. intros.
  split; intros. destruct v; simpl in *; try econstructor.
     eapply (Mem.valid_block_extends _ _ _ Ext). apply H. 
  destruct v; simpl in *; try econstructor.
     eapply (Mem.valid_block_extends _ _ _ Ext). apply H.
Qed.

Lemma mem_unchanged_on_refl: forall m f, mem_unchanged_on f m m.
Proof. intros. split; intros; trivial. Qed.

Lemma val_inject_split: forall v1 v3 j12 j23 (V: val_inject (compose_meminj j12 j23) v1 v3),
             exists v2, val_inject j12 v1 v2 /\ val_inject j23 v2 v3. 
Proof. intros. 
   inv V. 
     exists (Vint i). split; constructor.
     exists (Vfloat f). split; constructor. 
     apply compose_meminjD_Some in H. rename b2 into b3.
       destruct H as [b2 [ofs2 [ofs3 [J12 [J23 DD]]]]]; subst. 
       eexists. split. econstructor. apply J12. reflexivity. 
          econstructor. apply J23. rewrite Int.add_assoc. admit. (*ToDo: Check wrt overflow*) 
     exists Vundef. split; constructor.
Qed.     

Lemma inject_valvalid: forall j m1 m2 (Inj: Mem.inject j m1 m2) v2 (V:val_valid v2 m2) v1,
             val_inject j v1 v2 -> val_valid v1 m1.
Proof. intros.
  inv H. constructor. constructor.
     simpl in *. eapply Mem.valid_block_inject_1; eassumption. 
     constructor. 
Qed. 

(*
Module PUSHOUTS.
(*
Require Import veric.Address.
Require Import veric.sim.
Definition contents_at (m: mem) (loc: address) : memval := 
  ZMap.get (snd loc) (ZMap.get (fst loc) (Mem.mem_contents m)).

Definition access_at (m: mem) (loc: address) : option permission :=
   ZMap.get (fst loc) (Mem.mem_access m) (snd loc) Cur.  

Definition max_access_at (m: mem) (loc: address) : option permission :=
   ZMap.get (fst loc) (Mem.mem_access m) (snd loc) Max.  
*)

Section PO_EE.
(*Program Definition PO_EEmem:mem :=
  Mem.mkmem 
        (*content*) 
            (ZMap.init (ZMap.init Undef)) (*Todo: change this*)
        (*permissions*)
           (ZMap.init (fun ofs k => None))
        (*nextblock*)
           (Mem.nextblock m1')
        (*proof obligations*)  _ _ _ .
(*Definition PO_EE_cont: ZMap.t (ZMap.t memval).
    Proof. apply (@ZMap.map (Z -> memval)).
                    intros cont. Check ZMap.map. apply ZMap.map apply (ZMap.get b m1'.(Mem.mem_contents)).
                    eapply  ZMap.init. (fun b => None)).
Check (fun ofs => @ZMap.get memval ofs (ZMap.get b m1'.(Mem.mem_contents))).
                   intros b.*)
*)
(*
Lemma pushout_EE1: forall   m3 m3' v3 (Fwd3: Evolve m3 m3' v3 )
                 m1 m1' v1 (Fwd1: Evolve m1 m1' v1) m2 (Ext12: Mem.extends m1 m2)
                 (Ext23: Mem.extends m2 m3) (LD : Val.lessdef v1 v3) 
                                          (Ext13' : Mem.extends m1' m3')
                                          (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3'),
       exists m2',  Evolve m2 m2' v1 /\ Mem.extends m1' m2' /\ mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                                          Mem.extends m2' m3'.
Proof. intros m3 m3' v3 Fwd3.
  induction Fwd3; intros.
  (*EvolveVal*) rename m into m3. rename v into v3.
        exists m2. 
        split. apply EvolveVal. eapply val_valid_extends; eassumption.
        split. assumption.
        split. apply mem_unchanged_on_refl.
        intros m3 m3' v3 Fwd3.
         induction Fwd3; intros.
         (*EvolveVal*) assumption.
         (*EvolveAlloc*) rename m into m3. rename m'' into m3'. rename v into v3.
                 assert (Mem.nextblock m3 < Mem.nextblock m3').
                     apply Evolve_nextblock in Fwd3. apply Mem.nextblock_alloc in H0. rewrite H0 in Fwd3.  clear - Fwd3. omega.
                 assert (Mem.nextblock m3 = Mem.nextblock m3').
                     clear H0 Fwd3. destruct Ext23. rewrite <- mext_next. 
                                                destruct Ext12. rewrite <- mext_next0. 
                                                eapply Ext13'.
                exfalso. rewrite H2 in H1. clear - H1. omega.
        (*EvolveStore*) rename m into m3. rename m'' into m3'. rename v into v3. 
               unfold mem_unchanged_on in UnchOn3. unfold loc_out_of_bounds in UnchOn3.  rewrite <- mext_next0. 
destruct Ext13'. destruct Ext23. 
                    split; intros. rewrite <- mext_next0. rewrite mext_next. trivial.
                            split; intros. destruct mext_inj as [mi_perm12 _ _ ].
                                      destruct (Fwd3 b2). apply (Mem.valid_block_extends _ _ b2) in Ext23.
                                      eapply Ext23. inv H0. apply (Mem.perm_valid_block _ _ _ _ _ H1).
                                     
 eapply mext_inj0. apply H0. eapply mext_inj.
 *)
(*
Lemma pushout_EE: forall  m1 m1' v1 (Fwd1: Evolve m1 m1' v1) m2 (Ext12: Mem.extends m1 m2),
       exists m2',  Evolve m2 m2' v1 /\ Mem.extends m1' m2' /\ mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                          forall m3 m3' v3 (Fwd3: Evolve m3 m3' v3 ) (Ext23: Mem.extends m2 m3) (LD : Val.lessdef v1 v3) 
                                          (Ext13' : Mem.extends m1' m3')
                                          (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3'),
                                          Mem.extends m2' m3'.
Proof. intros m1 m1' v1 Fwd1.
  induction Fwd1; intros.
  (*EvolveVal*) rename m into m1. rename v into v1.
        exists m2. 
        split. apply EvolveVal. eapply val_valid_extends; eassumption.
        split. assumption.
        split. apply mem_unchanged_on_refl.
        intros m3 m3' v3 Fwd3.
         induction Fwd3; intros.
         (*EvolveVal*) assumption.
         (*EvolveAlloc*) rename m into m3. rename m'' into m3'. rename v into v3.
                 assert (Mem.nextblock m3 < Mem.nextblock m3').
                     apply Evolve_nextblock in Fwd3. apply Mem.nextblock_alloc in H0. rewrite H0 in Fwd3.  clear - Fwd3. omega.
                 assert (Mem.nextblock m3 = Mem.nextblock m3').
                     clear H0 Fwd3. destruct Ext23. rewrite <- mext_next. 
                                                destruct Ext12. rewrite <- mext_next0. 
                                                eapply Ext13'.
                exfalso. rewrite H2 in H1. clear - H1. omega.
        (*EvolveStore*) rename m into m3. rename m'' into m3'. rename v into v3. 
               unfold mem_unchanged_on in UnchOn3. unfold loc_out_of_bounds in UnchOn3.  rewrite <- mext_next0. 
destruct Ext13'. destruct Ext23. 
                    split; intros. rewrite <- mext_next0. rewrite mext_next. trivial.
                            split; intros. destruct mext_inj as [mi_perm12 _ _ ].
                                      destruct (Fwd3 b2). apply (Mem.valid_block_extends _ _ b2) in Ext23.
                                      eapply Ext23. inv H0. apply (Mem.perm_valid_block _ _ _ _ _ H1).
                                     
 eapply mext_inj0. apply H0. eapply mext_inj.
 
  

 inv Ext12. unfold mem_forward in Fwd1. inv mext_inj.
  (*exists PO_EEmem.*)
*)
Variable m1 m2 m1':mem.
Lemma pushout_EE: forall (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                          forall m3 (Ext23: Mem.extends m2 m3) m3' (Fwd3: mem_forward m3 m3') (Ext13' : Mem.extends m1' m3')
                                          (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3'),
                                          Mem.extends m2' m3'.
Proof. intros. inv Ext12. unfold mem_forward in Fwd1. inv mext_inj.
  (*exists PO_EEmem.*)
Admitted. (*We expect we can iteratively contruct m2' ie walk the blocks (and in the blocks, walk the ofs) to combine
  m1' with m2 pointwise using store operations of the memory model.
  The claim about m3 then (hopefully) follows by an induction on the construction, or is carried around in theproof of the first part*)

Definition pushout_EE_pointwise_contents (m2':mem) := 
        Mem.nextblock m2' = Mem.nextblock m1' 
        /\    forall b, if zlt b (Mem.nextblock m1)
                           then  forall k ofs p,
                                      (Mem.perm m2' b ofs k p  <->
                                           (Mem.perm m1' b ofs k p /\ Mem.perm m2 b ofs k p))
                                      /\
                                      (Mem.perm m1' b ofs k Readable ->
                                               (ZMap.get ofs (ZMap.get b m2'.(Mem.mem_contents)) = ZMap.get ofs (ZMap.get b m1'.(Mem.mem_contents))))
                                      /\  (~ Mem.perm m1' b ofs k Readable -> Mem.perm m2 b ofs k Readable ->
                                               (ZMap.get ofs (ZMap.get b m2'.(Mem.mem_contents)) = ZMap.get ofs (ZMap.get b m2.(Mem.mem_contents))))
                           else  (ZMap.get b m2'.(Mem.mem_contents) = ZMap.get b m1'.(Mem.mem_contents) /\
                                      (forall k ofs p,  Mem.perm m2' b ofs k p = Mem.perm m1' b ofs k p)).

Axiom pushoutEE_exists: exists m2',  pushout_EE_pointwise_contents m2'.
(*
Lemma po_EE:  forall (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                          forall m3 (Ext23: Mem.extends m2 m3) m3' (Fwd1: mem_forward m3 m3') 
                                          (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3'),
                                          Mem.extends m2' m3'.
Proof. intros.
  destruct pushoutEE_exists as [m2' [NB X]]. exists m2'.
  assert (Fwd2: mem_forward m2 m2').
            intros b; intros.
            assert (VB: Mem.valid_block m2' b).
                     clear X. unfold Mem.valid_block in *. rewrite NB. destruct Ext12. rewrite <- mext_next in H.
                     eapply (Fwd1 _ H).
            split; trivial.
            intros. specialize (X b). 
                remember (zlt b (Mem.nextblock m1)) as z.
                destruct z; apply eq_sym in Heqz.
                   destruct (X Max ofs p) as [P _]; clear X.
                      apply P. assumption.
                destruct X as [_ X]. rewrite X in H0.
                   unfold Mem.valid_block in *. destruct Ext12. rewrite <- mext_next in H.
                      clear - z H. exfalso. omega.
  split; trivial.
  assert (Ext12': Mem.extends m1' m2').
           split. clear X. rewrite NB. trivial.
           split; intros. 
                specialize (X b2). 
                remember (zlt b2 (Mem.nextblock m1)) as z.
                destruct z; apply eq_sym in Heqz.
                   destruct (X k (ofs + 0) p) as [P _]; clear X.
                      destruct Ext12. destruct mext_inj. specialize (mi_perm _ _ _ ofs k p H).
                      inv H. rewrite Zplus_0_r in *.
                      apply P. split; trivial. apply mi_perm. 
                      destruct (Fwd1 b2 z). apply H1.
                      destruct Ext12. destruct mext_inj. rewrite <- Zplus_0_r.
                      eapply (mi_perm b2 b2 0 _ _ _ (eq_refl _) ). H0).
                destruct X as [_ X]. rewrite X in H0.
                   unfold Mem.valid_block in *. destruct Ext12. rewrite <- mext_next in H.
                      clear - z H. exfalso. omega.
                   unfold mem_forward in Fwd1.

                   admit.
               *)

End PO_EE.

Section PO_EI.
Variable m1 m2 m1':mem. 
Lemma pushout_EI: forall (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                         forall j (UnchgdOn1: mem_unchanged_on (loc_unmapped j) m1 m1'),
                                       mem_unchanged_on (loc_unmapped j) m2 m2' /\
                                      forall m3 (Ext23: Mem.inject j m2 m3) m3' (Fwd1: mem_forward m3 m3') 
                                            (UnchOn3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3') j' 
                                             (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3) (Inj13': Mem.inject j' m1' m3'),
                                            Mem.inject j' m2' m3'.
Admitted. 
End PO_EI.

Section PO_IE.
Variable m1 m2 m1':mem. 
Lemma pushout_IE: forall j (Minj12 : Mem.inject j m1 m2) (Fwd1: mem_forward m1 m1') 
                          j' (InjInc: inject_incr j j')  (Sep12 : inject_separated j j' m1 m2) 
                          (UnchLUj: mem_unchanged_on (loc_unmapped j) m1 m1'),
exists m2',  Mem.inject j' m1' m2' /\ mem_forward m2 m2' /\
                    mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                    forall m3 m3' (Ext23 : Mem.extends m2 m3) (Fwd3: mem_forward m3 m3') 
                                             (UnchLOORj1_3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3'),
                                             Mem.extends m2' m3'.
Admitted.
End PO_IE.
End PUSHOUTS.
*)

Lemma po_trans: forall a b c, Mem.perm_order'' a b ->  Mem.perm_order'' b c ->
      Mem.perm_order'' a c.
Proof. intros.
   destruct a; destruct b; destruct c; simpl in *; try contradiction; try trivial.
   eapply perm_order_trans; eassumption.
Qed.

Lemma extends_perm: forall m1 m2 (Ext: Mem.extends m1 m2) b ofs k p,
   Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p.  
Proof. intros. destruct Ext. destruct mext_inj.
  specialize (mi_perm b b 0 ofs k p (eq_refl _) H).
  rewrite Zplus_0_r in mi_perm. assumption.
Qed.

Lemma extends_permorder: forall m1 m2 (Ext: Mem.extends m1 m2) b ofs k,
  Mem.perm_order'' (ZMap.get b (Mem.mem_access m2) ofs k)
                   (ZMap.get b (Mem.mem_access m1) ofs k).
Proof.
  intros. destruct Ext.  destruct mext_inj as [prm _ _].
  specialize (prm b b 0 ofs k). unfold Mem.perm in prm. 
  remember ((ZMap.get b (Mem.mem_access m2) ofs k)) as z.
  destruct z; apply eq_sym in Heqz; simpl  in *. 
    remember ((ZMap.get b (Mem.mem_access m1) ofs k)) as zz.
    destruct zz; trivial; apply eq_sym in Heqzz; simpl  in *.
       rewrite Zplus_0_r in prm. rewrite Heqz in prm. 
       specialize (prm p0 (eq_refl _)). apply prm. apply perm_refl. 
  remember ((ZMap.get b (Mem.mem_access m1) ofs k)) as zz.
    destruct zz; trivial; apply eq_sym in Heqzz; simpl  in *.
       rewrite Zplus_0_r in prm. rewrite Heqz in prm. 
       specialize (prm p (eq_refl _)). exfalso. apply prm. apply perm_refl. 
Qed.

Lemma fwd_maxperm: forall m1 m2 (FWD: mem_forward m1 m2) b 
  (V:Mem.valid_block m1 b) ofs p,
  Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Proof. intros. apply FWD; assumption. Qed. 

Lemma fwd_maxpermorder: forall m1 m2 (FWD: mem_forward m1 m2) b 
  (V:Mem.valid_block m1 b) ofs,
  Mem.perm_order'' (ZMap.get b (Mem.mem_access m1) ofs Max)
                   (ZMap.get b (Mem.mem_access m2) ofs Max).
Proof.
  intros. destruct (FWD b); try assumption. 
  remember ((ZMap.get b (Mem.mem_access m2) ofs Max)) as z.
  destruct z; apply eq_sym in Heqz; simpl  in *.
  remember ((ZMap.get b (Mem.mem_access m1) ofs Max)) as zz.
  destruct zz; apply eq_sym in Heqzz; simpl  in *.
  specialize (H0 ofs p).  unfold Mem.perm in H0. unfold Mem.perm_order' in H0. 
  rewrite Heqz in H0. rewrite Heqzz in H0. apply H0. apply perm_refl.
  specialize (H0 ofs p).  unfold Mem.perm in H0. unfold Mem.perm_order' in H0. 
  rewrite Heqz in H0. rewrite Heqzz in H0. apply H0. apply perm_refl.


  remember ((ZMap.get b (Mem.mem_access m1) ofs Max)) as zz.
  destruct zz; apply eq_sym in Heqzz; simpl in *; trivial.
Qed.

Lemma po_oo: forall p q, Mem.perm_order' p q = Mem.perm_order'' p (Some q).
Proof. intros. destruct p; trivial. Qed. 

Lemma load_E: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z),
  Mem.load chunk m b ofs = 
  if Mem.valid_access_dec m chunk b ofs Readable
  then Some(decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs ((ZMap.get b m.(Mem.mem_contents)))))
  else None.
Proof. intros. reflexivity. Qed.

Lemma extends_memwd: forall m1 m2 (Ext: Mem.extends m1 m2), mem_wd m2 -> mem_wd m1.
Proof.
  intros. eapply mem_wdI. intros.
  assert (Mem.perm m2 b ofs Cur Readable).
    eapply (Mem.perm_extends _ _ _ _ _ _ Ext R).
  assert (Mem.valid_block m2 b).
     apply (Mem.perm_valid_block _ _ _ _ _ H0). 
  destruct Ext. rewrite mext_next.
  assert (Mem.flat_inj (Mem.nextblock m2) b = Some (b,0)).
    apply flatinj_I. apply H1.
  destruct mext_inj. specialize (mi_memval b ofs b 0 (eq_refl _) R). rewrite Zplus_0_r in mi_memval.
  destruct H. specialize (mi_memval0 b ofs b 0 H2 H0). rewrite Zplus_0_r in mi_memval0. 
  remember (ZMap.get ofs (ZMap.get b (Mem.mem_contents m1))) as v.
  destruct v. constructor. constructor.
    econstructor. eapply flatinj_I. inv mi_memval. inv H4. rewrite Int.add_zero in H6. 
      rewrite <- H6 in mi_memval0. simpl in mi_memval0. inversion mi_memval0.
      apply flatinj_E in H4. apply H4. 
   rewrite Int.add_zero. reflexivity.
Qed. 

Definition AccessMap_EE_Property  (m1 m1' m2 m3':Mem.mem) 
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b, 
    (Mem.valid_block m2 b -> forall k ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get b AM ofs k = ZMap.get b m1'.(Mem.mem_access) ofs k) /\ 
         (~Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get b AM ofs k = ZMap.get b m2.(Mem.mem_access) ofs k))
     /\ (~ Mem.valid_block m2 b -> forall k ofs,
           ZMap.get b AM ofs k = ZMap.get b m3'.(Mem.mem_access) ofs k).
(*
Definition ContentMap_EE_Property (m1 m2 m3':Mem.mem) (CM:ZMap.t (ZMap.t memval)) :=
  forall b,
    (Mem.valid_block m2 b -> forall ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get ofs (ZMap.get b CM) = ZMap.get ofs (ZMap.get b m3'.(Mem.mem_contents))) /\ 
         (~Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get ofs (ZMap.get b CM) = ZMap.get ofs (ZMap.get b m2.(Mem.mem_contents))))
     /\ (~ Mem.valid_block m2 b -> forall ofs,
           ZMap.get ofs (ZMap.get b CM) = ZMap.get ofs (ZMap.get b m3'.(Mem.mem_contents))).
*)
Definition ContentMap_EE_Property (m1 m1' m2 m3':Mem.mem) (CM:ZMap.t (ZMap.t memval)) :=
  forall b, 
     (Mem.valid_block m1 b -> forall ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get ofs (ZMap.get b CM) = ZMap.get ofs (ZMap.get b m3'.(Mem.mem_contents))) /\ 
         (~Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get ofs (ZMap.get b CM) = ZMap.get ofs (ZMap.get b m2.(Mem.mem_contents)))) /\
     (~Mem.valid_block m1 b -> forall ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get ofs (ZMap.get b CM) = ZMap.get ofs (ZMap.get b m1'.(Mem.mem_contents))) /\ 
         (~Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get ofs (ZMap.get b CM) = ZMap.get ofs (ZMap.get b m2.(Mem.mem_contents)))).

Lemma EE_ok: forall (m1 m1' m2 m3 m3':Mem.mem) (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1')
             (Ext23: Mem.extends m2 m3) (Fwd3: mem_forward m3 m3') (Ext13' : Mem.extends m1' m3')
             (UnchOn13 :  mem_unchanged_on (loc_out_of_bounds m1) m3 m3')
(*also have this premise: (UnchOn23 :  mem_unchanged_on (loc_out_of_bounds m2) m3 m3')*)
             m2' (WD3': mem_wd m3')
             (NB: m2'.(Mem.nextblock)=m3'.(Mem.nextblock))
(*             (CONT:  ContentMap_EE_Property m1 m1' m2 m3' (m2'.(Mem.mem_contents))) *)
             (CONT: Mem.mem_contents m2' = Mem.mem_contents m3')
             (MaxAccess: AccessMap_EE_Property  m1 m1' m2 m3' (m2'.(Mem.mem_access))),
               mem_forward m2 m2' /\ Mem.extends m1' m2' /\ Mem.extends m2' m3' /\
                          mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                   (mem_wd m2 -> mem_wd m2').
Proof. intros.
assert (Fwd2: mem_forward m2 m2').
    split; intros.
     (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext23) in H. 
        apply Fwd3 in H. destruct H as[H _]. 
        unfold Mem.valid_block. rewrite NB. apply H.
      (*max*)
        destruct (MaxAccess b) as [X _].
        unfold Mem.perm in *. destruct (X H Max ofs). clear X MaxAccess.
        remember (Mem.perm_order'_dec (ZMap.get b (Mem.mem_access m1) ofs Max) Nonempty) as d.
        destruct d; clear Heqd.  
           clear H2. rewrite (H1 p0) in H0. clear H1. 
           rewrite po_oo in *.
           assert (ZZ:= fwd_maxpermorder _ _ Fwd1).
           apply (Mem.valid_block_extends _ _ b Ext12) in H. 
           assert (XX:= extends_permorder _ _ Ext12 b ofs Max).
           eapply po_trans. apply XX.
           eapply po_trans. apply (ZZ _ H). apply H0.
        clear H1. rewrite (H2 n) in H0. apply H0. 
split; trivial.
assert (Ext12':  Mem.extends m1' m2').  
    split. 
    (*nextblock*)
        rewrite NB. apply Ext13'.
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
            destruct k.
            (*MAX*)
              destruct (MaxAccess b1) as [Val Inval].
              unfold Mem.perm. rewrite po_oo.
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Max ofs); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. rewrite (H p0). apply H0. 
                clear H. rewrite (H1 n).
                   assert (ZZ:= fwd_maxpermorder _ _ Fwd1).
                   assert (XX:= extends_permorder _ _ Ext12 b2 ofs Max).
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z. 
                   eapply po_trans. apply XX.
                   eapply po_trans. apply (ZZ _ z). apply H0.
              clear Val. rewrite (Inval z).
                 eapply po_trans. apply (extends_permorder _ _ Ext13').
                                  apply H0.
             (*CUR*)
              destruct (MaxAccess b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Cur ofs); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm. rewrite (H p0). apply H0. 
                clear H. unfold Mem.perm. rewrite (H1 n). clear H1.
                   apply Mem.perm_max in H0.
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z. 
                   assert (ZZ:= fwd_maxperm _ _ Fwd1 _ z _ _ H0).
                   exfalso. apply n. eapply Mem.perm_implies. apply ZZ. apply perm_any_N.
              clear Val. unfold Mem.perm. rewrite po_oo in *. 
                 rewrite (Inval z Cur). clear Inval.
                 eapply po_trans. apply (extends_permorder _ _ Ext13').
                                  apply H0.
         (*mi_access*) unfold Mem.valid_access in *. destruct H0. inv H. rewrite Zplus_0_r.
             split; trivial. 
             intros off; intros. specialize (H0 _ H). 
              destruct (MaxAccess b2) as [Val Inval].
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Cur off); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 off Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm. rewrite (H2 p0). apply H0. 
                clear H. unfold Mem.perm. rewrite (H3 n). clear H1.
                   apply Mem.perm_max in H0.
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z. 
                   assert (ZZ:= fwd_maxperm _ _ Fwd1 _ z _ _ H0).
                   exfalso. apply n. eapply Mem.perm_implies. apply ZZ. apply perm_any_N.
              clear Val. unfold Mem.perm. rewrite po_oo in *. 
                 rewrite (Inval z Cur). clear Inval.
                 eapply po_trans. apply (extends_permorder _ _ Ext13').
                                  apply H0.
         (*mi_memval *) inv H. rewrite Zplus_0_r. rewrite CONT.
            destruct Ext13'. destruct mext_inj as [_ _ X]. 
            specialize (X b2 _ _ _ (refl_equal _) H0). rewrite Zplus_0_r in X. 
            apply X. 
         (*mi_memval  inv H. rewrite Zplus_0_r. 
            destruct (CONT b2) as [Val Inval]. 
            remember (zlt b2 (Mem.nextblock m1)) as z.
            destruct z. clear Inval. 
               destruct (Val z ofs) as [A B]. clear Val. 
               remember ( Mem.perm_dec m1 b2 ofs Max Nonempty) as zz.
               destruct zz.   
                  rewrite (A p). clear A B.
                  destruct Ext13'. destruct mext_inj as [_ _ X]. 
                  specialize (X b2 _ _ _ (refl_equal _) H0). rewrite Zplus_0_r in X. 
                  apply X.
               exfalso. apply n. eapply fwd_maxperm. apply Fwd1. apply z.
                 eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor.
    admit.
            clear Val. 
               destruct (Inval z ofs) as [A B]. clear Inval. 
               remember ( Mem.perm_dec m1 b2 ofs Max Nonempty) as zz.
               destruct zz.   
                  rewrite (A p). clear A B.
                  apply  memval_inject_id_refl. 
               rewrite (B n). clear A B.
               exfalso. apply n. eapply fwd_maxperm. apply Fwd1. apply z.
                 eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor.
               rewrite (B n). clear A B.
              destruct Ext13'. destruct mext_inj as [_ _ X]. 
              specialize (X b2 _ _ _ (refl_equal _) H0). rewrite Zplus_0_r in X. 
              apply X. 
            eapply (fwd_maxperm _ _ Fwd1).*)
split; trivial.
assert (Ext23': Mem.extends m2' m3').
    split. 
    (*nextblock*)
        apply NB. 
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
            destruct k.
            (*MAX*)
              destruct (MaxAccess b1) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Max ofs);  clear Val.
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d.
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm in *. rewrite (H p0) in H0. clear H p0.
                   destruct Ext13'. destruct mext_inj as [mperm _ _].
                   unfold Mem.perm in mperm. 
                   specialize (mperm b2 b2 0 ofs Max p (eq_refl _)).
                   rewrite Zplus_0_r in mperm. 
                   apply mperm. apply H0.
                clear H. unfold Mem.perm in *. rewrite (H1 n) in H0. clear H1.
                   eapply UnchOn13. apply n.
                   destruct Ext23. destruct mext_inj as [mperm _ _].
                   apply (mperm b2 b2 0) in H0. rewrite Zplus_0_r in H0. assumption.
                        reflexivity.
              clear Val. unfold Mem.perm in H0. rewrite (Inval z Max ofs) in H0. apply H0.
             (*CUR*)
              destruct (MaxAccess b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Cur ofs); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (H p0) in H0; clear H. 
                   eapply po_trans. eapply (extends_permorder _ _ Ext13' b2 ofs Cur).
                   apply H0. 
                clear H. 
                   eapply UnchOn13. apply n.
                   unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (H1 n) in H0; clear H1. 
                   apply (Mem.valid_block_extends _ _ b2 Ext23) in z. 
                   eapply po_trans. apply (extends_permorder _ _ Ext23 b2 ofs Cur). 
                       apply H0. 
              clear Val. unfold Mem.perm in *. rewrite po_oo in *. 
                 rewrite (Inval z Cur) in H0. clear Inval. apply H0.
         (*mi_access*) unfold Mem.valid_access in *. destruct H0. inv H. rewrite Zplus_0_r.
             split; trivial. 
             intros off; intros. specialize (H0 _ H). clear H.
              destruct (MaxAccess b2) as [Val Inval].
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Cur off); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 off Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (H p0) in H0; clear H. 
                   eapply po_trans. eapply (extends_permorder _ _ Ext13' b2 off Cur).
                   apply H0. 
                clear H. 
                   eapply UnchOn13. apply n.
                   unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (H2 n) in H0; clear H2. 
                   apply (Mem.valid_block_extends _ _ b2 Ext23) in z. 
                   eapply po_trans. apply (extends_permorder _ _ Ext23 b2 off Cur). 
                       apply H0. 
              clear Val. unfold Mem.perm in *. rewrite po_oo in *. 
                 rewrite (Inval z Cur) in H0. clear Inval. apply H0.
         (*mi_memval *) inv H. rewrite Zplus_0_r. rewrite CONT. 
            assert (ZZ: Mem.perm m3' b2 ofs Cur Readable). 
               destruct (MaxAccess b2) as [Val Inval].
               remember (zlt b2 (Mem.nextblock m2)) as z.
               destruct z. clear Inval. destruct (Val z Cur ofs); clear Val Heqz. 
                 remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                 destruct d; clear Heqd.  
                    clear H1. unfold Mem.perm in *. rewrite po_oo in *. 
                    rewrite (H p) in H0; clear H. 
                    eapply po_trans. apply (extends_permorder _ _ Ext13'). apply H0. 
                 clear H. unfold Mem.perm in *. rewrite (H1 n) in H0. clear H1.
                   eapply UnchOn13. apply n.
                   unfold Mem.perm. rewrite po_oo in *.  
                   eapply po_trans. apply (extends_permorder _ _ Ext23). apply H0.
               clear Val. unfold Mem.perm in *. rewrite po_oo in *. 
                  rewrite (Inval z) in H0. apply H0.
                  apply memval_inject_id_refl.
                  (*assert (WD: mem_wd m3'). admit.
                  destruct WD as [_ _ X].
                  assert (VAL:= Mem.perm_valid_block _ _ _  _ _ ZZ). 
                  assert (VV: Mem.flat_inj (Mem.nextblock m3') b2 = Some (b2, 0)). 
                    unfold Mem.flat_inj. unfold Mem.valid_block in VAL. 
                    destruct (zlt b2  (Mem.nextblock m3')). trivial.
                     clear - z VAL. exfalso. omega. 
                  specialize (X b2 ofs b2 0 VV ZZ). rewrite Zplus_0_r in *.
                  destruct X. constructor.
                    apply flatinj_E in H. destruct H as [? [? ?]]; subst.
                    econstructor. reflexivity. repeat rewrite Int.add_zero. trivial. 
                    destruct mv; try econstructor.
                       reflexivity. repeat rewrite Int.add_zero. trivial. *)
split; trivial.
assert (WD2: mem_wd m2').
  intros. eapply (extends_memwd _ _ Ext23' WD3'). 
split; intros; trivial.
(*mem_unchanged_on (loc_out_of_bounds m1) m2 m2'*)
     destruct UnchOn13 as [Unch1 Unch2].
     split; intros. clear Unch2.
        unfold loc_out_of_bounds in *.
        assert (XX:= extends_perm _ _ Ext23 _ _ _ _ H0).
        specialize (Unch1 _ _ k p H XX). 
          destruct (MaxAccess b) as [Val _].
          unfold Mem.perm.
          destruct (Val (Mem.perm_valid_block _ _ _ _ _ H0) k ofs) as [_ X]; clear Val.  
          rewrite (X H); clear X. apply H0. 
   unfold loc_out_of_bounds in H.
   admit. (*ToDo: explore whether ContentMap_EE_Property works
      rewrite load_E.
      destruct (MaxAccess b) as [Val Inval]. rewrite load_E in *. clear Unch1 Unch2.
        unfold loc_out_of_bounds in *.
        remember (Mem.valid_access_dec m2 chunk b ofs Readable) as z.
        destruct z. inv H0. destruct v0. unfold Mem.range_perm in *.
          assert (BValid2: Mem.valid_block m2 b).
            eapply Mem.perm_valid_block. apply (r ofs). 
               split. omega. destruct chunk; simpl; omega. 
          clear Inval; specialize (Val BValid2). 
          remember (Mem.valid_access_dec m2' chunk b ofs Readable) as zz. 
          destruct zz. xx Print size_chunk.     specialize (Val _ 
      assert (X: Mem.load chunk m3' b ofs = Some v). 
        apply (Unch2 _ _ _ v H). clear Unch2 MaxAccess H. 
        assert (XX:= Mem.load_extends _ _ _ _ _ _ Ext23 H0).
        rewrite load_E in *. 
        remember (Mem.valid_access_dec m2 chunk b ofs Readable) as z.
        destruct z; inv H0. 
        destruct Ext23. destruct mext_inj.
           clear Heqz. apply (mi_access b b 0) in v0; try reflexivity.
           rewrite Zplus_0_r in *. 
           remember (Mem.valid_access_dec m3 chunk b ofs Readable) as zz.
             destruct zz. Focus 2. exfalso. apply (n v0). SearchAbout Mem.load. 
             unfold Mem.getN. inv H0. 
      assert (X: Mem.load chunk m3' b ofs = Some v). 
      rewrite load_E in *. 
        remember (Mem.valid_access_dec m2 chunk b ofs Readable) as z.
        destruct z. unfold Mem.valid_access in v0. inv H0; clear Heqz. destruct v0. admit. *)
Qed.
 
Parameter mkAccessMap_EE_exists: 
           forall (m1 m1' m2 m3':Mem.mem), ZMap.t (Z -> perm_kind -> option permission).
Axiom mkAccessMap_EE_ok: forall m1 m1' m2 m3', 
      AccessMap_EE_Property m1 m1' m2 m3' (mkAccessMap_EE_exists m1 m1' m2 m3').

Definition mkEE (m1 m1' m2 m3 m3':Mem.mem) (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1')
                (Ext23: Mem.extends m2 m3) (Fwd3: mem_forward m3 m3') (Ext13' : Mem.extends m1' m3')
                (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3') : Mem.mem'.
eapply Mem.mkmem with (nextblock:=m3'.(Mem.nextblock))
                      (mem_access:=mkAccessMap_EE_exists m1 m1' m2 m3').
(* (NB: forall b, Mem.valid_block m2 b -> Mem.valid_block m3' b)*)
  apply m3'.(Mem.mem_contents).
  apply m3'.
  (*access_max*)
  intros. destruct (mkAccessMap_EE_ok m1 m1' m2 m3' b) as [Val Inval].
    remember (zlt b m2.(Mem.nextblock)) as z. 
    destruct z; clear Heqz.
    (*Case valid*) clear Inval.
        specialize (Val z). 
        destruct (Val Max ofs) as [MaxA MaxB].
        destruct (Val Cur ofs) as [CurA CurB]. clear Val. 
        remember (Mem.perm_dec m1 b ofs Max Nonempty) as zz.
        destruct zz; clear Heqzz.
          rewrite (CurA p). rewrite (MaxA p). apply m1'.
          rewrite (CurB n). rewrite (MaxB n). apply m2. (*apply m3'.*)
    (*Case invalid*) clear Val.
        specialize (Inval z). 
        rewrite (Inval Max ofs).
        rewrite (Inval Cur ofs). apply m3'. 
  (*nextblock_noaccess*)
    intros.  destruct (mkAccessMap_EE_ok m1 m1' m2 m3' b) as [_ Inval].
    rewrite Inval. apply m3'. apply H. 
    clear Inval Ext12 Fwd1 Ext13'. intros N. destruct Ext23. 
      unfold mem_forward, Mem.valid_block in *. 
      rewrite mext_next in N.
      apply Fwd3 in N.  destruct N as [X _]. clear - H X. omega.
Defined.

Lemma interpolate_EE: forall m1 m2 (Ext12: Mem.extends m1 m2) m1' 
            (Fwd1: mem_forward m1 m1') m3 (Ext23: Mem.extends m2 m3) m3' 
            (Fwd3: mem_forward m3 m3') (Ext13' : Mem.extends m1' m3')
            (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3') 
            (WD3': mem_wd m3'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ Mem.extends m2' m3' /\
                   mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                  (mem_wd m2 -> mem_wd m2').
Proof. intros.
   assert (NB:forall b, Mem.valid_block m2 b -> Mem.valid_block m3' b).
      intros. apply Fwd3. destruct Ext23. unfold Mem.valid_block. rewrite <- mext_next. apply H.
   exists (mkEE m1 m1' m2 m3 m3' Ext12 Fwd1 Ext23 Fwd3 Ext13' UnchOn3).
     eapply (EE_ok m1 m1' m2 m3 m3'); trivial.
     apply mkAccessMap_EE_ok.  
Qed. 
(*
Lemma inject_None_block_invalid: forall j m1 m2 (Inj: Mem.inject j m1 m2) b
   (N:  None = j b), ~ Mem.valid_block m1 b.     
Proof. intros. destruct Inj. destruct mi_inj as [prm _ _ ]. apply eq_sym in J.estruct Inj. destruct mi_inj as [prm _ _ ]. apply eq_sym in J.

Lemma inject_perm: forall j m1 m2 (Inj: Mem.inject j m1 m2) b b' ofs' 
   (J: Some (b', ofs') = j b) ofs k p,
   Mem.perm m1 b ofs k p -> Mem.perm m2 b' (ofs+ofs') k p.  
Proof. intros. eapply Inj. apply (eq_sym J). assumption. 
Qed.*)

Lemma inject_permorder: forall j m1 m2 (Inj : Mem.inject j m1 m2) b b' ofs'
      (J: Some (b', ofs') = j b) ofs k,
     Mem.perm_order'' (ZMap.get b' (Mem.mem_access m2) (ofs + ofs') k)
     (ZMap.get b (Mem.mem_access m1) ofs k).
Proof.
  intros. destruct Inj. destruct mi_inj as [prm _ _ ]. apply eq_sym in J.
  specialize (prm b b' ofs' ofs k). unfold Mem.perm in prm. 
  remember ((ZMap.get b' (Mem.mem_access m2) (ofs + ofs') k)) as z.
  destruct z; apply eq_sym in Heqz; simpl  in *. 
    remember ((ZMap.get b (Mem.mem_access m1) ofs k)) as zz.
    destruct zz; trivial; apply eq_sym in Heqzz; simpl  in *.
       eapply prm. apply J. apply perm_refl. 
  remember ((ZMap.get b (Mem.mem_access m1) ofs k)) as zz.
    destruct zz; trivial; apply eq_sym in Heqzz; simpl  in *.
       eapply prm. apply J. apply perm_refl. 
Qed.

Definition AccessMap_EI_Property  (m1 m1' m2 m3':Mem.mem) (j':meminj)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b, 
    (Mem.valid_block m2 b -> forall k ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get b AM ofs k = ZMap.get b m1'.(Mem.mem_access) ofs k) /\ 
         (~Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get b AM ofs k = ZMap.get b m2.(Mem.mem_access) ofs k))
     /\ (~ Mem.valid_block m2 b -> forall k ofs, 
           match j' b with 
              None => ZMap.get b AM ofs k = 
                      ZMap.get b m1'.(Mem.mem_access) ofs k
           | Some(b',ofs') => ZMap.get b AM ofs k = 
                              ZMap.get b' m3'.(Mem.mem_access) (ofs + ofs') k
           end).

Definition ContentMap_EI_Property (m1 m1' m2 m3':Mem.mem) (j':meminj) (CM:ZMap.t (ZMap.t memval)) :=
  forall b,
    (Mem.valid_block m2 b -> forall ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
               ZMap.get ofs (ZMap.get b CM) = 
               ZMap.get ofs (ZMap.get b m1'.(Mem.mem_contents))) /\ 
         (~Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get ofs (ZMap.get b CM) = ZMap.get ofs (ZMap.get b m2.(Mem.mem_contents))))
     /\ (~ Mem.valid_block m2 b -> forall ofs, 
              ZMap.get ofs (ZMap.get b CM) =
              ZMap.get ofs (ZMap.get b m1'.(Mem.mem_contents)))(*
          match j' b with 
             None => ZMap.get ofs (ZMap.get b CM) = Undef
           | Some(b',ofs') => ZMap.get ofs (ZMap.get b CM) = 
                              ZMap.get (ofs + ofs') (ZMap.get b' m3'.(Mem.mem_contents))
          end)*).
(*
Lemma EI_ok: forall (m1 m1' m2 m3 m3':Mem.mem) (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1')
             j23 (Inj23: Mem.inject j23 m2 m3) (Fwd3: mem_forward m3 m3') 
             j' (Inj13' : Mem.inject j' m1' m3')
             (UnchOn3: mem_unchanged_on (loc_out_of_reach j23 m1) m3 m3') 
             (InjInc: inject_incr j23 j') (InjSep: inject_separated j23 j' m1 m3)
             (UnchOn1: mem_unchanged_on (loc_unmapped j23) m1 m1')
             m2'
             (NB: m1'.(Mem.nextblock)=m2'.(Mem.nextblock))
             (CONT:  ContentMap_EI_Property m1 m1' m2 m3' j' (m2'.(Mem.mem_contents)))
             (MaxAccess: AccessMap_EI_Property  m1 m1' m2 m3' j' (m2'.(Mem.mem_access))),
       mem_forward m2 m2' /\ Mem.extends m1' m2' /\ Mem.inject j' m2' m3' /\
                   mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                   mem_unchanged_on (loc_unmapped j23) m2 m2'.
Proof. intros.
assert (Fwd2: mem_forward m2 m2').
    split; intros.
     (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext12) in H. 
        apply Fwd1 in H. destruct H as[H _]. 
        unfold Mem.valid_block. rewrite <- NB. apply H.
      (*max*)
        destruct (MaxAccess b) as [X _].
        unfold Mem.perm in *. destruct (X H Max ofs). clear X MaxAccess.
        remember (Mem.perm_order'_dec (ZMap.get b (Mem.mem_access m1) ofs Max) Nonempty) as d.
        destruct d; clear Heqd.  
           clear H2. rewrite (H1 p0) in H0. clear H1. 
           rewrite po_oo in *.
           assert (ZZ:= fwd_maxpermorder _ _ Fwd1).
           apply (Mem.valid_block_extends _ _ b Ext12) in H. 
           assert (XX:= extends_permorder _ _ Ext12 b ofs Max).
           eapply po_trans. apply XX.
           eapply po_trans. apply (ZZ _ H). apply H0.
        clear H1. rewrite (H2 n) in H0. apply H0. 
split; trivial.
assert (Ext12':  Mem.extends m1' m2').  
    split. 
    (*nextblock*)
        apply NB. 
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
            destruct k.
            (*MAX*)
              destruct (MaxAccess b1) as [Val Inval].
              unfold Mem.perm. rewrite po_oo.
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Max ofs); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. rewrite (H p0). apply H0. 
                clear H. rewrite (H1 n).
                   assert (ZZ:= fwd_maxpermorder _ _ Fwd1).
                   assert (XX:= extends_permorder _ _ Ext12 b2 ofs Max).
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z. 
                   eapply po_trans. apply XX.
                   eapply po_trans. apply (ZZ _ z). apply H0.
              clear Val Heqz.
                 specialize (Inval z Max ofs).
                 remember (j' b2) as x.
                 destruct x.
                   (*Some p0*) destruct p0 as [b' ofs'].
                      rewrite Inval. clear Inval.
                      eapply po_trans. apply (inject_permorder _ _ _ Inj13' _ _ _ Heqx).
                                  apply H0.
                   (*None*) rewrite Inval. apply H0. 
            (*CUR*)
              destruct (MaxAccess b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Cur ofs); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm. rewrite (H p0). apply H0. 
                clear H. unfold Mem.perm. rewrite (H1 n). clear H1.
                   apply Mem.perm_max in H0.
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z. 
                   assert (ZZ:= fwd_maxperm _ _ Fwd1 _ z _ _ H0).
                   exfalso. apply n. eapply Mem.perm_implies. apply ZZ. apply perm_any_N.
              clear Val. unfold Mem.perm. rewrite po_oo in *.
                 specialize (Inval z Cur ofs). 
                 remember (j' b2) as x.
                 destruct x.
                   (*Some p0*) destruct p0 as [b' ofs']. rewrite Inval; clear Inval.  
                      eapply po_trans.  apply (inject_permorder _ _ _ Inj13' _ _ _ Heqx).
                                  apply H0. 
                   (*None*) rewrite Inval. apply H0.
         (*mi_access*) unfold Mem.valid_access in *. destruct H0. inv H. rewrite Zplus_0_r.
             split; trivial. 
             intros off; intros. specialize (H0 _ H). 
              destruct (MaxAccess b2) as [Val Inval].
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Cur off); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 off Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm. rewrite (H2 p0). apply H0. 
                clear H. unfold Mem.perm. rewrite (H3 n). clear H1.
                   apply Mem.perm_max in H0.
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z. 
                   assert (ZZ:= fwd_maxperm _ _ Fwd1 _ z _ _ H0).
                   exfalso. apply n. eapply Mem.perm_implies. apply ZZ. apply perm_any_N.
              clear Val. unfold Mem.perm. rewrite po_oo in *. 
                 specialize (Inval z Cur off). 
                 remember (j' b2) as x.
                 destruct x.
                   (*Some p0*) destruct p0 as [b' ofs']. rewrite Inval; clear Inval.  
                      eapply po_trans.  apply (inject_permorder _ _ _ Inj13' _ _ _ Heqx).
                                  apply H0. 
                   (*None*) rewrite Inval. apply H0.
         (*mi_memval *) inv H. rewrite Zplus_0_r. 
            destruct (CONT b2) as [Val Inval]. 
            remember (zlt b2 (Mem.nextblock m2)) as z. 
            destruct z. 
            (*Val*) clear Inval.
              assert (ZZ:Mem.perm m1 b2 ofs Max Nonempty). 
                eapply Fwd1. apply (Mem.valid_block_extends _ _ _ Ext12). apply z. 
                eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor. 
              destruct (Val z ofs) as [X _]. clear Val. rewrite (X ZZ); clear X ZZ.
              apply memval_inject_id_refl.
            (*Inval*) clear Val.  specialize (Inval z ofs).
               rewrite Inval.
               apply memval_inject_id_refl.  
split; trivial.
assert (Ext23': Mem.inject j' m2' m3').
    split. 
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
            destruct k.
            (*MAX*)
              destruct (MaxAccess b1) as [Val Inval].
              remember (zlt b1 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Max ofs) as [NonEmp Emp]; clear Val.
                remember (Mem.perm_dec m1 b1 ofs Max Nonempty) as d.
                destruct d; clear Heqd.  
                   clear Emp. unfold Mem.perm in *. rewrite (NonEmp p0) in H0. clear NonEmp p0.
                   destruct Inj13'. destruct mi_inj as [mperm _ _].
                   unfold Mem.perm in mperm. eapply mperm. apply H. apply H0.
                clear NonEmp. unfold Mem.perm in *. rewrite (Emp n) in H0. clear Emp.
                   assert (J: j23 b1 = Some(b2,delta)).
                     remember (j23 b1) as zz.
                     destruct zz; apply eq_sym in Heqzz.
                        destruct p0. apply InjInc in Heqzz. rewrite Heqzz in H. apply H.
                     destruct (InjSep _ _ _ Heqzz H) as [Z _].
                        exfalso. apply Z. eapply (Mem.valid_block_extends _ _ _ Ext12). apply z.
                   apply eq_sym in H. rewrite po_oo in *.
                   destruct UnchOn3 as [UnchOn3A _]. 
                   specialize (UnchOn3A b2 (ofs + delta) Max p). unfold Mem.perm in UnchOn3A.
                   rewrite po_oo in UnchOn3A. eapply UnchOn3A. clear UnchOn3A.
                      intros b; intros.
                      remember (ZMap.get b1 (Mem.mem_access m1) ofs Max) as zz. 
                      destruct zz. exfalso. apply n. apply perm_any_N. intros N. apply n. 
                      assert (Z:= extends_permorder _ _ Ext12). unfold Mem.perm in *. 
                      rewrite po_oo in *. unfold loc_out_of_reach. 
                   destruct Inj23. destruct mi_inj as [mperm _ _]. 
                   specialize (mperm b1 b2 delta ofs Max p J). unfold Mem.perm in mperm.
                   rewrite po_oo in mperm.
Admitted.
                  admit.(*
                   eapply mperm. apply H0. 
              clear Val. unfold Mem.perm in H0. specialize (Inval z Max ofs). 
                  rewrite H in Inval. rewrite Inval in H0. apply H0.
continue here     *)        (*CUR*)
              destruct (MaxAccess b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Cur ofs); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (H p0) in H0; clear H. 
                   eapply po_trans. eapply (extends_permorder _ _ Ext13' b2 ofs Cur).
                   apply H0. 
                clear H. 
                   eapply UnchOn13. apply n.
                   unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (H1 n) in H0; clear H1. 
                   apply (Mem.valid_block_extends _ _ b2 Ext23) in z. 
                   eapply po_trans. apply (extends_permorder _ _ Ext23 b2 ofs Cur). 
                       apply H0. 
              clear Val. unfold Mem.perm in *. rewrite po_oo in *. 
                 rewrite (Inval z Cur) in H0. clear Inval. apply H0.
         (*mi_access*) unfold Mem.valid_access in *. destruct H0. inv H. rewrite Zplus_0_r.
             split; trivial. 
             intros off; intros. specialize (H0 _ H). clear H.
              destruct (MaxAccess b2) as [Val Inval].
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z Cur off); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 off Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (H p0) in H0; clear H. 
                   eapply po_trans. eapply (extends_permorder _ _ Ext13' b2 off Cur).
                   apply H0. 
                clear H. 
                   eapply UnchOn13. apply n.
                   unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (H2 n) in H0; clear H2. 
                   apply (Mem.valid_block_extends _ _ b2 Ext23) in z. 
                   eapply po_trans. apply (extends_permorder _ _ Ext23 b2 off Cur). 
                       apply H0. 
              clear Val. unfold Mem.perm in *. rewrite po_oo in *. 
                 rewrite (Inval z Cur) in H0. clear Inval. apply H0.
         (*mi_memval *) inv H. rewrite Zplus_0_r. rewrite CONT. 
            assert (ZZ: Mem.perm m3' b2 ofs Cur Readable). 
               destruct (MaxAccess b2) as [Val Inval].
               remember (zlt b2 (Mem.nextblock m2)) as z.
               destruct z. clear Inval. destruct (Val z Cur ofs); clear Val Heqz. 
                 remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                 destruct d; clear Heqd.  
                    clear H1. unfold Mem.perm in *. rewrite po_oo in *. 
                    rewrite (H p) in H0; clear H. 
                    eapply po_trans. apply (extends_permorder _ _ Ext13'). apply H0. 
                 clear H. unfold Mem.perm in *. rewrite (H1 n) in H0. clear H1.
                   eapply UnchOn13. apply n.
                   unfold Mem.perm. rewrite po_oo in *.  
                   eapply po_trans. apply (extends_permorder _ _ Ext23). apply H0.
               clear Val. unfold Mem.perm in *. rewrite po_oo in *. 
                  rewrite (Inval z) in H0. apply H0.
assert (WD: mem_wd m3'). admit.
                  destruct WD as [_ _ X].
                  assert (VAL:= Mem.perm_valid_block _ _ _  _ _ ZZ). 
                  assert (VV: Mem.flat_inj (Mem.nextblock m3') b2 = Some (b2, 0)). 
                    unfold Mem.flat_inj. unfold Mem.valid_block in VAL. 
                    destruct (zlt b2  (Mem.nextblock m3')). trivial.
                     clear - z VAL. exfalso. omega. 
                  specialize (X b2 ofs b2 0 VV ZZ). rewrite Zplus_0_r in *.
                  destruct X. constructor.
                    apply flatinj_E in H. destruct H as [? [? ?]]; subst.
                    econstructor. reflexivity. repeat rewrite Int.add_zero. trivial. 
                    destruct mv; try econstructor.
                       reflexivity. repeat rewrite Int.add_zero. trivial. 
split; trivial.
(*mem_unchanged_on (loc_out_of_bounds m1) m2 m2'*)
     destruct UnchOn13 as [Unch1 Unch2].
     split; intros. clear Unch2.
        unfold loc_out_of_bounds in *.
        assert (XX:= extends_perm _ _ Ext23 _ _ _ _ H0).
        specialize (Unch1 _ _ k p H XX). 
          destruct (MaxAccess b) as [Val _].
          unfold Mem.perm.
          destruct (Val (Mem.perm_valid_block _ _ _ _ _ H0) k ofs) as [_ X]; clear Val.  
          rewrite (X H); clear X. apply H0. 
   admit.
*)

Lemma interpolate_EI: forall (m1 m2 m1':mem) (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1')
                              m3 j (Ext23: Mem.inject j m2 m3) m3' (Fwd3: mem_forward m3 m3') j'
                             (Inj13': Mem.inject j' m1' m3')
                             (UnchOn3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
                             (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
                             (UnchOn1: mem_unchanged_on (loc_unmapped j) m1 m1') (WD2: mem_wd m2)
                             (WD3': mem_wd m3'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ Mem.inject j' m2' m3' /\ 
                   mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                   mem_unchanged_on (loc_unmapped j) m2 m2' /\
                   (mem_wd m2 -> mem_wd m2').
Admitted. 

Lemma interpolate_IE: forall m1 m1' m2 j (Minj12 : Mem.inject j m1 m2) (Fwd1: mem_forward m1 m1') 
                             j' (InjInc: inject_incr j j')  (Sep12 : inject_separated j j' m1 m2) 
                             (UnchLUj: mem_unchanged_on (loc_unmapped j) m1 m1')
                             m3 m3' (Ext23 : Mem.extends m2 m3) (Fwd3: mem_forward m3 m3') 
                             (UnchLOORj1_3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3')
                             (Inj13' : Mem.inject j' m1' m3')
                             (UnchLOOB23_3' : mem_unchanged_on (loc_out_of_bounds m2) m3 m3')
                             (WD2: mem_wd m2) (WD1' : mem_wd m1') (WD3': mem_wd m3'),
                 exists m2', Mem.inject j' m1' m2' /\ mem_forward m2 m2' /\ Mem.extends m2' m3' /\
                             mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                             (mem_wd m2 -> mem_wd m2').                                         
Admitted.

Lemma interpolate_II: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1' (Fwd1: mem_forward m1 m1') j23 m3
                             (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
                             j' (MInj13': Mem.inject j' m1' m3')
                             (InjIncr: inject_incr (compose_meminj j12 j23) j')
                             (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                             (Unch11': mem_unchanged_on (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                             (Unch33': mem_unchanged_on (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3')
                             (WD1: mem_wd m1) (WD1': mem_wd m1') (WD2: mem_wd m2) (WD3: mem_wd m3) (WD3' : mem_wd m3'),
                 exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                             inject_incr j12 j12' /\ inject_incr j23 j23' /\
                             Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\ Mem.inject j23' m2' m3' /\
                             mem_unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                             inject_separated j12 j12' m1 m2 /\ inject_separated j23 j23' m2 m3 /\
                             mem_unchanged_on (loc_unmapped j23) m2 m2' /\ 
                             mem_unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\
                             (mem_wd m2 -> mem_wd m2').                                 
Admitted.