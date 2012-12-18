Load loadpath.
Require Import veric.base.
Require Import Events.
Require Import veric.MemEvolve.


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

Lemma val_valid_extends: forall m m2 (Ext12 : Mem.extends m m2) v
                    (H : val_valid v m), val_valid v m2.
Proof. intros.
  destruct v; trivial. simpl in *.
  eapply (Mem.valid_block_extends _ _ b) in Ext12. eapply Ext12; eassumption.
Qed.

Lemma mem_unchanged_on_refl: forall m f, mem_unchanged_on f m m.
Proof. intros. split; intros; trivial. Qed.

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
