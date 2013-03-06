Load loadpath.

Require Import Events. (*is needed for some definitions (loc_unmapped etc, and
  also at the very end of this file, in order to convert between the 
  tweaked and the standard definitions of mem_unchanged_on etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Maps.

Require Import  sepcomp.mem_lemmas.
Require Import sepcomp.i_defs.

Definition AccessMap_EE_Property  (m1 m1' m2:Mem.mem) 
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b, 
    (Mem.valid_block m2 b -> forall k ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get b AM ofs k = ZMap.get b m1'.(Mem.mem_access) ofs k) /\ 
         (~Mem.perm m1 b ofs Max Nonempty ->
          ZMap.get b AM ofs k = ZMap.get b m2.(Mem.mem_access) ofs k))
     /\ (~ Mem.valid_block m2 b -> forall k ofs,
             ZMap.get b AM ofs k = ZMap.get b m1'.(Mem.mem_access) ofs k).

Definition Content_EE_Property 
  (m1 m1' m2:Mem.mem) (CM:ZMap.t (ZMap.t memval)):=
  forall b, 
    (Mem.valid_block m2 b -> forall ofs,
         (Mem.perm m1 b ofs Max Nonempty ->
           ZMap.get ofs (ZMap.get b CM) = 
           ZMap.get ofs (ZMap.get b m1'.(Mem.mem_contents))) /\ 
         (~Mem.perm m1 b ofs Max Nonempty ->
           ZMap.get ofs (ZMap.get b CM) = 
           ZMap.get ofs (ZMap.get b m2.(Mem.mem_contents))))
     /\ (~ Mem.valid_block m2 b -> forall ofs,
              ZMap.get ofs (ZMap.get b CM) = 
              ZMap.get ofs (ZMap.get b m1'.(Mem.mem_contents))).

Lemma EE_ok: forall (m1 m1' m2 m3 m3':Mem.mem)
             (Ext12: Mem.extends m1 m2)
             (Fwd1: mem_forward m1 m1')
             (Ext23: Mem.extends m2 m3)
             (Fwd3: mem_forward m3 m3')
             (Ext13' : Mem.extends m1' m3') 
             (UnchOn13 :  my_mem_unchanged_on (loc_out_of_bounds m1) m3 m3')
             m2' (WD3': mem_wd m3')
             (NB: m2'.(Mem.nextblock)=m3'.(Mem.nextblock))
             (CONT: Content_EE_Property  m1 m1' m2 (m2'.(Mem.mem_contents)))
             (ACCESS: AccessMap_EE_Property m1 m1' m2 (m2'.(Mem.mem_access))),
         mem_forward m2 m2' /\ 
             Mem.extends m1' m2' /\
             Mem.extends m2' m3' /\
             my_mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
            (mem_wd m2 -> mem_wd m2').
Proof. intros.
assert (Fwd2: mem_forward m2 m2').
    split; intros.
     (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext23) in H. 
        apply Fwd3 in H. destruct H as[H _]. 
        unfold Mem.valid_block. rewrite NB. apply H.
      (*max*)
        destruct (ACCESS b) as [X _].
        unfold Mem.perm in *. destruct (X H Max ofs). clear X ACCESS.
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
              destruct (ACCESS b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. destruct (Val z k ofs); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm. rewrite (H p0). apply H0. 
                clear H. unfold Mem.perm. rewrite (H1 n). clear H1.
                   apply Mem.perm_max in H0.
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z. 
                   assert (ZZ:= fwd_maxperm _ _ Fwd1 _ z _ _ H0).
                   exfalso. apply n. eapply Mem.perm_implies. 
                                       apply ZZ. apply perm_any_N.
              clear Val. unfold Mem.perm. rewrite po_oo in *. 
                 rewrite (Inval z k ofs); clear Inval Heqz. apply H0.
         (*mi_access*) unfold Mem.valid_access in *. 
             destruct H0. inv H. rewrite Zplus_0_r.
             split; trivial. 
             intros off; intros. specialize (H0 _ H). 
              destruct (ACCESS b2) as [Val Inval].
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval.
                destruct (Val z Cur off); clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 off Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear H1. unfold Mem.perm. rewrite (H2 p0). apply H0. 
                clear H. unfold Mem.perm. rewrite (H3 n). clear H1.
                   apply Mem.perm_max in H0.
                   apply (Mem.valid_block_extends _ _ b2 Ext12) in z. 
                   assert (ZZ:= fwd_maxperm _ _ Fwd1 _ z _ _ H0).
                   exfalso. apply n. eapply Mem.perm_implies. 
                                     apply ZZ. apply perm_any_N.
              clear Val. unfold Mem.perm.
                 rewrite (Inval z Cur off); clear Inval Heqz. apply H0.
         (*mi_memval *) inv H. rewrite Zplus_0_r. 
            destruct (CONT b2) as [Val Inval]; clear CONT.
            remember (zlt b2 (Mem.nextblock m2)) as d.
            destruct d.
              destruct (Val z ofs) as [A _]. clear Val Inval.
              rewrite A. 
                  apply memval_inject_id_refl.
                  eapply Fwd1. eapply (Mem.valid_block_extends _ _ _ Ext12).
                               apply z.
                     eapply Mem.perm_implies.
                       eapply Mem.perm_max. apply H0.
                       apply perm_any_N.
            rewrite (Inval z ofs); clear Val Inval Heqd.
                  apply memval_inject_id_refl.
split; trivial.
assert (Ext23': Mem.extends m2' m3').
    split. 
    (*nextblock*)
        apply NB. 
    (*mem_inj*)
       split; intros.
         (*mi_perm*)
              destruct (ACCESS b2) as [Val Inval].
              inv H. rewrite Zplus_0_r.
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. 
                destruct (Val z k ofs) as [A B]; clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear B. unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (A p0) in H0; clear A. 
                   eapply po_trans. 
                          eapply (extends_permorder _ _ Ext13' b2 ofs k).
                   apply H0. 
                clear A. unfold Mem.perm in H0. rewrite (B n) in H0. clear B.
                   destruct UnchOn13 as [U _].
                   rewrite <- U.
                        unfold Mem.perm. rewrite po_oo in *.
                          eapply po_trans.  eapply (extends_permorder _ _ Ext23). apply H0.
                        apply n.
                        rewrite <- (Mem.valid_block_extends _ _ _ Ext23). apply z.
              clear Val Heqz. unfold Mem.perm in H0. 
                 rewrite (Inval z k ofs) in H0; clear Inval.
                       unfold Mem.perm. rewrite po_oo in *.
                      eapply po_trans.  eapply (extends_permorder _ _ Ext13'). apply H0.
         (*mi_access*) 
             unfold Mem.valid_access in *. destruct H0. inv H. 
             rewrite Zplus_0_r.
             split; trivial. 
             intros off; intros. specialize (H0 _ H). clear H.
              destruct (ACCESS b2) as [Val Inval].
              remember (zlt b2 (Mem.nextblock m2)) as z.
              destruct z. clear Inval. 
                destruct (Val z Cur off) as [A B]; clear Val Heqz. 
                remember (Mem.perm_dec m1 b2 off Max Nonempty) as d. 
                destruct d; clear Heqd.  
                   clear B. unfold Mem.perm in *. rewrite po_oo in *. 
                   rewrite (A p0) in H0; clear A. 
                   eapply po_trans. 
                     eapply (extends_permorder _ _ Ext13' b2 off Cur).
                   apply H0. 
                clear A. unfold Mem.perm in H0. rewrite (B n) in H0. clear B.
                   destruct UnchOn13 as [U _].
                   rewrite <- U.
                          unfold Mem.perm. rewrite po_oo in *.
                            eapply po_trans.  eapply (extends_permorder _ _ Ext23). apply H0.
                          apply n.
                          rewrite <- (Mem.valid_block_extends _ _ _ Ext23). apply z. 
              clear Val Heqz. unfold Mem.perm in H0.
                 rewrite (Inval z Cur off) in H0; clear Inval.
                          unfold Mem.perm. rewrite po_oo in *.
                          eapply po_trans.  eapply (extends_permorder _ _ Ext13'). apply H0.
         (*mi_memval *) inv H. rewrite Zplus_0_r. 
            destruct (CONT b2) as [ValC InvalC].  
            destruct (ACCESS b2) as [ValA InvalA]. 
            remember (zlt b2 (Mem.nextblock m2)) as z.
            destruct z.
              clear InvalC InvalA. 
                 destruct (ValC z ofs) as [VA VB]; clear ValC Heqz. 
                 destruct (ValA z Cur ofs) as [AccA AccB]; clear ValA.
                 remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as d. 
                 destruct d; clear Heqd.  
                    rewrite (VA p). clear AccB VA VB. 
                    unfold Mem.perm in H0. rewrite (AccA p) in H0. clear AccA.
                    destruct Ext13'. destruct mext_inj.
                    specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0). 
                    rewrite Zplus_0_r in mi_memval. assumption.
                 rewrite (VB n). clear AccA VA VB.  
                    unfold Mem.perm in *. rewrite (AccB n) in H0. clear AccB.
                      assert (Mem.perm m3 b2 ofs Cur Readable).
                         unfold Mem.perm in *.
                         rewrite po_oo in *.
                         eapply po_trans. 
                            eapply (extends_permorder _ _ Ext23). apply H0.
                         eapply mymemvalUnchOnR. apply n. apply UnchOn13.
                            destruct Ext23. destruct mext_inj.
                            specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0).  
                              rewrite Zplus_0_r in mi_memval. assumption.
                            apply H.
                            eapply (Mem.valid_block_extends _ _ _ Ext12). 
                            apply z.
              clear ValA ValC. rewrite (InvalC z ofs); clear InvalC Heqz. 
                 unfold Mem.perm in H0.
                 rewrite (InvalA z Cur ofs) in H0; clear InvalA.
                    destruct Ext13'. destruct mext_inj.
                    specialize (mi_memval b2 ofs b2 0 (eq_refl _) H0). 
                    rewrite Zplus_0_r in mi_memval. assumption.
split; trivial.
assert (WD2: mem_wd m2').
  intros. eapply (extends_memwd _ _ Ext23' WD3'). 
split; intros; trivial. 
(*my_mem_unchanged_on (loc_out_of_bounds m1) m2 m2'*)
     destruct UnchOn13 as [UnchP UnchVal].
     split; intros. clear UnchVal. 
        specialize (UnchP _ _ k HP).
        destruct (ACCESS b) as [Val _]. 
        destruct (Val H k ofs) as [_ B]; clear Val.
          unfold Mem.perm. rewrite (B HP). trivial.
      clear UnchP. 
      assert (Hperm3 := Mem.perm_extends _ _ _ _ _ _ Ext23 HMeperm).
      assert (BV2:= Mem.perm_valid_block _ _ _ _ _ HMeperm). 
      specialize (UnchVal b ofs HP Hperm3 v).
      destruct (CONT b) as [Val _].
      destruct (Val BV2 ofs) as [_ B]; clear Val.
            rewrite (B HP). assumption.
Qed. 

Parameter mkAccessMap_EE_exists: forall (m1 m1' m2:Mem.mem), 
          ZMap.t (Z -> perm_kind -> option permission).
Axiom mkAccessMap_EE_ok: forall m1 m1' m2, 
      AccessMap_EE_Property m1 m1' m2 (mkAccessMap_EE_exists m1 m1' m2).

Parameter mkContentsMap_EE_exists: 
           forall (m1 m1' m2:Mem.mem), ZMap.t (ZMap.t memval).
Axiom mkContentsMap_EE_ok: forall m1 m1' m2, 
      Content_EE_Property m1 m1' m2 (mkContentsMap_EE_exists m1 m1' m2).

Definition mkEE (m1 m1' m2 m3 m3':Mem.mem) (Ext12: Mem.extends m1 m2) 
                (Fwd1: mem_forward m1 m1')
                (Ext23: Mem.extends m2 m3) (Fwd3: mem_forward m3 m3')
                (Ext13' : Mem.extends m1' m3')
                (UnchOn3: my_mem_unchanged_on (loc_out_of_bounds m1) m3 m3')
              : Mem.mem'.
eapply Mem.mkmem with (nextblock:=m3'.(Mem.nextblock))
                      (mem_access:=mkAccessMap_EE_exists m1 m1' m2).
(* (NB: forall b, Mem.valid_block m2 b -> Mem.valid_block m3' b)*)
  apply (mkContentsMap_EE_exists m1 m1' m2).
(*eapply Mem.mkmem with (nextblock:=m3'.(Mem.nextblock)) 
                        (mem_access:=(Mem.mem_access m2')).*)
  apply m3'.
  (*access_max*)
  intros. destruct (mkAccessMap_EE_ok m1 m1' m2 b) as [Val Inval].
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
        rewrite (Inval z Max ofs).
        rewrite (Inval z Cur ofs). apply m1'.
  (*nextblock_noaccess*)
    intros.  
    assert (NVB1': ~ Mem.valid_block m1' b).
        clear Ext12 Fwd1 Ext23. 
        intros N. apply (Mem.valid_block_extends _ _ b Ext13') in N. 
                  unfold Mem.valid_block in N. omega.
    assert (NVB2: ~ Mem.valid_block m2 b).
        clear Ext12 Fwd1 Ext13'. intros N. destruct Ext23.   
        unfold mem_forward, Mem.valid_block in *. 
        rewrite mext_next in N.
        apply Fwd3 in N.  destruct N as [X _]. clear - H X. omega.
    destruct (mkAccessMap_EE_ok m1 m1' m2 b) as [_ Inval].
        rewrite (Inval NVB2 k ofs); clear Inval. apply m1'. apply NVB1'.
Defined.

Lemma my_interpolate_EE: forall m1 m2 m1' m3 m3' 
           (Ext12: Mem.extends m1 m2) 
           (Fwd1: mem_forward m1 m1')
           (Ext23: Mem.extends m2 m3) 
           (Fwd3: mem_forward m3 m3')
           (Ext13' : Mem.extends m1' m3') 
           (UnchOn3: my_mem_unchanged_on (loc_out_of_bounds m1) m3 m3') 
           (WD3': mem_wd m3'),
      exists m2', mem_forward m2 m2' /\ 
               Mem.extends m1' m2' /\ 
               Mem.extends m2' m3' /\ 
               my_mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                   (mem_wd m2 -> mem_wd m2').
Proof. intros. 
   assert (NB:forall b, Mem.valid_block m2 b -> Mem.valid_block m3' b).
      intros. apply Fwd3. destruct Ext23. 
              unfold Mem.valid_block. rewrite <- mext_next. apply H.
   exists (mkEE m1 m1' m2 m3 m3' Ext12 Fwd1 Ext23 Fwd3 Ext13' UnchOn3).
     eapply (EE_ok m1 m1' m2 m3 m3'); trivial.
     apply mkContentsMap_EE_ok.  
     apply mkAccessMap_EE_ok.  
Qed.

Lemma interpolate_EE: forall m1 m2 (Ext12: Mem.extends m1 m2) m1' 
            (Fwd1: mem_forward m1 m1') m3 (Ext23: Mem.extends m2 m3) m3' 
            (Fwd3: mem_forward m3 m3') (Ext13' : Mem.extends m1' m3')
            (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3') 
            (WD3': mem_wd m3'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\
                   Mem.extends m2' m3' /\
                   mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                   (mem_wd m2 -> mem_wd m2').
Proof. intros. rewrite <- unchAx in UnchOn3. 
   destruct (my_interpolate_EE _ _ _ _ _ Ext12 Fwd1 Ext23 
                               Fwd3 Ext13' UnchOn3 WD3')
    as [m2' [Fwd2 [Ext12' [Ext23' [MU WD2']]]]].
   exists m2'. rewrite unchAx in MU.
    repeat (split; try eassumption). 
Qed.
