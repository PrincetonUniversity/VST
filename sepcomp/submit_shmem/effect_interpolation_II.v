Require Import Events. (*is needed for some definitions (loc_unmapped etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Axioms.

Require Import FiniteMaps.
Require Import sepcomp.StructuredInjections.
Require Import effect_simulations.
Require Import effect_simulations_lemmas.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.mem_interpolation_defs.
Require Import sepcomp.mem_interpolation_II.

(*Inserts the new injection entries into extern component, but not into foreign*)
Definition insert_as_extern (mu: SM_Injection) (j: meminj) (DomJ TgtJ:block->bool)
          : SM_Injection:=
  match mu with
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern =>
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local
      (fun b => orb (extBSrc b) (DomJ b))
      (fun b => orb (extBTgt b) (TgtJ b))
      fSrc
      fTgt
      (join extern (fun b => match local b with Some _ => None
                                              | None => j b end))
  end.

Definition convertL (nu12: SM_Injection) (j12':meminj) FreshSrc FreshMid:=
  insert_as_extern nu12 j12' FreshSrc FreshMid.

Definition convertR (nu23: SM_Injection) (j23':meminj) FreshMid FreshTgt:=
  insert_as_extern nu23 j23' FreshMid FreshTgt.

Lemma convertL_local: forall nu12 j12' FreshSrc FreshMid,
            local_of (convertL nu12 j12' FreshSrc FreshMid) =
            local_of nu12.
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_pub: forall nu12 j12' FreshSrc FreshMid,
            pub_of (convertL nu12 j12' FreshSrc FreshMid) =
            pub_of nu12.
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_priv: forall nu12 j12' FreshSrc FreshMid,
            priv_of (convertL nu12 j12' FreshSrc FreshMid) =
            priv_of nu12.
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_extern: forall nu12 j12' FreshSrc FreshMid,
            extern_of (convertL nu12 j12' FreshSrc FreshMid) =
            join (extern_of nu12)
                 (fun b => match (local_of nu12) b with Some _ => None | None => j12' b end).
Proof. intros. destruct nu12; simpl. reflexivity. Qed.

Lemma convertL_locBlocksSrc: forall nu12 j12' FreshSrc FreshMid,
            locBlocksSrc (convertL nu12 j12' FreshSrc FreshMid) =
            locBlocksSrc nu12.
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_locBlocksTgt: forall nu12 j12' FreshSrc FreshMid,
            locBlocksTgt (convertL nu12 j12' FreshSrc FreshMid) =
            locBlocksTgt nu12.
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_extBlocksSrc: forall nu12 j12' FreshSrc FreshMid,
            extBlocksSrc (convertL nu12 j12' FreshSrc FreshMid) =
            fun b => orb (extBlocksSrc nu12 b) (FreshSrc b).
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_extBlocksTgt: forall nu12 j12' FreshSrc FreshMid,
            extBlocksTgt (convertL nu12 j12' FreshSrc FreshMid) =
            fun b => orb (extBlocksTgt nu12 b) (FreshMid b).
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_DomSrc: forall nu12 j12' FreshSrc FreshMid,
            DomSrc (convertL nu12 j12' FreshSrc FreshMid) =
            (fun b => orb (DomSrc nu12 b) (FreshSrc b)).
Proof. intros. destruct nu12. unfold DomSrc; simpl in *.
       extensionality b. rewrite orb_assoc. reflexivity. Qed.

Lemma convertL_DomTgt: forall nu12 j12' FreshSrc FreshMid,
            DomTgt (convertL nu12 j12' FreshSrc FreshMid) =
            (fun b => orb (DomTgt nu12 b) (FreshMid b)).
Proof. intros. destruct nu12. unfold DomTgt; simpl in *.
       extensionality b. rewrite orb_assoc. reflexivity. Qed.

Lemma convertL_pubBlocksSrc: forall nu12 j12' FreshSrc FreshMid,
            pubBlocksSrc (convertL nu12 j12' FreshSrc FreshMid) =
            pubBlocksSrc nu12.
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_pubBlocksTgt: forall nu12 j12' FreshSrc FreshMid,
            pubBlocksTgt (convertL nu12 j12' FreshSrc FreshMid) =
            pubBlocksTgt nu12.
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_frgnBlocksSrc: forall nu12 j12' FreshSrc FreshMid,
            frgnBlocksSrc (convertL nu12 j12' FreshSrc FreshMid) =
            frgnBlocksSrc nu12.
Proof. intros. destruct nu12. simpl. reflexivity. Qed.

Lemma convertL_frgnBlocksTgt: forall nu12 j12' FreshSrc FreshMid,
            frgnBlocksTgt (convertL nu12 j12' FreshSrc FreshMid) =
            frgnBlocksTgt nu12.
Proof. intros. destruct nu12. reflexivity. Qed.

Lemma convertL_foreign: forall nu12 j12' FreshSrc FreshMid (WD12:SM_wd nu12),
            foreign_of (convertL nu12 j12' FreshSrc FreshMid) =
            foreign_of nu12.
Proof. intros. destruct nu12; simpl in *. extensionality b.
  remember (frgnBlocksSrc b) as d.
  destruct d; trivial. apply eq_sym in Heqd.
  destruct (frgnSrc _ WD12 _ Heqd) as [b2 [z [Frg _]]]. simpl in Frg.
  rewrite Heqd in Frg; unfold join. rewrite Frg; trivial. Qed.

Lemma convertR_local: forall nu23 j23' FreshMid FreshTgt,
            local_of (convertR nu23 j23' FreshMid FreshTgt) =
            local_of nu23.
Proof. intros. destruct nu23; simpl. reflexivity. Qed.

Lemma convertR_pub: forall nu23 j23' FreshMid FreshTgt,
            pub_of (convertR nu23 j23' FreshMid FreshTgt) =
            pub_of nu23.
Proof. intros. destruct nu23; simpl. reflexivity. Qed.

Lemma convertR_priv: forall nu23 j23' FreshMid FreshTgt,
            priv_of (convertR nu23 j23' FreshMid FreshTgt) =
            priv_of nu23.
Proof. intros. destruct nu23; simpl. reflexivity. Qed.

Lemma convertR_extern: forall nu23 j23' FreshMid FreshTgt,
            extern_of (convertR nu23 j23' FreshMid FreshTgt) =
            join (extern_of nu23)
                 (fun b => match (local_of nu23) b with Some _ => None | None => j23' b end).
Proof. intros. destruct nu23; simpl. reflexivity. Qed.

Lemma convertR_foreign: forall nu23 j23' FreshMid FreshTgt (WD23:SM_wd nu23),
            foreign_of (convertR nu23 j23' FreshMid FreshTgt) =
            foreign_of nu23.
Proof. intros. destruct nu23; simpl in *. extensionality b.
  remember (frgnBlocksSrc b) as d.
  destruct d; trivial. apply eq_sym in Heqd.
  destruct (frgnSrc _ WD23 _ Heqd) as [b2 [z [Frg _]]]. simpl in Frg.
  rewrite Heqd in Frg; unfold join. rewrite Frg; trivial. Qed.

Lemma convertR_locBlocksSrc: forall nu23 j23' FreshMid FreshTgt,
            locBlocksSrc (convertR nu23 j23' FreshMid FreshTgt) =
            locBlocksSrc nu23.
Proof. intros. destruct nu23. reflexivity. Qed.

Lemma convertR_locBlocksTgt: forall nu23 j23' FreshMid FreshTgt,
            locBlocksTgt (convertR nu23 j23' FreshMid FreshTgt) =
            locBlocksTgt nu23.
Proof. intros. destruct nu23. reflexivity. Qed.

Lemma convertR_extBlocksSrc: forall nu23 j23' FreshMid FreshTgt,
            extBlocksSrc (convertR nu23 j23' FreshMid FreshTgt) =
            fun b => orb (extBlocksSrc nu23 b) (FreshMid b).
Proof. intros. destruct nu23. reflexivity. Qed.

Lemma convertR_extBlocksTgt: forall nu23 j23' FreshMid FreshTgt,
            extBlocksTgt (convertR nu23 j23' FreshMid FreshTgt) =
            fun b => orb (extBlocksTgt nu23 b) (FreshTgt b).
Proof. intros. destruct nu23. reflexivity. Qed.

Lemma convertR_DomSrc: forall nu23 j23' FreshMid FreshTgt,
            DomSrc (convertR nu23 j23' FreshMid FreshTgt) =
            (fun b => orb (DomSrc nu23 b) (FreshMid b)).
Proof. intros. destruct nu23; simpl. unfold DomSrc; simpl.
       extensionality b. rewrite orb_assoc. reflexivity. Qed.

Lemma convertR_DomTgt: forall nu23 j23' FreshMid FreshTgt,
            DomTgt (convertR nu23 j23' FreshMid FreshTgt) =
            (fun b => orb (DomTgt nu23 b) (FreshTgt b)).
Proof. intros. destruct nu23; simpl. unfold DomTgt; simpl.
       extensionality b. rewrite orb_assoc. reflexivity. Qed.

Lemma convertR_pubBlocksSrc: forall nu23 j23' FreshMid FreshTgt,
            pubBlocksSrc (convertR nu23 j23' FreshMid FreshTgt) =
            pubBlocksSrc nu23.
Proof. intros. destruct nu23. reflexivity. Qed.

Lemma convertR_pubBlocksTgt: forall nu23 j23' FreshMid FreshTgt,
            pubBlocksTgt (convertR nu23 j23' FreshMid FreshTgt) =
            pubBlocksTgt nu23.
Proof. intros. destruct nu23. reflexivity. Qed.

Lemma convertR_frgnBlocksSrc: forall nu23 j23' FreshMid FreshTgt,
            frgnBlocksSrc (convertR nu23 j23' FreshMid FreshTgt) =
            frgnBlocksSrc nu23.
Proof. intros. destruct nu23. simpl. reflexivity. Qed.

Lemma convertR_frgnBlocksTgt: forall nu23 j23' FreshMid FreshTgt,
            frgnBlocksTgt (convertR nu23 j23' FreshMid FreshTgt) =
            frgnBlocksTgt nu23.
Proof. intros. destruct nu23; simpl. reflexivity. Qed.

Definition FreshDom (j j': meminj) b :=
  match j' b with
     None => false
   | Some(b',z) => match j b with
                     None => true
                   | Some _ => false
                   end
  end.
(*So FreshDom in src language is FreshDom j12 j12', equaling
        (not quite, due to unmapped!) DomSrc nu' - DomSrc nu (take DomSrc nu' - DomSrc nu, since
          that has all the unmapped ones, too, to satisfy nu' = sm_compose nu12' nu23'
     FreshDom in mid langauge is FreshDom j23 j23', and
     FreshDom in tgt language is DomTgt nu' - DomTgt nu*)

(*And frgnMid b = (match j23' b with
                        None => false
                      | Some (b',z) => frgnBlocksTgt nu' b' end)*)

Goal forall mu (WD: SM_wd mu) M,
          (forall b ofs, locBlocksSrc mu b = true -> loc_unmapped (pub_of mu) b ofs -> ~M b ofs)
          <-> (forall b, locBlocksSrc mu b = true -> forall ofs, M b ofs -> pubBlocksSrc mu b = true).
intros. split; intros.
  remember (pubBlocksSrc mu b) as d.
  destruct d; trivial; apply eq_sym in Heqd.
  exfalso. apply (H _ _ H0 (pubSrcContra _ _ Heqd) H1).
intros N. specialize (H _ H0 _ N).
  unfold loc_unmapped in H1.
  destruct (pubSrc _ WD _ H) as [b2 [d [P _]]].
  rewrite P in H1. discriminate.
Qed.

Definition AccessEffProperty nu23 nu12 (j12' :meminj) (m1 m1' m2 : mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2,
    (Mem.valid_block m2 b2 -> forall k ofs2,
       if (locBlocksSrc nu23 b2)
       then if (pubBlocksSrc nu23 b2)
            then match source (local_of nu12) m1 b2 ofs2 with
                   Some(b1,ofs1) => if pubBlocksSrc nu12 b1
                                    then PMap.get b2 AM ofs2 k =
                                         PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                                    else PMap.get b2 AM ofs2 k =
                                         PMap.get b2 m2.(Mem.mem_access) ofs2 k
                 | None =>  PMap.get b2 AM ofs2 k =
                            PMap.get b2 m2.(Mem.mem_access) ofs2 k
                 end
            else PMap.get b2 AM ofs2 k =
                 PMap.get b2 m2.(Mem.mem_access) ofs2 k
       else match source (as_inj nu12) m1 b2 ofs2 with
                   Some(b1,ofs1) =>  PMap.get b2 AM ofs2 k =
                                     PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                 | None => match (*j23*) (as_inj nu23) b2 with
                             None => PMap.get b2 AM ofs2 k  = PMap.get b2 m2.(Mem.mem_access) ofs2 k
                           | Some (b3,d3) =>  PMap.get b2 AM ofs2 k = None (* mem_interpolation_II.v has PMap.get b2 m2.(Mem.mem_access) ofs2 k here
                                            -- see the comment in the proof script below to see where None is needed*)
                           end


               end)
     /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
           match source j12' m1' b2 ofs2 with
              Some(b1,ofs1) => PMap.get b2 AM ofs2 k =
                               PMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None =>  PMap.get b2 AM ofs2 k = None
          end).

Definition ContentEffProperty nu23 nu12 (j12':meminj) (m1 m1' m2:Mem.mem)
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2,
  (Mem.valid_block m2 b2 -> forall ofs2,
    if locBlocksSrc nu23 b2
    then if (pubBlocksSrc nu23 b2)
         then match source (local_of nu12) m1 b2 ofs2 with
             Some(b1,ofs1) =>
                 if pubBlocksSrc nu12 b1
                 then ZMap.get ofs2 (PMap.get b2 CM) =
                            inject_memval j12'
                              (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
                 else ZMap.get ofs2 (PMap.get b2 CM) =
                           ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
           | None => ZMap.get ofs2 (PMap.get b2 CM) =
                     ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
            end
         else ZMap.get ofs2 (PMap.get b2 CM) =
              ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
    else match source (as_inj nu12) m1 b2 ofs2 with
             Some(b1,ofs1) => ZMap.get ofs2 (PMap.get b2 CM) =
                              inject_memval j12'
                                (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
           | None => ZMap.get ofs2 (PMap.get b2 CM) =
                     ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
         end)
  /\ (~ Mem.valid_block m2 b2 -> forall ofs2,
         match source j12' m1' b2 ofs2 with
                None => ZMap.get ofs2 (PMap.get b2 CM) = Undef
              | Some(b1,ofs1) =>
                   ZMap.get ofs2 (PMap.get b2 CM) =
                     inject_memval j12'
                       (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
         end)
   /\ fst CM !! b2 = Undef.

Lemma effect_interp_OK: forall m1 m2 nu12
                             (MInj12 : Mem.inject (as_inj nu12) m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') nu23 m3
                             (MInj23 : Mem.inject (as_inj nu23) m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                              nu' (WDnu' : SM_wd nu')
                             (SMvalNu' : sm_valid nu' m1' m3')
                             (MemInjNu' : Mem.inject (as_inj nu') m1' m3')

                             (ExtIncr: extern_incr (compose_sm nu12 nu23) nu')
                             (SMInjSep: sm_inject_separated (compose_sm nu12 nu23) nu' m1 m3)
                             (SMV12: sm_valid nu12 m1 m2)
                             (SMV23: sm_valid nu23 m2 m3)
                             (UnchPrivSrc: Mem.unchanged_on (fun b ofs => locBlocksSrc (compose_sm nu12 nu23) b = true /\
                                                      pubBlocksSrc (compose_sm nu12 nu23) b = false) m1 m1')

                             (UnchLOOR13: Mem.unchanged_on (local_out_of_reach (compose_sm nu12 nu23) m1) m3 m3')

                             (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                                         locBlocksTgt nu12 = locBlocksSrc nu23 /\
                                         extBlocksTgt nu12 = extBlocksSrc nu23 /\
                                         (forall b, pubBlocksTgt nu12 b = true ->
                                                    pubBlocksSrc nu23 b = true) /\
                                         (forall b, frgnBlocksTgt nu12 b = true ->
                                                    frgnBlocksSrc nu23 b = true))
                             (Norm12: forall b1 b2 d1, extern_of  nu12 b1 = Some(b2,d1) ->
                                             exists b3 d2, extern_of nu23 b2 = Some(b3, d2))
               prej12' j23' n1' n2'
               (HeqMKI: mkInjections m1 m1' m2 (as_inj nu12) (as_inj nu23) (as_inj nu') =
                            (prej12', j23', n1', n2'))
               j12' (Hj12': j12'= removeUndefs (as_inj nu12) (as_inj nu') prej12')
               m2'
               (NB: m2'.(Mem.nextblock)=n2')
               (CONT:  ContentEffProperty nu23 nu12 j12' m1 m1' m2
                                           (m2'.(Mem.mem_contents)))
               (ACCESS: AccessEffProperty nu23 nu12 (*(as_inj nu23)*) j12' m1 m1' m2
                                               (m2'.(Mem.mem_access))),

     Mem.unchanged_on (fun b ofs => locBlocksSrc nu23 b = true /\
                                    pubBlocksSrc nu23 b = false) m2 m2' /\
     Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2' /\
(*     Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3' /\*)
     exists (nu12' nu23':SM_Injection),
           nu12'  = (convertL nu12 (removeUndefs (as_inj nu12) (as_inj nu') prej12')
                    (*FreshSrc:*) (fun b => andb (DomSrc nu' b) (negb (DomSrc nu12 b)))
                    (*FreshMid:*) (FreshDom (as_inj nu23) j23'))
       /\ nu23' = (convertR nu23 j23'
                      (*FreshMid:*) (FreshDom (as_inj nu23) j23')
                      (*FreshTgt:*) (fun b => andb (DomTgt nu' b) (negb (DomTgt nu23 b))))
                      /\ nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             sm_inject_separated nu12 nu12' m1 m2 /\
                             sm_inject_separated nu23 nu23' m2 m3 /\
                             sm_valid nu12' m1' m2' /\ sm_valid nu23' m2' m3' /\
                             (SM_wd nu12' /\ SM_wd nu23' /\
                              locBlocksTgt nu12' = locBlocksSrc nu23' /\
                              extBlocksTgt nu12' = extBlocksSrc nu23' /\
                              (forall b, pubBlocksTgt nu12' b = true ->
                                         pubBlocksSrc nu23' b = true) /\
                              (forall b, frgnBlocksTgt nu12' b = true ->
                                         frgnBlocksSrc nu23' b = true)) /\
                             (forall b1 b2 d1, extern_of nu12' b1 = Some(b2,d1) ->
                                     exists b3 d2, extern_of nu23' b2 = Some(b3, d2)) /\
                             mem_forward m2 m2' /\
                             Mem.inject (as_inj nu12') m1' m2' /\
                             Mem.inject (as_inj nu23') m2' m3'.
Proof. intros.
  assert (VBj12_1: forall (b1 b2 : block) (ofs2 : Z),
                   (as_inj nu12) b1 = Some (b2, ofs2) -> Mem.valid_block m1 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj12).
  assert (VBj12_2: forall (b1 b2 : block) (ofs2 : Z),
                   (as_inj nu12) b1 = Some (b2, ofs2) -> Mem.valid_block m2 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj12).
  assert (VBj23_1: forall (b1 b2 : block) (ofs2 : Z),
                   (as_inj nu23) b1 = Some (b2, ofs2) -> Mem.valid_block m2 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj23).
  assert (VBj23_2: forall (b1 b2 : block) (ofs2 : Z),
                   (as_inj nu23) b1 = Some (b2, ofs2) -> Mem.valid_block m3 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj23).
  assert (VB12: forall (b3 b4 : block) (ofs3 : Z),
                 (as_inj nu12) b3 = Some (b4, ofs3) ->
                (b3 < Mem.nextblock m1 /\ b4 < Mem.nextblock m2)%positive).
      intros. split. apply (VBj12_1 _ _ _ H). apply (VBj12_2 _ _ _ H).
  assert (preinc12:= mkInjections_1_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1).
  assert (inc12:= inc_RU _ _ preinc12 (as_inj nu')).
  assert (presep12:= mkInjections_1_injsep _ _ _ _ _ _ _ _ _ _ HeqMKI).
  assert (sep12: inject_separated (as_inj nu12) (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1 m2).
       intros b; intros. eapply presep12. apply H.
       eapply RU_D. apply preinc12. apply H0.
  assert (InjIncr: inject_incr (compose_meminj (as_inj nu12) (as_inj nu23)) (as_inj nu')).
    subst. eapply extern_incr_inject_incr; eassumption.
  assert (InjSep: inject_separated (compose_meminj (as_inj nu12) (as_inj nu23)) (as_inj nu') m1 m3).
    subst. clear CONT ACCESS HeqMKI.
    apply sm_inject_separated_mem in SMInjSep.
    rewrite compose_sm_as_inj in SMInjSep.
      assumption.
      eapply GlueInvNu.
      eapply GlueInvNu.
      eapply GlueInvNu.
      eapply GlueInvNu.
      assumption.
  assert (inc23:= mkInjections_2_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1).
  assert (sep23:= mkInjections_2_injsep _ _ _ _ _ _ _ _ _ _ HeqMKI
                  VBj12_1 _ InjSep).
  assert (NB1:= forward_nextblock _ _ Fwd1).
  assert (XX: n1' = Mem.nextblock m1').
    destruct (mkInjections_0  _ _ _ _ _ _ _ _ _ _ HeqMKI)
      as [[NN [N1 [N2 [JJ1 JJ2]]]] | [n [NN [N1 [N2 N3]]]]].
    subst. eapply Pos.le_antisym; assumption. assumption.
 subst.
  assert (VBj': forall b1 b3 ofs3, (as_inj nu') b1 = Some (b3, ofs3) ->
                (b1 < Mem.nextblock m1')%positive).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MemInjNu').
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI
               InjIncr _ InjSep VBj12_1 VBj12_2 VBj23_1 VBj').
destruct GlueInvNu as [WDnu12 [WDnu23 [GlueLoc [GlueExt [GluePub GlueFrgn]]]]].
assert (Fwd2: mem_forward m2 m2').
  split; intros; rename b into b2.
  (*valid_block*)
     clear - H NB1 HeqMKI. unfold Mem.valid_block in *.
     destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI)
     as [HH | HH].
       destruct HH as [_ [_ [XX _]]]. rewrite XX in H. assumption.
       destruct HH as [n [NN [_ [_ X]]]]. rewrite <- X.
        xomega.
  (*max*)
     destruct (ACCESS b2) as [Val2 _].
     specialize (Val2 H Max ofs).
     remember (locBlocksSrc nu23 b2) as d.
     destruct d; apply eq_sym in Heqd.
     (*case locBlocksSrc nu23 b2 = false*)
       remember (pubBlocksSrc nu23 b2) as q.
       destruct q; apply eq_sym in Heqq.
         remember (source (local_of nu12) m1 b2 ofs) as src.
         destruct src.
           apply source_SomeE in Heqsrc.
           destruct Heqsrc as [b1 [delta [ofs1 [PBO [ValB1 [J1 [P1 Off2]]]]]]].
           subst.
           remember (pubBlocksSrc nu12 b1) as w.
           destruct w;
             rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2; trivial.
           eapply MInj12.
             apply local_in_all; eassumption.
             eapply Fwd1.
               apply ValB1.
               apply H0.
         rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; apply H0.
       rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; apply H0.
     (*case locBlocksSrc nu23 b2 = false*)
       remember (source (as_inj nu12) m1 b2 ofs) as src.
       destruct src.
         apply source_SomeE in Heqsrc.
         destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
         subst.
         rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2.
         eapply MInj12. apply J1.
           eapply Fwd1.
             apply Bounds.
             apply H0.
       remember (as_inj nu23 b2) as jb.
         destruct jb; apply eq_sym in Heqjb.
           destruct p0.
           unfold Mem.perm in H0. rewrite Val2 in H0. simpl in H0. contradiction.
         rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2. apply H0.

(*First unchOn condition - corresponds to UnchLOM2 loc_unmapped.*)
assert (UNCHA: Mem.unchanged_on
  (fun (b : block) (_ : Z) =>
   locBlocksSrc nu23 b = true /\ pubBlocksSrc nu23 b = false) m2 m2').
 split; intros. rename b into b2. rename H0 into ValB2.
        destruct H as [locBSrc pubBSrc].
        destruct (ACCESS b2) as [Val _].
        specialize (Val ValB2 k ofs).
        rewrite locBSrc, pubBSrc in Val.
        rewrite (perm_subst _ _ _ _ _ _ _ Val). split; auto.
  apply (cont_split _ _ _ _ _ (CONT b)); intros; clear CONT.
      (*case Mem.valid_block m2 b*)
          specialize (H2 ofs).
          destruct H as [locBSrc pubBSrc].
          rewrite locBSrc, pubBSrc in H2. simpl in H2.
          apply H2.
      (*case invalid*)
          apply Mem.perm_valid_block in H0. contradiction.
split; trivial.
assert (UNCHB: Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2').
 (*Second unchOn condition - corresponds to Unch2*)
  split; intros. rename b into b2. rename H0 into ValB2.
     destruct H as [locTgt2 HP].
     destruct (ACCESS b2) as [Val _].
     specialize (Val ValB2 k ofs).
     remember (locBlocksSrc nu23 b2) as d.
     destruct d; apply eq_sym in Heqd.
     (*case locBlocksSrc nu23 b2 = true*)
       remember (pubBlocksSrc nu23 b2) as q.
       destruct q; apply eq_sym in Heqq.
       (*case pubBlocksSrc nu23 b2 = true*)
          remember (source (local_of nu12) m1 b2 ofs) as ss.
          destruct ss.
            destruct p0.
            destruct (source_SomeE _ _ _ _ _ Heqss)
               as [b1 [d1 [ofs1 [PP [VB [JJ [PERM Off2]]]]]]]; clear Heqss.
            subst. apply eq_sym in PP. inv PP.
            remember (pubBlocksSrc nu12 b) as w.
            destruct w; apply eq_sym in Heqw;
              rewrite (perm_subst _ _ _ _ _ _ _ Val); clear Val.
              destruct (HP _ _ JJ).
                assert (Arith: z + d1 - d1 = z) by omega.
                rewrite Arith in H. contradiction.
              rewrite H in Heqw. discriminate.
            split; intros; trivial.
          rewrite (perm_subst _ _ _ _ _ _ _ Val); clear Val.
             split; intros; trivial.
       (*case pubBlocksSrc nu23 b2 = false*)
          rewrite (perm_subst _ _ _ _ _ _ _ Val); clear Val.
             solve[split; intros; trivial].
     (*case locBlocksSrc nu23 b2 = false*)
        rewrite GlueLoc in locTgt2. rewrite locTgt2 in Heqd. discriminate.
  destruct H as [locTgt2 HP]. rename b into b2.
  apply (cont_split _ _ _ _ _ (CONT b2)); intros; clear CONT.
  (* case Mem.valid_block m2 b*)
          specialize (H1 ofs).
          assert (locSrc2: locBlocksSrc nu23 b2 = true).
            rewrite GlueLoc in locTgt2. assumption.
          rewrite locSrc2 in *.
          remember (pubBlocksSrc nu23 b2) as d.
          destruct d; apply eq_sym in Heqd.
          (*case pubBlocksSrc nu23 b2 = true*)
            remember (source (local_of nu12) m1 b2 ofs) as ss.
            destruct ss.
              destruct p.
              destruct (source_SomeE _ _ _ _ _ Heqss)
               as [b1 [d1 [ofs1 [PP [VB [JJ [PERM Off2]]]]]]]; clear Heqss.
              subst. inv PP.
              destruct (HP _ _ JJ); clear HP.
                 assert (Arith : ofs1 + d1 - d1 = ofs1) by omega.
                 rewrite Arith in H3. contradiction.
              rewrite H3 in H1. trivial.
            apply H1.
          (*case pubBlocksSrc nu23 b2 = true*)
            apply H1.
       (*invalid*)
          exfalso.
          apply Mem.perm_valid_block in H0. contradiction.
split; trivial.

assert (UNCHC: Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3').
  (*third UnchOn condition - corresponds to UnchLOOR3*)
   clear - UnchLOOR13 WDnu12 GluePub MInj12.
   unfold local_out_of_reach.
   split; intros; rename b into b3.
      destruct H as[locTgt3 LOOR23].
      eapply UnchLOOR13; trivial; simpl.
        split; trivial.
        intros b1; intros; simpl in *.
        remember (pubBlocksSrc nu12 b1) as d.
        destruct d; try (right; reflexivity).
        left. apply eq_sym in Heqd.
        destruct (compose_meminjD_Some _ _ _ _ _ H)
          as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; subst; clear H.
        destruct (pubSrc _ WDnu12 _ Heqd) as [bb2 [dd1 [Pub12 PubTgt2]]].
        rewrite (pub_in_local _ _ _ _ Pub12) in LOC1. inv LOC1.
        apply GluePub in PubTgt2.
        destruct (LOOR23 _ _ LOC2); clear LOOR23.
          intros N. apply H.
          assert (Arith : ofs - (d1 + d2) + d1 = ofs - d2) by omega.
          rewrite <- Arith.
          eapply MInj12. eapply pub_in_all; try eassumption. apply N.
        rewrite H in PubTgt2. discriminate.
   destruct H as[locTgt3 LOOR23].
      eapply UnchLOOR13; trivial; simpl.
        split; trivial.
        intros b1; intros; simpl in *.
        remember (pubBlocksSrc nu12 b1) as d.
        destruct d; try (right; reflexivity).
        left. apply eq_sym in Heqd.
        destruct (compose_meminjD_Some _ _ _ _ _ H)
          as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; subst; clear H.
        destruct (pubSrc _ WDnu12 _ Heqd) as [bb2 [dd1 [Pub12 PubTgt2]]].
        rewrite (pub_in_local _ _ _ _ Pub12) in LOC1. inv LOC1.
        apply GluePub in PubTgt2.
        destruct (LOOR23 _ _ LOC2); clear LOOR23.
          intros N. apply H.
          assert (Arith : ofs - (d1 + d2) + d1 = ofs - d2) by omega.
          rewrite <- Arith.
          eapply MInj12. eapply pub_in_all; try eassumption. apply N.
        rewrite H in PubTgt2. discriminate.
(*split; trivial.*)
assert (VBj23': forall b2 b3 d2, j23' b2 = Some(b3,d2) -> Mem.valid_block m2' b2).
    assert (Val2: forall b2 b3 d2, as_inj nu23 b2 = Some(b3,d2) -> Mem.valid_block m2 b2).
       intros. eapply SMV23. eapply as_inj_DomRng; eassumption.
    intros.
    destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI Val2 _ _ _ H) as [MK | [MK | MK]].
       destruct MK. apply Fwd2. apply H1.
       destruct MK. subst. apply H1.
       destruct MK as [m Hm]; subst. apply Hm.
assert (Val12: (forall (b1 b2 : block) (ofs2 : Z),
  as_inj nu12 b1 = Some (b2, ofs2) ->
  (b1 < Mem.nextblock m1)%positive /\ (b2 < Mem.nextblock m2)%positive)).
   intros. split; eapply SMV12. eapply as_inj_DomRng; eassumption.
                eapply as_inj_DomRng; eassumption.
assert (Val23: (forall (b2 b3 : block) (ofs3 : Z),
  as_inj nu23 b2 = Some (b3, ofs3) -> (b2 < Mem.nextblock m2)%positive)).
   intros. eapply SMV23. eapply as_inj_DomRng; eassumption.
assert (NOVj12':= RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _
                  MInj23 _ _ _ _ _ HeqMKI).
exists (convertL nu12 (removeUndefs (as_inj nu12) (as_inj nu') prej12')
          (*FreshSrc:*) (fun b => andb (DomSrc nu' b) (negb (DomSrc nu12 b)))
          (*FreshMid:*) (FreshDom (as_inj nu23) j23')).
exists (convertR nu23 j23'
          (*FreshMid:*) (FreshDom (as_inj nu23) j23')
          (*FreshTgt:*) (fun b => andb (DomTgt nu' b) (negb (DomTgt nu23 b)))).
split; trivial.
split; trivial.
remember (removeUndefs (as_inj nu12) (as_inj nu') prej12') as j12'.
assert (ConvertL_J12':
    as_inj
     (convertL nu12 j12'
        (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
        (FreshDom (as_inj nu23) j23')) = j12').
    extensionality b.
    intros. unfold as_inj.
     rewrite convertL_extern, convertL_local.
     remember (j12' b) as d.
     destruct d; apply eq_sym in Heqd.
       destruct p. unfold join.
       remember (extern_of nu12 b) as q.
       destruct q; apply eq_sym in Heqq.
         destruct p. apply extern_in_all in Heqq.
            rewrite (inc12 _ _ _ Heqq) in Heqd. apply Heqd.
       remember (local_of nu12 b) as w.
       destruct w; apply eq_sym in Heqw.
         destruct p.
         apply local_in_all in Heqw.
            rewrite (inc12 _ _ _ Heqw) in Heqd. apply Heqd.
            assumption.
      rewrite Heqd. trivial.
     assert (A:= inject_incr_inv _ _ inc12 _ Heqd).
       destruct (joinD_None _ _ _ A).
       unfold join. rewrite H, H0, Heqd. trivial.
rewrite ConvertL_J12' in *.
 rewrite convertL_extern, convertL_frgnBlocksTgt,
         convertL_pubBlocksTgt, convertL_locBlocksTgt,
         convertL_extBlocksTgt.
assert (Inj12': Mem.inject j12' m1' m2').
    clear ConvertL_J12'.
    assert (Perm12': forall b1 b2 delta ofs k p,
             j12' b1 = Some (b2, delta) ->
             Mem.perm m1' b1 ofs k p -> Mem.perm m2' b2 (ofs + delta) k p).
        intros.
        apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
          specialize (H2 k (ofs+delta)).
          remember (as_inj nu12 b1) as AsInj1.
          destruct AsInj1; apply eq_sym in HeqAsInj1.
          Focus 2. clear H2. destruct (sep12 _ _ _ HeqAsInj1 H).
                   contradiction.
          destruct p0.
          rewrite (inc12 _ _ _ HeqAsInj1) in H.  inv H.
          assert (Val_b1:= VBj12_1 _ _ _ HeqAsInj1).
          assert (PMAX: Mem.perm m1 b1 ofs Max Nonempty).
                    apply Fwd1. assumption.
                    eapply Mem.perm_implies. eapply Mem.perm_max.
                               apply H0. apply perm_any_N.
          remember (locBlocksSrc nu23 b2) as Locb2.
          destruct Locb2; apply eq_sym in HeqLocb2.
          (*case locBlocksSrc nu23 b2 = true*)
            (*First, establish that local_of nu12 b1 = Some (b2, delta) etc*)
            destruct (joinD_Some _ _ _ _ _ HeqAsInj1) as [EXT12 | [NoEXT12 LOC12]].
              destruct (extern_DomRng _ WDnu12 _ _ _ EXT12) as [? ?].
              rewrite GlueExt in H3.
              destruct (disjoint_extern_local_Src _ WDnu23 b2); congruence.
            destruct (local_DomRng _ WDnu12 _ _ _ LOC12) as [locBSrc1 locBTgt2].
            assert (NOV_LocNu12: Mem.meminj_no_overlap (local_of nu12) m1).
               eapply meminj_no_overlap_inject_incr.
                 apply MInj12. apply local_in_all; assumption.
            remember (pubBlocksSrc nu23 b2) as PubB2.
            destruct PubB2; apply eq_sym in HeqPubB2.
            (*case pubBlocksSrc nu23 b2 = true*)
              remember (pubBlocksSrc nu12 b1) as PubSrcb1.
              destruct PubSrcb1; apply eq_sym in HeqPubSrcb1.
              (*case pubBlocksSrc nu12 b1 = true*)
                destruct (pubSrc _ WDnu12 _  HeqPubSrcb1) as [bb2 [dd1 [PUB12 TGT2]]].
                rewrite (pub_in_local _ _ _ _ PUB12) in LOC12. inv LOC12.
                rewrite (source_SomeI (local_of nu12) _  _ b1) in H2; trivial.
                  rewrite HeqPubSrcb1 in *.
                  rewrite (perm_subst _ _ _ _ _ _ _ H2). apply H0.
                  apply pub_in_local; assumption.
              (*case pubBlocksSrc nu12 b1 = false*)
                assert (PK: Mem.perm m1 b1 ofs k p).
                  eapply UnchPrivSrc.
                    simpl. split; assumption.
                    assumption.
                    assumption.
                rewrite (source_SomeI (local_of nu12) _  _ b1) in H2; trivial.
                rewrite HeqPubSrcb1 in H2.
                rewrite (perm_subst _ _ _ _ _ _ _ H2); clear H2.
                eapply MInj12; eassumption.
            (*case pubBlocksSrc nu23 b2 = false*)
               rewrite (perm_subst _ _ _ _ _ _ _ H2); clear H2.
               eapply MInj12. apply local_in_all; eassumption.
               eapply UnchPrivSrc; simpl; trivial.
               split; trivial.
               remember (pubBlocksSrc nu12 b1) as q.
               destruct q; trivial.
               apply eq_sym in Heqq.
               destruct (pubSrc _ WDnu12 _ Heqq) as [bb2 [dd1 [PUB12 Pub2]]].
               apply pub_in_local in PUB12. rewrite PUB12 in LOC12. inv LOC12.
               apply GluePub in Pub2. rewrite Pub2 in HeqPubB2; discriminate.
          (*case locBlocksSrc nu23 b2 = false*)
             destruct (joinD_Some _ _ _ _ _ HeqAsInj1) as [EXT1 | [NoEXT1 LOC1]].
             Focus 2. destruct (local_DomRng _ WDnu12 _ _ _ LOC1).
                      rewrite GlueLoc in H3. congruence.
             destruct (extern_DomRng _ WDnu12 _ _ _ EXT1) as [HeqLocb1 HeqExtTgtb2].
             remember (source (as_inj nu12) m1 b2 (ofs + delta)) as ss.
             destruct ss.
             (*case source = Some*)
               destruct (source_SomeE _ _ _ _ _ Heqss)
                 as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
               clear Heqss. subst.
               rewrite (perm_subst _ _ _ _ _ _ _ H2); clear H2.
               destruct (eq_block bb1 b1); subst.
                 rewrite JJ in HeqAsInj1. inv HeqAsInj1.
                 assert (Arith: ofs11 = ofs) by omega.
                 subst; assumption.
              destruct (Mem.mi_no_overlap _ _ _ MInj12
                           bb1 _ _ _ _ _ _ _ n JJ HeqAsInj1 PERM PMAX).
                exfalso. apply H; trivial.
                exfalso. apply H. rewrite Off2. trivial.
             (*case source = None*)
               remember (as_inj nu23 b2) as AsInj2.
               destruct AsInj2; apply eq_sym in HeqAsInj2.
               (*case as_inj nu23 b2 = Some(..)*)
                 destruct p0 as [b3 d2].
                 exfalso.
                 eapply (source_NoneE _ _ _ _ Heqss _
                        _ Val_b1 HeqAsInj1).
                 assert (Arith: ofs + delta - delta = ofs) by omega.
                 rewrite Arith. apply PMAX.
               (*case as_inj nu23 b2 = None*)
                  rewrite (perm_subst _ _ _ _ _ _ _ H2); clear H2.
                  remember (frgnBlocksSrc nu23 b2) as FrgnSrc2.
                  destruct FrgnSrc2; apply eq_sym in HeqFrgnSrc2.
                    destruct (frgnSrc _ WDnu23 _ HeqFrgnSrc2) as [b3 [d2 [FRG2 FrgTgt3]]].
                    rewrite (foreign_in_all _ _ _ _ FRG2) in HeqAsInj2. inv HeqAsInj2.
                  remember (frgnBlocksSrc nu12 b1) as FrgnSrc1.
                  destruct FrgnSrc1; apply eq_sym in HeqFrgnSrc1.
                    destruct (frgnSrc _ WDnu12 _ HeqFrgnSrc1) as [bb2 [dd1 [FRG1 FrgTgt2]]].
                    rewrite (foreign_in_extern _ _ _ _ FRG1) in EXT1. inv EXT1.
                    apply GlueFrgn in FrgTgt2. rewrite FrgTgt2 in HeqFrgnSrc2. inv HeqFrgnSrc2.
                 (*case frgnBlocksSrc nu12 b1 = frgnBlocksSrc nu23 b2 = false*)
                   exfalso.
                   eapply (source_NoneE _ _ _ _ Heqss _
                        _ Val_b1 HeqAsInj1).
                   assert (Arith: ofs + delta - delta = ofs) by omega.
                   rewrite Arith. apply PMAX.
        (*case ~ valid_block m2 b2*)
            specialize (H2 k (ofs+delta)).
            rewrite (source_SomeI j12' _  _ b1) in H2.
              rewrite (perm_subst _ _ _ _ _ _ _ H2). apply H0.
              subst. apply (RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _
                    MInj23 _ _ _ _ _ HeqMKI).
              assumption.
              eapply Mem.perm_implies. eapply Mem.perm_max.
                    apply H0. apply perm_any_N.
    assert (INJ:Mem.mem_inj j12' m1' m2').
      split. apply Perm12'.
      (*valid_access*)
          intros. rewrite Heqj12' in H.
          clear Heqj12'.
          unfold removeUndefs in H.
          remember (as_inj nu12 b1) as d.
          destruct d; apply eq_sym in Heqd.
            destruct p0 as [bb2 dd]. inv H.
            eapply MInj12. eassumption.
            assert (MR: Mem.range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p).
               intros z. intros. specialize (H0 _ H).
               eapply Fwd1. eapply VBj12_1. apply Heqd. apply H0.
               eassumption.
          remember (as_inj nu' b1) as q.
          destruct q; apply eq_sym in Heqq; try inv H.
          destruct p0.
            destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                      HeqMKI VB12 VBj23_1 _ _ _ H2)
            as [HX | [HX | HX]].
              destruct HX as [J12 [Val1 Val2]]. rewrite J12 in Heqd. inv Heqd.
              destruct HX as [? [? [? [? D]]]]. subst. apply Z.divide_0_r.
              destruct HX as [? [? [? [? [? D]]]]]. subst. apply Z.divide_0_r.
      (*memval  j12' m1' m2'.*)
          intros.
          apply (cont_split _ _ _ _ _ (CONT b2)); intros; clear CONT.
         (*case Mem.valid_block m2 b2*)
            specialize (H2 (ofs + delta)).
            remember (as_inj nu12 b1) as AsInj1.
            destruct AsInj1; apply eq_sym in HeqAsInj1.
            Focus 2. clear H2. destruct (sep12 _ _ _ HeqAsInj1 H).
                     contradiction.
            destruct p.
            rewrite (inc12 _ _ _ HeqAsInj1) in H.  inv H.
            assert (Val_b1:= VBj12_1 _ _ _ HeqAsInj1).
            assert (PMAX: Mem.perm m1 b1 ofs Max Nonempty).
                    apply Fwd1. assumption.
                    eapply Mem.perm_implies. eapply Mem.perm_max.
                               apply H0. apply perm_any_N.
            remember (locBlocksSrc nu23 b2) as Myb2.
            destruct Myb2; apply eq_sym in HeqMyb2.
            (*case locBlocksSrc nu23 b2 = true*)
              (*First, establish that local_of nu12 b1 = Some (b2, delta) etc*)
              destruct (joinD_Some _ _ _ _ _ HeqAsInj1) as [EXT12 | [NoEXT12 LOC12]].
                destruct (extern_DomRng _ WDnu12 _ _ _ EXT12) as [? ?].
                rewrite GlueExt in H4.
                destruct (disjoint_extern_local_Src _ WDnu23 b2); congruence.
              destruct (local_DomRng _ WDnu12 _ _ _ LOC12) as [locBSrc1 locBTgt2].
              remember (pubBlocksSrc nu23 b2) as PubB2.
              destruct PubB2; apply eq_sym in HeqPubB2.
              (*case pubBlocksSrc nu23 b2 = true*)
                destruct (pubSrc _ WDnu23 _ HeqPubB2) as [b3 [d2 [Pub23 PubTgt3]]].
                assert (AsInj23: as_inj nu23 b2 = Some (b3, d2)) by (apply pub_in_all; assumption).
                assert (NOVlocal12: Mem.meminj_no_overlap (local_of nu12) m1).
                  eapply meminj_no_overlap_inject_incr.
                  apply MInj12. apply local_in_all; assumption.
                rewrite (source_SomeI (local_of nu12) _  _ b1) in H2; trivial.
                remember (pubBlocksSrc nu12 b1) as PubSrcb1.
                destruct PubSrcb1; apply eq_sym in HeqPubSrcb1; rewrite H2; clear H2.
                (*case pubBlocksSrc nu12 b1 = true*)
                  destruct (pubSrc _ WDnu12 _  HeqPubSrcb1) as [bb2 [dd1 [PUB12 TGT2]]].
                  rewrite (pub_in_local _ _ _ _ PUB12) in LOC12. inv LOC12.
                  assert (Nu'b1: as_inj nu' b1 = Some (b3, delta+d2)).
                      rewrite ID. eapply compose_meminjI_Some; try eassumption.
                             apply inc12. eassumption. apply (inc23 _ _ _ AsInj23).
                  assert (MV:= Mem.mi_memval _ _ _
                                 (Mem.mi_inj _ _ _ MemInjNu') _ _ _ _ Nu'b1 H0).
                  inv MV; try constructor.
                           simpl.
                           rewrite ID in H4.
                           destruct (compose_meminjD_Some _ _ _ _ _ H4)
                              as [bb2 [dd1 [dd2 [JJ1 [JJ2 Delta]]]]].
                           rewrite JJ1. econstructor.
                             apply JJ1. reflexivity.
               (*case pubBlocksSrc nu12 b1 = false*)
                  assert (PK: Mem.perm m1 b1 ofs Cur Readable).
                    solve[eapply UnchPrivSrc; eauto].
                  destruct UnchPrivSrc as [_ UPS].
                  rewrite UPS; try assumption; try (split; assumption).
                  eapply memval_inject_incr.
                    apply MInj12; assumption.
                    apply inc12.
              (*case pubBlocksSrc nu23 b2 = false*)
                rewrite H2; clear H2.
                remember (pubBlocksSrc nu12 b1) as PubSrcb1.
                destruct PubSrcb1; apply eq_sym in HeqPubSrcb1.
                  destruct (pubSrc _ WDnu12 _  HeqPubSrcb1) as [bb2 [dd1 [PUB12 TGT2]]].
                  rewrite (pub_in_local _ _ _ _ PUB12) in LOC12. inv LOC12.
                  apply GluePub in TGT2. rewrite TGT2 in HeqPubB2. inv HeqPubB2.
                (*as the b1 is not public we can again aply Unch11*)
                assert (PK: Mem.perm m1 b1 ofs Cur Readable).
                  solve [eapply UnchPrivSrc; eauto].
                destruct UnchPrivSrc as [_ UPS].
                  rewrite UPS; try assumption; try (split; assumption).
                  eapply memval_inject_incr.
                    apply MInj12; assumption.
                    apply inc12.
            (*case locBlocksSrc nu23 b2 = false*)
              rewrite (source_SomeI (as_inj nu12) _  _ b1) in H2; try eassumption.
                   Focus 2. eapply MInj12.
              rewrite H2; clear H2.
              assert (EXT1: extern_of nu12 b1 = Some (b2, delta)).
                destruct (joinD_Some _ _ _ _ _ HeqAsInj1); trivial.
                destruct H.
                destruct (local_DomRng _ WDnu12 _ _ _ H2).
                rewrite GlueLoc in H5. congruence.
              destruct (Norm12 _ _ _ EXT1) as [b3 [d2 EXT2]].
               assert (Nu'b1: as_inj nu' b1 = Some (b3, delta+d2)).
                      rewrite ID. eapply compose_meminjI_Some; try eassumption.
                             apply inc12. eassumption.
                             apply inc23. apply (extern_in_all _ _ _ _ EXT2).
                  assert (MV:= Mem.mi_memval _ _ _
                                 (Mem.mi_inj _ _ _ MemInjNu') _ _ _ _ Nu'b1 H0).
                  inv MV; try constructor.
                           simpl.
                           rewrite ID in H4.
                           destruct (compose_meminjD_Some _ _ _ _ _ H4)
                              as [bb2 [dd1 [dd2 [JJ1 [JJ2 Delta]]]]].
                           rewrite JJ1. econstructor.
                             apply JJ1. reflexivity.
         (*case ~ Mem.valid_block m2 b2*)
            specialize (H2 (ofs + delta)).
            assert (J12: as_inj nu12 b1 = None).
               remember (as_inj nu12 b1) as d.
               destruct d; apply eq_sym in Heqd; trivial.
                     destruct p. rewrite (inc12 _ _ _ Heqd) in H. inv H.
                     exfalso. apply H1. apply (VBj12_2 _ _ _ Heqd).
            assert (MX: Mem.perm m1' b1 ofs Max Nonempty).
                  eapply Mem.perm_max. eapply Mem.perm_implies.
                  apply H0. apply perm_any_N.
            rewrite (source_SomeI _ _  _ b1) in H2; try eassumption.
            rewrite H2; clear H2.
            remember (ZMap.get ofs (PMap.get b1 (Mem.mem_contents m1'))) as v.
            remember (j23' b2) as j23'b2.
                   destruct j23'b2; apply eq_sym in Heqj23'b2.
                   (*j23' b2 = Some p*)
                       destruct p as [b3 delta3].
                       assert (COMP': as_inj nu' b1 = Some(b3, delta+delta3)).
                            rewrite ID. eapply compose_meminjI_Some; eassumption.
                       assert (MV:= Mem.mi_memval _ _ _
                           (Mem.mi_inj _ _ _ MemInjNu') _ _  _ _ COMP' H0).
                       subst.
                       inv MV; try constructor.
                       simpl. rewrite ID in H5.
                       apply compose_meminjD_Some in H5.
                       destruct H5 as [bb1 [off1 [off [JJ1 [JJ2 Delta]]]]].
                       subst.
                       rewrite JJ1. econstructor. apply JJ1. trivial.
                   (*j23' b2 = None - we do a slightly different proof than in interp6 mem_interpolationII etc*)
                       subst.
                       unfold removeUndefs in H. rewrite J12 in H.
                       remember (as_inj nu' b1) as d.
                       destruct d; try inv H.
                       destruct p.
                       assert (VB2: Mem.valid_block m2' b2).
                           destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI) as [XX | XX].
                             destruct XX as [? [? [? [? ?]]]]. subst. rewrite J12 in H4. discriminate.
                             destruct XX as [nn [? [? [? ?]]]].
                               destruct (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI _ _ _ H4) as [XX | [XX | XX]].
                                 rewrite XX in J12; discriminate.
                                 destruct XX as [? [? ?]]; subst. unfold Mem.valid_block. rewrite <- H6. xomega.
                                 destruct XX as [mm [[? ?] ?]]; subst.
                                 assert (Mem.valid_block m1' (Mem.nextblock m1 + mm)%positive).
                                   eapply VBj'. rewrite <- Heqd. reflexivity.
                                 clear - H2 H6 H7. unfold Mem.valid_block in *.
                                     rewrite <- H6. rewrite <- H2 in H7. clear H2 H6. xomega.
                       destruct (mkInjections_5 _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1 VBj12_2 VBj23_1 VBj' _ VB2 Heqj23'b2) as [[XXa XXb] | [[XXa XXb] | [nn [XXa XXb]]]].
                         contradiction.
                         assert (b1 = Mem.nextblock m1).
                           destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI) as [ZZ | ZZ].
                             destruct ZZ as [? [? [? [? ?]]]]. subst. rewrite J12 in H4. discriminate.
                             destruct ZZ as [nn [? [? [? ?]]]]. subst.
                               destruct (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI _ _ _ H4) as [AA | [AA | AA]].
                                 rewrite AA in J12; discriminate.
                                 destruct AA as [? [? ?]]; subst. trivial.
                                 destruct AA as [mm [[? ?] ?]]; subst. clear - H8. exfalso. rewrite Pos.add_comm in H8. apply eq_sym in H8. eapply Pos.add_no_neutral. apply H8.
                           subst. rewrite XXb in Heqd. discriminate.
                         assert (b1 = (Mem.nextblock m1 + nn)%positive). clear Heqd.
                           destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI) as [ZZ | ZZ].
                             destruct ZZ as [? [? [? [? ?]]]]. subst. rewrite J12 in H4. discriminate.
                             destruct ZZ as [kk [? [? [? ?]]]]. subst.
                               destruct (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI _ _ _ H4) as [AA | [AA | AA]].
                                 rewrite AA in J12; discriminate.
                                 destruct AA as [? [? ?]]; subst. clear - H8. exfalso. rewrite Pos.add_comm in H8. eapply Pos.add_no_neutral. apply H8.
                                 destruct AA as [mm [[? ?] ?]]; subst.
                                    assert (nn=mm); subst; trivial. clear - H8. eapply Pos.add_reg_l. eassumption.
                           subst. rewrite XXb in Heqd. discriminate.
   split. apply INJ.
   (* mi_freeblocks*)  intros b1 Hb1.
        remember (j12' b1) as d.
        destruct d; apply eq_sym in Heqd; trivial. destruct p.
        remember (as_inj nu12 b1) as dd.
        destruct dd; apply eq_sym in Heqdd.
            destruct p.
            exfalso. apply Hb1. apply Fwd1. apply (VBj12_1 _ _ _ Heqdd).
        remember (as_inj nu' b1) as ddd.
        destruct ddd; apply eq_sym in Heqddd.
            destruct p. exfalso. apply Hb1. apply (VBj' _ _ _ Heqddd).
        rewrite Heqj12' in Heqd.
        unfold removeUndefs in Heqd. rewrite Heqdd, Heqddd in Heqd.
        inv Heqd.
  (*mi_mappedblock*) intros.
     rewrite Heqj12' in H.
        unfold removeUndefs in H.
        remember (as_inj nu12 b) as dd.
        destruct dd; apply eq_sym in Heqdd.
            destruct p. inv H. apply Fwd2. apply (VBj12_2 _ _ _ Heqdd).
        remember (as_inj nu' b) as ddd.
        destruct ddd; apply eq_sym in Heqddd.
          destruct p.
          destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                      HeqMKI Val12 VBj23_1 _ _ _ H)
          as [MK | [MK | MK]].
            destruct MK as [J12 [Val1 Val2]]. apply Fwd2. apply Val2.
            destruct MK as [_ [_ [_ [_ D]]]]. apply D.
            destruct MK as [? [_ [_ [_ [_ D]]]]]. apply D.
        inv H.
  (*no_overlap*)
       rewrite Heqj12'.
       apply (RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _ MInj23 _ _ _ _ _ HeqMKI).
  (*representable*)
       intros.
       rewrite Heqj12' in H.
       unfold removeUndefs in H.
       remember (as_inj nu12 b) as d.
       destruct d; apply eq_sym in Heqd.
          destruct p. inv H.
          destruct H0.
          (*location ofs*)
            eapply MInj12. apply Heqd.
            left. apply Fwd1. apply (VBj12_1 _ _ _ Heqd). apply H.
          (*location ofs -1*)
            eapply MInj12. apply Heqd.
            right. apply Fwd1. apply (VBj12_1 _ _ _ Heqd). apply H.
       remember (as_inj nu' b) as dd.
       destruct dd; apply eq_sym in Heqdd.
          destruct p.
          destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                     HeqMKI VB12  VBj23_1 _ _ _ H).
              destruct H1. rewrite H1 in Heqd. discriminate.
              destruct H1 as [HH | HH].
              destruct HH as [A [B [C [D E]]]]; subst.
                 split. omega.
                        rewrite Zplus_0_r. apply Int.unsigned_range_2.
              destruct HH as [M [A [B [C [D E]]]]]; subst.
                 split. omega.
                        rewrite Zplus_0_r. apply Int.unsigned_range_2.
       inv H.
assert (ConvertR_J23': as_inj
     (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
        (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b))) = j23').
   clear ConvertL_J12'. unfold as_inj.
   rewrite convertR_extern, convertR_local.
   extensionality b. unfold join.
   remember (extern_of nu23 b) as d.
   destruct d; apply eq_sym in Heqd.
         destruct p. apply extern_in_all in Heqd.
         rewrite (inc23 _ _ _ Heqd). trivial.
   remember (local_of nu23 b) as q.
   destruct q; trivial; apply eq_sym in Heqq.
         destruct p.
         apply local_in_all in Heqq; trivial.
         rewrite (inc23 _ _ _ Heqq). trivial.
   destruct (j23' b); trivial. destruct p; trivial.
rewrite ConvertR_J23' in *.
  rewrite convertR_extern, convertR_frgnBlocksSrc,
          convertR_pubBlocksSrc, convertR_locBlocksSrc,
          convertR_extBlocksSrc.

assert (Inj23':Mem.inject j23' m2' m3').
  clear ConvertL_J12' ConvertR_J23'.
  assert (Perm23': forall b1 b2 delta ofs k p,
                j23' b1 = Some (b2, delta) ->
                Mem.perm m2' b1 ofs k p -> Mem.perm m3' b2 (ofs + delta) k p).
      intros b2 b3; intros.
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
      (*valid*)
        specialize (H2 k ofs).
        assert (FF: as_inj nu23 b2 = Some (b3, delta)).
           remember (as_inj nu23 b2) as dd.
           destruct dd; apply eq_sym in Heqdd.
             rewrite (inject_incr_coincide _ _ inc23 _ _ H _ Heqdd). trivial.
           destruct (sep23 _ _ _ Heqdd H). exfalso. apply (H3 H1).
        (*rewrite FF in H2.*)
        remember (locBlocksSrc nu23 b2) as LocB2.
        destruct LocB2; apply eq_sym in HeqLocB2.
        (*case locBlocksSrc nu23 b2 = true*)
          assert (extern_of nu23 b2 = None /\ local_of nu23 b2 = Some (b3, delta)).
            destruct (joinD_Some _ _ _ _ _ FF).
              destruct (extern_DomRng _ WDnu23 _ _ _ H3) as [? ?].
              destruct (disjoint_extern_local_Src _ WDnu23 b2); congruence.
            assumption.
          destruct H3 as [NoEXT23 LOC23].
          remember (pubBlocksSrc nu23 b2) as PubB2.
          destruct PubB2; apply eq_sym in HeqPubB2.
          (*case pubBlocksSrc nu23 b2 = true*)
            destruct (pubSrc _ WDnu23 _ HeqPubB2) as [b33 [d33 [PUB23 pubTGT3]]].
            rewrite (pub_in_local _ _ _ _ PUB23) in LOC23. inv LOC23.
            remember (source (local_of nu12) m1 b2 ofs) as d.
            destruct d.
            (*source (local_of nu12)  m1 b2 ofs = Some p0*)
              destruct p0.
              destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [d1 [ofs1 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
              subst. inv PP.
              rewrite <- Zplus_assoc.
                assert (J: as_inj nu' b1 = Some (b3, d1 + delta)).
                  rewrite ID.
                  eapply compose_meminjI_Some.
                     apply inc12. apply local_in_all; eassumption.
                     apply inc23. assumption.
              remember (pubBlocksSrc nu12 b1) as d.
              destruct d; apply eq_sym in Heqd;
                rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0; clear H2.
                eapply MemInjNu'. apply J. apply H0.
              apply UnchLOOR13.
                 split. eapply (pub_locBlocks _ WDnu23). eassumption.
                 intros bb1; intros. simpl.
                 remember (pubBlocksSrc nu12 bb1) as d.
                 destruct d; try (right; reflexivity).
                 apply eq_sym in Heqd0. left. intros N.
                 destruct (eq_block bb1 b1); subst; simpl.
                   rewrite Heqd0 in Heqd. discriminate.
                 assert (compose_meminj (as_inj nu12) (as_inj nu23) b1 = Some (b3, d1+delta)).
                   eapply compose_meminjI_Some; try eassumption. apply local_in_all; eassumption.
                 destruct (compose_meminjD_Some _ _ _ _ _ H2) as [bb2 [dd1 [dd2 [LC1 [LC2 DD]]]]]; clear H2.
                   apply local_in_all in LC1; trivial.
                   apply local_in_all in LC2; trivial.  subst.
                   assert (compose_meminj (as_inj nu12) (as_inj nu23) bb1 = Some (b3, dd1 + dd2)).
                    eapply compose_meminjI_Some; try eassumption.
                 destruct (Mem.mi_no_overlap _ _ _ (Mem.inject_compose _ _ _ _ _ MInj12 MInj23) bb1 _ _ _ _ _ _ _ n H2 H3 N PERM).
                   apply H4; trivial.
                   apply H4; clear H4. omega.
                eapply VBj23_2; eassumption.
              rewrite Zplus_assoc. eapply MInj23; eassumption.
            (*source (pub_of nu12) m1 b2 ofs = None*)
              rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0; clear H2.
              assert (MX: Mem.perm m2 b2 ofs Max Nonempty).
                  eapply Mem.perm_max. eapply Mem.perm_implies.
                     apply H0. apply perm_any_N.
              assert (SRC:= source_NoneE _ _ _ _ Heqd); clear Heqd.
              apply UnchLOOR13.
                 split. eapply (pub_locBlocks _ WDnu23); eassumption.
                 intros bb1; intros. simpl.
                 remember (pubBlocksSrc nu12 bb1) as d.
                 destruct d; try (right; reflexivity).
                 apply eq_sym in Heqd. left.
                 simpl in H2.
                 destruct (compose_meminjD_Some _ _ _ _ _ H2) as [bb2 [dd1 [dd2 [LC1 [LC2 DD]]]]]; clear H2.
                 subst.
                 destruct (eq_block bb2 b2); subst.
                   rewrite (pub_in_local _ _ _ _ PUB23) in LC2. inv LC2.
                   assert (Mem.valid_block m1 bb1).
                     eapply VBj12_1. apply local_in_all; eassumption.
                   assert (Arith: ofs + dd2 - (dd1 + dd2) = ofs - dd1) by omega.
                   rewrite Arith. apply (SRC _ _ H2 LC1).
                 intros N. apply local_in_all in LC1; trivial.
                   apply (Mem.perm_inject (as_inj nu12) _ _ _ _ _ _ _ _ LC1 MInj12) in N.
                   apply local_in_all in LC2; trivial.
                   destruct (Mem.mi_no_overlap _ _ _ MInj23 bb2 _ _ _ _ _ _ _ n LC2 FF N MX).
                   apply H2; trivial.
                   apply H2; clear H2. omega.
                eapply VBj23_2; eassumption.
              eapply MInj23; eassumption.
          (*case pubBlocksSrc nu23 b2 = false -- HERE IS THE SPOT THAT MOTIVATED THE NEW DEFINIEION LOCAL_OUT_OF_REACH*)
            rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0; clear H2.
              apply UNCHC.
                 split. eapply (local_locBlocks _ WDnu23). eassumption.
                 intros bb2; intros.
                 remember (pubBlocksSrc nu23 bb2) as d.
                 destruct d; try (right; reflexivity).
                 apply eq_sym in Heqd. left.
                 destruct (eq_block bb2 b2); subst.
                   rewrite Heqd in HeqPubB2; discriminate.
                 intros N. apply local_in_all in H2; trivial.
                   assert (MX: Mem.perm m2 b2 ofs Max Nonempty).
                     eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. apply perm_any_N.
                   destruct (Mem.mi_no_overlap _ _ _ MInj23 bb2 _ _ _ _ _ _ _ n H2 FF N MX).
                   apply H3; trivial.
                   apply H3; clear H3. omega.
                eapply VBj23_2; eassumption.
              eapply MInj23; eassumption.
        (*case locBlocksSrc nu23 b2 = false*)
          remember (source (as_inj nu12) m1 b2 ofs) as ss.
          destruct ss.
            destruct (source_SomeE _ _ _ _ _ Heqss)
                 as [b1 [d1 [ofs1 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqss.
            subst.
            rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0. clear H2.
            rewrite <- Zplus_assoc.
            eapply MemInjNu'; try eassumption.
              rewrite ID. eapply compose_meminjI_Some.
                     apply inc12. apply JJ.
                     apply inc23. assumption.
          (*source (as_inj nu12) m1 b2 ofs = None*)
            rewrite FF in H2.
            unfold Mem.perm in H0. rewrite H2 in H0. simpl in H0. contradiction.
            (*This case motivated setting perm m2' = None. In particular, assumption
              UnchLOOR13 does not help any more, in contrast to the development in
              mem_interpolation.v*)
      (*invalid*)
          assert (MX: Mem.perm m2' b2 ofs Max Nonempty).
              eapply Mem.perm_max. eapply Mem.perm_implies.
                apply H0. apply perm_any_N.
          assert (Max2':= H2 Max ofs).
          specialize (H2 k ofs).
          assert (J23: as_inj nu23 b2 = None).
              remember (as_inj nu23 b2) as d.
              destruct d; trivial. apply eq_sym in Heqd. destruct p0.
              assert (X:= VBj23_1 _ _ _ Heqd).
              exfalso.  apply (H1 X).
          remember (source j12' m1' b2 ofs) as d.
          destruct d. destruct p0.
              rewrite (perm_subst _ _ _ _ _ _ _ H2) in *; clear H2.
              rewrite (perm_subst _ _ _ _ _ _ _ Max2') in *; clear Max2'.
              destruct (source_SomeE _ _ _ _ _ Heqd)
                as [b1 [d1 [ofs1 [PP [VB [ JJ' [PERM Off2]]]]]]]; clear Heqd.
              subst. apply eq_sym in PP. inv PP.
              rewrite <- Zplus_assoc.
              assert (Jb: as_inj nu' b= Some (b3, d1 + delta)).
                  rewrite ID.
                  eapply compose_meminjI_Some; eassumption.
              eapply MemInjNu'. apply Jb. apply H0.
          unfold Mem.perm in MX. rewrite Max2' in MX.  inv MX.
  assert (MI: Mem.mem_inj j23' m2' m3').
      split.
      (*mi_perm *) apply Perm23'.
      (*valid_access*)
        intros b2 b3; intros.
          destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H)
            as [HH | [HH | HH]].
          destruct HH. eapply MInj23; try eassumption.
             intros z; intros. specialize (H0 _ H3).
              eapply Fwd2; try eassumption.
          destruct HH as [? [? ?]].
            assert (ZZ: compose_meminj j12' j23'  (Mem.nextblock m1) = Some (b3, delta)).
                   rewrite ID in H2; trivial.
            rewrite Heqj12' in ZZ. subst.
            destruct (compose_meminjD_Some _ _ _ _ _ ZZ) as
                  [b2 [dd1 [dd2 [JJ1 [JJ2 XX]]]]]; subst; clear ZZ.
            assert (J12': prej12' (Mem.nextblock m1) = Some(Mem.nextblock m2, 0)).
               remember (as_inj nu12 (Mem.nextblock m1)) as q.
               destruct q; apply eq_sym in Heqq.
                 destruct p0. rewrite (inc12 _ _ _ Heqq) in JJ1. inv JJ1.
                   apply VBj12_1 in Heqq. exfalso. unfold Mem.valid_block in Heqq. xomega.
                 unfold removeUndefs in JJ1. rewrite Heqq in JJ1. rewrite H2 in JJ1.
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ JJ1).
                   destruct H1. rewrite H1 in Heqq. discriminate.
                   destruct H1. destruct H1 as [_ [? [? [? ?]]]]. subst. assumption.
                   destruct H1 as [mm [? [? [? [? ?]]]]]; subst.
                     apply eq_sym in H1. rewrite Pos.add_comm in H1.
                     apply Pos.add_no_neutral in H1. intuition.
            assert (PRE: prej12' (Mem.nextblock m1) = Some (b2, dd1)).
              unfold removeUndefs in JJ1.
              remember (as_inj nu12 (Mem.nextblock m1)).
              destruct o; apply eq_sym in Heqo.
                destruct p0. apply VBj12_1 in Heqo. exfalso. unfold Mem.valid_block in Heqo. xomega.
              rewrite H2 in JJ1. assumption.
            rewrite J12' in PRE. inv PRE. simpl in *. clear JJ2.
            destruct (ACCESS (Mem.nextblock m2)) as [_ ZZ].
            assert (NVB2: ~ Mem.valid_block m2 (Mem.nextblock m2)).
                       unfold Mem.valid_block. xomega.
            assert (MR: Mem.range_perm m1' (Mem.nextblock m1) ofs (ofs + size_chunk chunk) Max p).
               intros z; intros.
               specialize (ZZ NVB2 Max z).
               remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1' (Mem.nextblock m2) z).
               destruct o.
               Focus 2. specialize (H0 _ H1). unfold Mem.perm in H0. rewrite ZZ in H0. simpl in H0. intuition.
               destruct (source_SomeE _ _ _ _ _ Heqo)
                        as [b1 [dd1 [ofs1 [PPP [VB [ JJ' [PERM Off2]]]]]]]; clear Heqo.
               subst. specialize (H0 _ H1).
               rewrite (perm_subst _ _ _ _ _ _ _ ZZ) in H0; clear ZZ.
               assert (prej12'  b1 = Some (Mem.nextblock m2, dd1)).
                 unfold removeUndefs in JJ'.
                 remember (as_inj nu12 b1).
                 destruct o; apply eq_sym in Heqo.
                   destruct p0. inv JJ'. apply VBj12_2 in Heqo. contradiction.
                 remember (as_inj nu' b1).
                 destruct o. destruct p0. assumption. inv JJ'.
               assert (b1 = Mem.nextblock m1).
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ H4).
                 destruct H5. apply VBj12_2 in H5. contradiction.
                 destruct H5. destruct H5; trivial.
                 destruct H5 as [mm1 [? [? [? [? ?]]]]]. subst.
                   apply eq_sym in H6. rewrite Pos.add_comm in H6.
                   apply Pos.add_no_neutral in H6. intuition.
               subst. rewrite J12' in H4. inv H4. rewrite Zplus_0_r. assumption.
             eapply MemInjNu'; eassumption.
          destruct HH as [mm [? [? ?]]]. subst. clear H3.
            assert (ZZ: compose_meminj (removeUndefs (as_inj nu12) (as_inj nu') prej12') j23' ((Mem.nextblock m1+ mm)%positive) = Some (b3, delta)).
                   rewrite <- ID; trivial.
               destruct (compose_meminjD_Some _ _ _ _ _ ZZ) as
                  [b2 [dd1 [dd2 [JJ1 [JJ2 XX]]]]]. subst; clear ZZ.
            assert (J12': prej12' ((Mem.nextblock m1+ mm)%positive) = Some((Mem.nextblock m2+ mm)%positive, 0)).
               remember (as_inj nu12 ((Mem.nextblock m1+ mm)%positive)) as q.
               destruct q; apply eq_sym in Heqq.
                 destruct p0. rewrite (inc12 _ _ _ Heqq) in JJ1. inv JJ1.
                   apply VBj12_1 in Heqq. exfalso. unfold Mem.valid_block in Heqq. xomega.
                 unfold removeUndefs in JJ1. rewrite Heqq in JJ1. rewrite H2 in JJ1.
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ JJ1).
                   destruct H1. rewrite H1 in Heqq. discriminate.
                   destruct H1. destruct H1 as [? [? [? [? ?]]]]. subst.
                     rewrite Pos.add_comm in H1.
                     apply Pos.add_no_neutral in H1. intuition.
                   destruct H1 as [mm2 [? [? [? [? ?]]]]]; subst.
                     apply Pos.add_reg_l in H1. subst.
                   assumption.
            assert (PRE: prej12' ((Mem.nextblock m1+ mm)%positive) = Some (b2, dd1)).
              unfold removeUndefs in JJ1.
              remember (as_inj nu12 ((Mem.nextblock m1+ mm)%positive)).
              destruct o; apply eq_sym in Heqo.
                destruct p0. apply VBj12_1 in Heqo. exfalso. unfold Mem.valid_block in Heqo. xomega.
              rewrite H2 in JJ1. assumption.
            rewrite J12' in PRE. inv PRE. simpl in *. clear JJ2.
            destruct (ACCESS ((Mem.nextblock m2+ mm)%positive)) as [_ ZZ].
            assert (NVB2: ~ Mem.valid_block m2 ((Mem.nextblock m2+ mm)%positive)).
                       unfold Mem.valid_block. xomega.
            assert (MR: Mem.range_perm m1' ((Mem.nextblock m1+ mm)%positive) ofs (ofs + size_chunk chunk) Max p).
               intros z; intros.
               specialize (ZZ NVB2 Max z).
               remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1'
                      (Mem.nextblock m2 + mm)%positive z).
               destruct o.
               Focus 2. specialize (H0 _ H1). unfold Mem.perm in H0. rewrite ZZ in H0. simpl in H0. intuition.
               destruct (source_SomeE _ _ _ _ _ Heqo)
                        as [bb1 [dd1 [ofs11 [PPP [VB [ JJ' [PERM Off2]]]]]]]. clear Heqo.
               subst. specialize (H0 _ H1).
               rewrite (perm_subst _ _ _ _ _ _ _ ZZ) in H0. clear ZZ.
               assert (prej12'  bb1 = Some ((Mem.nextblock m2+ mm)%positive, dd1)).
                 unfold removeUndefs in JJ'.
                 remember (as_inj nu12 bb1).
                 destruct o; apply eq_sym in Heqo.
                   destruct p0. inv JJ'. apply VBj12_2 in Heqo. contradiction.
                 remember (as_inj nu' bb1).
                 destruct o. destruct p0. assumption. inv JJ'.
               assert (bb1 = (Mem.nextblock m1+ mm)%positive).
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ H3).
                 destruct H4. apply VBj12_2 in H4. contradiction.
                 destruct H4. destruct H4 as [? [? ?]]; subst.
                   rewrite Pos.add_comm in H5.
                   apply Pos.add_no_neutral in H5. intuition.
                 destruct H4 as [mm1 [? [? [? [? ?]]]]]. subst.
                   apply Pos.add_reg_l in H5. subst. trivial.
               subst. rewrite J12' in H3. inv H3. rewrite Zplus_0_r. assumption.
             eapply MemInjNu'; eassumption.
      (*memval j23' m2' m3'*) intros b2 ofs2 b3 delta3 Jb2 Perm2.
          assert (Perm2Max: Mem.perm m2' b2 ofs2  Max Nonempty).
             eapply Mem.perm_max. eapply Mem.perm_implies.
                        apply Perm2. constructor.
          destruct (ACCESS b2) as [Valid Invalid].
          apply (cont_split _ _ _ _ _ (CONT b2)); intros; clear CONT.
          (*case Mem.valid_block m2 b2*)
             assert (ValidMax := Valid H Max ofs2).
             specialize (Valid H Cur ofs2). clear Invalid.
             specialize (H0 ofs2).
             assert (J23: as_inj nu23 b2 = Some (b3, delta3)).
                 remember (as_inj nu23 b2) as d. destruct d; apply eq_sym in Heqd.
                    destruct p. rewrite (inc23 _ _ _ Heqd) in Jb2. apply Jb2.
                    destruct (sep23 _ _ _ Heqd Jb2). exfalso. apply (H2 H).
             rewrite J23 in Valid, ValidMax. (*rewrite Jb2 in H0.*)
             remember (locBlocksSrc nu23 b2) as LocB2.
             destruct LocB2; apply eq_sym in HeqLocB2.
               assert (LOC23: local_of nu23 b2 = Some (b3, delta3)).
                  destruct (joinD_Some _ _ _ _ _ J23) as [EXT | [EXT LOC]]; trivial.
                  destruct (extern_DomRng _ WDnu23 _ _ _ EXT).
                  destruct (disjoint_extern_local_Src _ WDnu23 b2); congruence.
               remember (pubBlocksSrc nu23 b2) as PubB2.
               destruct PubB2; apply eq_sym in HeqPubB2.
                 remember (source (local_of nu12) m1 b2 ofs2) as ss.
                 destruct ss.
                 (*source (local_of nu12) m1 b2 ofs2  = Some p *)
                   destruct (source_SomeE _ _ _ _ _ Heqss)
                     as [b1 [delta2 [ofs1 [PP [Valb1 [ Jb1 [Perm1 Off]]]]]]].
                   clear Heqss; subst.
                     assert (J': as_inj nu' b1 = Some (b3, delta2 + delta3)).
                       rewrite ID. eapply compose_meminjI_Some; try eassumption.
                        apply inc12. apply local_in_all; eassumption.
                   remember (pubBlocksSrc nu12 b1) as d.
                   destruct d; apply eq_sym in Heqd.
                   (*case pubBlocksSrc nu12 b1 = true*)
                     rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2; clear Valid.
                     rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max; clear ValidMax.
                     rewrite H0 in *; clear H0. simpl in *.
                     assert (Perm1'Max: Mem.perm m1' b1 ofs1 Max Nonempty).
                       eapply Mem.perm_max; eassumption.
                     specialize (Mem.mi_memval _ _ _
                          (Mem.mi_inj _ _ _ MemInjNu') _ _  _ _ J' Perm2).
                     intros MemVal13'.
                     rewrite <- Zplus_assoc.
                     inv MemVal13'; simpl in *; try econstructor.
                        rewrite ID in H3.
                        destruct (compose_meminjD_Some _ _ _ _ _ H3)
                           as [bb2 [dd2 [dd3 [RR [JJ23  DD]]]]]; subst; clear H3.
                        rewrite RR. econstructor. eassumption.
                          rewrite Int.add_assoc. decEq. unfold Int.add.
                          apply Int.eqm_samerepr. auto with ints.
                   (*case pubBlocksSrc nu12 b1 = false*)
                     rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2; clear Valid.
                     rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max; clear ValidMax.
                     rewrite H0 in *; clear H0. simpl in *.
                     destruct UnchLOOR13 as [UP3 UV3].
                     rewrite UV3.
                       eapply memval_inject_incr. eapply MInj23. assumption. assumption. assumption.
                     split; simpl. eapply local_locBlocks; eassumption.
                       intros. destruct (compose_meminjD_Some _ _ _ _ _ H0) as [bb2 [dd1 [dd2 [LC12 [LC23 DD]]]]]; clear H0.
                         subst.
                         destruct (eq_block b0 b1); subst.
                           right; assumption.
                         remember (pubBlocksSrc nu12 b0) as d.
                         destruct d; try (right; reflexivity).
                         left; apply eq_sym in Heqd.
                         intros N.
                         assert (compose_meminj (as_inj nu12) (as_inj nu23) b0 = Some(b3,dd1+dd2)).
                            apply local_in_all in LC12; trivial.
                            apply local_in_all in LC23; trivial.
                            eapply compose_meminjI_Some; eassumption.
                         assert (compose_meminj (as_inj nu12) (as_inj nu23) b1 = Some(b3,delta2+delta3)).
                            apply local_in_all in Jb1; trivial.
                            eapply compose_meminjI_Some; eassumption.
                         destruct (Mem.mi_no_overlap _ _ _ (Mem.inject_compose _ _ _ _ _ MInj12 MInj23)
                                  _ _ _ _ _ _ _ _ n H0 H2 N Perm1).
                           apply H3; trivial.
                           apply H3; clear H3. omega.
                     eapply MInj23; eassumption.
                 (*case source  j12 m1 b2 ofs2  = None *)
                   rewrite H0. clear H0.
                   rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2. clear Valid.
                   rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max. clear ValidMax.
                   assert (LOOR: local_out_of_reach
                                (compose_sm nu12 nu23) m1 b3 (ofs2+delta3)).
                     split; simpl. eapply (local_DomRng _ WDnu23); eassumption.
                     intros.
                     destruct (compose_meminjD_Some _ _ _ _ _ H0) as [bb2 [dd1 [dd2 [LC12 [LC23 D]]]]]; clear H0.
                     rewrite D in *; clear delta D.
                     destruct (eq_block bb2 b2); subst.
                     (*case bb2=b2*)
                         rewrite LC23 in LOC23. inv LOC23.
                         assert (Arith: ofs2 + delta3 - (dd1 + delta3) = ofs2 - dd1) by omega.
                         rewrite Arith. left.
                         apply (source_NoneE _ _ _ _ Heqss).
                             apply local_in_all in LC12; trivial. apply (VBj12_1 _ _ _ LC12).
                             assumption.
                     (*case bb2<>b2*)
                         remember (pubBlocksSrc nu12 b0) as d.
                         destruct d; try (right; reflexivity).
                         left; apply eq_sym in Heqd.
                         intros N.
                         assert (NN2: Mem.perm m2 bb2
                                     (ofs2 + (delta3 - dd2)) Max Nonempty).
                             assert (Arith: ofs2 + delta3 - (dd1 + dd2) + dd1 =
                                      ofs2 + (delta3 - dd2)) by omega.
                             rewrite <- Arith.
                             eapply MInj12; try eassumption.
                               apply local_in_all; assumption.
                         apply local_in_all in LC23; trivial.
                         destruct (Mem.mi_no_overlap _ _ _
                                 MInj23 _ _ _ _ _ _ _ _ n LC23 J23 NN2 Perm2Max).
                                     apply H0; trivial.
                                     apply H0. omega.
                   assert (Perm3: Mem.perm m3 b3 (ofs2+delta3) Cur Readable).
                     eapply MInj23. apply J23. apply Perm2.
                   destruct UnchLOOR13 as [Uperm UVal].
                   rewrite (UVal _ _ LOOR Perm3).
                   eapply memval_inject_incr.
                     apply (Mem.mi_memval _ _ _
                            (Mem.mi_inj _ _ _  MInj23) _ _ _ _ J23 Perm2).
                     apply inc23.
               (*case pubBlocksSrc nu23 b2 = false*)
                 rewrite H0. clear H0.
                 rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2. clear Valid.
                 rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max. clear ValidMax.
                 assert (LOOR: local_out_of_reach nu23 m2 b3 (ofs2+delta3)).
                  split; simpl. eapply (local_DomRng _ WDnu23); eassumption.
                     intros bb2; intros.
                     destruct (eq_block bb2 b2); subst.
                     (*case bb2=b2*) right; assumption.
                     (*case bb2<>b2*)
                         remember (pubBlocksSrc nu23 bb2) as d.
                         destruct d; try (right; reflexivity).
                         left; apply eq_sym in Heqd.
                         intros N.
                         apply local_in_all in H0; trivial.
                         destruct (Mem.mi_no_overlap _ _ _
                                 MInj23 _ _ _ _ _ _ _ _ n H0 J23 N Perm2Max).
                                     apply H2; trivial.
                                     apply H2. omega.
                   assert (Perm3: Mem.perm m3 b3 (ofs2+delta3) Cur Readable).
                     eapply MInj23. apply J23. apply Perm2.
                   destruct UNCHC as [Uperm UVal].
                   rewrite (UVal _ _ LOOR Perm3).
                   eapply memval_inject_incr.
                     apply (Mem.mi_memval _ _ _
                            (Mem.mi_inj _ _ _  MInj23) _ _ _ _ J23 Perm2).
                     apply inc23.
             (*case locBlocksSrc nu23 b2 = false*)
                 remember (source (as_inj nu12) m1 b2 ofs2) as ss.
                 destruct ss.
                 (*source (local_of nu12) m1 b2 ofs2  = Some p *)
                   destruct (source_SomeE _ _ _ _ _ Heqss)
                     as [b1 [delta2 [ofs1 [PP [Valb1 [ Jb1 [Perm1 Off]]]]]]].
                   clear Heqss; subst.
                   rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2; clear Valid.
                   rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max; clear ValidMax.
                   rewrite H0; clear H0; simpl in *.
                   assert (J': as_inj nu' b1 = Some (b3, delta2 + delta3)).
                       rewrite ID. eapply compose_meminjI_Some; try eassumption.
                        apply inc12. eassumption.
                   specialize (Mem.mi_memval _ _ _
                          (Mem.mi_inj _ _ _ MemInjNu') _ _  _ _ J' Perm2).
                   intros MemVal13'.
                   rewrite <- Zplus_assoc.
                   inv MemVal13'; simpl in *; try econstructor.
                      rewrite ID in H3.
                        destruct (compose_meminjD_Some _ _ _ _ _ H3)
                           as [bb2 [dd2 [dd3 [RR [JJ23  DD]]]]]; subst; clear H3.
                        rewrite RR. econstructor. eassumption.
                          rewrite Int.add_assoc. decEq. unfold Int.add.
                          apply Int.eqm_samerepr. auto with ints.
                 (*case source  j12 m1 b2 ofs2  = None *)
                   rewrite H0; clear H0.
                   unfold Mem.perm in Perm2Max, Perm2.
                   rewrite Valid in Perm2; clear Valid.
                   simpl in Perm2. contradiction.
          (*case ~ Mem.valid_block m2 b2*)
             specialize (H0 ofs2). clear Valid.
             assert (InvalidMax := Invalid H Max ofs2).
             specialize (Invalid H Cur ofs2).
             assert (J23: as_inj nu23 b2 = None).
                 remember (as_inj nu23 b2) as d.
                 destruct d; apply eq_sym in Heqd; trivial.
                    destruct p. rewrite (inc23 _ _ _ Heqd) in Jb2. inv Jb2.
                          exfalso. apply H. apply (VBj23_1 _ _ _ Heqd).
             remember (source j12' m1' b2 ofs2) as ss.
             destruct ss.
             (*source f m1' b2 ofs2  = Some p *)
                 destruct p. rewrite H0 in *. clear H0.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid) in Perm2; clear Invalid.
                 rewrite (perm_subst _ _ _ _ _ _ _ InvalidMax) in Perm2Max; clear InvalidMax.
                 destruct (source_SomeE _ _ _ _ _ Heqss)
                    as [b1 [delta2 [ofs1 [PP [VB [RR1 [Perm1' Off2]]]]]]].
                 clear Heqss.
                 inv PP.
                 assert (JB: as_inj nu' b1 = Some (b3, delta2 + delta3)).
                       rewrite ID. eapply compose_meminjI_Some; try eassumption.
                 specialize (Mem.mi_memval _ _ _
                       (Mem.mi_inj _ _ _  MemInjNu') _ _  _ _ JB Perm2).
                 intros MemVal13'.
                 rewrite <- Zplus_assoc.
                 inv MemVal13'; simpl in *; try econstructor.
                 rewrite ID in H3.
                 destruct (compose_meminjD_Some _ _ _ _ _ H3)
                       as [bb2 [dd2 [ddd3 [RRR [JJJ23  DD]]]]]; subst.
                    rewrite RRR. econstructor. apply JJJ23.
                    rewrite Int.add_assoc. decEq. unfold Int.add.
                       apply Int.eqm_samerepr. auto with ints.
             (*source  j12' m1' b1 ofs  = None *)
                 unfold Mem.perm in Perm2. rewrite Invalid in Perm2. inv Perm2.
   split; trivial.
   (*mi_freeblocks*)
       intros. remember (j23' b) as d.
       destruct d; apply eq_sym in Heqd; trivial.
       destruct p. exfalso.

       destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI)
        as [HH | HH].
       destruct HH as [? [? [? [?  ?]]]]; subst.
         apply H. apply Fwd2. apply (VBj23_1 _ _ _ Heqd).
       destruct HH as [N [? [? [? ?]]]].
         destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ Heqd)
            as [HH | [HH | HH]].
         destruct HH. apply H. apply Fwd2. apply H5.
         destruct HH as [? [? ?]]; subst.
            apply (H H6).
         destruct HH as [M [BM [J' B]]]; subst.
            apply (H B).
   (*mi_mappedblocks*)
      intros.
      destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI
        VBj23_1 _ _ _ H)as [HH | [HH | HH]].
      destruct HH. apply Fwd3. apply (VBj23_2 _ _ _  H0).
      destruct HH as [? [? ?]]; subst.
        eapply MemInjNu'. apply H1.
         destruct HH as [M [BM [J' B]]]; subst.
           eapply MemInjNu'. apply J'.
   (*no_overlap*)
      intros b; intros.
      destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI
        VBj23_1 _ _ _ H0) as [HH | [HH | HH]].
      destruct HH as [j23b vbb].
         destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _
               HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2].
            eapply MInj23.
               apply H.
               apply j23b.
               apply j23b2.
               apply Fwd2. apply (VBj23_1 _ _ _ j23b). apply H2.
               apply Fwd2. apply (VBj23_1 _ _ _ j23b2). apply H3.
            destruct KK as [BM [J' B']]; subst.
              left. assert (as_inj nu23 (Mem.nextblock m2) = None).
                     remember (as_inj nu23 (Mem.nextblock m2)) as d.
                     destruct d; trivial.
                     destruct p. apply eq_sym in Heqd.
                     specialize (VBj23_1 _ _ _ Heqd).
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst.
                    destruct (sep23 _ _ _ H4 H1). apply H6.
                    eapply MInj23. apply j23b.
            destruct KK as [M [BM [J' B']]].
            left. assert (as_inj nu23 b2 = None).
                     remember (as_inj nu23 b2) as d.
                     destruct d; trivial.
                     destruct p. apply eq_sym in Heqd.
                     specialize (VBj23_1 _ _ _ Heqd).
                     clear - VBj23_1 BM. subst.
                     unfold Mem.valid_block in VBj23_1. xomega.
                  intros N; subst.
                    destruct (sep23 _ _ _ H4 H1). apply H6.
                    eapply MInj23. apply j23b.
         destruct HH as [NBb [j'b NBb']]; subst.
           destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _
                HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2].
             left. assert (as_inj nu23 (Mem.nextblock m2) = None).
                      remember (as_inj nu23 (Mem.nextblock m2)) as d.
                      destruct d; trivial. destruct p.
                      apply eq_sym in Heqd.
                      specialize (VBj23_1 _ _ _ Heqd).
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst.
                     destruct (sep23 _ _ _ H4 H0).
                     apply H6. eapply MInj23. apply j23b2.
            destruct KK as [BM [J' B']]; subst.
              exfalso. apply H; trivial.
            destruct KK as [M [BM [J' B']]]. subst.
          (*first case where both blocks are in m2' but not in m2*)
              assert (j23_None1: as_inj nu23 (Mem.nextblock m2) = None).
                 remember (as_inj nu23 (Mem.nextblock m2)) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2: as_inj nu23 ((Mem.nextblock m2 + M)%positive) = None).
                 remember (as_inj nu23 ((Mem.nextblock m2 + M)%positive)) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 exfalso. unfold Mem.valid_block in VBj23_1. xomega.
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : Mem.nextblock m1 <> (Mem.nextblock m1 + M)%positive).
                 apply add_no_neutral2.
              destruct (ACCESS (Mem.nextblock m2)) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).

              remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12')
                    m1' (Mem.nextblock m2) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  (Mem.nextblock m2 + M)%positive) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1'
                         (Mem.nextblock m2 + M)%positive ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p.
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3.
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

                     destruct (source_SomeE _ _ _ _ _ Heqd)
                         as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off1]]]]]]].
                     clear Heqd. subst. apply eq_sym in PP. inv PP.
                     unfold removeUndefs in JJ'.
                     remember (as_inj nu12 b1) as q.
                     destruct q; apply eq_sym in Heqq.
                       destruct p. inv JJ'. exfalso. apply NV2_1.
                           apply (VBj12_2 _ _ _ Heqq).
                     remember (as_inj nu' b1) as qq.
                     destruct qq; inv JJ'. apply eq_sym in Heqqq.
                     destruct p.
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst.
                       destruct (source_SomeE _ _ _ _ _ Heqd0) as
                           [bb2 [dd2 [ofs22 [PP2 [VB2 [ JJ2' [PERM2 Off2]]]]]]].
                       clear Heqd0. subst. apply eq_sym in PP2. inv PP2.
                       unfold removeUndefs in JJ2'.
                       remember (as_inj nu12 b2) as r.
                       destruct r; apply eq_sym in Heqr.
                           destruct p. inv JJ2'.
                           exfalso. apply NV2_2. apply (VBj12_2 _ _ _ Heqr).
                       remember (as_inj nu' b2) as rr.
                       destruct rr; inv JJ2'. apply eq_sym in Heqrr.
                       destruct p.
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H7)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst.
                              exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) M).
                                 rewrite Pos.add_comm. apply H10.
                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           apply Pos.add_reg_l in nbm. apply eq_sym in nbm.  subst.
                           eapply MemInjNu'.
                              apply NEQ.
                              assumption.
                              assumption.
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       exfalso. apply (add_no_neutral2 (Mem.nextblock m2) MM1).
                         apply H6.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2.
         destruct HH as [M1 [? [j'b1 NBb1]]]; subst.
           destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _
                HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2].
             left. assert (as_inj nu23 (Mem.nextblock m2 + M1)%positive = None).
                      remember (as_inj nu23 (Mem.nextblock m2 + M1)%positive) as d.
                      destruct d; trivial. destruct p.
                      apply eq_sym in Heqd.
                      specialize (VBj23_1 _ _ _ Heqd).
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst.
                     destruct (sep23 _ _ _ H4 H0).
                     apply H6. eapply MInj23. apply j23b2.
            destruct KK as [BM [J' B']]; subst.
          (*second case where both blocks are in m2' but not in m2*)
              assert (j23_None1: as_inj nu23 (Mem.nextblock m2 + M1)%positive = None).
                 remember (as_inj nu23 (Mem.nextblock m2 + M1)%positive) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2: as_inj nu23 (Mem.nextblock m2) = None).
                 remember (as_inj nu23 (Mem.nextblock m2)) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 exfalso. unfold Mem.valid_block in VBj23_1. xomega.
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : (Mem.nextblock m1 + M1)%positive <> Mem.nextblock m1).
                rewrite Pos.add_comm. apply Pos.add_no_neutral.
              destruct (ACCESS (Mem.nextblock m2 + M1)%positive) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).

              remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12')
                    m1' ((Mem.nextblock m2 +M1)%positive) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  (Mem.nextblock m2)) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1'
                         (Mem.nextblock m2) ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p.
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3.
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

                     destruct (source_SomeE _ _ _ _ _ Heqd)
                         as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off1]]]]]]].
                     clear Heqd. subst. apply eq_sym in PP. inv PP.
                     unfold removeUndefs in JJ'.
                     remember (as_inj nu12 b1) as q.
                     destruct q; apply eq_sym in Heqq.
                       destruct p. inv JJ'. exfalso. apply NV2_1.
                           apply (VBj12_2 _ _ _ Heqq).
                     remember (as_inj nu' b1) as qq.
                     destruct qq; inv JJ'. apply eq_sym in Heqqq.
                     destruct p.
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst.
                       exfalso. rewrite Pos.add_comm in H6.
                        apply Pos.add_no_neutral in H6. apply H6.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       apply Pos.add_reg_l in H6. apply eq_sym in H6. subst.
                       destruct (source_SomeE _ _ _ _ _ Heqd0) as
                           [bb2 [dd2 [ofs22 [PP2 [VB2 [ JJ2' [PERM2 Off2]]]]]]].
                       clear Heqd0. subst. apply eq_sym in PP2. inv PP2.
                       unfold removeUndefs in JJ2'.
                       remember (as_inj nu12 b2) as r.
                       destruct r; apply eq_sym in Heqr.
                           destruct p. inv JJ2'.
                           exfalso. apply NV2_2. apply (VBj12_2 _ _ _ Heqr).
                       remember (as_inj nu' b2) as rr.
                       destruct rr; inv JJ2'. apply eq_sym in Heqrr.
                       destruct p.
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H6)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst.
                           eapply MemInjNu'.
                              apply NEQ.
                              assumption.
                              assumption.
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.

                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) MM2).
                                 rewrite Pos.add_comm. rewrite <- nbm. trivial.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2.
            destruct KK as [M2 [BM [J2' B2']]]; subst.
          (*third case where both blocks are in m2' but not in m2*)
              assert (j23_None1: as_inj nu23 (Mem.nextblock m2 + M1)%positive = None).
                 remember (as_inj nu23 (Mem.nextblock m2 + M1)%positive) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2:  as_inj nu23 (Mem.nextblock m2 + M2)%positive = None).
                 remember (as_inj nu23 (Mem.nextblock m2 + M2)%positive) as d.
                 destruct d; trivial.
                 apply eq_sym in Heqd. destruct p.
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : (Mem.nextblock m1 + M1)%positive <> (Mem.nextblock m1 + M2)%positive).
                intros NN. apply Pos.add_cancel_l in NN. subst.
                apply H; trivial.
              destruct (ACCESS (Mem.nextblock m2 + M1)%positive) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).

              remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12')
                    m1' ((Mem.nextblock m2 +M1)%positive) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  ((Mem.nextblock m2 + M2)%positive)) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12')  m1'
                         ((Mem.nextblock m2 + M2)%positive) ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p.
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3.
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

                     destruct (source_SomeE _ _ _ _ _ Heqd)
                         as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off1]]]]]]].
                     clear Heqd. subst. apply eq_sym in PP. inv PP.
                     unfold removeUndefs in JJ'.
                     remember (as_inj nu12 b1) as q.
                     destruct q; apply eq_sym in Heqq.
                       destruct p. inv JJ'. exfalso. apply NV2_1.
                           apply (VBj12_2 _ _ _ Heqq).
                     remember (as_inj nu' b1) as qq.
                     destruct qq; inv JJ'. apply eq_sym in Heqqq.
                     destruct p.
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst.
                       exfalso. rewrite Pos.add_comm in H6.
                        apply Pos.add_no_neutral in H6. apply H6.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       apply Pos.add_reg_l in H6. apply eq_sym in H6. subst.
                       destruct (source_SomeE _ _ _ _ _ Heqd0) as
                           [bb2 [dd2 [ofs22 [PP2 [VB2 [ JJ2' [PERM2 Off2]]]]]]].
                       clear Heqd0. subst. apply eq_sym in PP2. inv PP2.
                       unfold removeUndefs in JJ2'.
                       remember (as_inj nu12 b2) as r.
                       destruct r; apply eq_sym in Heqr.
                           destruct p. inv JJ2'.
                           exfalso. apply NV2_2. apply (VBj12_2 _ _ _ Heqr).
                       remember (as_inj nu' b2) as rr.
                       destruct rr; inv JJ2'. apply eq_sym in Heqrr.
                       destruct p.
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H6)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst.
                           exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) M2).
                                 rewrite Pos.add_comm. trivial.

                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           apply Pos.add_cancel_l in nbm. subst.
                           eapply MemInjNu'.
                              apply NEQ.
                              assumption.
                              assumption.
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2.

   (*mi_representable*) intros. rename b into b2.
       destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H)
       as [HH | [ HH | HH]].
       (*first case*)
         destruct HH as [j23b2 Val2].
         destruct (ACCESS b2) as [Valid _].
         rewrite j23b2 in Valid.
         specialize (Valid Val2).
         remember (locBlocksSrc nu23 b2) as MyB2.
         destruct MyB2; apply eq_sym in HeqMyB2.
         (*case locBlocksSrc nu23 b2 = true*)
           remember (pubBlocksSrc nu23 b2) as PubB2.
           destruct PubB2; apply eq_sym in HeqPubB2.
           (*case pubBlocksSrc nu23 b2 = true*)
             destruct H0.
             (*location ofs*)
               specialize (Valid Max (Int.unsigned ofs)).
               remember (source (local_of nu12) m1 b2 (Int.unsigned ofs)) as d.
               destruct d.
               (*source ... m1 b2 (Int.unsigned ofs) = Some p*)
                 destruct p.
                 destruct (source_SomeE _ _ _ _ _ Heqd)
                   as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
                 clear Heqd. subst. apply eq_sym in PP. inv PP.
                 assert (PP2: Mem.perm m2 b2 (Int.unsigned ofs) Max Nonempty).
                   remember (pubBlocksSrc nu12 b) as PubB1.
                   destruct PubB1; apply eq_sym in HeqPubB1;
                   rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
                      rewrite Off1. eapply MInj12. apply local_in_all; eassumption. apply PERM.
                      assumption.
                 eapply MInj23. apply j23b2.
                   left. assumption.
               (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
                 rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
                 eapply MInj23. apply j23b2.
                 left. apply H0.
             (*location ofs -1*)
               specialize (Valid Max (Int.unsigned ofs -1)).
               remember (source (local_of nu12) m1 b2 (Int.unsigned ofs -1)) as d.
               destruct d.
               (*source .. m1 b2 (Int.unsigned ofs-1) = Some p*)
                 destruct p.
                 destruct (source_SomeE _ _ _ _ _ Heqd)
                   as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
                 clear Heqd. subst. apply eq_sym in PP. inv PP.
                 assert (PP2: Mem.perm m2 b2 (Int.unsigned ofs -1) Max Nonempty).
                   remember (pubBlocksSrc nu12 b) as PubB1.
                   destruct PubB1; apply eq_sym in HeqPubB1;
                   rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
                      rewrite Off1. eapply MInj12. apply local_in_all; eassumption. apply PERM.
                      assumption.
                 eapply MInj23. apply j23b2.
                   right. assumption.
               (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
                 rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
                 eapply MInj23. apply j23b2.
                 right. apply H0.
           (*case pubBlocksSrc nu23 b2 = false*)
             destruct H0.
             (*location ofs*)
               specialize (Valid Max (Int.unsigned ofs)).
               rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
               eapply MInj23. apply j23b2.
               left. apply H0.
             (*location ofs-1*)
               specialize (Valid Max (Int.unsigned ofs-1)).
               rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
               eapply MInj23. apply j23b2.
               right. apply H0.
         (*case locBlocksSrc nu23 b2 = false*)
             destruct H0.
             (*location ofs*)
               specialize (Valid Max (Int.unsigned ofs)).
               remember (source (as_inj nu12) m1 b2 (Int.unsigned ofs)) as d.
               destruct d.
               (*source ... m1 b2 (Int.unsigned ofs) = Some p*)
                 destruct p.
                 destruct (source_SomeE _ _ _ _ _ Heqd)
                   as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
                 clear Heqd. subst. apply eq_sym in PP. inv PP.
                 assert (PP2: Mem.perm m2 b2 (Int.unsigned ofs) Max Nonempty).
                   rewrite Off1. eapply MInj12; eassumption.
                 eapply MInj23. apply j23b2.
                   left. assumption.
               (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
                 unfold Mem.perm in H0; rewrite Valid in H0; simpl in H0. contradiction.
             (*location ofs-1*)
               specialize (Valid Max (Int.unsigned ofs-1)).
               remember (source (as_inj nu12) m1 b2 (Int.unsigned ofs-1)) as d.
               destruct d.
               (*source ... m1 b2 (Int.unsigned ofs) = Some p*)
                 destruct p.
                 destruct (source_SomeE _ _ _ _ _ Heqd)
                   as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
                 clear Heqd. subst. apply eq_sym in PP. inv PP.
                 assert (PP2: Mem.perm m2 b2 (Int.unsigned ofs-1) Max Nonempty).
                   rewrite Off1. eapply MInj12; eassumption.
                 eapply MInj23. apply j23b2.
                   right. assumption.
               (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
                 unfold Mem.perm in H0; rewrite Valid in H0; simpl in H0. contradiction.
       (*second case*)
         destruct HH as [? [j'b2 Val2']]. subst.
         destruct (ACCESS (Mem.nextblock m2)) as [_ InValid].
         assert (NVB2: ~Mem.valid_block m2 (Mem.nextblock m2)).
            unfold Mem.valid_block; xomega.
         specialize (InValid NVB2).
         destruct H0.
         (*location ofs*)
           specialize (InValid Max (Int.unsigned ofs)).
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1' (Mem.nextblock m2)
                            (Int.unsigned ofs)) as d.
           destruct d.
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (as_inj nu12 b); intros.
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (as_inj nu' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [_ [? [? ?]]]]; subst.
                    rewrite Zplus_0_r in *. subst.
                    eapply MemInjNu'. apply j'b2. left; apply PERM.
                destruct KK as [m [_ [? _]]].
                    exfalso. clear -H3. apply (add_no_neutral2 _ _ H3).
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
         (*location ofs -1*)
           specialize (InValid Max (Int.unsigned ofs-1)).
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1' (Mem.nextblock m2)
                            (Int.unsigned ofs-1)) as d.
           destruct d.
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (as_inj nu12 b); intros.
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (as_inj nu' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [_ [? [? ?]]]]; subst.
                    rewrite Zplus_0_r in *. subst.
                    eapply MemInjNu'. apply j'b2. right; apply PERM.
                destruct KK as [m [_ [? _]]].
                    exfalso. clear -H3. apply (add_no_neutral2 _ _ H3).
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs-1) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
       (*third case*)
         destruct HH as [m [? [j'b2 Val2']]]; subst.
         destruct (ACCESS ((Mem.nextblock m2+m)%positive)) as [_ InValid].
         assert (NVB2: ~Mem.valid_block m2 ((Mem.nextblock m2+m)%positive)).
            unfold Mem.valid_block; xomega.
         destruct H0.
         (*location ofs*)
           specialize (InValid NVB2 Max (Int.unsigned ofs)).
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1'
                            ((Mem.nextblock m2+m)%positive)
                            (Int.unsigned ofs)) as d.
           destruct d.
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (as_inj nu12 b); intros.
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (as_inj nu' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [? [? [? ?]]]]; subst.
                    exfalso. clear -H4. apply eq_sym in H4.
                    apply (add_no_neutral2 _ _ H4).
                destruct KK as [mm [? [? [? [? ?]]]]]. subst.
                   assert (mm = m).
                      clear -H4.
                      apply Pos.add_reg_l in H4.
                      subst; trivial.
                   rewrite Zplus_0_r in *. subst.
                   eapply MemInjNu'. apply j'b2. left. apply PERM.
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
         (*location ofs -1*)
           specialize (InValid NVB2 Max (Int.unsigned ofs-1)).
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1'
                            ((Mem.nextblock m2+m)%positive)
                            (Int.unsigned ofs-1)) as d.
           destruct d.
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (as_inj nu12 b); intros.
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (as_inj nu' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [? [? [? ?]]]]; subst.
                    exfalso. clear -H4. apply eq_sym in H4.
                    apply (add_no_neutral2 _ _ H4).
                destruct KK as [mm [? [? [? [? ?]]]]]. subst.
                   assert (mm = m).
                      clear -H4.
                      apply Pos.add_reg_l in H4.
                      subst; trivial.
                   rewrite Zplus_0_r in *. subst.
                   eapply MemInjNu'. apply j'b2. right. apply PERM.
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs-1) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.

specialize (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI Val12 Val23).
intros mkiVal3.
specialize (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI Val23). intros mkiVal4.
specialize (mkInjections_5 _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1 VBj12_2 VBj23_1 VBj'). intros mkiVal5.
clear CONT ACCESS HeqMKI.
assert (GOAL1: nu' =
compose_sm
  (convertL nu12 j12'
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23'))
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b)))).
  destruct ExtIncr as [AA [BB [CC [DD [EE [FF [GG [HH [II JJ]]]]]]]]]; simpl in *.
  unfold compose_sm; simpl in *. clear ConvertL_J12'. clear ConvertR_J23'.
  rewrite convertL_extern, convertL_local, convertL_frgnBlocksSrc,
          convertL_pubBlocksSrc, convertL_locBlocksSrc, convertL_extBlocksSrc.
  rewrite convertR_extern, convertR_local, convertR_frgnBlocksTgt,
          convertR_pubBlocksTgt, convertR_locBlocksTgt, convertR_extBlocksTgt.
  destruct nu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern'].
  simpl in *. unfold as_inj in *; simpl in *.
  f_equal; simpl; subst; simpl in *; trivial.
  (*1/3*)
     extensionality b.
     specialize (disjoint_extern_local_Src _ WDnu' b). intros.
     unfold DomSrc, DomTgt in *; simpl in *.
     specialize (CC b).
     clear - CC H.
     remember (locBlocksSrc nu12 b) as q.
     remember (extBlocksSrc nu12 b) as t.
     destruct q; destruct t; simpl in *; intuition.
     rewrite andb_true_r. trivial.
     rewrite andb_true_r. trivial.
  (*2/3*)
     extensionality b.
     specialize (disjoint_extern_local_Tgt _ WDnu' b). intros.
     unfold DomSrc, DomTgt in *; simpl in *.
     specialize (DD b).
     clear - DD H.
     remember (locBlocksTgt nu23 b) as q.
     remember (extBlocksTgt nu23 b) as t.
     destruct q; destruct t; simpl in *; intuition.
     rewrite andb_true_r. trivial.
     rewrite andb_true_r. trivial.
  (*3/3*)
     clear Inj12' NOVj12' Inj23' UNCHC MemInjNu' Fwd2 MInj23 Fwd1 MInj12 UnchPrivSrc UnchLOOR13 VBj'
           Fwd1 Fwd3 SMV12 SMV23 SMvalNu' InjSep VBj23_2 sep23 NB1 SMInjSep
           VBj23' Val12 Val23 mkiVal3 m3 m1' m3'.
     extensionality b1.
     remember (extern' b1) as d.
     destruct d; apply eq_sym in Heqd.
     (*case externNu' b1 = Some p*)
       destruct p as [b3 delta].
       assert (J: join extern' (compose_meminj (local_of nu12) (local_of nu23)) b1 = Some (b3, delta)).
         apply join_incr_left. apply Heqd.
       rewrite ID in J; clear ID.
       destruct (compose_meminjD_Some _ _ _ _ _ J)
        as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear J.
       apply eq_sym.
       eapply compose_meminjI_Some with (b2:=b2).
       (*condition 1*)
         remember (extern_of nu12 b1) as q.
         destruct q; apply eq_sym in Heqq.
         (*case extern_of nu12 b1 = Some p*)
           destruct p as [bb2 dd1].
           unfold join. rewrite Heqq.
           apply extern_in_all in Heqq.
           apply inc12 in Heqq. unfold as_inj in Heqq. simpl in *.
             rewrite Heqq in J1. apply J1.
         (*case extern_of nu12 b1 = Some p*)
           unfold join. rewrite Heqq.
           remember (local_of nu12 b1) as w.
           destruct w; trivial; apply eq_sym in Heqw.
           destruct p as [bb dd].
           assert (locBlocksSrc nu12 b1 = true).
             eapply local_locBlocks; eassumption.
           assert (locBlocksSrc nu12 b1 = false).
             eapply (extern_DomRng' _ WDnu'). simpl. apply Heqd.
           rewrite H0 in H. inv H.
       (*condition 2*)
         unfold join.
         remember (extern_of nu23 b2) as q.
         destruct q; apply eq_sym in Heqq.
           destruct p.
           rewrite (inject_incr_coincide _ _ inc23 _ _ J2 _
               (extern_in_all _ _ _ _ Heqq)). trivial.
         remember (local_of nu23 b2) as w.
         destruct w; apply eq_sym in Heqw; trivial.
         destruct p.
         assert (E:= inject_incr_coincide _ _ inc23 _ _ J2 _
               (local_in_all _ WDnu23 _ _ _ Heqw)); inv E.
         assert (locBlocksTgt nu23 b = true).
           eapply local_locBlocks; eassumption.
         assert (locBlocksTgt nu23 b = false).
           eapply (extern_DomRng' _ WDnu'). simpl. apply Heqd.
         rewrite H0 in H. inv H.
     (*externNu' b1 = None*)
        unfold as_inj in inc12. simpl in inc12.
        remember (compose_meminj (local_of nu12) (local_of nu23) b1) as q.
        destruct q; apply eq_sym in Heqq.
        (*case compose_meminj (local_of nu12) (local_of nu23) b1 = Some p*)
          destruct p as [b3 delta].
          destruct (compose_meminjD_Some _ _ _ _ _ Heqq)
            as [b2 [d1 [d2 [Loc12 [Loc23 D]]]]]; subst; clear Heqq.
          apply eq_sym.
          destruct (disjoint_extern_local _ WDnu12 b1).
            unfold compose_meminj, join. rewrite H, Loc12. trivial.
          rewrite H in Loc12. inv Loc12.
        (*case compose_meminj (local_of nu12) (local_of nu23) b1 = None*)
          assert (compose_meminj
            (removeUndefs (join (extern_of nu12) (local_of nu12))
               (join extern' (compose_meminj (local_of nu12) (local_of nu23))) prej12')
            j23' b1 = None).
              rewrite <- ID. unfold join. rewrite Heqd. trivial.
          clear ID.
          remember (extern_of nu12 b1) as w.
          destruct w; apply eq_sym in Heqw.
          (*case extern_of nu12 b1 = Some p*)
            destruct p as [b2 d1].
            assert (R: removeUndefs (join (extern_of nu12) (local_of nu12))
                        (join extern' (compose_meminj (local_of nu12) (local_of nu23)))
                         prej12' b1 = Some (b2, d1)).
                apply inc12. apply extern_in_all. apply Heqw.
            destruct (compose_meminjD_None _ _ _ H); clear H.
               rewrite H0 in R. inv R.
            destruct H0 as [bb2 [dd1 [XX J23']]].
            rewrite R in XX. apply eq_sym in XX. inv XX.
            apply eq_sym.
            apply compose_meminjI_None. right.
            exists b2, d1; split. apply join_incr_left. assumption.
            remember (extern_of nu23 b2) as t.
            destruct t; apply eq_sym in Heqt.
               destruct p as [b3 d2].
               apply extern_in_all in Heqt. apply inc23 in Heqt.
               rewrite Heqt in J23'. discriminate.
            unfold join. rewrite Heqt, J23'.
              destruct (local_of nu23 b2); trivial.
          (*case extern_of nu12 b1 = None*)
            destruct (compose_meminjD_None _ _ _ Heqq); clear Heqq.
            (*case local_of nu12 b1 = None*)
              clear inc12.
              destruct (compose_meminjD_None _ _ _ H); clear H.
              (*case removeUndefs ... = None*)
                apply eq_sym.
                apply compose_meminjI_None. left.
                apply joinI_None. assumption.
                rewrite H0. apply H1.
              (*case removeUndefs ... = Some*)
                destruct H1 as [b2 [d1 [R J23']]].
                apply eq_sym.
                apply compose_meminjI_None. right.
                exists b2, d1; split.
                  unfold join. rewrite Heqw. rewrite H0. apply R.
                assert (as_inj nu23 b2 = None).
                  apply (inject_incr_inv _ _ inc23 _ J23').
                destruct (joinD_None _ _ _ H).
                unfold join. rewrite H1, H2. apply J23'.
            (*case local_of nu12 b1 = Some*)
              destruct H0 as [b2 [d1 [Loc1 Loc2]]].
              apply eq_sym.
              apply compose_meminjI_None. left.
              destruct (disjoint_extern_local _ WDnu12 b1).
                unfold join. rewrite H0, Loc1. trivial.
              rewrite H0 in Loc1. inv Loc1.
split; trivial.
assert (GOAL2: extern_incr nu12
  (convertL nu12 (removeUndefs (as_inj nu12) (as_inj nu') prej12')
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23'))).
  split. rewrite convertL_extern. apply join_incr_left.
  split. rewrite convertL_local. trivial.
  split. rewrite convertL_extBlocksSrc. intuition.
  split. rewrite convertL_extBlocksTgt. intuition.
  split. rewrite convertL_locBlocksSrc. trivial.
  split. rewrite convertL_locBlocksTgt. trivial.
  split. rewrite convertL_pubBlocksSrc. trivial.
  split. rewrite convertL_pubBlocksTgt. trivial.
  split. rewrite convertL_frgnBlocksSrc. trivial.
  rewrite convertL_frgnBlocksTgt. trivial.
split. rewrite <- Heqj12' in GOAL2. assumption.
assert (GOAL3: (extern_incr nu23
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b))))).
  clear GOAL1 GOAL2 ConvertL_J12' ConvertR_J23'.
  split. rewrite convertR_extern. apply join_incr_left.
  split. rewrite convertR_local. trivial.
  split. rewrite convertR_extBlocksSrc. intuition.
  split. rewrite convertR_extBlocksTgt. intuition.
  split. rewrite convertR_locBlocksSrc. trivial.
  split. rewrite convertR_locBlocksTgt. trivial.
  split. rewrite convertR_pubBlocksSrc. trivial.
  split. rewrite convertR_pubBlocksTgt. trivial.
  split. rewrite convertR_frgnBlocksSrc. trivial.
  rewrite convertR_frgnBlocksTgt. trivial.
split. assumption.
assert (GOAL4: sm_inject_separated nu12
  (convertL nu12 j12'
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23')) m1 m2).
  split. rewrite ConvertL_J12'; clear ConvertL_J12' GOAL1 ConvertR_J23'.
         intros.
         destruct (sep12 _ _ _ H H0) as [NV1 NV2].
         split.
           remember (DomSrc nu12 b1) as q.
           destruct q; trivial; apply eq_sym in Heqq.
           apply SMV12 in Heqq. contradiction.
         remember (DomTgt nu12 b2) as q.
           destruct q; trivial; apply eq_sym in Heqq.
           apply SMV12 in Heqq. contradiction.
  rewrite convertL_DomSrc, convertL_DomTgt.
  split; intros; rewrite H in H0; simpl in *.
         rewrite andb_true_r in H0.
         eapply SMInjSep. apply H. apply H0.
       unfold FreshDom in H0.
           remember (j23' b2) as q.
           destruct q; apply eq_sym in Heqq.
              destruct p.
              remember (as_inj nu23 b2) as w.
              destruct w; apply eq_sym in Heqw. inv H0.
              eapply sep23; eassumption.
           inv H0.
split. assumption.
assert (GOAL5: sm_inject_separated nu23
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b))) m2 m3).
  split. rewrite ConvertR_J23'; clear ConvertL_J12' GOAL1 ConvertR_J23'.
         intros.
         destruct (sep23 _ _ _ H H0) as [NV1 NV2].
         split.
           remember (DomSrc nu23 b1) as q.
           destruct q; trivial; apply eq_sym in Heqq.
           apply SMV23 in Heqq. contradiction.
         remember (DomTgt nu23 b2) as q.
           destruct q; trivial; apply eq_sym in Heqq.
           apply SMV23 in Heqq. contradiction.
  rewrite convertR_DomSrc, convertR_DomTgt.
  split; intros; rewrite H in H0; simpl in H0.
         unfold FreshDom in H0.
           remember (j23' b1) as q.
           destruct q; apply eq_sym in Heqq.
              destruct p.
              remember (as_inj nu23 b1) as w.
              destruct w; apply eq_sym in Heqw. inv H0.
              eapply sep23; eassumption.
           inv H0.
           rewrite andb_true_r in H0.
           eapply SMInjSep. apply H. apply H0.
split. assumption.
assert (GOAL6: sm_valid
  (convertL nu12 j12'
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23')) m1' m2').
  split. unfold DOM. rewrite convertL_DomSrc.
         clear ConvertL_J12' GOAL1 ConvertR_J23'.
         intros.
         remember (DomSrc nu12 b1) as d.
         destruct d; apply eq_sym in Heqd; simpl in H.
           apply Fwd1.
           eapply SMV12. apply Heqd.
         rewrite andb_true_r in H.
           eapply SMvalNu'. apply H.
  unfold RNG. rewrite convertL_DomTgt.
         intros.
         remember (DomTgt nu12 b2) as d.
         destruct d; apply eq_sym in Heqd; simpl in H.
           apply Fwd2.
           eapply SMV12. apply Heqd.
         unfold FreshDom in H.
           remember (j23' b2) as q.
           destruct q; apply eq_sym in Heqq.
              destruct p.
              remember (as_inj nu23 b2) as w.
              destruct w; apply eq_sym in Heqw. inv H.
              apply (VBj23' _ _ _ Heqq).
            inv H.
split. assumption.
split. (*This is GOAL7: sm_valid
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b))) m2' m3').*)
  split. unfold DOM. rewrite convertR_DomSrc.
         clear ConvertL_J12' GOAL1 ConvertR_J23'.
         intros.
         remember (DomSrc nu23 b1) as d.
         destruct d; apply eq_sym in Heqd; simpl in H.
           apply Fwd2.
           eapply SMV23. apply Heqd.
         unfold FreshDom in H.
           remember (j23' b1) as q.
           destruct q; apply eq_sym in Heqq.
              destruct p.
              remember (as_inj nu23 b1) as w.
              destruct w; apply eq_sym in Heqw. inv H.
              apply (VBj23' _ _ _ Heqq).
            inv H.
  unfold RNG. rewrite convertR_DomTgt.
         intros.
         remember (DomTgt nu23 b2) as d.
         destruct d; apply eq_sym in Heqd; simpl in H.
           apply Fwd3.
           eapply SMV23. apply Heqd.
         rewrite andb_true_r in H.
           eapply SMvalNu'. apply H.
split. (*Glue invariant*)
  split. (*This is GOAL8: SM_wd
  (convertL nu12 f
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23'))).*)
   clear ConvertL_J12' ConvertR_J23'.
   split.
   (*1/8*) rewrite convertL_locBlocksSrc, convertL_extBlocksSrc.
           intros. unfold DomSrc.
           specialize (disjoint_extern_local_Src _ WDnu12 b); intros.
           remember (locBlocksSrc nu12 b) as d.
           destruct d; apply eq_sym in Heqd.
             destruct H. inv H.
             rewrite H. right. simpl. rewrite andb_false_r. trivial.
           left; trivial.
   (*2/8*) rewrite convertL_locBlocksTgt, convertL_extBlocksTgt.
           intros.
           specialize (disjoint_extern_local_Tgt _ WDnu12 b); intros.
           remember (locBlocksTgt nu12 b) as d.
           destruct d; apply eq_sym in Heqd.
             destruct H. inv H.
             rewrite H. right. rewrite orb_false_l.
             unfold FreshDom.
             remember (j23' b) as q.
             destruct q; trivial; apply eq_sym in Heqq.
             destruct p.
             remember (as_inj nu23 b) as t.
             destruct t; trivial; apply eq_sym in Heqt.
             assert (DomSrc nu23 b = false).
                eapply GOAL5. apply Heqt.
                destruct (joinD_None _ _ _ Heqt).
                apply joinI. rewrite convertR_extern, convertR_local.
                unfold join; simpl. rewrite H0, H1. left; eassumption.
             unfold DomSrc in H0. rewrite GlueLoc in Heqd. rewrite Heqd in H0.
               discriminate.
           left; trivial.
   (*3/8*) rewrite convertL_local, convertL_locBlocksSrc, convertL_locBlocksTgt.
           apply WDnu12.
   (*4/8*) rewrite convertL_extern, convertL_extBlocksSrc, convertL_extBlocksTgt.
           intros.
            destruct (joinD_Some _ _ _ _ _ H); clear H.
              destruct (extern_DomRng _ WDnu12 _ _ _ H0) as [? ?].
              intuition.
            destruct H0.
            remember (local_of nu12 b1) as d.
            destruct d; apply eq_sym in Heqd. inv H0.
              destruct (sep12 b1 b2 z); trivial.
                apply joinI_None; trivial.
            remember (DomSrc nu12 b1) as q.
            destruct q; apply eq_sym in Heqq.
              exfalso. apply H1. apply SMV12. apply Heqq.
            remember (DomTgt nu12 b2) as w.
            destruct w; apply eq_sym in Heqw.
              exfalso. apply H2. apply SMV12. apply Heqw.
            simpl.
            unfold DomSrc in Heqq. apply orb_false_iff in Heqq. destruct Heqq.
            unfold DomTgt in Heqw. apply orb_false_iff in Heqw. destruct Heqw.
            rewrite H4, H6; simpl.
            rewrite andb_true_r. clear GOAL1.
            rewrite GlueLoc, GlueExt in *.
            remember (as_inj nu23 b2) as ww.
            destruct ww; apply eq_sym in Heqww.
               destruct p.
               destruct (as_inj_DomRng _ _ _ _ Heqww WDnu23).
               unfold DomSrc in H7. rewrite H5, H6 in H7. discriminate.
            remember (as_inj nu' b1) as qq.
            destruct qq; apply eq_sym in Heqqq.
               destruct p.
               assert (DomSrc nu' b1 = true).
                  eapply as_inj_DomRng. eassumption.
                  assumption.
               rewrite H7. split; trivial.
               rewrite ID in Heqqq.
               destruct (compose_meminjD_Some _ _ _ _ _ Heqqq)
                  as [b22 [dd1 [dd2 [FF [JJ DD]]]]]; clear Heqqq.
               clear ID. rewrite FF in H0. inv H0.
               unfold FreshDom. rewrite JJ, Heqww. trivial.
            rewrite Heqj12' in H0.
            unfold removeUndefs in H0. rewrite Heqqq in H0.
               assert (AI: as_inj nu12 b1 = None). apply joinI_None; eassumption.
               rewrite AI in H0. inv H0.
   (*5/8*) rewrite convertL_pubBlocksSrc, convertL_pubBlocksTgt, convertL_local.
            apply WDnu12.
   (*6/8*) rewrite convertL_frgnBlocksSrc, convertL_frgnBlocksTgt.
            rewrite convertL_extern; trivial. intros.
            destruct (frgnSrcAx _ WDnu12 _ H) as [b2 [d [EXT FT]]].
             unfold join. rewrite EXT. exists b2, d. split; trivial.
   (*7/8*) rewrite convertL_pubBlocksTgt, convertL_locBlocksTgt.
           apply WDnu12.
   (*8/8*) rewrite convertL_frgnBlocksTgt, convertL_extBlocksTgt.
           intros. rewrite (frgnBlocksExternTgt _ WDnu12 _ H). trivial.
split. (*This is GOAL9: SM_wd
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b)))).*)
   clear ConvertL_J12' ConvertR_J23'.
   split.
   (*1/8*) rewrite convertR_locBlocksSrc, convertR_extBlocksSrc.
          intros.
           specialize (disjoint_extern_local_Src _ WDnu23 b); intros.
           remember (locBlocksSrc nu23 b) as d.
           destruct d; apply eq_sym in Heqd.
             destruct H. inv H.
             rewrite H. right. rewrite orb_false_l.
             unfold FreshDom.
             remember (j23' b) as q.
             destruct q; trivial; apply eq_sym in Heqq.
             destruct p.
             remember (as_inj nu23 b) as t.
             destruct t; trivial; apply eq_sym in Heqt.
             assert (DomSrc nu23 b = false).
                eapply GOAL5. apply Heqt.
                destruct (joinD_None _ _ _ Heqt).
                apply joinI. rewrite convertR_extern, convertR_local.
                unfold join; simpl. rewrite H0, H1. left; eassumption.
             unfold DomSrc in H0. rewrite Heqd, H in H0.
               discriminate.
           left; trivial.
   (*2/8*) rewrite convertR_locBlocksTgt, convertR_extBlocksTgt.
           intros. specialize (disjoint_extern_local_Tgt _ WDnu23 b). intros.
           remember (locBlocksTgt nu23 b) as d.
           destruct d; apply eq_sym in Heqd.
             destruct H. inv H.
             right; rewrite H. simpl.
             assert (DomTgt nu23 b = true).
               unfold DomTgt; rewrite Heqd. trivial.
             rewrite H0; simpl. rewrite andb_false_r. trivial.
           left; trivial.
   (*3/8*) rewrite convertR_locBlocksTgt, convertR_locBlocksSrc, convertR_local.
           apply WDnu23.
   (*4/8*) rewrite convertR_extBlocksTgt, convertR_extBlocksSrc, convertR_extern.
           intros.
           destruct (joinD_Some _ _ _ _ _ H) as [EXT23 | [EXT23 LOC23]]; clear H.
              destruct (extern_DomRng _ WDnu23 _ _ _ EXT23).
              rewrite H, H0; simpl. split; trivial.
           remember ( local_of nu23 b1) as q.
           destruct q; try inv LOC23; apply eq_sym in Heqq.
           assert (AI: as_inj nu23 b1 = None).
              apply joinI_None; assumption.
           destruct GOAL5 as [? _].
           destruct (H b1 b2 z AI); clear H.
              apply joinI. rewrite convertR_extern, convertR_local.
              unfold join. rewrite EXT23, Heqq. left; trivial.
           unfold FreshDom. rewrite LOC23, AI, H1; simpl.
           assert (DomTgt nu' b2 = true).
             destruct (mkiVal4 _ _ _ LOC23) as [[MK _] | [MK | MK]].
             (*1/3*) congruence.
             (*2/3*) destruct MK as [? [? ?]].
                   eapply as_inj_DomRng; eassumption.
             (*3/3*) destruct MK as [mm [? [? ?]]].
                   eapply as_inj_DomRng; eassumption.
           rewrite H. intuition.
   (*5/8*) rewrite convertR_pubBlocksTgt, convertR_pubBlocksSrc, convertR_local.
           apply WDnu23.
   (*6/8*) rewrite convertR_frgnBlocksTgt, convertR_frgnBlocksSrc.
           rewrite convertR_extern; trivial. intros.
           destruct (frgnSrcAx _ WDnu23 _ H) as [b2 [d [EXT FT]]].
           exists b2, d; unfold join. rewrite EXT; split; trivial.
   (*7/8*) rewrite convertR_locBlocksTgt, convertR_pubBlocksTgt.
            apply WDnu23.
   (*8/8*) rewrite convertR_frgnBlocksTgt, convertR_extBlocksTgt.
            intros. rewrite (frgnBlocksExternTgt _ WDnu23 _ H); trivial.
  split. assumption.
  split. rewrite GlueExt. trivial.
  split. assumption.
  intros. apply GlueFrgn; trivial.
split. intros. (*Proof of NORM*) clear GOAL1 ConvertR_J23'.
   subst.
   destruct (joinD_Some _ _ _ _ _ H) as [EXT | [EXT LOC]]; clear H.
      destruct (Norm12 _ _ _ EXT) as [b3 [d2 EXT2]].
      exists b3, d2. apply joinI; left. assumption.
   remember (local_of nu12 b1) as q.
   destruct q; apply eq_sym in Heqq. inv LOC.
   assert (AsInj12: as_inj nu12 b1 = None).
     apply joinI_None; assumption.
   destruct (sep12 _ _ _ AsInj12 LOC).
   remember (extern_of nu23 b2) as d.
   destruct d; apply eq_sym in Heqd.
     destruct p. exfalso. apply H0. eapply VBj23_1. apply extern_in_all; eassumption.
   remember (local_of nu23 b2) as w.
   destruct w; apply eq_sym in Heqw.
     destruct p. exfalso. apply H0. eapply VBj23_1. apply local_in_all; eassumption.
   unfold join. rewrite Heqd, Heqw.
   unfold removeUndefs in LOC. rewrite AsInj12 in LOC.
   remember (as_inj nu' b1) as t.
   destruct t; try inv LOC. destruct p; apply eq_sym in Heqt.
   remember (j23' b2) as u.
   destruct u; apply eq_sym in Hequ.
     destruct p. exists b0, z0; trivial.
   destruct (mkiVal3 _ _ _ H2) as [[X _] | [X | X]]; clear mkiVal3.
      rewrite X in AsInj12. discriminate.
      destruct X as [B1 [B2 [D2 [VB1 VB2]]]].
      exfalso. destruct (mkiVal5 _ VB2 Hequ) as [[Ya Yb] | [[Ya Yb] | [mm [Ya Yb]]]].
        subst. clear - Ya. unfold Mem.valid_block in Ya. xomega.
        subst. rewrite Heqt in Yb. discriminate.
        subst. clear - Ya. rewrite Pos.add_comm in Ya. apply eq_sym in Ya.
                    eapply Pos.add_no_neutral. apply Ya.
      destruct X as [m [B1 [B2 [D1 [VB1 VB2]]]]].
      exfalso. destruct (mkiVal5 _ VB2 Hequ) as [[Ya Yb] | [[Ya Yb] | [mm [Ya Yb]]]].
        subst. clear - Ya. unfold Mem.valid_block in Ya. xomega.
        subst.  clear - Ya. rewrite Pos.add_comm in Ya.
                    eapply Pos.add_no_neutral. apply Ya.
        subst. assert (mm=m). clear - Ya. xomega. subst.
               rewrite Heqt in Yb. discriminate.
repeat (split; trivial).
Qed.

Section MEMORY_CONSTRUCTION_EFF.
Variable nu23 nu12 : SM_Injection.
Variable j23 j12':meminj.
Variable m1 m1' m2 : mem.

Definition AccessMap_EFF_FUN (b2:block):
           Z -> perm_kind -> option permission :=
  if plt b2 (Mem.nextblock m2)
  then fun ofs2 k =>
       if (locBlocksSrc nu23 b2)
       then if (pubBlocksSrc nu23 b2)
            then match source (local_of nu12) m1 b2 ofs2 with
                   Some(b1,ofs1) => if pubBlocksSrc nu12 b1
                                    then PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                                    else PMap.get b2 m2.(Mem.mem_access) ofs2 k
                 | None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
                 end
            else PMap.get b2 m2.(Mem.mem_access) ofs2 k
       else match source (as_inj nu12) m1 b2 ofs2 with
                   Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                 | None => match j23 b2 with
                             None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
                           | Some (b3,d3) => None
                           end
(*Was:                            PMap.get b2 m2.(Mem.mem_access) ofs2 k*)

               end
     else fun ofs2 k =>
           match source j12' m1' b2 ofs2 with
              Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None => None
          end.

(*Excactly the same proof as in mem_interpolation_II.v*)
Lemma mkAccessMap_EFF_existsT: forall N
       (VB : (Mem.nextblock m2 <= N)%positive)
       (VBJ12': forall b1 b2 delta, j12' b1 = Some (b2,delta) ->
                                   (b2 < N)%positive),
      { M : PMap.t (Z -> perm_kind -> option permission) |
          fst M = (fun k ofs => None) /\
          forall b, PMap.get b M = AccessMap_EFF_FUN b}.
Proof. intros.
  apply (pmap_construct_c _ AccessMap_EFF_FUN
              N (fun ofs k => None)).
    intros. unfold AccessMap_EFF_FUN.
    remember (plt n (Mem.nextblock m2)) as d.
    destruct d; clear Heqd; trivial.
       exfalso. xomega.
    extensionality ofs. extensionality k.
      remember (source j12' m1' n ofs) as src.
      destruct src; trivial.
        destruct p.
        destruct (source_SomeE _ _ _ _ _ Heqsrc)
          as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
        clear Heqsrc; subst. apply eq_sym in PP. inv PP.
        apply VBJ12' in JJ.
        exfalso. xomega.
Qed.

Definition ContentMap_EFF_ValidBlock_FUN b2 ofs2: memval :=
    if locBlocksSrc nu23 b2
    then if (pubBlocksSrc nu23 b2)
         then match source (local_of nu12) m1 b2 ofs2 with
             Some(b1,ofs1) =>
                 if pubBlocksSrc nu12 b1
                 then inject_memval j12'
                      (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
                 else ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
           | None => ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
            end
         else ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
    else match source (as_inj nu12) m1 b2 ofs2 with
             Some(b1,ofs1) => inject_memval j12'
                                (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
           | None => ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
         end.

Definition ContentMap_EFF_InvalidBlock_FUN b2 ofs2: memval :=
   match source j12' m1' b2 ofs2 with
                None => Undef
              | Some(b1,ofs1) => inject_memval j12'
                       (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
   end.

Definition ContentMap_EFF_Block_FUN b ofs : memval:=
  if plt b (Mem.nextblock m2)
  then ContentMap_EFF_ValidBlock_FUN b ofs
  else ContentMap_EFF_InvalidBlock_FUN b ofs.

Variable MINMAX_Offset: block -> option (Z * Z).

Hypothesis MINMAX: forall b2 ,
                   match MINMAX_Offset b2 with
                    Some(mn,mx) =>
                      (forall ofs, ofs < mn \/ ofs > mx ->
                        Plt b2 (Mem.nextblock m2) ->
                        ZMap.get ofs (Mem.mem_contents m2)!!b2 = Undef) /\
                      forall b1 delta, as_inj nu12 b1 = Some(b2,delta) \/ j12' b1 = Some(b2,delta)->
                       forall z, z + delta < mn \/ z + delta > mx ->
                                 ZMap.get z (Mem.mem_contents m1')!!b1 = Undef
                   | None =>
                      (Plt b2 (Mem.nextblock m2) ->
                          forall ofs, ZMap.get ofs (Mem.mem_contents m2)!!b2 = Undef)
                      /\
                       forall b1 delta, as_inj nu12 b1 = Some(b2,delta) \/ j12' b1 = Some(b2,delta)->
                       forall z, ZMap.get z (Mem.mem_contents m1')!!b1 = Undef
                    end.

Variable WDnu12: SM_wd nu12.

Lemma CM_block_EFF_existsT: forall b,
      { M : ZMap.t memval |
          fst M = Undef /\
          forall ofs, ZMap.get ofs M =
                      ContentMap_EFF_Block_FUN b ofs}.
Proof. intros. clear j23.
  remember (zmap_finite_c _ (PMap.get b m2.(Mem.mem_contents))) as LH2.
  apply eq_sym in HeqLH2. destruct LH2 as [lo2 hi2].
  specialize (zmap_finite_sound_c _ _ _ _ HeqLH2).
  intros Bounds2; clear HeqLH2.
   assert (Undef2: fst (Mem.mem_contents m2) !! b = Undef). apply m2.
   rewrite Undef2 in *. clear Undef2.
  specialize (MINMAX b).
  remember (MINMAX_Offset b) as MM.
  destruct MM; apply eq_sym in HeqMM.
    destruct p as [mn mx].
    destruct MINMAX as [MINMAX_A MINMAX_B]; clear MINMAX.
    destruct (zmap_construct_c _
              (ContentMap_EFF_Block_FUN b)
              (Z.min mn lo2)
              (Z.max mx hi2)
            Undef) as [M PM].
    intros. unfold ContentMap_EFF_Block_FUN; simpl.
        unfold ContentMap_EFF_ValidBlock_FUN.
        unfold ContentMap_EFF_InvalidBlock_FUN.
   destruct (plt b (Mem.nextblock m2)).
   (*validblock m2 b*)
      remember (locBlocksSrc nu23 b) as d.
      destruct d; apply eq_sym in Heqd.
       remember (pubBlocksSrc nu23 b) as q.
       destruct q; apply eq_sym in Heqq.
         remember (source (local_of nu12) m1 b n) as src.
         destruct src; trivial.
           destruct p0.
           destruct (source_SomeE _ _ _ _ _ Heqsrc)
             as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc; subst. apply eq_sym in PP. inv PP.
            assert (as_inj nu12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
              left; eapply local_in_all; try eassumption.
            remember (pubBlocksSrc nu12 b0) as w.
            destruct w; apply eq_sym in Heqw.
              rewrite (MINMAX_B _ _ H0 z). simpl. trivial.
              clear -H.
              destruct H.
              apply Z.min_glb_lt_iff in H. left. omega.
              assert (Z.max mx hi2 < z + dd1) by omega.
                apply Z.max_lub_lt_iff in H0. right; omega.
             (*case pubBlocksSrc nu12 b0 = false*)
             eapply MINMAX_A.
               clear -H. xomega.
               apply p.
         (*case source ... = None*)
           eapply MINMAX_A.
             clear -H. xomega.
             apply p.
      (*case pubBlocksSrc nu23 b = false*)
      eapply MINMAX_A.
        clear -H. xomega.
        apply p.
       (*alterative proof: apply Bounds2.
           clear -H.
           destruct H.
             apply Z.min_glb_lt_iff in H. left. omega.
             assert (Z.max mx hi2 < n) by omega.
               apply Z.max_lub_lt_iff in H0. right; omega.*)
    (*Case myblocksSrc nu23 b = false*)
         remember (source (as_inj nu12) m1 b n) as src.
         destruct src; trivial.
           destruct p0.
           destruct (source_SomeE _ _ _ _ _ Heqsrc)
             as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc; subst. apply eq_sym in PP. inv PP.
            assert (as_inj nu12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
              left; eassumption.
            rewrite (MINMAX_B _ _ H0 z). simpl. trivial.
              clear -H.
              destruct H.
               apply Z.min_glb_lt_iff in H. left. omega.
               assert (Z.max mx hi2 < z + dd1) by omega.
                 apply Z.max_lub_lt_iff in H0. right; omega.
         (*case source ... = None*)
           eapply MINMAX_A.
               clear -H. xomega.
               apply p.
   (*invalidblock m2 b*)
       remember (source j12' m1' b n) as src.
       destruct src; trivial.
       destruct p.
         destruct (source_SomeE _ _ _ _ _ Heqsrc)
           as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
          clear Heqsrc; subst. apply eq_sym in PP. inv PP.
         assert (as_inj nu12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
            right; trivial.
         rewrite (MINMAX_B _ _ H0 z). simpl. trivial.

         clear -H.
         destruct H.
           apply Z.min_glb_lt_iff in H. left. omega.
           assert (Z.max mx hi2 < z + dd1) by omega.
             apply Z.max_lub_lt_iff in H0. right; omega.

  exists M. apply PM.

(*case MINMAX_Offset b = None*)
  exists (ZMap.init Undef).
    split. reflexivity.
    destruct MINMAX as [MINMAX_A MINMAX_B]; clear MINMAX.
    intros. rewrite ZMap.gi.
    unfold ContentMap_EFF_Block_FUN.
    destruct (plt b (Mem.nextblock m2)).
      unfold ContentMap_EFF_ValidBlock_FUN.
      rewrite (MINMAX_A p).
      remember (locBlocksSrc nu23 b) as d.
      destruct d; apply eq_sym in Heqd.
        remember (pubBlocksSrc nu23 b) as w.
        destruct w; trivial; apply eq_sym in Heqw.
        remember (source (local_of nu12) m1 b ofs) as src.
        destruct src; trivial.
          destruct p0.
          destruct (source_SomeE _ _ _ _ _ Heqsrc)
             as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc; subst. apply eq_sym in PP. inv PP.
           assert (as_inj nu12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
              left. apply local_in_all; eassumption.
        rewrite (MINMAX_B _ _ H z). simpl.
          destruct (pubBlocksSrc nu12 b0); trivial.
     (*case locBlocksSrc nu23 b = false*)
        remember (source (as_inj nu12) m1 b ofs) as src.
        destruct src; trivial.
          destruct p0.
          destruct (source_SomeE _ _ _ _ _ Heqsrc)
             as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
            clear Heqsrc; subst. apply eq_sym in PP. inv PP.
           assert (as_inj nu12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
              left; assumption.
        rewrite (MINMAX_B _ _ H z). simpl. trivial.


    unfold ContentMap_EFF_InvalidBlock_FUN.
      remember (source j12' m1' b ofs) as src.
      destruct src; trivial.
        destruct p.
        destruct (source_SomeE _ _ _ _ _ Heqsrc)
           as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
          clear Heqsrc; subst. apply eq_sym in PP. inv PP.
         assert (as_inj nu12 b0 = Some (b, dd1) \/ j12' b0 = Some (b, dd1)).
            right; trivial.
        rewrite (MINMAX_B _ _ H z). simpl. trivial.
Qed.

Definition ContentsMap_EFF_FUN  (NB2' b:block) : ZMap.t memval.
destruct (plt b NB2').
  apply (CM_block_EFF_existsT b).
apply (ZMap.init Undef).
Defined.

Lemma ContentsMap_EFF_existsT:
      forall (NB2':block) ,
      { M : PMap.t (ZMap.t memval) |
        fst M = ZMap.init Undef /\
        forall b, PMap.get b M =
           ContentsMap_EFF_FUN NB2' b}.
Proof. intros.
  apply (pmap_construct_c _ (ContentsMap_EFF_FUN NB2')
              NB2' (ZMap.init Undef)).
    intros. unfold ContentsMap_EFF_FUN. simpl.
    remember (plt n NB2') as d.
    destruct d; clear Heqd; trivial.
      exfalso. xomega.
Qed.

Definition mkEFF
            (NB2':block)
            (Hyp1: (Mem.nextblock m2 <= NB2')%positive)
            (Hyp2: forall (b1 b2 : block) (delta : Z),
                       j12' b1 = Some (b2, delta) -> (b2 < NB2')%positive)
           : Mem.mem'.
destruct (mkAccessMap_EFF_existsT NB2' Hyp1 Hyp2) as [AM [ADefault PAM]].
destruct (ContentsMap_EFF_existsT NB2') as [CM [CDefault PCM]].
eapply Mem.mkmem with (nextblock:=NB2')
                      (mem_access:=AM)
                      (mem_contents:=CM).
  (*access_max*)
  intros. rewrite PAM. unfold AccessMap_EFF_FUN.
     destruct (plt b (Mem.nextblock m2)).
     (*valid_block m2 b*)
        destruct (locBlocksSrc nu23 b).
          destruct (pubBlocksSrc nu23 b).
            destruct (source (local_of nu12) m1 b ofs).
              destruct p0.
              destruct (pubBlocksSrc nu12 b0). apply m1'. apply m2.
            apply m2.
          apply m2.
        destruct (source (as_inj nu12) m1 b ofs).
            destruct p0. apply m1'.
        destruct (j23 b). destruct p0. reflexivity. apply m2.
     (*invalid_block m2 b*)
        destruct (source j12' m1' b ofs).
          destruct p. apply m1'.
        reflexivity.
  (*nextblock_noaccess*)
    intros. rewrite PAM.
    unfold AccessMap_EFF_FUN.
    destruct (plt b (Mem.nextblock m2)).
      exfalso. apply H; clear - Hyp1 p. xomega.
    remember (source j12' m1' b ofs) as src.
    destruct src; trivial.
      destruct p.
      exfalso. apply H. clear - Heqsrc Hyp2.
      apply source_SomeE in Heqsrc.
      destruct Heqsrc as [b1 [delta [ofs1
          [PBO [Bounds [J1 [P1 Off2]]]]]]]; subst.
        apply (Hyp2 _ _ _ J1).
  (*contents_default*)
    intros.
    rewrite PCM; clear PCM.
    unfold ContentsMap_EFF_FUN.
    destruct (plt b NB2').
     remember (CM_block_EFF_existsT b).
     destruct s. apply a.
    reflexivity.
Defined.

Lemma mkEff_nextblock: forall N Hyp1 Hyp2,
         Mem.nextblock (mkEFF N Hyp1 Hyp2) = N.
Proof. intros. unfold mkEFF.
  remember (mkAccessMap_EFF_existsT N Hyp1 Hyp2).
  destruct s as [X1 X2].
  destruct X2. simpl in *.
  remember (ContentsMap_EFF_existsT N).
  destruct s as [Y1 Y2].
  destruct Y2; simpl in *. reflexivity.
Qed.

End MEMORY_CONSTRUCTION_EFF.

Section MINMAX_EFF.
Variable nu12: SM_Injection.
Variable j12' :meminj.
Variable m1' m2: mem.

Definition MINMAX_Offset (b2:block) : option (Z * Z) :=
  if plt b2 (Mem.nextblock m2)
  then match (zmap_finite_c _ (PMap.get b2 m2.(Mem.mem_contents)))
       with (min2, max2) =>
          match minmax m1' (as_inj nu12) b2 with
             Some(min1, max1) =>
                  Some(Z.min min1 min2, Z.max max1 max2)
           | None => Some(min2,max2)
          end
       end
  else minmax m1' j12' b2.

Hypothesis inc12: inject_incr (as_inj nu12) j12'.
Hypothesis VBj12'_1: forall b1 b2 delta,
                     j12' b1 = Some (b2, delta) ->
                     Mem.valid_block m1' b1.
Hypothesis JJ: forall b1 b2 delta,
                       j12' b1 = Some (b2, delta) ->
                       Mem.valid_block m2 b2 ->
                       as_inj nu12 b1 = Some (b2, delta).

Lemma MINMAX: forall b2 ,
        match MINMAX_Offset b2 with
          Some(mn,mx) =>
              (forall ofs, ofs < mn \/ ofs > mx ->
                  Plt b2 (Mem.nextblock m2) ->
                  ZMap.get ofs (Mem.mem_contents m2)!!b2 = Undef) /\
              forall b1 delta, as_inj nu12 b1 = Some(b2,delta) \/
                               j12' b1 = Some(b2,delta)->
                forall z, z + delta < mn \/ z + delta > mx ->
                       ZMap.get z (Mem.mem_contents m1')!!b1 = Undef
        | None =>
             (Plt b2 (Mem.nextblock m2) ->
                forall ofs, ZMap.get ofs (Mem.mem_contents m2)!!b2 = Undef)
             /\ forall b1 delta,
                     as_inj nu12 b1 = Some(b2,delta) \/ j12' b1 = Some(b2,delta)->
                 forall z, ZMap.get z (Mem.mem_contents m1')!!b1 = Undef
         end.
Proof. intros.
unfold MINMAX_Offset.
remember (zmap_finite_c memval (Mem.mem_contents m2) !! b2) as MM2.
destruct MM2 as [min2 max2]. apply eq_sym in HeqMM2.
destruct (plt b2 (Mem.nextblock m2)).
  specialize (minmax_sound m1' (as_inj nu12) b2).
  remember (minmax m1' (as_inj nu12) b2) as MM; intros.
  destruct MM.
    destruct p0 as [mn mx].
    split; intros.
       apply zmap_finite_sound_c with (n:=ofs) in HeqMM2.
       rewrite HeqMM2. apply m2.
       clear - H0. xomega.
    intros. assert (as_inj nu12 b1 = Some(b2,delta)).
              destruct H0. trivial. apply (JJ _ _ _ H0 p).
            apply (H b1 delta); trivial.
              apply inc12 in H2. apply (VBj12'_1 _ _ _ H2).
            clear - H1. xomega.
  split; intros.
       apply zmap_finite_sound_c with (n:=ofs) in HeqMM2.
       rewrite HeqMM2. apply m2.
       clear - H0. xomega.
     assert (as_inj nu12 b1 = Some(b2,delta)).
              destruct H0. trivial. apply (JJ _ _ _ H0 p).
     apply (H b1 delta); trivial.
       apply inc12 in H2. apply (VBj12'_1 _ _ _ H2).
specialize (minmax_sound m1' j12' b2).
  remember (minmax m1' j12' b2) as MM; intros.
  destruct MM.
    destruct p as [mn mx].
    split; intros. contradiction.
    assert (j12' b1 = Some(b2,delta)).
      destruct H0. apply inc12; assumption. assumption.
    apply (H b1 delta); trivial.
      apply (VBj12'_1 _ _ _ H2).
  split; intros. contradiction.
     assert (j12' b1 = Some(b2,delta)).
       destruct H0. apply inc12; assumption. assumption.
     apply (H b1 delta); trivial.
       apply (VBj12'_1 _ _ _ H1).
Qed.

End MINMAX_EFF.

(*The interpolation for the afterExternal rule*)
Lemma EFF_interp_II_strong: forall m1 m2 nu12
                             (MInj12 : Mem.inject (as_inj nu12) m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') nu23 m3
                             (MInj23 : Mem.inject (as_inj nu23) m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                              nu' (WDnu' : SM_wd nu')
                             (SMvalNu' : sm_valid nu' m1' m3')
                             (MemInjNu' : Mem.inject (as_inj nu') m1' m3')

                             (ExtIncr: extern_incr (compose_sm nu12 nu23) nu')
                             (SMInjSep: sm_inject_separated (compose_sm nu12 nu23) nu' m1 m3)
                             (SMV12: sm_valid nu12 m1 m2)
                             (SMV23: sm_valid nu23 m2 m3)
                             (UnchPrivSrc: Mem.unchanged_on (fun b ofs => locBlocksSrc (compose_sm nu12 nu23) b = true /\
                                                      pubBlocksSrc (compose_sm nu12 nu23) b = false) m1 m1')
                             (UnchLOOR13: Mem.unchanged_on (local_out_of_reach (compose_sm nu12 nu23) m1) m3 m3')

                             (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                                         locBlocksTgt nu12 = locBlocksSrc nu23 /\
                                         extBlocksTgt nu12 = extBlocksSrc nu23 /\
                                         (forall b, pubBlocksTgt nu12 b = true ->
                                                    pubBlocksSrc nu23 b = true) /\
                                         (forall b, frgnBlocksTgt nu12 b = true ->
                                                    frgnBlocksSrc nu23 b = true))
                             (Norm12: forall b1 b2 d1, extern_of nu12 b1 = Some(b2,d1) ->
                                             exists b3 d2, extern_of nu23 b2 = Some(b3, d2)),
     exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\
                             Mem.inject (as_inj nu23') m2' m3' /\
                             sm_inject_separated nu12 nu12' m1 m2 /\
                             sm_inject_separated nu23 nu23' m2 m3 /\
                             sm_valid nu12' m1' m2' /\ sm_valid nu23' m2' m3' /\
                             (SM_wd nu12' /\ SM_wd nu23' /\
                              locBlocksTgt nu12' = locBlocksSrc nu23' /\
                              extBlocksTgt nu12' = extBlocksSrc nu23' /\
                              (forall b, pubBlocksTgt nu12' b = true ->
                                         pubBlocksSrc nu23' b = true) /\
                              (forall b, frgnBlocksTgt nu12' b = true ->
                                         frgnBlocksSrc nu23' b = true)) /\
                             (forall b1 b2 d1, extern_of nu12' b1 = Some(b2,d1) ->
                                     exists b3 d2, extern_of nu23' b2 = Some(b3, d2)) /\
                              Mem.unchanged_on (fun b ofs => locBlocksSrc nu23 b = true /\
                                                             pubBlocksSrc nu23 b = false) m2 m2' /\
                              Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2' /\
                 (*             Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3' /\*)
                   (forall b1 b2 d1, as_inj nu12' b1 = Some(b2,d1) ->
                       as_inj nu12 b1 = Some(b2,d1) \/
                       exists b3 d, as_inj nu' b1 = Some(b3,d)) /\
                   (forall b2 b3 d2, as_inj nu23' b2 = Some(b3,d2) ->
                       as_inj nu23 b2 = Some(b3,d2) \/
                       exists b1 d, as_inj nu' b1 = Some(b3,d)) /\
                   (forall b1 b2 ofs2, as_inj nu12' b1 = Some(b2,ofs2) ->
                     (as_inj nu12 b1 = Some (b2,ofs2)) \/
                     (b1 = Mem.nextblock m1 /\ b2 = Mem.nextblock m2 /\ ofs2 = 0) \/
                     (exists m, (b1 = Mem.nextblock m1 + m /\ b2=Mem.nextblock m2 + m)%positive /\ ofs2=0)) /\
                   (forall b2 b3 ofs3, as_inj nu23' b2 = Some(b3,ofs3) ->
                     (as_inj nu23 b2 = Some (b3,ofs3)) \/
                     (b2 = Mem.nextblock m2 /\ as_inj nu' (Mem.nextblock m1) = Some(b3,ofs3)) \/
                     (exists m, (b2 = Mem.nextblock m2 + m)%positive /\
                            as_inj nu' ((Mem.nextblock m1+m)%positive) = Some(b3,ofs3))).
Proof. intros.
  remember (mkInjections m1 m1' m2 (as_inj nu12) (as_inj nu23) (as_inj nu')) as MKI.
  apply eq_sym in HeqMKI. destruct MKI as [[[j12' j23'] n1'] n2'].
  assert (VBj12_1: forall (b1 b2 : block) (ofs2 : Z),
                as_inj nu12 b1 = Some (b2, ofs2) -> Mem.valid_block m1 b1).
      intros. eapply SMV12. eapply as_inj_DomRng. eassumption. apply GlueInvNu.
  assert (VBj12_2: forall (b1 b2 : block) (ofs2 : Z),
                as_inj nu12 b1 = Some (b2, ofs2) -> Mem.valid_block m2 b2).
      intros. eapply SMV12. eapply as_inj_DomRng. eassumption. apply GlueInvNu.
  assert (VBj23: forall (b1 b2 : block) (ofs2 : Z),
                as_inj nu23 b1 = Some (b2, ofs2) -> Mem.valid_block m2 b1).
      intros. eapply SMV23. eapply as_inj_DomRng. eassumption. apply GlueInvNu.
  assert (inc12:= mkInjections_1_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1).
  assert (sep12:= mkInjections_1_injsep _ _ _ _ _ _ _ _ _ _ HeqMKI).
  assert (inc23:= mkInjections_2_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23).
  assert (InjSep: inject_separated (compose_meminj (as_inj nu12) (as_inj nu23)) (as_inj nu') m1 m3).
    specialize (sm_inject_separated_mem _ _ _ _ SMInjSep WDnu'). intros.
    rewrite compose_sm_as_inj in H. apply H.
    eapply GlueInvNu. eapply GlueInvNu. eapply GlueInvNu.  eapply GlueInvNu.
  assert (sep23:= mkInjections_2_injsep _ _ _ _ _ _ _ _ _ _
                   HeqMKI VBj12_1 _ InjSep).
  assert (VBj': forall b1 b3 ofs3, as_inj nu' b1 = Some (b3, ofs3) ->
             (b1 < Mem.nextblock m1')%positive).
      intros. eapply SMvalNu'. eapply as_inj_DomRng; eassumption.
  assert (WDnu12: SM_wd nu12). apply GlueInvNu.
  assert (WDnu23: SM_wd nu23). apply GlueInvNu.

destruct (mkInjections_0  _ _ _ _ _ _ _ _ _ _ HeqMKI)
   as [HH | HH].
destruct HH as [? [? [? [? ?]]]]. subst.
  assert (Mem.nextblock m1' = Mem.nextblock m1).
      apply forward_nextblock in Fwd1. eapply Pos.le_antisym; assumption.
  rewrite H0 in *.
  assert (VB1': forall (b1 b2 : block) (delta : Z),
             as_inj nu12 b1 = Some (b2, delta) -> Mem.valid_block m1' b1).
     intros. unfold Mem.valid_block. rewrite H0. apply (VBj12_1 _ _ _ H1).
  assert (JJ12: forall (b1 b2 : block) (delta : Z),
                as_inj nu12 b1 = Some (b2, delta) ->
                Mem.valid_block m2 b2 -> as_inj nu12 b1 = Some (b2, delta)).
     auto.
(*  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI InjIncr _
                 InjSep VBj12_1 VBj12_2 VBj23 VBj').*)
  assert (RU: (removeUndefs (as_inj nu12) (as_inj nu') (as_inj nu12)) = as_inj nu12).
      unfold removeUndefs. extensionality b.
      remember (as_inj nu12 b) as d.
      destruct d. destruct p; trivial.
      destruct (as_inj nu'); trivial. destruct p; trivial.
  exists (mkEFF nu23 nu12 (as_inj nu23) (as_inj nu12) m1 m1' m2
                  (MINMAX_Offset nu12 (as_inj nu12) m1' m2)
               (MINMAX nu12 (as_inj nu12) m1' m2 inc12 VB1' JJ12) WDnu12 _ (Pos.le_refl _) VBj12_2).

  destruct (effect_interp_OK _ _ _ MInj12 _ Fwd1 _ _ MInj23
      _ Fwd3 _ WDnu' SMvalNu' MemInjNu' ExtIncr SMInjSep SMV12 SMV23
      UnchPrivSrc UnchLOOR13 GlueInvNu Norm12 _ _ _ _
      HeqMKI _ (eq_refl _)
      (mkEFF nu23 nu12 (as_inj nu23) (as_inj nu12) m1 m1' m2
                  (MINMAX_Offset nu12 (as_inj nu12) m1' m2)
               (MINMAX nu12 (as_inj nu12) m1' m2 inc12 VB1' JJ12) WDnu12 _ (Pos.le_refl _) VBj12_2))
     as [unchA [unchB (*[unchC*) [nu12' [nu23' [Hnu12' [Hnu23'
           [Hnu' [extInc12 [extInc23 [smSep12 [smSep23
             [smvNu12' [smvNu23' [Glue123 [Ext123 [Fwd2 [MInjNu12' InjNu23']]]]]]]]]]]]]]]]].
   (*discharge application condition "nextblock" *)
     unfold mkEFF.
     destruct (mkAccessMap_EFF_existsT nu23 nu12 (as_inj nu23) (as_inj nu12) m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_EFF_existsT nu23 nu12 (as_inj nu12) m1 m1' m2
                (MINMAX_Offset nu12 (as_inj nu12) m1' m2)
                (MINMAX nu12 (as_inj nu12) m1' m2 inc12 VB1' JJ12)
                WDnu12 (Mem.nextblock m2))
       as [CM [CDefault PCM]].
     simpl. reflexivity.
   (*discharge application condition "ContentMapOK"*)
     unfold ContentEffProperty, mkEFF.
     destruct (mkAccessMap_EFF_existsT nu23 nu12 (as_inj nu23) (as_inj nu12) m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_EFF_existsT nu23 nu12 (as_inj nu12) m1 m1' m2
                (MINMAX_Offset nu12 (as_inj nu12) m1' m2)
                (MINMAX nu12 (as_inj nu12) m1' m2 inc12 VB1' JJ12)
                WDnu12 (Mem.nextblock m2))
       as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PCM; clear PCM.
        unfold ContentsMap_EFF_FUN.
        destruct (CM_block_EFF_existsT nu23 nu12 (as_inj nu12) m1 m1' m2
                (MINMAX_Offset nu12 (as_inj nu12) m1' m2)
                (MINMAX nu12 (as_inj nu12) m1' m2 inc12 VB1' JJ12)
                WDnu12 b2)
                 as [B [FB HB]].
        simpl in *. rewrite RU.
        destruct (plt b2 (Mem.nextblock m2)).
          split; intros.
          remember (locBlocksSrc nu23 b2) as d.
          destruct d; apply eq_sym in Heqd.
            remember (pubBlocksSrc nu23 b2) as q.
            destruct q; apply eq_sym in Heqq.
              destruct (pubSrc _ WDnu23 _ Heqq) as [b3 [d2 [Pub23 Tgt3]]].
              remember (source (local_of nu12) m1 b2 ofs2) as src.
              destruct src.
                destruct p0. rewrite HB.
                unfold ContentMap_EFF_Block_FUN.
                destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                unfold ContentMap_EFF_ValidBlock_FUN.
                rewrite Heqd, Heqq.
                rewrite <- Heqsrc.
                destruct (pubBlocksSrc nu12 b); trivial.
              rewrite HB.
                unfold ContentMap_EFF_Block_FUN.
                destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                unfold ContentMap_EFF_ValidBlock_FUN.
                rewrite <- Heqsrc. rewrite Heqd, Heqq. trivial.
            rewrite HB.
              unfold ContentMap_EFF_Block_FUN.
              destruct (plt b2 (Mem.nextblock m2)); try contradiction.
              unfold ContentMap_EFF_ValidBlock_FUN.
              rewrite Heqd, Heqq. trivial.
          (*case locBlocksSrc nu23 b2 = false*)
              remember (source (as_inj nu12) m1 b2 ofs2) as src.
              destruct src.
                destruct p0. rewrite HB.
                unfold ContentMap_EFF_Block_FUN.
                destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                unfold ContentMap_EFF_ValidBlock_FUN.
                rewrite Heqd.
                rewrite <- Heqsrc. trivial.
              rewrite HB.
                unfold ContentMap_EFF_Block_FUN.
                destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                unfold ContentMap_EFF_ValidBlock_FUN.
                rewrite Heqd. rewrite <- Heqsrc. trivial.
          split; intros. contradiction.
          apply FB.
        (*invalid m2 b2*)
          split; intros; try contradiction.
          split; intros.
             remember (source (as_inj nu12) m1' b2 ofs2) as src.
             destruct src.
               destruct p.
               apply source_SomeE in Heqsrc.
               destruct Heqsrc as [b1 [delta [ofs1
                  [PBO [Bounds [J1 [P1 Off2]]]]]]].
               (*clear ID RUD.*) inv PBO.
               exfalso. apply (H1 (VBj12_2 _ _ _ J1)).
             rewrite ZMap.gi. trivial.
           reflexivity.
   (*discharge application condition AccessMapOK*)
     rewrite RU in *.
     unfold AccessEffProperty, mkEFF.
     destruct (mkAccessMap_EFF_existsT nu23 nu12 (as_inj nu23) (as_inj nu12) m1 m1' m2 (Mem.nextblock m2)
         (Pos.le_refl (Mem.nextblock m2)) VBj12_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_EFF_existsT nu23 nu12 (as_inj nu12) m1 m1' m2
                (MINMAX_Offset nu12 (as_inj nu12) m1' m2)
                (MINMAX nu12 (as_inj nu12) m1' m2 inc12 VB1' JJ12)
                WDnu12 (Mem.nextblock m2))
       as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PAM; clear PAM.
       unfold AccessMap_EFF_FUN.
       simpl in *.
       destruct (plt b2 (Mem.nextblock m2)).
         split; intros; try contradiction.
           remember (locBlocksSrc nu23 b2) as d.
           destruct d.
             remember (pubBlocksSrc nu23 b2) as q.
             destruct q; apply eq_sym in Heqq.
               destruct (pubSrc _ WDnu23 _ Heqq) as [b3 [d2 [Pub23 T3]]].
               remember (source (local_of nu12) m1 b2 ofs2) as src.
               destruct src.
                 destruct p0.
                 destruct (pubBlocksSrc nu12 b); trivial.
               trivial.
             trivial.
           (*case locBlocksSrc nu23 b2 = false*)
              remember (source (as_inj nu12) m1 b2 ofs2) as src.
              destruct src.
                destruct p0. trivial.
              destruct (as_inj nu23 b2); trivial. destruct p0; trivial.
         split; intros; try contradiction.
           remember (source (as_inj nu12) m1' b2 ofs2) as src.
           destruct src; trivial.
             destruct p; trivial.
  exists nu12', nu23'.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
(*  split; trivial.*)
  split; intros.
    clear - H1 extInc12 Hnu12' Glue123.
    remember (as_inj nu12 b1) as d.
    destruct d; apply eq_sym in Heqd.
      destruct p. apply extern_incr_as_inj in extInc12.
      rewrite (extInc12 _ _ _ Heqd) in H1.
      left; trivial.
      apply  Glue123.
    clear Glue123; subst.
      destruct (joinD_None _ _ _ Heqd).
      destruct (joinD_Some _ _ _ _ _ H1)
            as [EXT | [EXT LOC]]; clear H1;
         rewrite convertL_extern in EXT.
       unfold join, removeUndefs in EXT.
          rewrite H, H0, Heqd in EXT.
          destruct (as_inj nu' b1); try discriminate.
          destruct p; congruence.
      rewrite convertL_local in LOC. congruence.
  split; intros.
    clear - H1 extInc23 Hnu23' Glue123.
    remember (as_inj nu23 b2) as d.
    destruct d; apply eq_sym in Heqd.
      destruct p. apply extern_incr_as_inj in extInc23.
      rewrite (extInc23 _ _ _ Heqd) in H1.
      left; trivial.
      apply  Glue123.
    clear Glue123; subst.
      destruct (joinD_None _ _ _ Heqd).
      destruct (joinD_Some _ _ _ _ _ H1)
            as [EXT | [EXT LOC]]; clear H1;
         rewrite convertR_extern in EXT.
       unfold join, removeUndefs in EXT.
          rewrite H, H0, Heqd in EXT. inv EXT.
      rewrite convertR_local in LOC. congruence.
  destruct GlueInvNu as [WD12 [WD23 _]].
  split; intros.
    rewrite Hnu12' in H1. clear - WD12 H1.
    destruct (joinD_Some _ _ _ _ _ H1) as [EXT12' | [EXT12' LOC12']];
       clear H1; rewrite convertL_extern in EXT12'.
      destruct (joinD_Some _ _ _ _ _ EXT12') as
          [EXT12 | [EXT12 LOC12]]; clear EXT12'.
        left; apply joinI; left; assumption.
      remember (local_of nu12 b1) as d.
       destruct d; apply eq_sym in Heqd. inv LOC12.
        unfold removeUndefs in LOC12.
        remember (as_inj nu12 b1) as q.
        destruct q. destruct p. left; assumption.
        destruct (as_inj nu' b1); try congruence. destruct p; congruence.
    rewrite convertL_local in LOC12'.
      left; apply joinI; right.
      split; trivial.
      destruct (disjoint_extern_local _ WD12 b1); trivial. congruence.
  rewrite Hnu23' in H1. clear - WD23 H1.
    destruct (joinD_Some _ _ _ _ _ H1) as [EXT23' | [EXT23' LOC23']];
       clear H1; rewrite convertR_extern in EXT23'.
      destruct (joinD_Some _ _ _ _ _ EXT23') as
          [EXT23 | [EXT23 LOC23]]; clear EXT23'.
        left; apply joinI; left; assumption.
      remember (local_of nu23 b2) as d.
       destruct d; apply eq_sym in Heqd. inv LOC23.
        unfold removeUndefs in LOC23.
        remember (as_inj nu23 b2) as q.
        destruct q; try discriminate.
        destruct p. left; assumption.
    rewrite convertR_local in LOC23'.
      left; apply joinI; right.
      split; trivial.
      destruct (disjoint_extern_local _ WD23 b2); trivial. congruence.
(*CASE WHERE m2' actually has additional blocks*)
destruct HH as [N [? [? [? ?]]]]. subst.
  rewrite <- H1 in *.
(*  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI InjIncr _
                 InjSep VBj12_1 VBj12_2 VBj23 VBj').*)
  assert (VB2: (Mem.nextblock m2 <= Mem.nextblock m2 + Pos.of_nat N)%positive).
    xomega.
  assert (VBj12: forall (b1 b2 : block) (ofs2 : Z),
                 as_inj nu12 b1 = Some (b2, ofs2) ->
                 (b1 < Mem.nextblock m1)%positive /\ (b2 < Mem.nextblock m2)%positive).
     intros. split; eapply SMV12; eapply as_inj_DomRng; eassumption.

  assert (RUD:= RU_D _ _ inc12 (as_inj nu')).
  assert (VBj12'_2: forall (b1 b2 : block) (delta : Z),
        (removeUndefs (as_inj nu12) (as_inj nu') j12') b1 = Some (b2, delta) ->
        (b2 < Mem.nextblock m2 + Pos.of_nat N)%positive).
    intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]].  xomega.
       destruct KK as [? [? [? [? U]]]]; apply U.
       destruct KK as [M [? [? [? [? U]]]]]; apply U.
  assert (INC12RU: inject_incr (as_inj nu12) (removeUndefs (as_inj nu12) (as_inj nu') j12')).
     unfold removeUndefs. intros b; intros.
     rewrite H0. trivial.
  assert (VBj12'_1: forall (b1 b2 : block) (delta : Z),
        (removeUndefs (as_inj nu12) (as_inj nu') j12') b1 = Some (b2, delta) ->
        (b1 < Mem.nextblock m1 + Pos.of_nat N)%positive).
    intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]].  xomega.
       destruct KK as [? [? [? [U ?]]]]; apply U.
       destruct KK as [M [? [? [? [U ?]]]]]; apply U.
  assert (VB1': forall (b1 b2 : block) (delta : Z),
               removeUndefs (as_inj nu12) (as_inj nu') j12' b1 = Some (b2, delta) ->
               Mem.valid_block m1' b1).
    intros. unfold Mem.valid_block. rewrite <- H1.
            eapply VBj12'_1; eassumption.
  assert (JJ12: forall (b1 b2 : block) (delta : Z),
                removeUndefs (as_inj nu12) (as_inj nu') j12' b1 = Some (b2, delta) ->
                Mem.valid_block m2 b2 -> as_inj nu12 b1 = Some (b2, delta)).
     intros. apply RUD in H0.
    destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12 VBj23 _ _ _ H0)
      as [KK | [KK |KK]].
       destruct KK as [? [? ?]]. assumption.
       destruct KK as [? [? [? [U ?]]]]. subst.
         unfold Mem.valid_block in H2. xomega.
       destruct KK as [M [? [? [? [U ?]]]]]. subst.
         unfold Mem.valid_block in H2. xomega.
  exists (mkEFF nu23 nu12 j23' (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                  (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2)
               (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                    m1' m2 INC12RU VB1' JJ12)
                WDnu12 _ VB2 VBj12'_2).
  destruct (effect_interp_OK _ _ _ MInj12 _ Fwd1 _ _ MInj23
      _ Fwd3 _ WDnu' SMvalNu' MemInjNu' ExtIncr SMInjSep SMV12 SMV23
      UnchPrivSrc UnchLOOR13 GlueInvNu Norm12 _ _ _ _
      HeqMKI _ (eq_refl _)
      (mkEFF nu23 nu12 j23' (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                  (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2)
               (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                    m1' m2 INC12RU VB1' JJ12)
                WDnu12 _ VB2 VBj12'_2))
       as [unchA [unchB (*[unchC*) [nu12' [nu23' [Hnu12' [Hnu23'
           [Hnu' [extInc12 [extInc23 [smSep12 [smSep23
             [smvNu12' [smvNu23' [Glue123 [Ext123 [Fwd2 [MInjNu12' InjNu23']]]]]]]]]]]]]]]]].
   (*discharge application condition "nextblock" *)
     unfold mkEFF.
     destruct (mkAccessMap_EFF_existsT nu23 nu12 j23'
         (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_EFF_existsT nu23 nu12
         (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
         (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
            m1' m2)
         (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
            INC12RU VB1' JJ12) WDnu12
         (Mem.nextblock m2 + Pos.of_nat N)%positive)
       as [CM [CDefault PCM]].
     simpl. reflexivity.
   (*discharge application condition "ContentMapOK"*)
     unfold ContentEffProperty, mkEFF.
     destruct (mkAccessMap_EFF_existsT nu23 nu12 j23'
         (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_EFF_existsT nu23 nu12
         (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
         (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
            m1' m2)
         (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
            INC12RU VB1' JJ12) WDnu12
         (Mem.nextblock m2 + Pos.of_nat N)%positive)
       as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PCM; clear PCM.
     (*block valid*)
      split; intros.
          remember (locBlocksSrc nu23 b2) as d.
          destruct d; apply eq_sym in Heqd.
            remember (pubBlocksSrc nu23 b2) as q.
            destruct q; apply eq_sym in Heqq.
              destruct (pubSrc _ WDnu23 _ Heqq) as [b3 [d2 [Pub23 Tgt3]]].
              apply (pub_in_all _ WDnu23) in Pub23.
              remember (source (local_of nu12) m1 b2 ofs2) as src.
              destruct src.
                destruct p.
                remember (pubBlocksSrc nu12 b) as w.
                destruct w; apply eq_sym in Heqw.
                  unfold ContentsMap_EFF_FUN.
                  destruct (plt b2 (Mem.nextblock m2 + Pos.of_nat N)); try contradiction.
                  remember (CM_block_EFF_existsT nu23 nu12
                      (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                      (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                             m1' m2)
                      (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
                         INC12RU VB1' JJ12) WDnu12 b2).
                  destruct s; clear Heqs. destruct a.
                  rewrite H3; clear H3.
                  unfold ContentMap_EFF_Block_FUN.
                  destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                  unfold ContentMap_EFF_ValidBlock_FUN.
                  rewrite Heqd, Heqq. rewrite <- Heqsrc. rewrite Heqw. trivial.
                  exfalso. apply n. clear -H0. unfold Mem.valid_block in H0. xomega.
                unfold ContentsMap_EFF_FUN.
                  destruct (plt b2 (Mem.nextblock m2 + Pos.of_nat N)); try contradiction.
                  remember (CM_block_EFF_existsT nu23 nu12
                      (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                     (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                             m1' m2)
                      (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
                         INC12RU VB1' JJ12) WDnu12 b2).
                  destruct s; clear Heqs. destruct a.
                  rewrite H3; clear H3.
                  unfold ContentMap_EFF_Block_FUN.
                  destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                  unfold ContentMap_EFF_ValidBlock_FUN.
                  rewrite Heqd, Heqq. rewrite <- Heqsrc. rewrite Heqw. trivial.
                  exfalso. apply n. clear -H0. unfold Mem.valid_block in H0. xomega.
             unfold ContentsMap_EFF_FUN.
                  destruct (plt b2 (Mem.nextblock m2 + Pos.of_nat N)); try contradiction.
                  remember (CM_block_EFF_existsT nu23 nu12
                      (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                      (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                             m1' m2)
                      (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
                         INC12RU VB1' JJ12) WDnu12 b2).
                  destruct s; clear Heqs. destruct a.
                  rewrite H3; clear H3.
                  unfold ContentMap_EFF_Block_FUN.
                  destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                  unfold ContentMap_EFF_ValidBlock_FUN.
                  rewrite Heqd, Heqq. rewrite <- Heqsrc. trivial.
                  exfalso. apply n. clear -H0. unfold Mem.valid_block in H0. xomega.
            unfold ContentsMap_EFF_FUN.
                  destruct (plt b2 (Mem.nextblock m2 + Pos.of_nat N)); try contradiction.
                  remember (CM_block_EFF_existsT nu23 nu12
                      (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                      (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                             m1' m2)
                      (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
                         INC12RU VB1' JJ12) WDnu12 b2).
                  destruct s; clear Heqs. destruct a.
                  rewrite H3; clear H3.
                  unfold ContentMap_EFF_Block_FUN.
                  destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                  unfold ContentMap_EFF_ValidBlock_FUN.
                  rewrite Heqd, Heqq. trivial.
                  exfalso. apply n. clear -H0. unfold Mem.valid_block in H0. xomega.
          unfold ContentsMap_EFF_FUN.
                  destruct (plt b2 (Mem.nextblock m2 + Pos.of_nat N)); try contradiction.
                  remember (CM_block_EFF_existsT nu23 nu12
                      (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                      (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                             m1' m2)
                      (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
                         INC12RU VB1' JJ12) WDnu12 b2).
                  destruct s; clear Heqs. destruct a.
                  rewrite H3; clear H3.
                  unfold ContentMap_EFF_Block_FUN.
                  destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                  unfold ContentMap_EFF_ValidBlock_FUN.
                  rewrite Heqd.
                  remember (source (as_inj nu12) m1 b2 ofs2) as src.
                  destruct src; trivial. destruct p1; trivial.
                exfalso. apply n. clear -H0. unfold Mem.valid_block in H0. xomega.
    split; intros.
     (*~ Mem.valid_block m2 b2*)
            unfold ContentsMap_EFF_FUN.
                  destruct (plt b2 (Mem.nextblock m2 + Pos.of_nat N)); try contradiction.
                  remember (CM_block_EFF_existsT nu23 nu12
                      (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                      (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                             m1' m2)
                      (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
                         INC12RU VB1' JJ12) WDnu12 b2).
                  destruct s; clear Heqs. destruct a.
                  rewrite H3; clear H3.
                  unfold ContentMap_EFF_Block_FUN.
                  destruct (plt b2 (Mem.nextblock m2)); try contradiction.
                  unfold ContentMap_EFF_InvalidBlock_FUN.
                  remember (source (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' b2 ofs2) as src.
                  destruct src. destruct p0; trivial. trivial.
               remember (source (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' b2 ofs2) as src.
                  destruct src. destruct p.
                    destruct (source_SomeE _ _ _ _ _ Heqsrc)
                      as [bb1 [dd1 [ofs11 [PP [VBB [ JJ [PERM Off2]]]]]]].
                    clear Heqsrc; subst. apply eq_sym in PP. inv PP.
                    apply VBj12'_2 in JJ. contradiction.
                  rewrite ZMap.gi. trivial.
             unfold ContentsMap_EFF_FUN.
                  destruct (plt b2 (Mem.nextblock m2 + Pos.of_nat N)); try contradiction.
                  remember (CM_block_EFF_existsT nu23 nu12
                      (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
                      (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
                             m1' m2)
                      (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
                         INC12RU VB1' JJ12) WDnu12 b2).
                  destruct s. clear Heqs. apply a.
                reflexivity.
   (*discharge application condition AccessMapOK*)
     unfold AccessEffProperty, mkEFF.
     destruct (mkAccessMap_EFF_existsT nu23 nu12 j23'
         (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
         (Mem.nextblock m2 + Pos.of_nat N) VB2 VBj12'_2) as [AM [ADefault PAM]].
     simpl.
     destruct (ContentsMap_EFF_existsT nu23 nu12
         (removeUndefs (as_inj nu12) (as_inj nu') j12') m1 m1' m2
         (MINMAX_Offset nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12')
            m1' m2)
         (MINMAX nu12 (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' m2
            INC12RU VB1' JJ12) WDnu12
         (Mem.nextblock m2 + Pos.of_nat N)%positive)
       as [CM [CDefault PCM]].
     simpl.
     intros. rewrite PAM; clear PAM.
       unfold AccessMap_EFF_FUN.
       simpl in *.
       destruct (plt b2 (Mem.nextblock m2)).
         split; intros; try contradiction.
           remember (locBlocksSrc nu23 b2) as d.
           destruct d.
             remember (pubBlocksSrc nu23 b2) as q.
             destruct q; apply eq_sym in Heqq.
               destruct (pubSrc _ WDnu23 _ Heqq) as [b3 [d2 [Pub23 T3]]].
               apply (pub_in_all _ WDnu23) in Pub23.
               remember (source (local_of nu12) m1 b2 ofs2) as src.
               destruct src; trivial.
                 destruct p0.
                 destruct (pubBlocksSrc nu12 b); trivial.
               trivial.
           (*case locBlocksSrc nu23 b2 = false*)
              remember (source (as_inj nu12) m1 b2 ofs2) as src.
              destruct src.
                destruct p0; trivial.
                remember (as_inj nu23 b2) as q.
                destruct q; apply eq_sym in Heqq.
                  destruct p0. rewrite (inc23 _ _ _ Heqq). trivial.
              remember (j23' b2) as w.
                destruct w; trivial; apply eq_sym in Heqw.
                destruct p0.
                destruct (sep23 _ _ _ Heqq Heqw). contradiction.
         split; intros; try contradiction.
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') j12') m1' b2 ofs2) as d.
           destruct d; trivial. destruct p; trivial.
  exists nu12', nu23'.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
(*  split; trivial.*)
  split; intros.
    clear - H0 extInc12 Hnu12' Glue123.
    remember (as_inj nu12 b1) as d.
    destruct d; apply eq_sym in Heqd.
      destruct p. apply extern_incr_as_inj in extInc12.
      rewrite (extInc12 _ _ _ Heqd) in H0.
      left; trivial.
      apply  Glue123.
    clear Glue123; subst.
      destruct (joinD_None _ _ _ Heqd).
      destruct (joinD_Some _ _ _ _ _ H0)
            as [EXT | [EXT LOC]]; clear H0;
         rewrite convertL_extern in EXT.
       unfold join, removeUndefs in EXT.
          rewrite H, H1, Heqd in EXT.
          destruct (as_inj nu' b1); try discriminate.
          destruct p. right. exists b, z; trivial.
      rewrite convertL_local in LOC. congruence.
  split; intros.
    remember (as_inj nu23 b2) as d.
    destruct d; apply eq_sym in Heqd.
      destruct p. apply extern_incr_as_inj in extInc23.
      rewrite (extInc23 _ _ _ Heqd) in H0.
      left; trivial.
      apply  Glue123.
    clear Glue123; rewrite Hnu12', Hnu23', Hnu' in *.
      clear Hnu12' Hnu23' Hnu'; subst.
      destruct (joinD_None _ _ _ Heqd).
      destruct (joinD_Some _ _ _ _ _ H0)
            as [EXT | [EXT LOC]]; clear H0;
         rewrite convertR_extern in EXT.
       unfold join, removeUndefs in EXT.
          rewrite H2, H3 in EXT.
          destruct (mkInjections_4 _ _ _ _ _ _ _ _ _ _ HeqMKI
             _ _ _ EXT) as [AA | [AA | AA]].
            congruence.
            destruct AA; right. exists (Mem.nextblock m1), d2. assumption.
            destruct AA as [mm [? ?]]; right.
              exists (Mem.nextblock m1 + mm)%positive, d2. assumption.
      rewrite convertR_local in LOC. congruence.
  destruct GlueInvNu as [WD12 [WD23 _]].
  split; intros.
    rewrite Hnu12' in H0. clear - HeqMKI WD12 H0.
    destruct (joinD_Some _ _ _ _ _ H0) as [EXT12' | [EXT12' LOC12']];
       clear H0; rewrite convertL_extern in EXT12'.
      destruct (joinD_Some _ _ _ _ _ EXT12') as
          [EXT12 | [EXT12 LOC12]]; clear EXT12'.
        left; apply joinI; left; assumption.
      remember (local_of nu12 b1) as d.
       destruct d; apply eq_sym in Heqd. inv LOC12.
        unfold removeUndefs in LOC12.
        remember (as_inj nu12 b1) as q.
        destruct q; apply eq_sym in Heqq.
        destruct p. left; assumption.
        destruct (as_inj nu' b1); try congruence.
        destruct p.
        destruct (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI
           _ _ _ LOC12) as [AA | AA].
          congruence.
          right. apply AA.
    rewrite convertL_local in LOC12'.
      left; apply joinI; right.
      split; trivial.
      destruct (disjoint_extern_local _ WD12 b1); trivial. congruence.
  rewrite Hnu23' in H0.
    destruct (joinD_Some _ _ _ _ _ H0) as [EXT23' | [EXT23' LOC23']];
       clear H0; rewrite convertR_extern in EXT23'.
      destruct (joinD_Some _ _ _ _ _ EXT23') as
          [EXT23 | [EXT23 LOC23]]; clear EXT23'.
        left; apply joinI; left; assumption.
      remember (local_of nu23 b2) as d.
       destruct d; apply eq_sym in Heqd. inv LOC23.
       apply (mkInjections_4 _ _ _ _ _ _ _ _ _ _ HeqMKI _ _ _ LOC23).
    rewrite convertR_local in LOC23'.
      left; apply joinI; right.
      split; trivial.
      destruct (disjoint_extern_local _ WD23 b2); trivial. congruence.
Qed.

Lemma EFF_interp_II: forall m1 m2 nu12
                             (MInj12 : Mem.inject (as_inj nu12) m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') nu23 m3
                             (MInj23 : Mem.inject (as_inj nu23) m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                              nu' (WDnu' : SM_wd nu')
                             (SMvalNu' : sm_valid nu' m1' m3')
                             (MemInjNu' : Mem.inject (as_inj nu') m1' m3')

                             (ExtIncr: extern_incr (compose_sm nu12 nu23) nu')
                             (SMInjSep: sm_inject_separated (compose_sm nu12 nu23) nu' m1 m3)
                             (SMV12: sm_valid nu12 m1 m2)
                             (SMV23: sm_valid nu23 m2 m3)
                             (UnchPrivSrc: Mem.unchanged_on (fun b ofs => locBlocksSrc (compose_sm nu12 nu23) b = true /\
                                                      pubBlocksSrc (compose_sm nu12 nu23) b = false) m1 m1')
                             (UnchLOOR13: Mem.unchanged_on (local_out_of_reach (compose_sm nu12 nu23) m1) m3 m3')

                             (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                                         locBlocksTgt nu12 = locBlocksSrc nu23 /\
                                         extBlocksTgt nu12 = extBlocksSrc nu23 /\
                                         (forall b, pubBlocksTgt nu12 b = true ->
                                                    pubBlocksSrc nu23 b = true) /\
                                         (forall b, frgnBlocksTgt nu12 b = true ->
                                                    frgnBlocksSrc nu23 b = true))
                             (Norm12: forall b1 b2 d1, extern_of nu12 b1 = Some(b2,d1) ->
                                             exists b3 d2, extern_of nu23 b2 = Some(b3, d2)),
     exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\
                             Mem.inject (as_inj nu23') m2' m3' /\
                             sm_inject_separated nu12 nu12' m1 m2 /\
                             sm_inject_separated nu23 nu23' m2 m3 /\
                             sm_valid nu12' m1' m2' /\ sm_valid nu23' m2' m3' /\
                             (SM_wd nu12' /\ SM_wd nu23' /\
                              locBlocksTgt nu12' = locBlocksSrc nu23' /\
                              extBlocksTgt nu12' = extBlocksSrc nu23' /\
                              (forall b, pubBlocksTgt nu12' b = true ->
                                         pubBlocksSrc nu23' b = true) /\
                              (forall b, frgnBlocksTgt nu12' b = true ->
                                         frgnBlocksSrc nu23' b = true)) /\
                             (forall b1 b2 d1, extern_of nu12' b1 = Some(b2,d1) ->
                                     exists b3 d2, extern_of nu23' b2 = Some(b3, d2)) /\
                              Mem.unchanged_on (fun b ofs => locBlocksSrc nu23 b = true /\
                                                             pubBlocksSrc nu23 b = false) m2 m2' /\
                              Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2'
                          (* /\ Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3'*).
Proof. intros.
  destruct (EFF_interp_II_strong _ _ _ MInj12 _ Fwd1 _ _ MInj23 _
              Fwd3 _ WDnu' SMvalNu' MemInjNu' ExtIncr SMInjSep
              SMV12 SMV23 UnchPrivSrc UnchLOOR13 GlueInvNu Norm12)
  as [m2' [nu12' [nu23' [A [B [C [D [E [F [G [H [I [J [K [L [M [N P]]]]]]]]]]]]]]]]].
  exists m2', nu12', nu23'. intuition.
Qed.
