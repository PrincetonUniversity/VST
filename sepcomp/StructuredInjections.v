Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Axioms.

Require Import sepcomp.mem_lemmas.

Lemma compose_meminjI_Some: forall j k b1 b2 d1 b3 d2
          (J:j b1 = Some(b2,d1)) (K:k b2 = Some(b3,d2)),
          compose_meminj j k b1 = Some(b3, d1+d2).
Proof. intros. unfold compose_meminj.
  rewrite J, K. trivial.
Qed.

Lemma compose_meminjI_None: forall j k b1
          (H: (j b1 = None) \/ 
              (exists b2 d1, j b1 =Some(b2,d1) /\ k b2=None)),
          compose_meminj j k b1 = None.
Proof. intros. unfold compose_meminj.
  destruct H. rewrite H; trivial.
  destruct H as [b2 [d1 [J K]]]. rewrite J, K; trivial.
Qed.

Lemma inject_incr_coincide: forall f g (INC: inject_incr f g) b p
          (G:g b = Some p) q (F:f b = Some q),p=q.
Proof. intros. destruct p; destruct q.
  rewrite (INC _ _ _ F) in G. inv G. trivial.
Qed.

Lemma inject_incr_inv: forall f g (INC: inject_incr f g) b
                       (G: g b =None), f b = None.
Proof. intros.
  remember (f b) as d; destruct d; trivial; apply eq_sym in Heqd.
  destruct p. rewrite (INC _ _ _ Heqd) in G. inv G.
Qed.

Lemma forall2_val_inject_D: forall vals1 vals2 j (ValInjMu : Forall2 (val_inject j) vals1 vals2)
          v1 (IN: In v1 vals1), exists v2, val_inject j v1 v2 /\ In v2 vals2.
Proof. intros vals1.
  induction vals1; simpl; intros.
    contradiction.
  inv ValInjMu.
  destruct IN; subst.
    exists y; split. assumption. left. trivial.
  destruct (IHvals1 _ _ H3 _ H) as [v2 [INV INN]].
    exists v2; split. assumption. right. trivial.
Qed.

Definition join (j k:meminj):meminj := fun b =>
  match j b with
     Some (b1, delta) => Some (b1,delta)
   | None => k b
  end.

Definition disjoint (j k:meminj):Prop :=
    forall b, j b = None \/ k b = None.

Lemma join_assoc: forall f g h, join f (join g h) = join (join f g) h.
Proof. intros. unfold join.
  extensionality b.
  destruct (f b); trivial. destruct p. trivial.
Qed.  

Lemma join_com: forall f g, disjoint f g -> join f g = join g f.
Proof. intros. unfold join.
extensionality b.
destruct (H b); rewrite H0.
  destruct (g b); intuition. 
  destruct (f b); intuition.
Qed. 

Lemma disjoint_com: forall f g, disjoint f g = disjoint g f.
Proof. intros. unfold disjoint. apply prop_ext. 
 split; intros. destruct (H b); intuition. destruct (H b); intuition.
Qed.

Lemma disjoint_sub: forall j k (D: disjoint j k) j' k'
              (J: inject_incr j' j) (K:inject_incr k' k),
              disjoint j' k'.
Proof. intros.
  intros b.
  remember (j' b) as d.
  destruct d; try (left; reflexivity).
  apply eq_sym in Heqd; destruct p.
  remember (k' b) as q.
  destruct q; try (right; reflexivity).
  apply eq_sym in Heqq; destruct p.
  specialize (D b).
  rewrite (J _ _ _ Heqd) in D.
  rewrite (K _ _ _ Heqq) in D.
  destruct D; inv H.
Qed.

Lemma joinI: forall f g b p
             (Hp: f b = Some p \/ (f b = None /\ g b = Some p)),
      join f g b = Some p.
Proof. intros. unfold join.
  destruct Hp as [Hf | [Hf Hg]]; rewrite Hf; trivial.
    destruct p; trivial.
Qed.

Lemma joinD: forall j k (D: disjoint j k) b,
   match join j k b with
     Some(b1,delta) => (j b = Some(b1,delta) /\ k b = None) \/
                       (k b = Some(b1,delta) /\ j b = None)
   | None => j b = None /\ k b = None
  end.
Proof. intros.
  unfold join. destruct (D b); rewrite H.
     case_eq (k b); eauto.
     destruct p; eauto.
   case_eq (j b); eauto.
     destruct p; eauto. 
Qed.

Lemma joinD_Some:
      forall j k b b' delta (J: join j k b = Some(b',delta)),
      j b = Some(b',delta) \/ (j b = None /\ k b = Some(b',delta)).
Proof. intros. unfold join in J.
  remember (j b) as d.
  destruct d; apply eq_sym in Heqd.
    destruct p; left. assumption.
  right; split; auto. 
Qed.

Lemma joinD_None:
      forall j k b (J: join j k b = None),
      j b = None /\ k b = None.
Proof. intros. unfold join in J.
  remember (j b) as d.
  destruct d; apply eq_sym in Heqd; auto.
    destruct p. inv J. 
Qed.


Lemma joinI_None: forall j k b (J:j b = None) (K:k b = None),
                  join j k b = None.
Proof. intros.
  unfold join. rewrite J. assumption. 
Qed.

Lemma inject_incr_join: forall j j' k k'
  (J: inject_incr j j') (K: inject_incr k k')
  (D: disjoint j' k'),
  inject_incr (join j k) (join j' k').
Proof. intros.
  intros b; intros.
  unfold join in *.
  remember (j b) as d.
  destruct d; apply eq_sym in Heqd.
      destruct p. inv H.
      rewrite (J _ _ _ Heqd).
      trivial.
  destruct (D b).
    rewrite H0. apply K. apply H.
  rewrite (K _ _ _ H) in H0. inv H0.
Qed.

Lemma join_incr_left: forall j k, inject_incr j (join j k).
Proof. intros. intros b; intros.
  unfold join; rewrite H; trivial.
Qed.

Lemma join_incr_right: forall j k (D:disjoint j k), 
                       inject_incr k (join j k).
Proof. intros. intros b; intros.
  unfold join.
  destruct (D b) as [K | K]; rewrite K in *. trivial.
  inv H.
Qed.

Lemma disjointD_left: 
      forall j k b b' delta (J: j b = Some (b',delta)) 
             (D:disjoint j k), k b = None.
Proof. intros.
  destruct (D b) as [K | K]; rewrite K in *. inv J. trivial.
Qed. 

Lemma disjointD_right:
      forall j k b b' delta (K: k b = Some (b',delta))
             (D:disjoint j k), j b = None.
Proof. intros.
  destruct (D b) as [J | J]; rewrite J in *. trivial. inv K.
Qed.

Lemma join_left_agree: 
      forall j k b b1 d1 (JK: join j k b = Some(b1,d1))
             b2 d2 (J: j b = Some(b2,d2)), 
      b1=b2 /\ d1=d2.
Proof. intros. rewrite (join_incr_left _ _ _ _ _ J) in JK.
  inv JK; split; trivial.
Qed.

Lemma join_right_agree:
      forall j k b b1 d1 (JK: join j k b = Some(b1,d1))
             b2 d2 (K: k b = Some(b2,d2)) (D:disjoint j k),
      b1=b2 /\ d1=d2.
Proof. intros. rewrite (join_incr_right _ _ D _ _ _ K) in JK.
  inv JK; split; trivial.
Qed.

Lemma join_disjoint: forall f g h (FH: disjoint f h) (GH: disjoint g h),
                     disjoint (join f g) h.
Proof. intros. intros b.
destruct (FH b); try (right; assumption).
destruct (GH b); try (right; assumption).
left. apply joinI_None; assumption.
Qed.

(*
Record shareable_injection := {
   si_blocksL: block -> Prop;
   si_blocksR: block -> Prop;
   si_f: meminj;
   si_sharedL: block -> Prop; (*subset of DOM f, hence of blocksL*)
   si_sharedR: block -> Prop; (*subset of RNG f, hence of blocksR*)

   si_sharedL_f: forall b1, si_sharedL b1 -> exists b2 delta,
                         si_f b1 = Some(b2,delta) /\ si_sharedR b2;

   si_sharedR_f: forall b2, si_sharedR b2 -> exists b1 delta, 
                         si_f b1 = Some(b2,delta); (*b1 not necessarily in sharedL!*)

   si_dom_rng: forall b1 b2 delta, si_f b1 = Some(b2, delta) ->
                         si_blocksL b1 /\ si_blocksR b2
}.

Record sh_inj j m1 m2 := {
   shi_inj: Mem.inject (si_f j) m1 m2;
   shi_L: forall b, Mem.valid_block m1 b <-> si_blocksL j b;
   shi_R: forall b, Mem.valid_block m2 b <-> si_blocksR j b
}.      

Definition distinct (A B: block -> Prop) :=
  forall b, A b -> B b -> False.

Lemma distinct': forall A B (D: distinct A B) b, B b -> A b -> False.
Proof. intros. eapply D; eauto. Qed.

Record structured_Injection := {
   st_intern: shareable_injection; (*knowlegde about locally allocated blocks*)
   st_extern: shareable_injection; (*knowlegde about foreign blocks*)
   st_distL: distinct (si_blocksL st_intern) (si_blocksL st_extern); 
   st_distR: distinct (si_blocksR st_intern) (si_blocksR st_extern)
}.

Definition st_blocksL (j:structured_Injection) (b:block):Prop := 
   si_blocksL (st_intern j) b \/ si_blocksL (st_extern j) b.
Definition st_blocksR (j:structured_Injection) (b:block):Prop := 
   si_blocksR (st_intern j) b \/ si_blocksR (st_extern j) b.

Record st_inj j m1 m2 := {
   sti_inj: Mem.inject (join (si_f (st_intern j)) (si_f (st_extern j))) m1 m2;
   sti_L: forall b, Mem.valid_block m1 b <-> st_blocksL j b;
   sti_R: forall b, Mem.valid_block m2 b <-> st_blocksR j b
}.      

*)


Record SM_Injection :=
  { locBlocksSrc : block -> bool;
                     (* The blocks allocated by THIS module in the
                        source language SRC*)
    locBlocksTgt : block -> bool; 
                     (* The blocks allocated by THIS module in the
                        target language TGT*) 
    pubBlocksSrc : block -> bool; (*subset of locBlocksSrc that have been 
                        made public. Must be mapped by pubInj.*)
    pubBlocksTgt : block -> bool; (*subset of locBlocksTgt that have been 
                        made public. Contains the image of pubInj.*)
    local_of: meminj; (* meminj on blocks allocated by THIS module.
                        Remains unchanged by external steps,
                        and is partitioned by pubBlocksSrc/Tgt into
                        exported (public)
                        and non-exporrted (private) component.  *)

    extBlocksSrc: block -> bool; (*blocks allocated by OTHER modules in SRC *)
    extBlocksTgt: block -> bool; (*blocks allocated by OTHER modules in TGT *)

    frgnBlocksSrc : block -> bool; (*subset of extBlocksSrc that have been 
                        made visible to THIS module. Must be apped by foreign.*)
    frgnBlocksTgt : block -> bool; (*subset of extBlocksTgt that have been 
                        made visible to THIS module. Contains image of foreign*)
   
    extern_of: meminj (* a meminj on blocks allocated by OTHER modules; 
                        the injection is not modified by coresteps, and
                        is partitioned by frgnBlocksSrc/Tgt into 
                        foreign (leaked to this module) and unknown (non-leaked)
                        components, where the former blocks are 
                        accessible by THIS module. 
                        THIS module behaves uniformly over block mentioned by frgnInj, and
                        assumes that blocks in frgnInj remain mapped. Compilation of THIS 
                        module neither merges nor unmaps blocks from here, 
                        nor does it spill into them*)
}.

(*The four projections*)
Definition unknown_of (mu: SM_Injection) : meminj :=
  match mu with 
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern => 
    fun b => if locBSrc b then None else if fSrc b then None else extern b 
  end.

Definition foreign_of (mu: SM_Injection) : meminj :=
  match mu with 
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern => 
    fun b => if fSrc b then extern b else None
  end.

Definition pub_of (mu: SM_Injection) : meminj :=
  match mu with 
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern => 
    fun b => if pSrc b then local b else None
  end.

Definition priv_of (mu: SM_Injection) : meminj :=
  match mu with 
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern => 
    fun b => if pSrc b then None else local b
  end.

Lemma local_pubpriv: forall mu, 
      local_of mu = join (pub_of mu) (priv_of mu).
Proof. intros. unfold pub_of, priv_of.
unfold join; extensionality b.
destruct mu; simpl.
remember (pubBlocksSrc0 b) as d.
destruct d; trivial.
destruct (local_of0 b); trivial.
destruct p; trivial.
Qed.

Definition shared_of (mu: SM_Injection) : meminj :=
  join (foreign_of mu) (pub_of mu).

Lemma unknown_in_extern: forall mu,
      inject_incr (unknown_of mu) (extern_of mu).
Proof. intros. 
    destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl.
    intros b; intros. 
    destruct (locBSrc b). inv H. 
    destruct (fSrc b). inv H. trivial. 
Qed. 

Lemma foreign_in_extern: forall mu,
      inject_incr (foreign_of mu) (extern_of mu).
Proof. intros. 
    destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl.
    intros b; intros. 
    destruct (fSrc b). trivial. inv H.
Qed.

Lemma foreign_in_shared: forall mu,
      inject_incr (foreign_of mu) (shared_of mu).
Proof. intros. apply join_incr_left. Qed.

Lemma pub_in_local: forall mu,
      inject_incr (pub_of mu) (local_of mu).
Proof. intros. 
    destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl.
    intros b; intros. 
    destruct (pSrc b). trivial. inv H. 
Qed.

Lemma priv_in_local: forall mu,
      inject_incr (priv_of mu) (local_of mu).
Proof. intros. 
    destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl.
    intros b; intros. 
    destruct (pSrc b). inv H. trivial.
Qed.

Lemma disjoint_pub_priv: forall mu, disjoint (pub_of mu) (priv_of mu).
Proof. intros.
    destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl.
    intros b; simpl. 
    destruct (pSrc b). right; trivial. left; trivial.
Qed. 

Lemma disjoint_frgn_unknown: forall mu, disjoint (foreign_of mu) (unknown_of mu).
Proof. intros.
    destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl.
    intros b; simpl. 
    destruct (fSrc b).
      right. destruct (locBSrc b); trivial.
    left; trivial.
Qed. 

Record SM_wd (mu:SM_Injection):Prop := {
  disjoint_extern_local_Src: forall b, locBlocksSrc mu b = false \/ extBlocksSrc mu b = false;
  disjoint_extern_local_Tgt: forall b, locBlocksTgt mu b = false \/ extBlocksTgt mu b = false;

  local_DomRng: forall b1 b2 z, local_of mu b1 = Some(b2,z) -> 
               (locBlocksSrc mu b1 = true /\ locBlocksTgt mu b2 = true);
  extern_DomRng: forall b1 b2 z, extern_of mu b1 = Some(b2,z) -> 
               (extBlocksSrc mu b1 = true /\ extBlocksTgt mu b2 = true);

  pubSrc: forall b1, pubBlocksSrc mu b1 = true -> 
              exists b2 z, pub_of mu b1 = Some(b2,z) /\
                           pubBlocksTgt mu b2 = true;
  frgnSrc: forall b1, frgnBlocksSrc mu b1 = true -> 
              exists b2 z, foreign_of mu b1 = Some(b2,z) /\
                           frgnBlocksTgt mu b2 = true;

  pubBlocksLocalTgt: forall b, pubBlocksTgt mu b = true -> 
                               locBlocksTgt mu b = true;
  frgnBlocksExternTgt: forall b, frgnBlocksTgt mu b = true -> 
                              extBlocksTgt mu b = true
}.

Lemma extBlocksSrc_locBlocksSrc: forall mu (WD: SM_wd mu) b, 
      extBlocksSrc mu b = true -> locBlocksSrc mu b = false.
Proof. intros.
  destruct (disjoint_extern_local_Src _ WD b); congruence. 
Qed.

Lemma extBlocksSrc_locBlocksTgt: forall mu (WD: SM_wd mu) b, 
      extBlocksTgt mu b = true -> locBlocksTgt mu b = false.
Proof. intros.
  destruct (disjoint_extern_local_Tgt _ WD b); congruence. 
Qed.

Lemma locBlocksSrc_extBlocksSrc: forall mu (WD: SM_wd mu) b, 
      locBlocksSrc mu b = true -> extBlocksSrc mu b = false.
Proof. intros.
  destruct (disjoint_extern_local_Src _ WD b); congruence. 
Qed.

Lemma locBlocksSrc_extBlocksTgt: forall mu (WD: SM_wd mu) b, 
      locBlocksTgt mu b = true -> extBlocksTgt mu b = false.
Proof. intros.
  destruct (disjoint_extern_local_Tgt _ WD b); congruence. 
Qed.

Lemma pubBlocksLocalSrc: forall mu (WD: SM_wd mu) b, 
      pubBlocksSrc mu b = true -> locBlocksSrc mu b = true.
Proof. intros.
  destruct (pubSrc _ WD _ H) as [b2 [d1 [P T]]].
  apply pub_in_local in P.
  apply (local_DomRng _ WD _ _ _ P).
Qed.

Lemma frgnBlocksSrc_extBlocksSrc: forall mu (WD: SM_wd mu) b, 
      frgnBlocksSrc mu b = true -> extBlocksSrc mu b = true.
Proof. intros.
  destruct (frgnSrc _ WD _ H) as [b2 [d1 [F T]]].
  apply foreign_in_extern in F.
  apply (extern_DomRng _ WD _ _ _ F).
Qed.

Lemma locBlocksSrc_externNone: forall mu (WD:SM_wd mu) b
      (MB: locBlocksSrc mu b = true), extern_of mu b = None.
Proof. intros.
  remember (extern_of mu b) as d; destruct d; apply eq_sym in Heqd; trivial.
  destruct p. destruct (extern_DomRng _ WD _ _ _ Heqd) as [A B].
  destruct (disjoint_extern_local_Src _ WD b); congruence.
Qed.

Lemma locBlocksSrc_foreignNone: forall mu (WD:SM_wd mu) b
      (MB: locBlocksSrc mu b = true), foreign_of mu b = None.
Proof. intros.
       apply (locBlocksSrc_externNone _ WD) in MB.
       eapply inject_incr_inv; try eassumption.
       apply foreign_in_extern.
Qed.

Lemma frgnBlocksSrc_locBlocksSrc: forall mu (WD:SM_wd mu) b
      (FB: frgnBlocksSrc mu b = true), locBlocksSrc mu b = false.
Proof. intros. apply (frgnBlocksSrc_extBlocksSrc _ WD) in FB.
       destruct (disjoint_extern_local_Src _ WD b); congruence. 
Qed.

Lemma locBlocksSrc_frgnBlocksSrc: forall mu (WD:SM_wd mu) b
      (MB: locBlocksSrc mu b = true), frgnBlocksSrc mu b = false.
Proof. intros.
       remember (frgnBlocksSrc mu b) as d; destruct d; trivial.
       apply eq_sym in Heqd.
       destruct (frgnBlocksSrc_locBlocksSrc _ WD _ Heqd); intuition. 
Qed.

Lemma locBlocksTgt_frgnBlocksTgt: forall mu (WD:SM_wd mu) b
      (MB: locBlocksTgt mu b = true), frgnBlocksTgt mu b = false.
Proof. intros.
       remember (frgnBlocksTgt mu b) as d; destruct d; trivial.
       apply eq_sym in Heqd.
       apply (frgnBlocksExternTgt _ WD) in Heqd.
       destruct (disjoint_extern_local_Tgt _ WD b); congruence.
Qed.

Lemma frgnBlocksTgt_locBlocksTgt: forall mu (WD:SM_wd mu) b
      (FB: frgnBlocksTgt mu b = true), locBlocksTgt mu b = false.
Proof. intros.
       remember (locBlocksTgt mu b) as d; destruct d; trivial.
       apply eq_sym in Heqd.
       rewrite (locBlocksTgt_frgnBlocksTgt _ WD _ Heqd) in FB. inv FB.
Qed.

Lemma locBlocksTgt_frgnBlocksTgt_D: forall mu (WD:SM_wd mu) b
            (MB: locBlocksTgt mu b = true) (FB: frgnBlocksTgt mu b = true),
      False.
Proof. intros. 
       rewrite (locBlocksTgt_frgnBlocksTgt _ WD _ MB) in FB. inv FB.
Qed.

Lemma locBlocksSrc_unknownNone: forall mu (WD:SM_wd mu) b
      (MB: locBlocksSrc mu b = true), unknown_of mu b = None.
Proof. intros.
       apply (locBlocksSrc_externNone _ WD) in MB.
       eapply inject_incr_inv; try eassumption.
       apply unknown_in_extern.
Qed.

Lemma extern_foreignunknown: forall mu (WD: SM_wd mu), 
      extern_of mu = join (foreign_of mu) (unknown_of mu).
Proof. intros. unfold foreign_of, unknown_of.
unfold join; extensionality b.
specialize (frgnBlocksSrc_locBlocksSrc _ WD b); intros.
specialize (locBlocksSrc_externNone _ WD b); intros.
destruct mu; simpl in *.
remember (frgnBlocksSrc0 b) as d.
destruct d; apply eq_sym in Heqd.
  rewrite H; trivial. 
  destruct (extern_of0 b); trivial.
  destruct p; trivial.
remember (locBlocksSrc0 b) as q.
destruct q; trivial.
apply H0; trivial.
Qed.

Lemma pubChar: forall mu (WD: SM_wd mu) b1 b2 z, pub_of mu b1 = Some(b2,z) ->
               pubBlocksSrc mu b1 = true /\ pubBlocksTgt mu b2 = true.
Proof. intros.
  unfold pub_of in H.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl.
  case_eq (pSrc b1); intros P; rewrite P in *; try discriminate.
    destruct (pubSrc _ WD _ P) as [bb2 [d [X1 X2]]]; simpl in *.
    rewrite P in X1. rewrite X1 in H. inv H. split; trivial.
Qed.

Lemma privChar: forall mu b1 b2 z, priv_of mu b1 = Some(b2,z) ->
                pubBlocksSrc mu b1 = false.
Proof. intros.
  unfold priv_of in H.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl.
  destruct (pSrc b1); trivial. inv H.
Qed.

Lemma pubSrcContra: forall mu b1, 
         pubBlocksSrc mu b1 = false -> pub_of mu b1 = None.
Proof. intros.
  unfold pub_of.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  rewrite H. trivial. 
Qed.

Lemma pubTgtContra: forall mu (WD: SM_wd mu) b2, pubBlocksTgt mu b2 = false -> 
            ~ exists b1 d, pub_of mu b1 = Some(b2,d).
Proof. intros. intros N.
  destruct N as [b1 [d PUB]].
  destruct (pubChar _ WD _ _ _ PUB). rewrite H1 in H. discriminate. 
Qed.

Lemma disjoint_extern_local: forall mu (WD: SM_wd mu),
     disjoint (extern_of mu) (local_of mu).
Proof. intros.
  intros b; intros.
  remember (local_of mu b) as q.
  destruct q; try (right; reflexivity). 
  apply eq_sym in Heqq; destruct p.
  destruct (local_DomRng _ WD _ _ _ Heqq).
  left; apply (locBlocksSrc_externNone _ WD _ H).
Qed.

Lemma disjoint_foreign_pub: forall mu (WD: SM_wd mu),
      disjoint (foreign_of mu) (pub_of mu).
Proof. intros. eapply disjoint_sub.
  eapply disjoint_extern_local; eassumption.
  apply foreign_in_extern.
  apply pub_in_local.
Qed.

Lemma pub_in_shared: forall mu (WD: SM_wd mu),
      inject_incr (pub_of mu) (shared_of mu).
Proof. intros. unfold shared_of. 
    apply join_incr_right. 
    apply disjoint_foreign_pub. assumption. 
Qed.

(*DOM/RNG: all blocks mentioned by a SM_Injection. Used for
  stating match_validblocks etc*)
Definition DomSrc (mu: SM_Injection) (b1: block): bool := 
     locBlocksSrc mu b1 || extBlocksSrc mu b1.
Definition DOM (mu: SM_Injection) (b1: block): Prop := DomSrc mu b1 = true.
  
Definition DomTgt (mu: SM_Injection) (b2: block): bool := 
     locBlocksTgt mu b2 || extBlocksTgt mu b2.
Definition RNG (mu: SM_Injection) (b2:block): Prop := DomTgt mu b2 = true.

(*in contrast to effect_simulations2.v, we enforce
  pub_of mu = pub_of mu', via
  pubBlocksSrc/Tgt mu = pubBlocksSrc/Tgt mu': 
  it suffices to reclassify at atExternal.
  This simplifies/enables the proof of 
  effect_corediagram_trans.diagram_injinj etc*)
Definition intern_incr (mu mu': SM_Injection): Prop := 
   inject_incr (local_of mu) (local_of mu') /\
   (extern_of mu = extern_of mu') /\
   (forall b, locBlocksSrc mu b = true -> locBlocksSrc mu' b = true) /\
   (forall b, locBlocksTgt mu b = true -> locBlocksTgt mu' b = true) /\
   (pubBlocksSrc mu = pubBlocksSrc mu') /\
   (pubBlocksTgt mu = pubBlocksTgt mu') /\
   (frgnBlocksSrc mu = frgnBlocksSrc mu') /\
   (frgnBlocksTgt mu = frgnBlocksTgt mu') /\
   (extBlocksSrc mu = extBlocksSrc mu') /\
   (extBlocksTgt mu = extBlocksTgt mu').

Lemma intern_incr_DomSrc: 
      forall mu mu' (Inc: intern_incr mu mu') b,
      DomSrc mu b = true -> DomSrc mu' b = true.
Proof. unfold DomSrc. intros.
  destruct Inc as [_ [_ [? [_ [_ [_ [_ [_ [? _]]]]]]]]].
  apply orb_true_iff in H.
  destruct H. intuition. rewrite H1 in H. intuition.
Qed.
Lemma intern_incr_DOM: 
      forall mu mu' (Inc: intern_incr mu mu') b,
      DOM mu b -> DOM mu' b.
Proof. intros. apply (intern_incr_DomSrc _ _ Inc _ H). Qed.

Lemma intern_incr_DomTgt: 
      forall mu mu' (Inc: intern_incr mu mu') b,
      DomTgt mu b = true -> DomTgt mu' b = true.
Proof. unfold DomTgt. intros.
  destruct Inc as [_ [_ [_ [? [_ [_ [_ [_ [_ ?]]]]]]]]].
  apply orb_true_iff in H.
  destruct H. intuition. rewrite H1 in H. intuition.
Qed.

Lemma intern_incr_RNG: 
      forall mu mu' (Inc: intern_incr mu mu') b,
      RNG mu b -> RNG mu' b.
Proof. intros. apply (intern_incr_DomTgt _ _ Inc _ H). Qed.

Lemma intern_incr_DomSrc_inv: forall mu mu' (INC: intern_incr mu mu') b, 
      DomSrc mu' b = false -> DomSrc mu b = false.
Proof. intros.
  remember (DomSrc mu b) as d; destruct d; trivial; apply eq_sym in Heqd.
  apply (intern_incr_DomSrc _ _ INC) in Heqd. congruence.  
Qed.
  
Lemma intern_incr_DomTgt_inv: forall mu mu' (INC: intern_incr mu mu') b, 
      DomTgt mu' b = false -> DomTgt mu b = false.
Proof. intros.
  remember (DomTgt mu b) as d; destruct d; trivial; apply eq_sym in Heqd.
  apply (intern_incr_DomTgt _ _ INC) in Heqd. congruence.
Qed.

Lemma intern_incr_locBlocksSrc_inv: forall mu mu' (INC: intern_incr mu mu') b, 
      locBlocksSrc mu' b = false -> locBlocksSrc mu b = false.
Proof. intros.
  remember (locBlocksSrc mu b) as d; destruct d; trivial; apply eq_sym in Heqd.
  apply INC in Heqd. rewrite Heqd in H; trivial.
Qed.

Lemma intern_incr_locBlocksTgt_inv: forall mu mu' (INC: intern_incr mu mu') b, 
      locBlocksTgt mu' b = false -> locBlocksTgt mu b = false.
Proof. intros.
  remember (locBlocksTgt mu b) as d; destruct d; trivial; apply eq_sym in Heqd.
  apply INC in Heqd. rewrite Heqd in H; trivial.
Qed.

Lemma intern_incr_priv: forall mu mu' (INC: intern_incr mu mu'),
      inject_incr (priv_of mu) (priv_of mu').
Proof. intros.
  unfold priv_of.
  assert (INCL: inject_incr (local_of mu) (local_of mu')) by apply INC.
  assert (pubBlocksSrc mu = pubBlocksSrc mu') by apply INC. clear INC.
  intros b; intros.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  subst. 
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  destruct (pSrc' b); trivial.
  apply INCL. assumption. 
Qed.

Lemma intern_incr_pub: forall mu mu' (INC: intern_incr mu mu')
       (WD: SM_wd mu), pub_of mu = pub_of mu'. 
Proof. intros.
  unfold pub_of.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  extensionality b.
  destruct INC as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  simpl in *. subst.
  remember (pSrc' b) as d; destruct d; trivial. apply eq_sym in Heqd.
  specialize (pubSrc _ WD). simpl; intros.
  destruct (H0 _ Heqd) as [b2 [z [A B]]].
  rewrite Heqd in A. rewrite A. rewrite (H _ _ _ A). trivial.
Qed.

Lemma intern_incr_foreign: forall mu mu' (INC: intern_incr mu mu'),
      foreign_of mu = foreign_of mu'. 
Proof. intros.
  unfold foreign_of.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  extensionality b.
  destruct INC as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  simpl in *. subst. trivial.
Qed.

Lemma intern_incr_unknown: forall mu mu' (INC: intern_incr mu mu')
       (WD': SM_wd mu'), unknown_of mu = unknown_of mu'. 
Proof. intros.
  unfold foreign_of.
  specialize (locBlocksSrc_externNone _ WD'); intros.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  extensionality b.
  destruct INC as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  simpl in *. subst.
  remember (fSrc' b) as q; destruct q; apply eq_sym in Heqq.
    remember (locBSrc b) as d; destruct d; apply eq_sym in Heqd. 
      apply H2 in Heqd. rewrite Heqd. trivial.
      destruct (locBSrc' b); trivial.
    remember (locBSrc b) as d; destruct d; apply eq_sym in Heqd. 
      apply H2 in Heqd. rewrite Heqd. trivial.
      remember (locBSrc' b) as p; destruct p; apply eq_sym in Heqp; trivial.
  apply H. apply Heqp.
Qed.

Definition extern_incr (mu mu': SM_Injection): Prop := 
   inject_incr (extern_of mu) (extern_of mu') /\
   (local_of mu = local_of mu') /\
   (forall b, extBlocksSrc mu b = true -> extBlocksSrc mu' b = true) /\
   (forall b, extBlocksTgt mu b = true -> extBlocksTgt mu' b = true) /\
   (locBlocksSrc mu = locBlocksSrc mu') /\
   (locBlocksTgt mu = locBlocksTgt mu') /\
   (pubBlocksSrc mu = pubBlocksSrc mu') /\
   (pubBlocksTgt mu = pubBlocksTgt mu') /\
   (forall b, frgnBlocksSrc mu b = true -> frgnBlocksSrc mu' b = true) /\
   (forall b, frgnBlocksTgt mu b = true -> frgnBlocksTgt mu' b = true).

Lemma extern_incr_DomSrc: 
      forall mu mu' (Inc: extern_incr mu mu') b,
      DomSrc mu b = true -> DomSrc mu' b = true.
Proof. unfold DomSrc. intros.
  destruct Inc as [_ [_ [? [_ [? _]]]]].
  apply orb_true_iff in H.
  destruct H. rewrite H1 in H. intuition. intuition.
Qed.
Lemma extern_incr_DOM: 
      forall mu mu' (Inc: extern_incr mu mu') b,
      DOM mu b -> DOM mu' b.
Proof. intros. apply (extern_incr_DomSrc _ _ Inc _ H). Qed.

Lemma extern_incr_DomTgt: 
      forall mu mu' (Inc: extern_incr mu mu') b,
      DomTgt mu b = true -> DomTgt mu' b = true.
Proof. unfold DomTgt. intros.
  destruct Inc as [_ [_ [_ [? [_ [? _]]]]]].
  apply orb_true_iff in H.
  destruct H. rewrite H1 in H. intuition. intuition. 
Qed.

Lemma extern_incr_RNG: 
      forall mu mu' (Inc: extern_incr mu mu') b,
      RNG mu b -> RNG mu' b.
Proof. intros. apply (extern_incr_DomTgt _ _ Inc _ H). Qed.


(* although coherence with intern_incr would suggest to prove
   inject_incr (unknown_of mu) (unknown_of mu') instead of
   inject_incr (unknown_of mu) (extern_of mu'), we prove the
   latter, since additional intermediate external calls 
   may trigger reclassification of unknown entries as 
   foreign in third-part cores*)
Lemma extern_incr_unknown: forall mu mu' (INC: extern_incr mu mu'),
   inject_incr (unknown_of mu) (extern_of mu').
Proof. intros.
  unfold unknown_of.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  intros b; intros. 
  destruct INC as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  simpl in *. subst.
  remember (locBSrc' b) as d; destruct d; trivial. inv H. apply eq_sym in Heqd.
  remember (fSrc b) as q; destruct q; trivial. inv H.
  apply (H0 _ _ _ H).
Qed.

Lemma extern_incr_foreign: forall mu mu' (INC: extern_incr mu mu'),
   inject_incr (foreign_of mu) (foreign_of mu').
Proof. intros.
  unfold foreign_of.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  intros b; intros. 
  destruct INC as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  simpl in *. subst.
  remember (fSrc b) as q; destruct q; apply eq_sym in Heqq.
    rewrite (H8 _ Heqq).
    apply (H0 _ _ _ H).
  inv H.
Qed.

Lemma extern_incr_pub: forall mu mu' (INC: extern_incr mu mu'),
   pub_of mu = pub_of mu'.
Proof. intros.
  unfold pub_of.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  destruct INC as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  simpl in *. subst. trivial.
Qed.

Lemma extern_incr_priv: forall mu mu' (INC: extern_incr mu mu'),
   priv_of mu = priv_of mu'.
Proof. intros.
  unfold priv_of.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  destruct INC as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  simpl in *. subst. trivial.
Qed.

(*The join of all four components - useful for stating
  match_state conditions*)
Definition as_inj (mu: SM_Injection) : meminj :=
  join (extern_of mu) (local_of mu).

Lemma local_in_all: forall j (PR:SM_wd j), inject_incr (local_of j) (as_inj j).
Proof. intros. apply join_incr_right. eapply (disjoint_extern_local _ PR). Qed.

Lemma pub_in_all: forall j (PR:SM_wd j), inject_incr (pub_of j) (as_inj j).
Proof. intros.
  eapply inject_incr_trans.
  apply pub_in_local. apply (local_in_all _ PR).
Qed.

Lemma priv_in_all: forall j (PR:SM_wd j), inject_incr (priv_of j) (as_inj j).
Proof. intros.
  eapply inject_incr_trans.
  apply priv_in_local. apply (local_in_all _ PR).
Qed.

Lemma extern_in_all: forall mu, inject_incr (extern_of mu) (as_inj mu).
Proof. intros. apply join_incr_left. Qed. 

Lemma foreign_in_all: forall mu, inject_incr (foreign_of mu) (as_inj mu).
Proof. intros.
  eapply inject_incr_trans.
  apply foreign_in_extern. apply extern_in_all. 
Qed. 

Lemma unknown_in_all: forall mu, inject_incr (unknown_of mu) (as_inj mu).
Proof. intros.
  eapply inject_incr_trans.
  apply unknown_in_extern. apply extern_in_all. 
Qed. 

Lemma shared_in_all: forall j (PR:SM_wd j), inject_incr (shared_of j) (as_inj j).
Proof. intros. intros b; intros.
  unfold shared_of in H.
  destruct (joinD_Some _ _ _ _ _ H); clear H.
    eapply foreign_in_all; eassumption.
  destruct H0.
    eapply pub_in_all; eassumption.
Qed.

Lemma as_injD_None: forall mu b1, as_inj mu b1 = None ->
   extern_of mu b1 = None /\ 
   local_of mu b1 = None.
Proof. intros. apply joinD_None in H. assumption. Qed.

Lemma local_ofD_None: forall mu b1, local_of mu b1 = None ->
   pub_of mu b1 = None /\ 
   priv_of mu b1 = None.
Proof. intros. 
split; eapply inject_incr_inv; try eassumption.
  apply pub_in_local.
  apply priv_in_local.
Qed.
 
Lemma extern_ofD_None: forall mu b1, extern_of mu b1 = None ->
   foreign_of mu b1 = None /\ 
   unknown_of mu b1 = None.
Proof. intros.
split; eapply inject_incr_inv; try eassumption.
  apply foreign_in_extern.
  apply unknown_in_extern.
Qed.

Lemma disjoint_foreign_priv: forall mu (WD: SM_wd mu),
      disjoint (foreign_of mu) (priv_of mu).
Proof. intros. eapply disjoint_sub.
  eapply disjoint_extern_local; eassumption.
  apply foreign_in_extern.
  eapply priv_in_local.
Qed.

Lemma disjoint_foreign_local: forall mu (WD: SM_wd mu),
      disjoint (foreign_of mu) (local_of mu).
Proof. intros. eapply disjoint_sub.
  eapply disjoint_extern_local; eassumption.
  apply foreign_in_extern.
  apply inject_incr_refl.
Qed.

Lemma disjoint_unknown_local: forall mu (WD: SM_wd mu),
      disjoint (unknown_of mu) (local_of mu).
Proof. intros. eapply disjoint_sub.
  eapply disjoint_extern_local; eassumption.
  apply unknown_in_extern; assumption.
  apply inject_incr_refl.
Qed.

Lemma disjoint_unknown_pub: forall mu (WD: SM_wd mu),
      disjoint (unknown_of mu) (pub_of mu).
Proof. intros. eapply disjoint_sub.
  eapply disjoint_unknown_local; eassumption.
  apply inject_incr_refl.
  apply pub_in_local.
Qed.

Lemma disjoint_unknown_priv: forall mu (WD: SM_wd mu),
      disjoint (unknown_of mu) (priv_of mu).
Proof. intros. eapply disjoint_sub.
  eapply disjoint_unknown_local; eassumption.
  apply inject_incr_refl.
  apply priv_in_local; assumption.
Qed.

Lemma disjoint_shared_priv: forall mu (WD: SM_wd mu),
      disjoint (shared_of mu) (priv_of mu).
Proof. intros. unfold shared_of.
  apply join_disjoint.
   apply disjoint_foreign_priv; trivial.
  apply disjoint_pub_priv.
Qed.
 
Lemma disjoint_shared_unknown: forall mu (WD: SM_wd mu),
      disjoint (shared_of mu) (unknown_of mu).
Proof. intros. unfold shared_of.
  apply join_disjoint.
   apply disjoint_frgn_unknown; trivial.
  rewrite disjoint_com. apply disjoint_unknown_pub; trivial.
Qed.
 
Lemma as_inj_DomRng: forall mu b1 b2 d, as_inj mu b1 = Some(b2, d) -> SM_wd mu ->
                DomSrc mu b1 = true /\ DomTgt mu b2 = true.
Proof. intros. 
  unfold DomSrc, DomTgt.
  apply joinD_Some in H.
  destruct H as [ExtSome | [ExtNone LocalSome]].
    apply extern_DomRng in ExtSome; intuition.
    apply local_DomRng in LocalSome; intuition. 
Qed.

Lemma local_locBlocks: forall mu (WD:SM_wd mu)
                  b1 b2 z (L: local_of mu b1 = Some(b2,z)), 
      locBlocksSrc mu b1  = true /\ locBlocksTgt mu b2  = true /\
      extBlocksSrc mu b1 = false /\ extBlocksTgt mu b2 = false /\
      frgnBlocksSrc mu b1 = false /\ frgnBlocksTgt mu b2 = false /\
      DomSrc mu b1 = true /\ DomTgt mu b2 = true.
Proof. intros.
  assert (locBlocksSrc mu b1  = true /\ locBlocksTgt mu b2  = true).
    split; eapply WD; apply L.
  destruct H.
  split; trivial.
  split; trivial.
  split. destruct (disjoint_extern_local_Src _ WD b1); congruence.
  split. destruct (disjoint_extern_local_Tgt _ WD b2); congruence.
  split. apply locBlocksSrc_frgnBlocksSrc; eassumption.
  split. apply locBlocksTgt_frgnBlocksTgt; eassumption.
  unfold DomSrc, DomTgt; intuition. 
Qed.

Lemma pub_locBlocks: forall mu (WD:SM_wd mu)
                  b1 b2 z (L: pub_of mu b1 = Some(b2,z)), 
      pubBlocksSrc mu b1 = true /\ pubBlocksTgt mu b2 = true /\
      locBlocksSrc mu b1 = true /\ locBlocksTgt mu b2 = true /\
      extBlocksSrc mu b1 = false /\ extBlocksTgt mu b2 = false /\
      frgnBlocksSrc mu b1 = false /\ frgnBlocksTgt mu b2 = false /\
      DomSrc mu b1 = true /\ DomTgt mu b2 = true.
Proof. intros.
  split. eapply pubChar; eassumption.
  split. eapply pubChar; eassumption.
  eapply local_locBlocks; trivial. 
  eapply pub_in_local; eassumption.
Qed.

Lemma priv_locBlocks: forall mu (WD:SM_wd mu)
                  b1 b2 z (L: priv_of mu b1 = Some(b2,z)), 
      pubBlocksSrc mu b1 = false /\ 
      locBlocksSrc mu b1 = true /\ locBlocksTgt mu b2 = true /\
      extBlocksSrc mu b1 = false /\ extBlocksTgt mu b2 = false /\
      frgnBlocksSrc mu b1 = false /\ frgnBlocksTgt mu b2 = false /\
      DomSrc mu b1 = true /\ DomTgt mu b2 = true.
Proof. intros.
  split. eapply privChar; eassumption.
  eapply local_locBlocks; trivial. 
  eapply priv_in_local; eassumption.
Qed.

Lemma extern_DomRng': forall mu (WD:SM_wd mu) b1 b2 d
                      (L:extern_of mu b1 = Some(b2,d)),
      pubBlocksSrc mu b1 = false /\ pubBlocksTgt mu b2 = false /\ 
      locBlocksSrc mu b1 = false /\ locBlocksTgt mu b2 = false /\ 
      extBlocksSrc mu b1 = true /\ extBlocksTgt mu b2 = true /\
      DomSrc mu b1 = true /\ DomTgt mu b2 = true.
Proof. intros.
   apply (extern_DomRng _ WD) in L; destruct L as [A B].
   destruct (disjoint_extern_local_Src _ WD b1); try congruence.
   destruct (disjoint_extern_local_Tgt _ WD b2); try congruence.
   unfold DomSrc, DomTgt. intuition.
   remember (pubBlocksSrc mu b1) as q.
      destruct q; trivial. apply eq_sym in Heqq.
      rewrite (pubBlocksLocalSrc _ WD _ Heqq) in H; congruence.
   remember (pubBlocksTgt mu b2) as p.
      destruct p; trivial; apply eq_sym in Heqp.
      rewrite (pubBlocksLocalTgt _ WD _ Heqp) in H0; congruence.
Qed.

Lemma foreign_DomRng: forall mu (WD:SM_wd mu) b1 b2 d
                      (L:foreign_of mu b1 = Some(b2,d)),
      pubBlocksSrc mu b1 = false /\ pubBlocksTgt mu b2 = false /\ 
      locBlocksSrc mu b1 = false /\ locBlocksTgt mu b2 = false /\ 
      frgnBlocksSrc mu b1 = true /\ frgnBlocksTgt mu b2 = true /\
      extBlocksSrc mu b1 = true /\ extBlocksTgt mu b2 = true /\ 
      DomSrc mu b1 = true /\ DomTgt mu b2 = true.
Proof. intros.
   specialize (foreign_in_extern _ _ _ _ L). intros EXT.
   apply (extern_DomRng' _ WD) in EXT.
   intuition. clear - WD L. 
   unfold foreign_of in L.
     destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
     destruct (fSrc b1); trivial; inv L.
   clear - WD L. 
   remember (frgnBlocksSrc mu b1) as q.
   destruct q; apply eq_sym in Heqq.
     destruct (frgnSrc _ WD _ Heqq) as [? [? [? ?]]]. congruence.
   unfold foreign_of in L.
     destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
     rewrite Heqq in L; congruence. 
Qed.

Lemma unknown_DomRng: forall mu (WD:SM_wd mu) b1 b2 d
                      (L: unknown_of mu b1 = Some(b2,d)),
      pubBlocksSrc mu b1 = false /\ pubBlocksTgt mu b2 = false /\ 
      locBlocksSrc mu b1 = false /\ locBlocksTgt mu b2 = false /\ 
      extBlocksSrc mu b1 = true /\ extBlocksTgt mu b2 = true /\ 
      frgnBlocksSrc mu b1 = false /\ 
      DomSrc mu b1 = true /\ DomTgt mu b2 = true.
Proof. intros.
specialize (unknown_in_extern _ _ _ _ L). intros E.
apply (extern_DomRng' _ WD) in E. intuition.
clear - WD L H0.
unfold unknown_of in L.
destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
rewrite H0 in L.
destruct (fSrc b1); trivial. inv L.
Qed. 

Definition locvisible_of mu := join (foreign_of mu) (local_of mu) .
Definition extvisible_of mu := join (extern_of mu) (pub_of mu).

Lemma locvisible_sharedprivate: forall mu, 
      locvisible_of mu = join (shared_of mu) (priv_of mu).
Proof. intros. unfold locvisible_of, shared_of.
rewrite <- join_assoc.
rewrite local_pubpriv.
trivial.
Qed.

Lemma shared_in_locvisible: forall mu, 
      inject_incr (shared_of mu) (locvisible_of mu).
Proof. intros. 
rewrite locvisible_sharedprivate.
apply join_incr_left.
Qed.

Lemma local_in_locvisible: forall mu (WD: SM_wd mu), 
      inject_incr (local_of mu) (locvisible_of mu).
Proof. intros. 
apply join_incr_right.
apply (disjoint_foreign_local _ WD).
Qed.

Lemma private_in_locvisible: forall mu (WD: SM_wd mu), 
      inject_incr (priv_of mu) (locvisible_of mu).
Proof. intros. 
rewrite locvisible_sharedprivate.
apply join_incr_right.
apply (disjoint_shared_priv _ WD). 
Qed.

Lemma pub_in_locvisible: forall mu (WD: SM_wd mu), 
      inject_incr (pub_of mu) (locvisible_of mu).
Proof. intros. 
eapply inject_incr_trans.
apply pub_in_local.
apply (local_in_locvisible _ WD).
Qed.

Lemma extvisible_sharedunknown: forall mu (WD: SM_wd mu), 
      extvisible_of mu = join (shared_of mu) (unknown_of mu).
Proof. intros. unfold extvisible_of, shared_of.
rewrite extern_foreignunknown; trivial.
rewrite <- join_assoc.
rewrite <- join_assoc.
rewrite (join_com (pub_of mu)); trivial.
rewrite disjoint_com.
apply (disjoint_unknown_pub _ WD).
Qed.

Lemma shared_in_extvisible: forall mu( WD: SM_wd mu), 
      inject_incr (shared_of mu) (extvisible_of mu).
Proof. intros. 
rewrite extvisible_sharedunknown; trivial.
apply join_incr_left.
Qed.

Lemma unknown_in_extvisible: forall mu (WD: SM_wd mu), 
      inject_incr (unknown_of mu) (extvisible_of mu).
Proof. intros. 
rewrite extvisible_sharedunknown; trivial.
apply join_incr_right.
apply (disjoint_shared_unknown _ WD). 
Qed.

(*an inject_separated-like property wrt DOM/RNG instead of
  wrt validity in suitable memories*) 
Definition sm_inject_separated (mu mu' : SM_Injection) (m1 m2:mem):Prop :=
  (forall b1 b2 d, as_inj mu b1 = None -> as_inj mu' b1 = Some(b2,d) ->
                   (DomSrc mu b1 = false /\ DomTgt mu b2 = false)) /\
  (forall b1, DomSrc mu b1 = false -> DomSrc mu' b1 = true -> ~Mem.valid_block m1 b1) /\
  (forall b2, DomTgt mu b2 = false -> DomTgt mu' b2 = true -> ~Mem.valid_block m2 b2).

Lemma sm_inject_separated_mem: forall mu mu' m1 m2
        (SEP: sm_inject_separated mu mu' m1 m2) (WD': SM_wd mu'),
      inject_separated (as_inj mu) (as_inj mu') m1 m2.
Proof.
  intros.
  destruct SEP as [A B].
  intros b1 b2; intros.
  destruct (A _ _ _ H H0); clear A.
  destruct (as_inj_DomRng _ _ _ _ H0); trivial.
  split; eapply B; assumption.
Qed. 

Definition freshloc m m' b := andb (valid_block_dec m' b) (negb (valid_block_dec m b)).
Lemma freshloc_charT: forall m m' b, 
      (freshloc m m' b = true) <-> (Mem.valid_block m' b /\ ~Mem.valid_block m b).
Proof. intros.
  unfold freshloc.
  remember (valid_block_dec m' b) as s'; destruct s'; simpl.
    remember (valid_block_dec m b) as s; destruct s; simpl.
    split; intros. inv H. destruct H. contradiction.
    split; auto.
  split; intros. inv H. destruct H. contradiction.
Qed.
Lemma freshloc_charF: forall m m' b, 
      (freshloc m m' b = false) <-> (Mem.valid_block m b \/ ~Mem.valid_block m' b).
Proof. intros.
  unfold freshloc.
  remember (valid_block_dec m' b) as s'; destruct s'; simpl.
    remember (valid_block_dec m b) as s; destruct s; simpl.
    split; intros. left. assumption. trivial.
    split; intros. discriminate. destruct H; contradiction.
  split; intros. right; assumption. trivial. 
Qed.
Lemma freshloc_irrefl: forall m b, freshloc m m b = false.
Proof. intros. apply freshloc_charF.
  destruct (valid_block_dec m b).
  left; trivial. right; trivial.
Qed.
Lemma freshloc_trans: forall m m'' m' b
     (FWD: mem_forward m m'') (FWD': mem_forward m'' m'),
     (orb (freshloc m m'' b) (freshloc m'' m' b)) = freshloc m m' b.
Proof. intros.
   remember (freshloc m m' b) as d.
   remember (freshloc m m'' b) as e.
   remember (freshloc m'' m' b) as f.
   destruct d; apply eq_sym in Heqd;
   destruct e; apply eq_sym in Heqe;
   destruct f; apply eq_sym in Heqf;
   simpl; try reflexivity.
   apply freshloc_charT in Heqd. destruct Heqd.   
     apply freshloc_charF in Heqe. destruct Heqe. contradiction.
     apply freshloc_charF in Heqf. destruct Heqf; contradiction.
   apply freshloc_charT in Heqe. destruct Heqe.   
     apply freshloc_charT in Heqf. destruct Heqf. contradiction.
   apply freshloc_charT in Heqe. destruct Heqe.
     destruct (FWD' b H) as [? _].
     apply freshloc_charF in Heqf. destruct Heqf; try contradiction.
       apply freshloc_charF in Heqd. destruct Heqd; try contradiction.
   apply freshloc_charT in Heqf. destruct Heqf.
     apply freshloc_charF in Heqe. destruct Heqe.
      destruct (FWD b H1) as [? _]. contradiction.
     apply freshloc_charF in Heqd. destruct Heqd; try contradiction.
      destruct (FWD b H2) as [? _]. contradiction.
Qed.
  
(*Expresses that the evolution soundly and completely tracks what happened during
  related coresteps. sm_locally_allocated is typically be used in conjunction with
  intern_incr, so extern mu = extern mu', and equalities
  (pSrc,pTgt,fSrc,fTgt)=(pSrc',pTgt',fSrc',fTgt') hold, too.*) 
Definition sm_locally_allocated (mu mu' : SM_Injection) (m1 m2 m1' m2':mem):Prop :=
  match mu, mu' with
     Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern,
     Build_SM_Injection locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern'
  =>    locBSrc' = (fun b => orb (locBSrc b) (freshloc m1 m1' b))
     /\ locBTgt' = (fun b => orb (locBTgt b) (freshloc m2 m2' b))
     /\ extBSrc' = extBSrc
     /\ extBTgt' = extBTgt
  end.

Lemma sm_locally_allocatedChar: forall mu mu' m1 m2 m1' m2',
  sm_locally_allocated mu mu' m1 m2 m1' m2' <->
  (    DomSrc mu' = (fun b => orb (DomSrc mu b) (freshloc m1 m1' b))
    /\ DomTgt mu' = (fun b => orb (DomTgt mu b) (freshloc m2 m2' b))
    /\ locBlocksSrc mu' = (fun b => orb (locBlocksSrc mu b) (freshloc m1 m1' b))
    /\ locBlocksTgt mu' = (fun b => orb (locBlocksTgt mu b) (freshloc m2 m2' b))
    /\ extBlocksSrc mu' = extBlocksSrc mu
    /\ extBlocksTgt mu' = extBlocksTgt mu).
Proof. intros.
destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern].
destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern'].
simpl in *.
unfold DomSrc, DomTgt in *. simpl in *; subst. 
intuition. 
subst.
  extensionality b. rewrite <- orb_assoc. rewrite <- orb_assoc.
     rewrite (orb_comm (extBSrc b)). trivial.
subst.
  extensionality b. rewrite <- orb_assoc. rewrite <- orb_assoc.
     rewrite (orb_comm (extBTgt b)). trivial. 
Qed.

Lemma sm_inject_separated_intern_MYB: forall mu mu' m1 m2 m1' m2'
        (SEP: sm_inject_separated mu mu' m1 m2)
        (LAL: sm_locally_allocated mu mu' m1 m2 m1' m2'),
      (forall b, locBlocksSrc mu b = false -> locBlocksSrc mu' b = true -> ~ Mem.valid_block m1 b) /\
      (forall b, locBlocksTgt mu b = false -> locBlocksTgt mu' b = true -> ~ Mem.valid_block m2 b).
Proof.
  intros.
  destruct SEP.
  destruct mu as [locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern]; simpl in *.
  destruct mu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern']; simpl in *.
  destruct LAL as [? [? [? ?]]]. subst. unfold as_inj in *; simpl in *.
split; intros; rewrite H1 in H2; simpl in H2.
   eapply freshloc_charT. eassumption.
   eapply freshloc_charT. eassumption.
Qed. 

(*in extern_incr steps, sm_inject_separated_intern_MYB is not needed/trivial,
 since locBlocksSrc mu b = locBlocksSrc mu' b and locBlocksTgt mu b = locBlocksTgt mu' b*)

Definition sm_valid (mu : SM_Injection) (m1 m2: mem) :=
       (forall b1, DOM mu b1 -> Mem.valid_block m1 b1)  
    /\ (forall b2, RNG mu b2 -> Mem.valid_block m2 b2).

Lemma intern_incr_refl: forall mu, intern_incr mu mu.
Proof. intros.
split. apply inject_incr_refl.
intuition.
Qed.

Lemma extern_incr_refl: forall mu, extern_incr mu mu.
Proof. intros.
split. apply inject_incr_refl.
intuition.
Qed.

Lemma intern_incr_local: forall mu mu' (INC: intern_incr mu mu'),
      inject_incr (local_of mu) (local_of mu').
Proof. intros. apply INC. Qed.
  
Lemma intern_incr_extern: forall mu mu' (INC: intern_incr mu mu'),
      extern_of mu = extern_of mu'.
Proof. intros. apply INC. Qed.
  
Lemma extern_incr_extern: forall mu mu' (INC: extern_incr mu mu'),
      inject_incr (extern_of mu) (extern_of mu').
Proof. intros. apply INC. Qed.

Lemma extern_incr_local: forall mu mu' (INC: extern_incr mu mu'),
      local_of mu = local_of mu'.
Proof. intros. apply INC. Qed.

Lemma intern_incr_trans: forall mu mu' mu'' 
      (Inc: intern_incr mu mu') (Inc': intern_incr mu' mu''),
      intern_incr mu mu''.
Proof. intros.
split. eapply inject_incr_trans.
  apply intern_incr_local; eassumption.
  apply intern_incr_local; eassumption.
split. rewrite (intern_incr_extern _ _ Inc).
  apply (intern_incr_extern _ _ Inc'). 
destruct Inc as [A [B [C [D [E [F [G [H [I J]]]]]]]]].
destruct Inc' as [A' [B' [C' [D' [E' [F' [G' [H' [I' J']]]]]]]]].
simpl in *. subst.
rewrite G, H, I, J, E, F in *.
repeat (split; eauto).
Qed.

Lemma extern_incr_trans: forall mu mu' mu'' 
      (Inc: extern_incr mu mu') (Inc': extern_incr mu' mu''),
      extern_incr mu mu''.
Proof. intros.
split. eapply inject_incr_trans.
  apply extern_incr_extern; eassumption.
  apply extern_incr_extern; eassumption.
split. rewrite (extern_incr_local _ _ Inc).
  apply (extern_incr_local _ _ Inc'). 
destruct Inc as [A [B [C [D [E [F [G [H [I J]]]]]]]]].
destruct Inc' as [A' [B' [C' [D' [E' [F' [G' [H' [I' J']]]]]]]]].
simpl in *. subst.
rewrite E, F, G, H in *.
repeat (split; eauto).
Qed.

Lemma sm_inject_separated_same_sminj: forall mu m m',
   sm_inject_separated mu mu m m'.
Proof. intros.
split; simpl; intros.
  rewrite H0 in H. inv H.
split; intros.
  rewrite H0 in H. inv H.
  rewrite H0 in H. inv H.
Qed. 

Lemma intern_incr_as_inj: forall mu mu'
      (INC: intern_incr mu mu') (WD': SM_wd mu'),
      inject_incr (as_inj mu) (as_inj mu').
Proof. intros.
  intros b1; intros.
  unfold as_inj in *.
  apply joinD_Some in H. 
  destruct H as[EXT | [EXT LOC]];
     rewrite (intern_incr_extern _ _ INC) in EXT.
     apply join_incr_left. apply EXT.
   apply join_incr_right. 
     apply disjoint_extern_local. apply WD'.
     eapply intern_incr_local. apply INC. apply LOC.
Qed.

Lemma extern_incr_as_inj: forall mu mu'
     (INC: extern_incr mu mu') (WD': SM_wd mu'),
     inject_incr (as_inj mu) (as_inj mu').
Proof. intros.
  intros b1; intros.
  unfold as_inj in *.
  apply joinD_Some in H. 
  destruct H as[EXT | [EXT LOC]].
     apply join_incr_left. 
     apply (extern_incr_extern _ _ INC). apply EXT.
   apply join_incr_right. 
     apply disjoint_extern_local. apply WD'.
     rewrite (extern_incr_local _ _ INC) in LOC. apply LOC.
Qed.

Lemma inject_separated_intern_incr_fwd:
  forall mu mu' m1 m2 mu'' m2'
  (SEP: sm_inject_separated mu mu' m1 m2)
  (SEP': sm_inject_separated mu' mu'' m1 m2')
  (INC: intern_incr mu mu') (INC': intern_incr mu' mu'')
  (FWD: mem_forward m2 m2')
  (WD': SM_wd mu') (WD'': SM_wd mu''),
  sm_inject_separated mu mu'' m1 m2.
Proof. intros.
split. intros.
  remember (as_inj mu' b1) as q.
  destruct q; apply eq_sym in Heqq.
    destruct p.
    apply intern_incr_as_inj in INC'; trivial.
    rewrite (INC' _ _ _ Heqq) in H0. inv H0.
    solve [eapply SEP; eassumption].
  assert (DomSrc mu' b1 = false /\ DomTgt mu' b2=false)
        by (eapply SEP'; eassumption).
    destruct H1.
    split. eapply intern_incr_DomSrc_inv; eassumption.
      eapply intern_incr_DomTgt_inv; eassumption.
split; intros.
  remember (DomSrc mu' b1) as d; destruct d; apply eq_sym in Heqd.
    eapply SEP; assumption.
    eapply SEP'; assumption.
  remember (DomTgt mu' b2) as d; destruct d; apply eq_sym in Heqd.
    eapply SEP; assumption.
    intros N. apply FWD in N. destruct N. eapply SEP'; try eassumption.
Qed.

Lemma intern_separated_incr_fwd2:
  forall mu0 mu mu' m10 m20 m1 m2,
  intern_incr mu mu' ->
  sm_inject_separated mu mu' m1 m2 ->
  intern_incr mu0 mu ->
  mem_forward m10 m1 ->
  sm_inject_separated mu0 mu m10 m20 ->
  mem_forward m20 m2 -> 
  SM_wd mu' ->
  sm_inject_separated mu0 mu' m10 m20.
Proof. intros.
split; intros; simpl.
  remember (as_inj mu b1) as q.
  destruct q; apply eq_sym in Heqq.
    destruct p.
    rewrite (intern_incr_as_inj _ _ H H5 _ _ _ Heqq) in H7. inv H7. 
    eapply H3. assumption. eassumption.
  assert (DomSrc mu b1 = false /\ DomTgt mu b2 = false).
    eapply H0. assumption. eassumption.
  destruct H8.
    split. apply (intern_incr_DomSrc_inv _ _ H1 _ H8). 
    apply (intern_incr_DomTgt_inv _ _ H1 _ H9).
split; intros.
  remember (DomSrc mu b1) as q.
  destruct q; apply eq_sym in Heqq.
    eapply H3; assumption.
    assert (~ Mem.valid_block m1 b1).
      eapply H0; assumption.
    intros N. apply H8. apply H2 in N. apply N.
remember (DomTgt mu b2) as q.
  destruct q; apply eq_sym in Heqq.
    eapply H3; assumption.
    assert (~ Mem.valid_block m2 b2).
      eapply H0; assumption.
    intros N. apply H8. apply H4 in N. apply N.
Qed.

Lemma sm_locally_allocated_trans: forall mu mu' mu'' m2 m3 m2' m3' m2'' m3''
(LocAlloc23 : sm_locally_allocated mu mu' m2 m3 m2'' m3')
(LocAlloc23' : sm_locally_allocated mu' mu'' m2'' m3' m2' m3'')
(Fwd2 : mem_forward m2 m2'')
(Fwd2' : mem_forward m2'' m2')
(Fwd3 : mem_forward m3 m3')
(Fwd3' : mem_forward m3' m3''),
sm_locally_allocated mu mu'' m2 m3 m2' m3''.
Proof. intros.
apply sm_locally_allocatedChar.
apply sm_locally_allocatedChar in LocAlloc23.
destruct LocAlloc23 as [LA1 [LA2 [LA3 [LA4 [LA5 LA6]]]]].
apply sm_locally_allocatedChar in LocAlloc23'.
destruct LocAlloc23' as [LA1' [LA2' [LA3' [LA4' [LA5' LA6']]]]].
split. extensionality b.
  rewrite LA1'; clear LA1'.
  rewrite LA1; clear LA1.
  rewrite <- orb_assoc.
  rewrite freshloc_trans; trivial.
split. extensionality b.
  rewrite LA2'; clear LA2'.
  rewrite LA2; clear LA2.
  rewrite <- orb_assoc.
  rewrite freshloc_trans; trivial.
split. extensionality b.
  rewrite LA3'; clear LA3'.
  rewrite LA3; clear LA3.
  rewrite <- orb_assoc.
  rewrite freshloc_trans; trivial.
split. extensionality b.
  rewrite LA4'; clear LA4'.
  rewrite LA4; clear LA4.
  rewrite <- orb_assoc.
  rewrite freshloc_trans; trivial.
rewrite LA5', LA6'.  
  intuition. 
Qed.

Definition sharedSrc mu b := 
    match shared_of mu b 
    with Some _ => true | None => false
    end.

Lemma sharedSrc_iff: forall mu b, sharedSrc mu b = true <->
                     exists b2 d, shared_of mu b = Some(b2,d).
Proof. intros.
  unfold sharedSrc.
  destruct (shared_of mu b).
    destruct p. split; intros; trivial.
    exists b0, z; intuition.
  split; intros. intuition. destruct H as [b2 [d X]]; discriminate.
Qed.

Lemma pubSrc_shared: forall mu (WD: SM_wd mu) b, 
                     pubBlocksSrc mu b = true -> 
                     sharedSrc mu b = true.
Proof. intros.
  destruct (pubSrc _ WD _ H) as [b2 [d [P T]]].
  unfold sharedSrc.
  rewrite (pub_in_shared _ WD _ _ _ P).
  trivial.
Qed.

Lemma frgnSrc_shared: forall mu (WD: SM_wd mu) b, 
                     frgnBlocksSrc mu b = true -> 
                     sharedSrc mu b = true.
Proof. intros.
  destruct (frgnSrc _ WD _ H) as [b2 [d [P T]]].
  unfold sharedSrc.
  rewrite (foreign_in_shared _ _ _ _ P).
  trivial.
Qed.

Lemma sharedSrc_iff_frgnpub: forall mu (WD: SM_wd mu), 
      sharedSrc mu = fun b => orb (frgnBlocksSrc mu b) (pubBlocksSrc mu b).
Proof. intros. extensionality b.
  remember (sharedSrc mu b) as d.
  destruct d; apply eq_sym in Heqd. 
    apply sharedSrc_iff in Heqd. destruct Heqd as [b2 [d SH]]. 
    destruct (joinD_Some _ _ _ _ _ SH); clear SH.
      assert (frgnBlocksSrc mu b = true).
        eapply foreign_DomRng; eassumption.
      rewrite H0; intuition.
    destruct H. 
      assert (pubBlocksSrc mu b = true).
        eapply pub_locBlocks; eassumption.
      rewrite H1; intuition.
  remember (frgnBlocksSrc mu b) as q.
  destruct q; apply eq_sym in Heqq.
    rewrite (frgnSrc_shared _ WD _ Heqq) in Heqd. inv Heqd. 
  clear Heqq.
  remember (pubBlocksSrc mu b) as q.
  destruct q; apply eq_sym in Heqq.
    rewrite (pubSrc_shared _ WD _ Heqq) in Heqd. inv Heqd.
  trivial.
Qed.

Definition sharedTgt mu b := orb (frgnBlocksTgt mu b) (pubBlocksTgt mu b).


Lemma shared_SrcTgt: forall mu (WD: SM_wd mu) b 
                    (SH: sharedSrc mu b = true),
      exists jb d, shared_of mu b = Some (jb, d) /\ sharedTgt mu jb = true.
Proof. intros. apply sharedSrc_iff in SH. destruct SH as [b2 [d SH]].
  rewrite SH. exists b2, d; split; trivial.
  unfold sharedTgt. apply orb_true_iff. 
  destruct (joinD_Some _ _ _ _ _ SH).
    left. eapply foreign_DomRng; eassumption.
  destruct H.
    right. eapply pub_locBlocks; eassumption.
Qed.


(***********************NORMALIZATION*********************)
Definition normalize (j k: meminj) : meminj :=
  fun b => match j b with 
             None => None
           | Some (b', delta) => match k b' with 
                                   None => None
                                 | Some (b'',delta') => Some (b', delta)
                                 end
           end.

Lemma normalize_compose: forall j k,
   compose_meminj (normalize j k) k = compose_meminj j k.
Proof. intros. unfold compose_meminj, normalize.
  extensionality b.
  remember (j b) as d.
  destruct d; trivial. destruct p as [b2 d1].
  remember (k b2) as q.
  destruct q; trivial. destruct p as [b3 d2].
  rewrite <- Heqq. trivial.
Qed.

Lemma normalize_norm: forall j k b b2 d1, normalize j k b = Some (b2,d1) <->
          j b = Some(b2, d1) /\ exists p, k b2 = Some p.
Proof. intros. unfold normalize.
  remember (j b) as d.
  destruct d. destruct p as [b2' d1'].
     remember (k b2') as q.
     destruct q. destruct p as [b3 d2].
     split; intros. split; trivial. inv H. rewrite <- Heqq. eexists; reflexivity.
     destruct H; assumption.
    split; intros. inv H. destruct H. destruct H0. inv H. rewrite H0 in Heqq. inv Heqq.
  split; intros. inv H. destruct H. inv H.
Qed.    

Lemma normalize_inject: forall j k m1 m2 m3 (InjJ: Mem.inject j m1 m2)
                               (InjK: Mem.inject k m2 m3)
                               (ValJ: forall b1 b2 d1, j b1 = Some(b2,d1) -> 
                                      Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2),
                        Mem.inject (normalize j k) m1 m2.
Proof. intros.
split; intros.
  split; intros.
    apply normalize_norm in H; destruct H as [J [[b3 d2] K]].
     eapply InjJ; eassumption.
    apply normalize_norm in H; destruct H as [J [[b3 d2] K]].
     eapply InjJ; eassumption.
    apply normalize_norm in H; destruct H as [J [[b3 d2] K]].
     specialize (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ InjJ) _ _ _ _ J H0). intros.
     inv H; try constructor.
     assert (Perm2: Mem.perm m2 b2 (ofs+delta) Cur Readable).
       eapply InjJ; eassumption.
     specialize (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ InjK) _ _ _ _ K Perm2). intros.
       rewrite <- H2 in H. clear H2.
       inv H.
       econstructor. unfold normalize. rewrite H3. rewrite H5. reflexivity. reflexivity.
     unfold normalize. 
       remember (j b) as d. destruct d; trivial; apply eq_sym in Heqd. destruct p.
       exfalso. apply H. eapply (ValJ _ _ _ Heqd).
    apply normalize_norm in H; destruct H as [J [[b3 d2] K]].
       eapply (ValJ _ _ _ J).
   intros b1 b1'; intros.
     apply normalize_norm in H0; destruct H0 as [J [[b3 d2] K]].
     apply normalize_norm in H1; destruct H1 as [J' [[b3' d2'] K']].
     eapply InjJ; eassumption.
  destruct H0. 
    apply normalize_norm in H; destruct H as [J [[b3 d2] K]].
    eapply InjJ; try eassumption. left; trivial.
  apply normalize_norm in H; destruct H as [J [[b3 d2] K]].
    eapply InjJ; try eassumption. right; trivial.
Qed.

Definition sm_extern_normalize mu12 mu23:SM_Injection :=
  match mu12 with 
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern =>
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt (normalize extern (extern_of mu23)) 
  end.

Lemma sm_extern_normalize_locBlocksSrc: forall mu mu',
            locBlocksSrc (sm_extern_normalize mu mu') = locBlocksSrc mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_locBlocksTgt: forall mu mu',
            locBlocksTgt (sm_extern_normalize mu mu') = locBlocksTgt mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_extBlocksSrc: forall mu mu',
            extBlocksSrc (sm_extern_normalize mu mu') = extBlocksSrc mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_extBlocksTgt: forall mu mu',
            extBlocksTgt (sm_extern_normalize mu mu') = extBlocksTgt mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_DomSrc: forall mu mu',
            DomSrc (sm_extern_normalize mu mu') = DomSrc mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_DomTgt: forall mu mu',
            DomTgt (sm_extern_normalize mu mu') = DomTgt mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_pubBlocksSrc: forall mu mu',
            pubBlocksSrc (sm_extern_normalize mu mu') = pubBlocksSrc mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_pubBlocksTgt: forall mu mu',
            pubBlocksTgt (sm_extern_normalize mu mu') = pubBlocksTgt mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_frgnBlocksSrc: forall mu mu',
            frgnBlocksSrc (sm_extern_normalize mu mu') = frgnBlocksSrc mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_frgnBlocksTgt: forall mu mu',
            frgnBlocksTgt (sm_extern_normalize mu mu') = frgnBlocksTgt mu.
Proof. intros. destruct mu; simpl. reflexivity. Qed.

Lemma sm_extern_normalize_local: forall mu12 mu23,
  local_of (sm_extern_normalize mu12 mu23) = local_of mu12.
Proof. intros. destruct mu12. reflexivity. Qed.

Lemma sm_extern_normalize_extern: forall mu12 mu23,
  extern_of (sm_extern_normalize mu12 mu23) = normalize (extern_of mu12) (extern_of mu23).
Proof. intros. destruct mu12. reflexivity. Qed.

Lemma sm_extern_normalize_foreign: forall mu12 mu23 
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
  foreign_of (sm_extern_normalize mu12 mu23) = foreign_of mu12.
Proof. intros. destruct mu12; simpl.
  extensionality b.
  remember (frgnBlocksSrc0 b) as d.
  destruct d; apply eq_sym in Heqd; trivial.
  destruct (frgnSrc _ WD12 _ Heqd) as [b2 [d1 [F T]]]. simpl in *.
  rewrite Heqd in F. apply HypFrgn in T.  
  destruct (frgnSrc _ WD23 _ T) as [b3 [d2 [F2 T2]]]. simpl in *.
  unfold normalize. rewrite F. rewrite (foreign_in_extern _ _ _ _ F2). trivial.
Qed.

Lemma sm_extern_normalize_priv: forall mu12 mu23,
  priv_of (sm_extern_normalize mu12 mu23) = priv_of mu12.
Proof. intros. unfold priv_of. destruct mu12. reflexivity. Qed.

Lemma sm_extern_normalize_pub: forall mu12 mu23,
  pub_of (sm_extern_normalize mu12 mu23) = pub_of mu12.
Proof. intros. unfold pub_of. destruct mu12. reflexivity. Qed.

Lemma sm_extern_normalize_shared: forall mu12 mu23
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
  shared_of (sm_extern_normalize mu12 mu23) = shared_of mu12.
Proof. intros. unfold shared_of.
  rewrite sm_extern_normalize_pub, sm_extern_normalize_foreign; trivial.
Qed.

Lemma sm_extern_normalize_sharedSrc: forall mu12 mu23
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
   sharedSrc (sm_extern_normalize mu12 mu23) = sharedSrc mu12.
Proof. intros. unfold sharedSrc.
  rewrite sm_extern_normalize_shared; trivial.
Qed. 

Lemma sm_extern_normalize_sharedTgt: forall mu12 mu23
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
   sharedTgt (sm_extern_normalize mu12 mu23) = sharedTgt mu12.
Proof. intros. unfold sharedTgt.
  rewrite sm_extern_normalize_frgnBlocksTgt, 
          sm_extern_normalize_pubBlocksTgt.
  trivial.
Qed. 
  
Lemma sm_extern_normalize_norm: forall mu12 mu23 b1 b2 d1,
          extern_of (sm_extern_normalize mu12 mu23) b1 = Some (b2, d1) -> 
      (extern_of mu12 b1 = Some (b2, d1) /\ exists p, extern_of mu23 b2 = Some p).
Proof. intros. destruct mu12; simpl in *. 
   apply normalize_norm in H. assumption.
Qed.

Lemma sm_extern_normalize_WD: forall mu12 mu23 
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
          SM_wd (sm_extern_normalize mu12 mu23).
Proof. intros. 
  specialize (sm_extern_normalize_norm mu12 mu23); intros NN.
  destruct mu12; simpl in *.
  repeat (split; try eapply WD12).
  simpl in *. destruct (NN _ _ _ H). apply H0.
  simpl in *. destruct (NN _ _ _ H). apply H0.
  simpl in *. intros. rewrite H. 
   destruct (frgnSrc _ WD12 _ H) as [b2 [d1 [F12 T12]]]; simpl in *.
   rewrite H in F12. specialize (HypFrgn _ T12). 
   destruct (frgnSrc _ WD23 _ HypFrgn) as [b3 [d2 [F23 T23]]]; simpl in *.
   apply foreign_in_extern in F23. 
   unfold normalize. rewrite F12, F23.
   exists b2, d1; split; trivial.
Qed. 

Lemma sm_extern_normalize_as_inj_norm: forall mu12 mu23 (WD12: SM_wd mu12) b1 b2 d1,
         as_inj (sm_extern_normalize mu12 mu23) b1 = Some (b2, d1) -> 
      as_inj mu12 b1 = Some (b2, d1).
Proof. intros. apply joinI. destruct (joinD_Some _ _ _ _ _ H); clear H.
  (*extern*) left. eapply sm_extern_normalize_norm. apply H0. 
  (*intern*) destruct H0. unfold sm_extern_normalize in *.
             destruct mu12; simpl in *. right.
             destruct (disjoint_extern_local _ WD12 b1); simpl in *.
               split; trivial.
               rewrite H0 in H1; discriminate.
Qed.

Lemma sm_extern_normalize_as_inj_norm2: forall mu12 mu23
         (WD12: SM_wd mu12) (WD23: SM_wd mu23) b1 b2 d1 b3 d2
         (AsInj12: as_inj mu12 b1 = Some (b2, d1)) (AsInj23: as_inj mu23 b2 = Some (b3, d2))
         (HypL: locBlocksTgt mu12 = locBlocksSrc mu23)
         (HypE: extBlocksTgt mu12 = extBlocksSrc mu23),
       as_inj (sm_extern_normalize mu12 mu23) b1 = Some (b2, d1).
Proof. intros.
  destruct (joinD_Some _ _ _ _ _ AsInj12) as [EXT12 | [EXT12 LOC12]]; clear AsInj12.
    destruct (extern_DomRng _ WD12 _ _ _ EXT12) as [eSrc eTgt].
    rewrite HypE in eTgt.
    destruct (joinD_Some _ _ _ _ _ AsInj23) as [EXT23 | [EXT23 LOC23]]; clear AsInj23.
      apply joinI; left. rewrite sm_extern_normalize_extern.
           eapply normalize_norm. split; trivial. exists (b3,d2); trivial.
      destruct (local_DomRng _ WD23 _ _ _ LOC23) as [? ?].
        destruct (disjoint_extern_local_Src _ WD23 b2); congruence.
    apply joinI; right. rewrite sm_extern_normalize_extern, sm_extern_normalize_local.
       split; trivial. unfold normalize. rewrite EXT12. trivial.
Qed. 

(*Lemma sm_normalize_inject in StructuredInjections.v shows this:
   forall mu12 mu23 
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true)
          (HypMyblocks: locBlocksTgt mu12 = locBlocksSrc mu23)
          m1 
          (RC: reach_closed m1 (fun b => locBlocksSrc mu12 b || frgnBlocksSrc mu12 b))
          m2 (Inj12: Mem.inject (as_inj mu12) m1 m2)
          m3 (Inj23: Mem.inject (as_inj mu23) m2 m3),
      Mem.inject (as_inj (sm_extern_normalize mu12 mu23)) m1 m2.
*)

Lemma normalize_compose_commute: forall f g h,
        normalize (compose_meminj f g) h 
      = compose_meminj (normalize f (normalize g h))
                       (normalize g h).
Proof. intros. 
  extensionality b. unfold normalize, compose_meminj.
  remember (f b) as d. destruct d; trivial. destruct p as [b2 d1].
  remember (g b2) as q. destruct q; trivial. destruct p as [b3 d2].
  remember (h b3) as w. destruct w; trivial. destruct p as [b4 d3].
  rewrite <- Heqq. rewrite <- Heqw. trivial.
Qed.
  
(*Maybe a more general form of closure is this:*)
Definition sm_equiv mu mu': Prop :=
  match mu, mu' with 
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern,
    Build_SM_Injection locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern'
  => locBSrc = locBSrc' /\ locBTgt = locBTgt' /\ extBSrc = extBSrc' /\ extBTgt = extBTgt'
     /\ pSrc = pSrc' /\ pTgt = pTgt' /\ fSrc = fSrc' /\ fTgt = fTgt' /\ local = local' /\
     foreign_of mu = foreign_of mu' /\ SM_wd mu /\ SM_wd mu'  
  end.

Lemma sm_extern_normal_equiv: forall mu12 mu23 
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
          sm_equiv mu12 (sm_extern_normalize mu12 mu23).
Proof. intros. specialize (sm_extern_normalize_WD _ _ WD12 WD23 HypFrgn). intros.
  destruct mu12; simpl in *.
  repeat (split; try eauto).
  extensionality b.
  remember (frgnBlocksSrc0 b) as d.
  destruct d; trivial.
  apply eq_sym in Heqd.
  destruct (frgnSrc _ WD12 _ Heqd) as [b2 [d1 [F12 T12]]]; simpl in *.
   rewrite Heqd in F12. specialize (HypFrgn _ T12). 
   destruct (frgnSrc _ WD23 _ HypFrgn) as [b3 [d2 [F23 T23]]]; simpl in *.
   apply foreign_in_extern in F23. 
   unfold normalize. rewrite F12, F23. trivial.
Qed.

Lemma sm_equiv_refl: forall mu (WD: SM_wd mu), sm_equiv mu mu.
Proof. intros. destruct mu; simpl. intuition. Qed.

Lemma sm_equiv_sym: forall mu mu' (WD: SM_wd mu) (WD': SM_wd mu'), 
          sm_equiv mu mu' -> sm_equiv mu' mu.
Proof. intros. destruct mu; destruct mu'; simpl in *. intuition. Qed.

Lemma sm_equiv_trans: forall mu mu' mu'' (WD: SM_wd mu) (WD': SM_wd mu') (WD'': SM_wd mu''), 
          sm_equiv mu mu' -> sm_equiv mu' mu'' -> sm_equiv mu mu''.
Proof. intros. destruct mu; destruct mu'; destruct mu''; simpl in *.
  destruct H as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]. subst.
  destruct H0 as [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]. subst.
  intuition. rewrite H9. apply H8. Qed.

Definition EraseUnknown (mu : SM_Injection) : SM_Injection :=
  match mu with
  Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern =>
  Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt (fun b => if fSrc b then extern b else None) 
  end.

Lemma EraseUnknown_unknown: forall mu, 
      unknown_of (EraseUnknown mu) = fun b => None.
Proof. intros. destruct mu. simpl.
  extensionality b.
  destruct (locBlocksSrc0 b); trivial.
  destruct (frgnBlocksSrc0 b); trivial.
Qed.

Lemma EraseUnknown_foreign: forall mu,
      foreign_of (EraseUnknown mu) = foreign_of mu.
Proof. intros. destruct mu. simpl.
  extensionality b.
  destruct (frgnBlocksSrc0 b); trivial.
Qed.

Lemma EraseUnknown_extern: forall mu,
      extern_of (EraseUnknown mu) = 
      (fun b => if frgnBlocksSrc mu b then extern_of mu b else None).
Proof. intros. destruct mu. simpl. reflexivity.
Qed.

Lemma EraseUnknown_local: forall mu,
      local_of (EraseUnknown mu) = local_of mu.
Proof. intros. destruct mu. simpl. reflexivity.
Qed.

Lemma EraseUnknown_pub: forall mu,
      pub_of (EraseUnknown mu) = pub_of mu.
Proof. intros. destruct mu. simpl. reflexivity.
Qed.

Lemma EraseUnknown_priv: forall mu,
      priv_of (EraseUnknown mu) = priv_of mu.
Proof. intros. destruct mu. simpl. reflexivity.
Qed.

Lemma EraseUnknown_shared: forall mu,
      shared_of (EraseUnknown mu) = shared_of mu.
Proof. intros. unfold shared_of; simpl. 
  rewrite EraseUnknown_pub.  
  rewrite EraseUnknown_foreign.
  trivial.
Qed.

Lemma EraseUnknown_locvisible: forall mu,
      locvisible_of (EraseUnknown mu) = locvisible_of mu.
Proof. intros. unfold locvisible_of; simpl. 
  rewrite EraseUnknown_local.  
  rewrite EraseUnknown_foreign.
  trivial.
Qed.

Definition TrimUnknown (mu : SM_Injection) : SM_Injection :=
  match mu with
  Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern =>
  Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt
             (fun b => match extern b with
                           None => None
                         | Some(b',d) => if fTgt b'
                                         then Some(b',d) else None
                       end)
  end.

Lemma TrimUnknown_unknown: forall mu, 
      unknown_of (TrimUnknown mu) = 
      fun b => match unknown_of mu b with
                 None => None
              | Some(b',d) => if frgnBlocksTgt mu b' 
                              then Some(b',d) else None
               end.
Proof. intros. destruct mu. simpl.
  extensionality b.
  destruct (locBlocksSrc0 b); trivial.
  destruct (frgnBlocksSrc0 b); trivial.
Qed.

Lemma TrimUnknown_foreign: forall mu (WD: SM_wd mu),
      foreign_of (TrimUnknown mu) = foreign_of mu.
Proof. intros. destruct mu. simpl.
  extensionality b.
  remember (frgnBlocksSrc0 b) as d. 
  destruct d; trivial. apply eq_sym in Heqd.
  destruct (frgnSrc _ WD _ Heqd) as [b' [delta [F FT]]].
  simpl in *.
  rewrite Heqd in F. rewrite F. rewrite FT. trivial.
Qed.

Lemma TrimUnknown_extern: forall mu,
      extern_of (TrimUnknown mu) = 
      (fun b => match extern_of mu b with
                 None => None
              | Some(b',d) => if frgnBlocksTgt mu b' 
                              then Some(b',d) else None
               end). 
Proof. intros. destruct mu. simpl. reflexivity.
Qed.

Lemma TrimUnknown_local: forall mu,
      local_of (TrimUnknown mu) = local_of mu.
Proof. intros. destruct mu. simpl. reflexivity.
Qed.

Lemma TrimUnknown_pub: forall mu,
      pub_of (TrimUnknown mu) = pub_of mu.
Proof. intros. destruct mu. simpl. reflexivity.
Qed.

Lemma TrimUnknown_priv: forall mu,
      priv_of (TrimUnknown mu) = priv_of mu.
Proof. intros. destruct mu. simpl. reflexivity.
Qed.

Lemma TrimUnknown_shared: forall mu(WD: SM_wd mu),
      shared_of (TrimUnknown mu) = shared_of mu.
Proof. intros. unfold shared_of; simpl. 
  rewrite TrimUnknown_pub.  
  rewrite TrimUnknown_foreign; trivial.
Qed.

Lemma TrimUnknown_locvisible: forall mu(WD: SM_wd mu),
      locvisible_of (TrimUnknown mu) = locvisible_of mu.
Proof. intros. unfold locvisible_of; simpl. 
  rewrite TrimUnknown_local.  
  rewrite TrimUnknown_foreign; trivial.
Qed.

Lemma Trim_extern_normalize: forall mu12 mu23
          (WD12: SM_wd mu12) (WD23: SM_wd mu23)
          (HypFrgn: forall b, frgnBlocksTgt mu12 b = true -> 
                              frgnBlocksSrc mu23 b = true),
  inject_incr (as_inj (TrimUnknown mu12)) 
              (as_inj (sm_extern_normalize mu12 mu23)).
Proof. intros. unfold as_inj. intros b1; intros.
  rewrite TrimUnknown_local, TrimUnknown_extern in H.
  rewrite sm_extern_normalize_local, sm_extern_normalize_extern.
  apply joinI.
  destruct (joinD_Some _ _ _ _ _ H) as [EXT | [EXT LOC]]; clear H.
    left. unfold normalize.
    remember (extern_of mu12 b1) as d.
    destruct d; trivial. destruct p; apply eq_sym in Heqd.
    remember (frgnBlocksTgt mu12 b) as q.
    destruct q; inv EXT; apply eq_sym in Heqq.
      apply HypFrgn in Heqq.
      destruct (frgnSrc _ WD23 _ Heqq) as [b3 [delta3 [F FT]]].
      rewrite (foreign_in_extern _ _ _ _ F). trivial.
  right. split; trivial.
    unfold normalize.
    destruct (disjoint_extern_local _ WD12 b1); rewrite H in *. trivial. inv LOC.
Qed.

Lemma Trim_extern_normalize2: forall mu12 
          (WD12: SM_wd mu12),
  exists mu23, SM_wd mu23 /\ 
               (forall b, frgnBlocksTgt mu12 b = true -> 
                          frgnBlocksSrc mu23 b = true) /\
               (TrimUnknown mu12) = (sm_extern_normalize mu12 mu23).
Proof. intros. 
  exists (Build_SM_Injection (locBlocksTgt mu12) (locBlocksTgt mu12)
                             (pubBlocksTgt mu12) (pubBlocksTgt mu12)
                             (fun b => if locBlocksTgt mu12 b then Some(b,0) else None)
                             (extBlocksTgt mu12) (extBlocksTgt mu12) 
                             (frgnBlocksTgt mu12) (frgnBlocksTgt mu12) 
                             (fun b => if frgnBlocksTgt mu12 b then Some(b,0) else None)).  
split; simpl; intros.
  (*WD*)
  split; simpl; intros; try solve[eapply WD12].
  remember (locBlocksTgt mu12 b1) as d.
    destruct d; inv H; intuition. 
  remember (frgnBlocksTgt mu12 b1) as d.
     destruct d; inv H. apply eq_sym in Heqd.
     rewrite (frgnBlocksExternTgt _ WD12 _ Heqd). intuition.
  rewrite H. rewrite (pubBlocksLocalTgt _ WD12 _ H).
     exists b1, 0. intuition.
  rewrite H. exists b1, 0. intuition.
  apply (pubBlocksLocalTgt _ WD12 _ H). 
  apply (frgnBlocksExternTgt _ WD12 _ H). 
split; intros.
  assumption.
unfold TrimUnknown, sm_extern_normalize; simpl.
  destruct mu12; simpl. f_equal.
  extensionality b. unfold normalize.
  remember (extern_of0 b) as d.
  destruct d; trivial. destruct p.
  destruct (frgnBlocksTgt0 b0); trivial.
Qed.

(*Construction used in make_initial_core: put incoming injection
  into foreign/unknown component as specified, initialize local_of,
  locBlocksSrc/Tgt, and pubBlocksSrc/Tgt as empty*)
Definition initial_SM (extS extT frgnS frgnT: block->bool) 
                     (extern:meminj): SM_Injection :=
  Build_SM_Injection 
      (*locBlocksSrc/Tgt:*) (fun b => false) (fun b => false)
      (*pubBlocksSrc/Tgt:*)(fun b => false) (fun b => false) 
      (*local:*)(fun b => None)
      (*extBlocksSrc/Tgt:*) extS extT
      (*frgnBlocksSrc/Tgt:*) frgnS frgnT
      extern.

Lemma initial_SM_wd: forall extS extT frgnS frgnT extern
                       (EXT: forall b1 b2 d, extern b1 =Some(b2,d) -> 
                            extS b1 = true /\ extT b2 = true)
                       (F: forall b1, frgnS b1 = true -> 
                           exists b2 z, extern b1 = Some (b2, z) /\ frgnT b2 = true)
                       (FS: forall b, frgnS b = true -> extS b = true)
                       (FT: forall b, frgnT b = true -> extT b = true),
                       SM_wd (initial_SM extS extT frgnS frgnT extern). 
Proof. intros.
constructor; unfold initial_SM; simpl in *; intros; try (solve [inv H]).
  left; trivial.
  left; trivial.
  destruct (EXT _ _ _ H). auto. 
  rewrite H. auto. 
  auto.
Qed. 

Lemma initial_SM_as_inj: forall extS extT frgnS frgnT j,
      as_inj (initial_SM extS extT frgnS frgnT j) = j.
Proof. intros.
  unfold as_inj; simpl. extensionality b. 
  unfold join. destruct (j b); intuition.
Qed.