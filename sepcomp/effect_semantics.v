Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.

Require Import Axioms.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.StructuredInjections.

Lemma unch_on_validblock: forall m m' (U V: Values.block -> Z -> Prop)
   (UV: forall b ofs, Mem.valid_block m b -> (U b ofs -> V b ofs)),
   Mem.unchanged_on V m m' -> Mem.unchanged_on U m m'.
  Proof. intros.
    destruct H.
    split; intros. 
       eapply unchanged_on_perm; try eassumption. eauto.
       eapply unchanged_on_contents; try eassumption. 
       apply Mem.perm_valid_block in H0. eauto.
Qed.

Lemma unch_on_validblock_invariant: forall m m' U V
   (UV: forall b ofs, Mem.valid_block m b -> (U b ofs <-> V b ofs)),
   Mem.unchanged_on V m m' <-> Mem.unchanged_on U m m'.
  Proof. intros.
    split; intros. 
       eapply unch_on_validblock; try eassumption.
          intros. destruct (UV _ ofs H0). eauto.
       eapply unch_on_validblock; try eassumption.
          intros. destruct (UV _ ofs H0). eauto.
Qed.

Lemma unch_on_perm_intersection: forall m m' U (Fwd: mem_forward m m'),
   Mem.unchanged_on U m m' <-> 
   Mem.unchanged_on (fun b z => U b z /\ Mem.perm m b z Max Nonempty)  m m'.
  Proof. intros.
    split; intros Hyp.
    split; intros; eapply Hyp; eauto. apply H. apply H.
    split; intros.
      remember (Mem.perm_dec m b ofs Max Nonempty).
      destruct s; clear Heqs.
         eapply Hyp; eauto.
      split; intros. exfalso. apply n; clear Hyp n.
         eapply Mem.perm_implies. eapply Mem.perm_max; eassumption. 
               apply perm_any_N.
        exfalso. apply n; clear Hyp n.
         eapply (Fwd _ H0).
           eapply Mem.perm_implies. eapply Mem.perm_max; eassumption. 
               apply perm_any_N.
     eapply Hyp; trivial.
       split; trivial.
        eapply Mem.perm_implies. eapply Mem.perm_max; eassumption. 
               apply perm_any_N.
Qed.


Lemma mem_unchanged_on_trans: forall m1 m2 m3 U
      (U1: Mem.unchanged_on U m1 m2) 
      (U2: Mem.unchanged_on U m2 m3)
      (Fwd12: mem_forward m1 m2),
  Mem.unchanged_on U m1 m3.
Proof. intros.
split; intros.
  split; intros.
    eapply U2; trivial. apply Fwd12; trivial.
    eapply U1; trivial.
  eapply U1; trivial. eapply U2; trivial. apply Fwd12; trivial.
destruct U1 as [P1 V1]; destruct U2 as [P2 V2].
  rewrite (V2 _ _ H).
    apply V1; trivial.
  apply P1; trivial. eapply Mem.perm_valid_block; eassumption.
Qed.
 
Record EffectSem {G C} :=
  { sem :> CoopCoreSem G C;

    effstep: G -> (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop;

    effax1: forall M g c m c' m',
       effstep g M c m c' m' ->
            corestep sem g c m c' m'  
         /\ Mem.unchanged_on (fun b ofs => M b ofs = false) m m';

    effax2: forall g c m c' m',
       corestep sem g c m c' m' ->
       exists M, effstep g M c m c' m';

    effstep_sub_val: forall g U V c m c' m'
         (UV: forall b ofs, Mem.valid_block m b -> 
              U b ofs = true -> V b ofs = true),
         effstep g U c m c' m' -> effstep g V c m c' m'
 }.

Section effsemlemmas.
  Context {G C:Type} (Sem: @EffectSem G C) (g:G).
(*
Lemma effstep_perm: forall M g c m c' m',
      effstep Sem g M c m c' m' -> 
      forall b ofs, M b ofs = true -> Mem.valid_block m b -> Mem.perm m b ofs Max Nonempty.
Proof. intros.
  apply effax in H.
  destruct H. apply H; assumption.
Qed.
*)
Lemma effstep_corestep: forall M g c m c' m',
      effstep Sem g M c m c' m' -> corestep Sem g c m c' m'. 
Proof. intros.
  apply effax1 in H. apply H.
Qed.

Lemma effstep_unchanged: forall M g c m c' m',
      effstep Sem g M c m c' m' -> 
      Mem.unchanged_on (fun b ofs => M b ofs = false) m m'.
Proof. intros.
  apply effax1 in H. apply H.
Qed.
(*
Lemma effstep_rev: forall M g c m c' m',
      corestep Sem g c m c' m' ->
      Mem.unchanged_on (fun b ofs => M b ofs = false) m m' ->
      (forall b ofs, M b ofs = true -> Mem.valid_block m b) -> 
      effstep Sem g M c m c' m'.
Proof. intros.
  apply effax. 
  split; trivial.
Qed.
*)
  Lemma effstep_fwd: forall U c m c' m',
    effstep Sem g U c m c' m' -> mem_forward m m'.
  Proof. intros. destruct Sem.
         eapply corestep_fwd. eapply effax1. apply H.
  Qed.

Lemma effstep_sub: forall U V c m c' m'
         (UV: forall b ofs, U b ofs = true -> V b ofs = true),
         (effstep Sem g U c m c' m' -> effstep Sem g V c m c' m').
Proof. intros. eapply (effstep_sub_val _ _ U V). intuition. assumption.
Qed.
(*
Lemma effstep_sub_val: forall U V c m c' m'
         (UV: forall b ofs, Mem.valid_block m b -> U b ofs = true -> V b ofs = true),
         (effstep Sem g U c m c' m' -> effstep Sem g V c m c' m').
Proof. intros. rewrite effax; rewrite effax in H.
  destruct H as [CS Unch].
      split; trivial.
      split; intros; eapply Unch; trivial.
          remember (U b ofs) as d.
          destruct d; try reflexivity. apply eq_sym in Heqd.
          rewrite (UV _ _ H0 Heqd) in H. inv H.

          remember (U b ofs) as d.
          destruct d; try reflexivity. apply eq_sym in Heqd.
          apply Mem.perm_valid_block in H0.
          rewrite (UV _ _ H0 Heqd) in H. inv H.
Qed.
*)         
(*
Record EffectSem {G C} :=
  { sem :> CoopCoreSem G C;

    effstep: G -> (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop;

    effax: forall M g c m c' m',
       effstep g M c m c' m' <->
       (corestep sem g c m c' m' /\ 
        Mem.unchanged_on (fun b ofs => M b ofs = false /\ Mem.perm m b ofs Max Nonempty) m m')
 }.

Record EffectSemA {G C} :=
  { semA :> CoopCoreSem G C;

    effstepA: G -> (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop;

    effaxA: forall M g c m c' m',
       effstepA g M c m c' m' <->
       (corestep semA g c m c' m' /\ 
        Mem.unchanged_on (fun b ofs => M b ofs = false) m m');
    effstep_perm: forall M g c m c' m',
       effstepA g M c m c' m' -> 
       forall b ofs, M b ofs = true -> Mem.perm m b ofs Max Nonempty
  }.
 

Goal forall G C, @EffectSem G C -> @EffectSemA G C.
Proof. intros. destruct X.
eapply Build_EffectSemA with (effstepA := effstep0)(semA:=sem0).
intros.
split; intros.
  split. eapply effax0. apply H.
  apply effax0 in H. destruct H.
  apply unch_on_perm_intersection in H0. apply H0.
  apply corestep_fwd in H. assumption.
destruct H.
  apply effax0; clear effax0.
  split; trivial.
  apply unch_on_perm_intersection. 
    apply corestep_fwd in H. assumption.
    apply H0.
Qed.
Goal forall G C, @EffectSemA G C -> @EffectSem G C.
Proof. intros. destruct X.
eapply Build_EffectSem with (effstep := effstepA0)(sem:=semA0).
intros.
split; intros.
  split. eapply effaxA0. apply H.
  apply effaxA0 in H. destruct H.
  apply unch_on_perm_intersection.
    apply corestep_fwd in H. assumption.
     apply H0.

  apply effaxA0. destruct H. split; trivial.
  apply unch_on_perm_intersection in H0. apply H0.
    apply corestep_fwd in H. assumption.

intros.
  apply effaxA0 in H. destruct H.
destruct H.
  apply effax0; clear effax0.
  split; trivial.
  apply unch_on_perm_intersection. 
    apply corestep_fwd in H. assumption.
    apply H0.
Qed.


But, since sem :> CoopCoreSem G C implies that 

Section effsemlemmas.
  Context {G C:Type} (Sem: @EffectSem G C) (g:G).

Lemma effstep_valid_block: forall U V c m c' m'
         (UV: forall b ofs, Mem.valid_block m b -> (U b ofs = V b ofs)),
         (effstep Sem g U c m c' m' <-> effstep Sem g V c m c' m').
Proof. intros.
  split; intros H; rewrite effax; rewrite effax in H;
    destruct H as [CS Unch]; split; trivial.
    split; intros; eapply Unch; trivial.
      rewrite (UV _ _ H0). apply H.
    apply Mem.perm_valid_block in H0.
      rewrite (UV _ _ H0). apply H.

    split; intros; eapply Unch; trivial.
      rewrite <- (UV _ _ H0). apply H.
    apply Mem.perm_valid_block in H0.
      rewrite <- (UV _ _ H0). apply H.
Qed.
  *)
(*
Lemma effchar: forall c m c' m' Mod, 
 effstep sem g Mod c m c' m' <->
    ( corestep sem g c m c' m' /\
      forall b ofs, Mod b ofs = true \/ 
       Mem.unchanged_on (fun bb z => bb=b /\ z=ofs) m m').
Proof. intros.
split; intros.
  apply effax in H. destruct H.
  split; intros; trivial.
  remember  (Mod b ofs) as d.
  destruct d; apply eq_sym in Heqd.
    left; trivial.
  right.
  destruct H0.
  split; intros.
    destruct H0; subst. auto.
    destruct H0; subst.
    apply unchanged_on_contents.
    apply Mem.perm_valid_block in H1. auto.
    assumption.
apply effax. destruct H.
  split; trivial.
  split; intros.
     destruct (H0 b ofs) as [HMod | Hunch].
        rewrite HMod in H1; intuition. 
     eapply Hunch; auto.
  destruct (H0 b ofs) as [HMod | Hunch].
        rewrite HMod in H1; intuition. 
     eapply Hunch; auto.
Qed.
*)
(*
Lemma effchar': forall {G C} (sem : @EffectSem G C) (g:G)
    c m c' m' Mod, effstep sem g Mod c m c' m' <->
    ( corestep sem g c m c' m' /\
      forall b ofs, Mem.valid_block m b ->
       Mod b ofs = true \/ 
       Mem.unchanged_on (fun bb z => bb=b /\ z=ofs) m m').
Proof. intros.
split; intros.
  apply effax in H. destruct H.
  split; intros; trivial.
  remember  (Mod b ofs) as d.
  destruct d; apply eq_sym in Heqd.
    left; trivial.
  right.
  destruct H0.
  split; intros.
    destruct H0; subst. auto.
    destruct H0; subst. auto.
apply effax. destruct H.
  split; trivial.
  split; intros.
     specialize (H1 H2).
     destruct (H0 b ofs H2) as [HMod | Hunch].
        rewrite HMod in H1; intuition. 
     eapply Hunch; auto.
  assert (VB:= Mem.perm_valid_block _ _ _ _ _ H2).
  destruct (H0 b ofs VB) as [HMod | Hunch].
        rewrite HMod in H1; intuition. 
     eapply Hunch; auto.
Qed.
    
*)(*
  Lemma effstep_sub: forall c m c' m' (U V : block -> Z -> bool),
     effstep Sem g U c m c' m' ->
     (forall b z, V b z = true -> Mem.valid_block m b -> Mem.perm m b z Max Nonempty) -> 
     (forall b z, U b z = true -> V b z = true) ->
     effstep Sem g V c m c' m'.
  Proof. intros.
    rewrite effax. rewrite effax in H.
    destruct H as [Perm [CS Unch]].
    split; trivial. 
    split; trivial.
      split; intros; eapply Unch; trivial.
         remember (U b ofs) as d.
         destruct d; trivial; apply eq_sym in Heqd.
         rewrite (H1 _ _ Heqd) in H. inv H.

         remember (U b ofs) as d.
         destruct d; trivial; apply eq_sym in Heqd.
         rewrite (H1 _ _ Heqd) in H. inv H.
  Qed.*)
(*
  Lemma effstep_sub: forall c m c' m' (U V : block -> Z -> bool),
     effstep Sem g U c m c' m' ->
     (forall b z, U b z = true -> V b z = true) ->
     effstep Sem g V c m c' m'.
  Proof. intros. apply effchar in H. apply effchar. 
     destruct H. split; trivial.
     intros.
     destruct (H1 b ofs); auto.
  Qed.
*)
  Fixpoint effstepN (n:nat) : (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop :=
    match n with
      | O => fun U c m c' m' => (c,m) = (c',m')
      | S k => fun U c1 m1 c3 m3 => exists c2, exists m2,
        effstep Sem g U c1 m1 c2 m2 /\
        effstepN k (fun b ofs => U b ofs  || freshloc m1 m2 b)  c2 m2 c3 m3
    end.

  Lemma effstepN_fwd: forall n U c m c' m',
    effstepN n U c m c' m' -> mem_forward m m'.
  Proof. intros n.
         induction n; intros; simpl in *.
           inv H. eapply mem_forward_refl.
         destruct H as [c1 [c2 [Eff1 Eff2]]].
         eapply mem_forward_trans.
           eapply effstep_fwd; eassumption.
           eapply IHn; eassumption. 
  Qed.

  Lemma effstepN_corestepN: forall n E c m c' m',
      effstepN n E c m c' m' -> corestepN Sem g n c m c' m'. 
  Proof. intros n.
    induction n; intros.
      inv H. constructor.
      destruct H as [c1 [m1 [Estep EN]]].
        apply effstep_corestep in Estep.
        apply IHn in EN. econstructor.
        exists m1. split; eassumption.
  Qed.

  Lemma effstepN_unchanged: forall n U c1 m1 c2 m2,
        effstepN n U c1 m1 c2 m2 -> 
        Mem.unchanged_on (fun b z => U b z = false) m1 m2.
  Proof. intros n.
    induction n; simpl; intros.
      inv H. apply Mem.unchanged_on_refl.
    rename c2 into c3. rename m2 into m3.
    destruct H as [c2 [m2 [E EN]]].
    apply IHn in EN; clear IHn.
    assert (FWD:= effstep_fwd _ _ _ _ _ E).
    apply effstep_unchanged in E.
    split; intros.
     split; intros. apply EN. rewrite H; simpl.
        apply freshloc_charF. left; assumption.
        apply (FWD _ H0). 
     apply E; try assumption.

     apply E; try assumption.
       apply EN; try assumption. rewrite H; simpl.
        apply freshloc_charF. left; assumption.
        apply (FWD _ H0).

     destruct EN. rewrite unchanged_on_contents.
        apply E; try eassumption.  rewrite H; simpl.
        apply freshloc_charF. apply Mem.perm_valid_block in H0. left; assumption.
       apply E; try assumption. apply Mem.perm_valid_block in H0. apply H0.
Qed.

(*
  Lemma effstepN_perm: forall n M c m c' m'
       (Step: effstepN n M c m c' m'),
       (c,m) = (c',m') \/
       (forall b ofs, M b ofs = true -> Mem.valid_block m b -> Mem.perm m b ofs Max Nonempty).
  Proof. intros n.
     induction n; simpl; intros. left; assumption. 
     destruct Step as [c2 [m2 [Step StepN]]]. 
     right. intros. eapply effstep_perm; eassumption.
  Qed.

  Lemma effstepSN_perm: forall n M c m c' m'
       (Step: effstepN (S n) M c m c' m'),
       forall b ofs, M b ofs = true -> Mem.valid_block m b -> Mem.perm m b ofs Max Nonempty.
  Proof. intros. 
     destruct Step as [c2 [m2 [Step StepN]]]. 
     eapply effstep_perm; eassumption.
  Qed.
*)

  Lemma effstepN_sub: forall n U V c m c' m'
         (UV: forall b ofs, U b ofs = true -> V b ofs = true),
         (effstepN n U c m c' m' -> effstepN n V c m c' m').
  Proof. intros n.
    induction n; simpl; intros; trivial.
    rename c' into c3. rename m' into m3.
    destruct H as [c2 [m2 [E EN]]].
    exists c2, m2.
    split. eapply effstep_sub; eassumption.
      eapply IHn; try eassumption.
      simpl; intros.
      apply orb_true_iff. apply orb_true_iff in H.
      destruct H; eauto.
  Qed.

  Lemma effstepN_add : forall n m U c1 m1 c3 m3,
    effstepN (n+m) U c1 m1 c3 m3 <->
    exists c2, exists m2,
      effstepN n U c1 m1 c2 m2 /\
      effstepN m (fun b z => U b z || freshloc m1 m2 b) c2 m2 c3 m3.
  Proof.
    induction n; simpl; intuition.
     exists c1, m1; split; trivial.
       eapply effstepN_sub; try eassumption.
       intros. intuition. 
     destruct H as [c2 [m2 [EQ EN]]]. inv EQ. 
       eapply effstepN_sub; try eassumption.
       simpl; intros. rewrite freshloc_irrefl in H.
       rewrite orb_false_r in H. assumption.
     destruct H as [c2 [m2 [E EN]]].
       rename c3 into c4. rename m3 into m4.
       apply IHn in EN; clear IHn.
       destruct EN as [c3 [m3 [En Em]]].
       exists c3, m3; split.
         exists c2, m2; split; trivial.
         eapply effstepN_sub; try eassumption.
           simpl; intros.
           apply effstep_fwd in E.
           apply effstepN_fwd in En. clear Em.
           rewrite <- orb_assoc in H.
           rewrite freshloc_trans in H; trivial.
     rename c3 into c4. rename m3 into m4.
       destruct H as [c3 [m3 [E Em]]].
       destruct E as [c2 [m2 [E En]]].
       exists c2, m2; split; trivial.
         eapply IHn; clear IHn.
         exists c3, m3; split; trivial.
         eapply effstepN_sub; try eassumption.
           simpl; intros.
           apply effstep_fwd in E.
           apply effstepN_fwd in En. clear Em.
           rewrite <- orb_assoc.
           rewrite freshloc_trans; trivial.
  Qed.
(*
  Lemma effstepN_add : forall n m U c1 m1 c3 m3,
    effstepN (n+m) U c1 m1 c3 m3 <->
    exists c2, exists m2,
      effstepN n U c1 m1 c2 m2 /\
      effstepN m U c2 m2 c3 m3.
  Proof.
    induction n; simpl; intuition.
    firstorder. firstorder.
    inv H. auto.
    decompose [ex and] H. clear H.
    destruct (IHn m U x x0 c3 m3).
    apply H in H2. 
    decompose [ex and] H2. clear H2.
    repeat econstructor; eauto.
    decompose [ex and] H. clear H.
    exists x1. exists x2; split; auto.
    destruct (IHn m U x1 x2 c3 m3). 
    eauto.
  Qed.
*)

  Definition effstep_plus U c m c' m' :=
    exists n, effstepN (S n) U c m c' m'.

  Definition effstep_star U c m c' m' :=
    exists n, effstepN n U c m c' m'.

  Lemma effstep_plus_star : forall U c1 c2 m1 m2,
    effstep_plus U c1 m1 c2 m2 -> effstep_star U c1 m1 c2 m2.
  Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma effstep_plus_trans : forall U c1 c2 c3 m1 m2 m3,
    effstep_plus U c1 m1 c2 m2 -> effstep_plus U c2 m2 c3 m3 -> 
    effstep_plus U c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (effstepN_add (S n1) (S n2) U c1 m1 c3 m3) as [_ H].
    eexists. apply H. exists c2. exists m2. split; try assumption.
    eapply effstepN_sub; try eassumption.
    simpl; intros. rewrite H0; trivial.
  Qed.

  Lemma effstep_star_plus_trans : forall U c1 c2 c3 m1 m2 m3,
    effstep_star U c1 m1 c2 m2 -> effstep_plus U c2 m2 c3 m3 -> 
    effstep_plus U c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (effstepN_add n1 (S n2) U c1 m1 c3 m3) as [_ H]. 
    rewrite <- plus_n_Sm in H.
    eexists. apply H.  exists c2. exists m2.  split; try assumption.
    eapply effstepN_sub; try eassumption.
    simpl; intros. rewrite H0; trivial.
  Qed.

  Lemma effstep_plus_star_trans: forall U c1 c2 c3 m1 m2 m3,
    effstep_plus U c1 m1 c2 m2 -> effstep_star U c2 m2 c3 m3 -> 
    effstep_plus U c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (effstepN_add (S n1) n2 U c1 m1 c3 m3) as [_ H]. 
    rewrite plus_Sn_m in H.
    eexists. apply H.  exists c2. exists m2. split; try assumption.
    eapply effstepN_sub; try eassumption.
    simpl; intros. rewrite H0; trivial.
  Qed.

  Lemma effstep_star_trans: forall U c1 c2 c3 m1 m2 m3, 
    effstep_star U c1 m1 c2 m2 -> effstep_star U c2 m2 c3 m3 -> 
    effstep_star U c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (effstepN_add n1 n2 U c1 m1 c3 m3) as [_ H]. 
    eexists. apply H.  exists c2. exists m2. split; try assumption.
    eapply effstepN_sub; try eassumption.
    simpl; intros. rewrite H0; trivial.
  Qed.

  Lemma effstep_plus_one: forall U c m c' m',
    effstep Sem g U c m c' m' -> effstep_plus U c m c' m'.
  Proof. intros. unfold effstep_plus, effstepN. simpl.
    exists O. exists c'. exists m'. eauto. 
  Qed.

  Lemma effstep_plus_two: forall U c m c' m' c'' m'',
    effstep  Sem g U c m c' m' -> effstep Sem g U c' m' c'' m'' -> 
    effstep_plus U c m c'' m''.
  Proof. intros. 
    exists (S O). exists c'. exists m'. split; trivial. 
    exists c''. exists m''. 
    split. eapply effstep_sub; try eassumption; intuition.
           reflexivity. 
  Qed.

  Lemma effstep_star_zero: forall U c m, effstep_star U c m c m.
  Proof. intros. exists O. reflexivity. Qed.

  Lemma effstep_star_one: forall U c m c' m',
    effstep  Sem g U c m c' m' -> effstep_star U c m c' m'.
  Proof. intros. 
    exists (S O). exists c'. exists m'. split; trivial. reflexivity. 
  Qed.

  Lemma effstep_plus_split: forall U c m c' m',
    effstep_plus U c m c' m' ->
    exists c'', exists m'', effstep Sem g U c m c'' m'' /\ 
      effstep_star (fun b z => U b z || freshloc m m'' b) c'' m'' c' m'.
  Proof. intros.
    destruct H as [n [c2 [m2 [Hstep Hstar]]]]. simpl in*. 
    exists c2. exists m2. split. assumption. exists n. assumption.
  Qed.

  Lemma effstep_star_fwd: forall U c m c' m',
    effstep_star U c m c' m' -> mem_forward m m'.
  Proof. intros. destruct H as [n H]. 
      eapply effstepN_fwd; eassumption.
  Qed.

  Lemma effstep_plus_fwd: forall U c m c' m',
    effstep_plus U c m c' m' -> mem_forward m m'.
  Proof. intros. destruct H as [n H]. 
      eapply effstepN_fwd; eassumption.
  Qed.

  Lemma effstep_plus_sub: forall c m c' m' (U V : block -> Z -> bool),
     effstep_plus U c m c' m' ->
     (forall b z, U b z = true -> V b z = true) ->
     effstep_plus V c m c' m'.
  Proof. intros.
    destruct H as [n H].
    exists n. eapply effstepN_sub; eassumption.
  Qed. 

  Lemma effstep_star_sub: forall c m c' m' (U V : block -> Z -> bool),
     effstep_star U c m c' m' ->
     (forall b z, U b z = true -> V b z = true) ->
     effstep_star V c m c' m'.
  Proof. intros.
    destruct H as [n H].
    exists n. eapply effstepN_sub; eassumption.
  Qed. 

  Lemma effstepN_sub_val: forall n c m c' m' (U V : block -> Z -> bool),
     effstepN n U c m c' m' ->
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstepN n V c m c' m'.
  Proof. intros n. 
     induction n; simpl; intros.
        apply H.
    rename c' into c3. rename m' into m3.
    destruct H as [c2 [m2 [E EN]]].
    exists c2, m2.
    split. eapply effstep_sub_val; eassumption.
      eapply IHn; try eassumption.
      simpl; intros.
      apply orb_true_iff. apply orb_true_iff in H1.
      remember (freshloc m m2 b) as d.
      destruct d; try (right; reflexivity); apply eq_sym in Heqd.
      destruct H1; try (right; assumption). left.
      apply freshloc_charF in Heqd. destruct Heqd; intuition.
  Qed.

  Lemma effstep_plus_sub_val: forall c m c' m' (U V : block -> Z -> bool),
     effstep_plus U c m c' m' ->
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstep_plus V c m c' m'.
  Proof. intros.
    destruct H as [n H].
    exists n. eapply effstepN_sub_val; eassumption.
  Qed. 

  Lemma effstep_star_sub_val: forall c m c' m' (U : block -> Z -> bool)
     (EFF: effstep_star U c m c' m') (V : block -> Z -> bool),
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstep_star V c m c' m'.
  Proof. intros.
    destruct EFF as [n EFF].
    exists n. eapply effstepN_sub_val; eassumption.
  Qed. 
(*
  Lemma effstep_sub_valid: forall c m c' m' (U V : block -> Z -> bool),
     effstep Sem g U c m c' m' ->
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstep Sem g V c m c' m'.
  Proof. intros.
    rewrite effax. rewrite effax in H. destruct H as [CS Unch].
    split; trivial.
    split; intros; eapply Unch; trivial. 
        remember (U b ofs) as d.
        destruct d; trivial; apply eq_sym in Heqd.
        rewrite (H0 _ _ H1 Heqd) in H. inv H.
    remember (U b ofs) as d.
        destruct d; trivial; apply eq_sym in Heqd.
        apply Mem.perm_valid_block in H1. 
        rewrite (H0 _ _ H1 Heqd) in H. inv H.
   Qed.
    
    
    apply (effstep_valid_block Sem U (fun b ofs => if valid_block_dec m b then U b ofs else false)) in H.
    apply effchar in H. apply effchar. 
     destruct H. split; trivial.
     intros.
     destruct (H1 b ofs); eauto.
     left.
      case_eq (valid_block_dec m b); intros; rewrite H3 in H2.
        auto.
       discriminate.
     intros. 
      case_eq (valid_block_dec m b); intros. trivial. contradiction.
  Qed.

  Lemma effstep_plus_perm: forall M c m c' m'
       (Step: effstep_plus M c m c' m'),
       forall b ofs, M b ofs = true -> Mem.perm m b ofs Max Nonempty.
  Proof. intros. 
     destruct Step as [n Stepn]. 
     eapply effstepSN_perm; eassumption.
  Qed.

  Lemma effstep_star_perm: forall M c m c' m'
       (Step: effstep_star M c m c' m'),
       (c,m) = (c',m') \/
       (forall b ofs, M b ofs = true -> Mem.perm m b ofs Max Nonempty).
  Proof. intros. 
     destruct Step as [n Stepn]. 
     eapply effstepN_perm; eassumption.
  Qed.
*)
(*
  Lemma eff_comp: forall n n' M M' c m c' m' c'' m'' 
    (EX1: effstepN n M c m c' m') (EX2: effstepN n' M' c' m' c'' m''),
    effstepN (n+n') (fun b ofs => if M b ofs then true 
                            else if M' b ofs then valid_block_dec m b else false)
              c m c'' m''.
  Proof. intros n.
         induction n; simpl; intros.
           inv EX1. eapply effstepN_sub. eassumption.
           intros. remember (M b z) as d.
           destruct d. trivial.
           rewrite H. admit. admit is OK - it's in a comment
         rewrite effchar in EX1, EX2. rewrite effchar.
         destruct 

  Lemma effstepN_valid_block_aux: forall n m0 U V c m c' m'
         (UV: forall b ofs, Mem.valid_block m0 b -> (U b ofs = V b ofs)),
         mem_forward m0 m ->
         (effstepN n (fun b ofs => if valid_block_dec m0 b then U b ofs else false) c m c' m' <-> 
          effstepN n (fun b ofs => if valid_block_dec m0 b then V b ofs else false) c m c' m').
  Proof. intros n.
    induction n; simpl; intros.
      split; intros; assumption.
    split; intros.
      destruct H0 as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply effstep_valid_block; try eassumption.
             intros. simpl. 
             remember (valid_block_dec m0 b) as d.
             destruct d; trivial. 
             rewrite UV; trivial.
      eapply IHn; try eassumption.
        intros. rewrite UV; trivial.
      apply effstep_fwd in Step.
        eapply mem_forward_trans; eassumption.
    destruct H0 as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply effstep_valid_block; try eassumption.
             intros. simpl. 
             remember (valid_block_dec m0 b) as d.
             destruct d; trivial. 
             rewrite UV; trivial.
      eapply IHn; try eassumption.
      apply effstep_fwd in Step.
        eapply mem_forward_trans; eassumption.
Qed.
  Lemma effstepN_valid_block_aux1: forall n P U V 
         (UV: forall b ofs, P b ofs = true -> (U b ofs = V b ofs))
         (Hyp: forall c m c' m',effstep Sem g (fun b ofs => if P b ofs then U b ofs else false) c m c' m' <-> 
                   effstep Sem g (fun b ofs => if P b ofs then V b ofs else false) c m c' m')
         c m c' m',
        (effstepN n (fun b ofs => if P b ofs then U b ofs else false) c m c' m' <-> 
          effstepN n (fun b ofs => if P b ofs then V b ofs else false) c m c' m').
  Proof. intros n.
    induction n; simpl; intros.
      split; intros; assumption.
    split; intros.
      destruct H as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply Hyp; try eassumption.
      eapply IHn; simpl.
        intros. rewrite UV; trivial.
        intros. rewrite Hyp. split; intros; trivial.
      apply StepN.
    destruct H as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply Hyp; try eassumption.
      eapply IHn; simpl.
        intros. rewrite UV; trivial.
        intros. rewrite Hyp. split; intros; trivial.
      apply StepN.
Qed.
*)
(*

  Lemma effstepN_valid_block_aux1: forall n m0 U V c m c' m'
         (UV: forall b ofs, Mem.valid_block m0 b -> (U b ofs = V b ofs)),
         mem_forward m0 m' ->
         (effstepN n (fun b ofs => if valid_block_dec m0 b then U b ofs else false) c m c' m' <-> 
          effstepN n (fun b ofs => if valid_block_dec m0 b then V b ofs else false) c m c' m').
  Proof. intros n.
    induction n; simpl; intros.
      split; intros; assumption.
    split; intros.
      destruct H0 as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply effstep_valid_block; try eassumption.
             intros. simpl. 
             remember (valid_block_dec m0 b) as d.
             destruct d; trivial. 
             rewrite UV; trivial.
      eapply IHn; try eassumption.
        intros. rewrite UV; trivial.
      apply effstep_fwd in Step.
        eapply mem_forward_trans; eassumption.
    destruct H0 as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply effstep_valid_block; try eassumption.
             intros. simpl. 
             remember (valid_block_dec m0 b) as d.
             destruct d; trivial. 
             rewrite UV; trivial.
      eapply IHn; try eassumption.
      apply effstep_fwd in Step.
        eapply mem_forward_trans; eassumption.
Qed.

  Lemma effstepN_valid_block_aux': forall n m0 U V c m c' m'
         (UV: forall b ofs, Mem.valid_block m0 b -> (U b ofs = V b ofs)),
         mem_forward m0 m ->
         (effstepN n U c m c' m' <-> 
          effstepN n V c m c' m').
  Proof. intros.
    induction n; simpl; intros.
      split; intros; assumption.
    split; intros.
      destruct H0 as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply effstep_valid_block; try eassumption.
             intros. simpl. 
             rewrite UV; trivial.
      eapply IHn; try eassumption.
        intros. rewrite UV; trivial.
      apply effstep_fwd in Step.
        eapply mem_forward_trans; eassumption.
    destruct H0 as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply effstep_valid_block; try eassumption.
             intros. simpl. 
             remember (valid_block_dec m0 b) as d.
             destruct d; trivial. 
             rewrite UV; trivial.
      eapply IHn; try eassumption.
      apply effstep_fwd in Step.
        eapply mem_forward_trans; eassumption.  intros n.
  Lemma effstepN_valid_block: forall n U V c m c' m'
         (UV: forall b ofs, Mem.valid_block m b -> (U b ofs = V b ofs)),
         (effstepN n U c m c' m' <-> 
          effstepN n V c m c' m').
  Proof. intros.
    destruct (effstepN_valid_block_aux n m U V c m c' m' UV (mem_forward_refl _)).
    split; intros.
      
     intros.
extensionality b. rewrite UV. trivial.
      eapply IHn; try eassumption. 

  Lemma effstepN_valid_block_aux: forall n m0 U V c m c' m'
         (UV: forall b ofs, Mem.valid_block m0 b -> (U b ofs = V b ofs)),
         mem_forward m0 m ->
         (effstepN n U c m c' m' <-> effstepN n V c m c' m').
  Proof. intros n.
    induction n; simpl; intros.
      split; intros; assumption.
    specialize (IHn m0 (fun b ofs => if valid_block_dec m0 b then U b ofs else false) (fun b ofs => if valid_block_dec m0 b then V b ofs else false)).
    split; intros.
      destruct H0 as [c2 [m2 [Step StepN]]].
      exists c2, m2.
      split. eapply effstep_valid_block; try eassumption.
             intros. rewrite UV. trivial.
      eapply IHn; try eassumption. 


  Lemma effstepN_sub_valid: 
  forall n c m c' m' (U V : block -> Z -> bool),
     effstepN n U c m c' m' ->
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstepN n V c m c' m'.
  Proof. intros n. 
    apply (effstep_valid_block Sem U (fun b ofs => if valid_block_dec m b then U b ofs else false)) in H.
    apply effchar in H. apply effchar. 
     destruct H. split; trivial.
     intros.
     destruct (H1 b ofs); eauto.
     left.
      case_eq (valid_block_dec m b); intros; rewrite H3 in H2.
        auto.
       discriminate.
     intros. 
      case_eq (valid_block_dec m b); intros. trivial. contradiction.
  Qed.
  Lemma effstepN_sub_valid: 
  forall n c m c' m' (U V : block -> Z -> bool),
     effstepN n U c m c' m' ->
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstepN n V c m c' m'.
  Proof. intros n. 
     induction n; simpl; intros.
        apply H.
     destruct H as [c2 [m2 [Step StepN]]].
     exists c2, m2; split.
       eapply effstep_sub_valid; try eassumption.
       specialize (IHn c2 m2 c' m' (fun b ofs => if valid_block_dec m b then U b ofs else true) V).
       eapply IHn; try eassumption.
         eapply effstepN_sub; try eassumption.
         intros. rewrite H.
         case_eq (valid_block_dec m b); intros; trivial.
       intros. apply effstep_fwd in Step.
         apply H0; auto.
  Qed.

  Lemma effstep_plus_sub_valid:
  forall c m c' m' (U V : block -> Z -> bool),
     effstep_plus U c m c' m' ->
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstep_plus V c m c' m'.
  Proof. intros.
    destruct H as [n H].
    exists n. eapply effstepN_sub; eassumption.
  Qed. 

  Lemma effstep_star_sub_valid:
  forall c m c' m' (U V : block -> Z -> bool),
     effstep_plus U c m c' m' ->
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstep_star V c m c' m'.
  Proof. intros.
    destruct H as [n H].
    exists (S n). eapply effstepN_sub; eassumption.
  Qed. 
*)
(*
Lemma effstep_validblock: forall U c m c' m'
        (E: effstep Sem g U c m c' m'),
         effstep Sem g (fun b z => if valid_block_dec m b then U b z else false) c m c' m'.
Proof. intros. rewrite effax; rewrite effax in E.
  destruct E as [CS Unch].
      split; trivial.
      split; intros; eapply Unch; trivial.
       remember (U b ofs) as d.
       destruct d; trivial; apply eq_sym in Heqd.
       remember (valid_block_dec m b) as d.
       destruct d. inv H. contradiction.

       remember (U b ofs) as d.
       destruct d; trivial; apply eq_sym in Heqd.
       remember (valid_block_dec m b) as d.
       destruct d. inv H. apply Mem.perm_valid_block in H0. contradiction.
Qed.

Lemma effstepN_validblock: forall n U c m c' m'
        (E: effstepN n U c m c' m'),
         effstepN n (fun b z => if valid_block_dec m b then U b z else false) c m c' m'.
Proof. intros n.
  induction n; simpl; intros. apply E.
  destruct E as [c2 [m2 [E EN]]].
  apply effstep_validblock in E.
  eexists. eexists. split. eassumption.
    assert (FWD: mem_forward m m2).
      eapply corestep_fwd. apply effax in E. apply E.
  clear E.
  assert (effstepN n ( c2 m2 c' m').
  eapply effstepN_sub. eassumption.
  intros. 
  remember (valid_block_dec m b). simpl in H.
  destruct s; clear Heqs.
    assert (FWD: mem_forward m m2).
      eapply corestep_fwd. apply effax in E. apply E.
    destruct (FWD _ v).  
    destruct (valid_block_dec m2 b). trivial. contradiction.
  remember (valid_block_dec m2 b).
  destruct s. admit. inv H. admit is OK - it's in a comment
  
 rewrite effax; rewrite effax in E.
  destruct E as [CS Unch].
      split; trivial.
      split; intros; eapply Unch; trivial.
       remember (U b ofs) as d.
       destruct d; trivial; apply eq_sym in Heqd.
       remember (valid_block_dec m b) as d.
       destruct d. inv H. contradiction.

       remember (U b ofs) as d.
       destruct d; trivial; apply eq_sym in Heqd.
       remember (valid_block_dec m b) as d.
       destruct d. inv H. apply Mem.perm_valid_block in H0. contradiction.
Qed.
*)

End effsemlemmas.


Definition EmptyEffect: Values.block -> Z -> bool := fun b z => false.

Lemma EmptyEffect_alloc: forall m lo hi m' b (ALLOC: Mem.alloc m lo hi = (m', b)),
      Mem.unchanged_on (fun b ofs => EmptyEffect b ofs = false) m m'.
Proof. intros.
       eapply Mem.alloc_unchanged_on; eassumption.
Qed. 

Definition FreeEffect m lo hi (sp b:Values.block) (ofs:Z): bool := 
   if valid_block_dec m b 
   then eq_block b sp && zle lo ofs && zlt ofs hi
   else false.

Lemma FreeEffect_free: forall m sp lo hi m'
             (FREE: Mem.free m sp lo hi = Some m'),
     Mem.unchanged_on  (fun b ofs => FreeEffect m lo hi sp b ofs = false) m m'.
Proof. intros.
       eapply Mem.free_unchanged_on; try eassumption.
               intros. unfold FreeEffect; simpl. intros N.
               destruct (valid_block_dec m sp).
               apply andb_false_iff in N. destruct H.
               destruct (eq_block sp sp); simpl in *.
                 destruct N. destruct (zle lo i). inv H1. xomega.
               destruct (zlt i hi). inv H1. xomega.
               apply n; trivial.
               apply Mem.free_range_perm in FREE.
                 apply n; clear n.
                 eapply Mem.perm_valid_block.
                 eapply (FREE lo). omega.
Qed. 

Definition FreelistEffect m (L: list (Values.block * Z * Z)) (b:Values.block) (ofs:Z): bool := 
  List.fold_right (fun X E b z => match X with (bb,lo,hi) =>
                                   E b z || FreeEffect m lo hi bb b z
                                 end) 
                 EmptyEffect L b ofs.

Lemma FreelistEffect_Dfalse: forall m bb lo hi L b ofs
      (F:FreelistEffect m ((bb, lo, hi) :: L) b ofs = false),
      FreelistEffect m L b ofs = false /\
      FreeEffect m lo hi bb b ofs = false. 
Proof. intros.
  unfold FreelistEffect in F. simpl in F.
  apply orb_false_iff in F. apply F.
Qed. 

Lemma FreelistEffect_Dtrue: forall m bb lo hi L b ofs
      (F:FreelistEffect m ((bb, lo, hi) :: L) b ofs = true),
      FreelistEffect m L b ofs = true \/
      FreeEffect m lo hi bb b ofs = true.
Proof. intros.
  unfold FreelistEffect in F. simpl in F.
  apply orb_true_iff in F. apply F.
Qed. 

Lemma FreelistEffect_same: forall m bb lo hi mm L
          (F:Mem.free m bb lo hi = Some mm)
          b (VB: Mem.valid_block mm b) ofs,
      FreelistEffect mm L b ofs = false <-> FreelistEffect m L b ofs = false.
Proof. intros  m bb lo hi mm L.
  induction L; simpl; intros. intuition.
  intuition. 
    apply orb_false_iff in H0. destruct H0.
    specialize (H _ VB ofs).
    apply H in H0. rewrite H0. simpl. clear H H0.
    unfold FreeEffect in *; simpl in *.
    apply Mem.nextblock_free in F. 
    destruct (valid_block_dec m b). 
      destruct (valid_block_dec mm b); trivial.
      red in v. rewrite <- F in v. elim n. apply v.
    trivial.
  apply orb_false_iff in H0. destruct H0.
    specialize (H _ VB ofs).
    apply H in H0. rewrite H0. simpl. clear H H0.
    unfold FreeEffect in *; simpl in *.
    apply Mem.nextblock_free in F. 
    destruct (valid_block_dec mm b). 
      destruct (valid_block_dec m b); trivial.
      red in v. rewrite F in v. elim n. apply v.
    trivial.
Qed.

Lemma FreelistEffect_freelist: forall L m m' (FL: Mem.free_list m L = Some m'),
      Mem.unchanged_on (fun b ofs => FreelistEffect m L b ofs = false) m m'.
Proof. intros L.
  induction L; simpl; intros.
    inv FL. apply Mem.unchanged_on_refl.
  destruct a as [[bb lo] hi].
    remember (Mem.free m bb lo hi) as d.
    destruct d; try inv FL. apply eq_sym in Heqd.
    specialize (IHL _ _ H0).
    assert (FF:= FreeEffect_free _ _ _ _ _ Heqd). 
    eapply (mem_unchanged_on_trans _ m0 _).
      eapply mem_unchanged_on_sub; try eassumption.
        intuition. apply orb_false_iff in H. apply H.
      clear FF.
      specialize (unch_on_validblock_invariant m0 m' (fun (b : block) (ofs : Z) => FreelistEffect m0 L b ofs = false) (fun (b : block) (ofs : Z) => FreelistEffect m L b ofs = false)).
      intros. apply H in IHL. clear H.
        eapply mem_unchanged_on_sub; try eassumption.
        intuition. apply orb_false_iff in H. apply H.
      clear IHL H. intros.
       eapply FreelistEffect_same; eassumption.
   eapply free_forward; eassumption.
Qed.

Definition StoreEffect (tv:val)(vl : list memval) (b:Values.block) (z:Z):bool := 
  match tv with Vptr bb ofs => eq_block bb b && 
             zle (Int.unsigned ofs) z && zlt z (Int.unsigned ofs + Z.of_nat (length vl))
         | _ => false
  end.

Lemma StoreEffect_Storev: forall m chunk tv tv' m' 
         (STORE : Mem.storev chunk m tv tv' = Some m'),
      Mem.unchanged_on (fun b ofs => StoreEffect tv (encode_val chunk tv') b ofs = false) m m'.
Proof. intros.
  destruct tv; inv STORE.
  unfold StoreEffect.
  split; intros.
      split; intros. eapply Mem.perm_store_1; eassumption.
      eapply Mem.perm_store_2; eassumption.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ H0). clear H0.
  destruct (eq_block b b0); subst; simpl in *.
    rewrite PMap.gss. apply andb_false_iff in H.  
    apply Mem.setN_outside.
    destruct H. destruct (zle (Int.unsigned i) ofs ); simpl in *. inv H.
                left. xomega.
    right. remember (Z.of_nat (length (encode_val chunk tv'))).
       destruct (zlt ofs (Int.unsigned i + z)); simpl in *. inv H. apply g.
  rewrite PMap.gso. trivial. intros N; subst. elim n; trivial. 
Qed.

Parameter BuiltinEffect : forall {F V: Type} (ge: Genv.t F V) (sg: signature) 
                    (vargs:list val) (m:mem), block -> Z -> bool.
(*
Axiom BUILTIN: forall (name: ident) (F V: Type) (ge: Genv.t F V) (sg: signature) 
                    (vargs:list val)
                       (m:mem) (t:trace) (v: val) (m': mem),
      extcall_io_sem name sg ge vargs m t v m' ->
      Mem.unchanged_on (fun b z => BuiltinEffect ge sg vargs m b z = false) m m'.
*)
Axiom ec_builtinEffectPolymorphic:
   forall {F V:Type} ef (g : Genv.t F V) vargs m t vres m',
   external_call ef g vargs m t vres m' ->
   Mem.unchanged_on (fun b z=> BuiltinEffect g (ef_sig ef) vargs m b z = false) m m'.