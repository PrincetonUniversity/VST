
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

Lemma unch_on_validblock_invariant: forall m m' U V
   (UV: forall b ofs, Mem.valid_block m b -> (U b ofs <-> V b ofs)),
   Mem.unchanged_on V m m' <-> Mem.unchanged_on U m m'.
  Proof. intros.
    split; intros Hyp; destruct Hyp.
    split; intros. 
       eapply unchanged_on_perm; try eassumption.
       destruct (UV _ ofs H0). eauto.

       eapply unchanged_on_contents; try eassumption.
       apply Mem.perm_valid_block in H0.
       destruct (UV _ ofs H0). eauto.
    split; intros. 
       eapply unchanged_on_perm; try eassumption.
       destruct (UV _ ofs H0). eauto.

       eapply unchanged_on_contents; try eassumption.
       apply Mem.perm_valid_block in H0.
       destruct (UV _ ofs H0). eauto.
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
 
Record EffectSem {G C} :=
  { sem :> CoopCoreSem G C;

    effstep: G -> (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop;

    effax: forall M g c m c' m',
       effstep g M c m c' m' <->
            corestep sem g c m c' m'  
         /\ Mem.unchanged_on (fun b ofs => M b ofs = false) m m'
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
  apply effax in H. apply H.
Qed.

Lemma effstep_unchanged: forall M g c m c' m',
      effstep Sem g M c m c' m' -> 
      Mem.unchanged_on (fun b ofs => M b ofs = false) m m'.
Proof. intros.
  apply effax in H. apply H.
Qed.

Lemma effstep_rev: forall M g c m c' m',
      corestep Sem g c m c' m' ->
      Mem.unchanged_on (fun b ofs => M b ofs = false) m m' ->
      (forall b ofs, M b ofs = true -> Mem.valid_block m b) -> 
      effstep Sem g M c m c' m'.
Proof. intros.
  apply effax. 
  split; trivial.
Qed.

  Lemma effstep_fwd: forall U c m c' m',
    effstep Sem g U c m c' m' -> mem_forward m m'.
  Proof. intros. destruct Sem.
         eapply corestep_fwd. eapply effax. apply H.
  Qed.

Lemma effstep_sub: forall U V c m c' m'
         (UV: forall b ofs, U b ofs = true -> V b ofs = true),
         (effstep Sem g U c m c' m' -> effstep Sem g V c m c' m').
Proof. intros. rewrite effax; rewrite effax in H.
  destruct H as [CS Unch].
      split; trivial.
      split; intros; eapply Unch; trivial.
       remember (U b ofs) as d.
       destruct d; trivial; apply eq_sym in Heqd.
       rewrite (UV _ _ Heqd) in H. assumption.

       remember (U b ofs) as d.
       destruct d; trivial; apply eq_sym in Heqd.
       rewrite (UV _ _ Heqd) in H. assumption.
Qed.

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
     effstep_plus U c m c' m' ->
     (forall b z, U b z = true -> V b z = true) ->
     effstep_star V c m c' m'.
  Proof. intros.
    destruct H as [n H].
    exists (S n). eapply effstepN_sub; eassumption.
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

  Lemma effstep_star_sub_val: forall c m c' m' (U V : block -> Z -> bool),
     effstep_plus U c m c' m' ->
     (forall b z, Mem.valid_block m b -> U b z = true -> V b z = true) ->
     effstep_star V c m c' m'.
  Proof. intros.
    destruct H as [n H].
    exists (S n). eapply effstepN_sub_val; eassumption.
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
           rewrite H. admit. 
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
  destruct s. admit. inv H.
  
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
(*
Definition join (j k:meminj):meminj := fun b =>
  match j b with
     Some (b1, delta) => Some (b1,delta)
   | None => k b
  end.

Definition disjoint (j k:meminj):Prop :=
    forall b, j b = None \/ k b = None.

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

Record SM_Injection :=
  { myBlocksSrc : block -> Prop;
                     (* The blocks allocated by THIS module in the
                        source language SRC*)
    myBlocksTgt : block -> Prop; 
                     (* The blocks allocated by THIS module in the
                        target language TGT*)
    frgnInj: meminj; (* a meminj on blocks allocated by other modules; 
                        the injection itself is not modified by coresteps
                        but blocks mentioned by it are accessible. THIS module
                        behaves UNIFORMLY over block mentioned by frgnInj, and
                        assumes that blocks in frgnInj remain mapped during
                        "compilation of the environment". Compilation of THIS 
                        module neither merges nor unmaps blocks from here, 
                        not does it spill into them*)
    pubInj: meminj; (* a meminj on blocks allocated by THIS module.
                       This injection (and hence its constituent blocks) 
                       is revealed to other modules in at_external and halted, 
                       hence other modules may read from / write to blocks 
                       mentioned here - but do so only in a UNIFORM manner.
                       THIS module may spill into blocks mentioned here, but its
                       compilation should not unmap blocks from here (since they
                       have been revealed to other modules).*)
    privInj: meminj; (* another meminj on blocks allocated by THIS module.
                        This injection is entirely private: it is not revealed
                        to other modules at at_external or halted,
                        so blocks in here will necessarily remain unmodified 
                        over external calls. Compilation of THIS module
                        may arbitrarily unmap a block b from dom privinj 
                        in some later phase. Compilation may also spill into 
                        such a block, and may map it with a block
                        b' from dom pubInj or dom privInj (but not frgnInj). 
                        If b' is from pubInj, the resulting merged block b1 will 
                        then necessarily be mapped by all later compilation phases,
                        and is revealed at at_external and halted from TGT
                        onwards (since b' already was revealed in SRC or earlier).
                        However, even downstream from TGT, locations in b1 that
                        "originate" from b remain unmodified across external calls,
                        since the invoked module OTHER did not know about these
                        locations in the SRC and behaves UNFORMLY
                        over the locations in b'. In particular, foreign modules
                        don't spill into b, b' or b1, while THIS module may
                        safely spill into all three blocks. *)
    dist : disjoint pubInj privInj;
    localDOM: forall b1 b2 z, join pubInj privInj b1 = Some(b2,z) -> 
               (myBlocksSrc b1 /\ myBlocksTgt b2);
    foreignDOM: forall b1 b2 z, frgnInj b1 = Some(b2,z) -> 
               (~myBlocksSrc b1 /\ ~myBlocksTgt b2)
  }.


(*DOM/RNG: all blocks mentioned by a SM_Injection. Used for
  stating match_validblocks etc*)
Definition DOM (X: SM_Injection) (b1: block): Prop.
  destruct X as [BSrc BTgt frgn pub priv _ _ _]. 
  apply (BSrc b1 \/ exists b2 z, frgn b1 = Some (b2,z)).
Defined.
  
Definition RNG (X: SM_Injection) (b2:block): Prop.
  destruct X as [BSrc BTgt frgn pub priv _ _ _].
  apply (BTgt b2 \/ exists b1 z, frgn b1 = Some (b2,z)).
Defined.

(*The join of all three components - useful for stating
  match_state conditions*)
Definition as_inj (X: SM_Injection) : meminj.
  destruct X as [BSrc BTgt frgn pub priv _ _ _].
  apply (join frgn (join pub priv)).
Defined.

(*The three projections*)
Definition foreign_of (X: SM_Injection) : meminj.
  destruct X as [BSrc BTgt frgn pub priv _ _ _].
  apply frgn.
Defined.

Definition pub_of (X: SM_Injection) : meminj.
  destruct X as [BSrc BTgt frgn pub priv _ _ _].
  apply pub.
Defined.

Definition priv_of (X: SM_Injection) : meminj.
  destruct X as [BSrc BTgt frgn pub priv _ _ _].
  apply priv.
Defined.

(*Two derived notions, local and shared*)
Definition local_of (X: SM_Injection) : meminj.
  destruct X as [BSrc BTgt frgn pub priv _ _ _].
  apply (join pub priv).
Defined.

Definition shared_of (X: SM_Injection) : meminj.
  destruct X as [BSrc BTgt frgn pub priv _ _ _].
  apply (join frgn pub).
Defined.

(*Obvious incject_incr relationships*)
Lemma pub_in_local: forall j, inject_incr (pub_of j) (local_of j).
Proof. intros.
  destruct j as [BSrc BTgt frgn pub priv dst locDom frgnDom]; simpl in *.
  intros b1; intros.
  unfold join. rewrite H. trivial.
Qed.

Lemma priv_in_local: forall j, inject_incr (priv_of j) (local_of j).
Proof. intros.
  destruct j as [BSrc BTgt frgn pub priv dst locDom frgnDom]; simpl in *.
  intros b1; intros.
  unfold join. rewrite H.
  case_eq (pub b1); intros; trivial.
  destruct p. 
  destruct (dst b1) as [D | D]; rewrite D in *; congruence. 
Qed.

Lemma local_in_all: forall j, inject_incr (local_of j) (as_inj j).
Proof. intros.
  destruct j as [BSrc BTgt frgn pub priv dst locDom frgnDom]; simpl in *.
  intros b1; intros.
  destruct (locDom _ _ _ H).
  unfold join in *. rewrite H.
  case_eq (frgn b1); intros; trivial.
  destruct p. destruct (frgnDom _ _ _ H2); contradiction.
Qed.

Lemma pub_in_all: forall j, inject_incr (pub_of j) (as_inj j).
Proof. intros.
  eapply inject_incr_trans.
  apply pub_in_local. apply local_in_all.
Qed.

Lemma priv_in_all: forall j, inject_incr (priv_of j) (as_inj j).
Proof. intros.
  eapply inject_incr_trans.
  apply priv_in_local. apply local_in_all.
Qed.

Lemma pub_in_shared: forall j, inject_incr (pub_of j) (shared_of j).
Proof. intros.
  destruct j as [BSrc BTgt frgn pub priv dst locDom frgnDom]; simpl in *.
  intros b1; intros.
  unfold join. rewrite H.
  case_eq (frgn b1); intros; trivial.
  destruct p.
  destruct (frgnDom _ _ _ H0).
  exfalso. apply H1.
  apply (locDom b1 b' delta). 
  unfold join. rewrite H. trivial.
Qed.

Lemma foreign_in_shared: forall j, inject_incr (foreign_of j) (shared_of j).
Proof. intros.
  destruct j as [BSrc BTgt frgn pub priv dst locDom frgnDom]; simpl in *.
  intros b1; intros.
  unfold join. rewrite H. trivial.
Qed.

Lemma shared_in_all: forall j, inject_incr (shared_of j) (as_inj j).
Proof. intros.
  destruct j as [BSrc BTgt frgn pub priv dst locDom frgnDom]; simpl in *.
  intros b1; intros.
  unfold join in *.
  remember (frgn b1) as d; destruct d; intros.
    destruct p. apply H.
  rewrite H. trivial.
Qed.

Lemma foreign_in_all: forall j, inject_incr (foreign_of j) (as_inj j).
Proof. intros.
  eapply inject_incr_trans.
  apply foreign_in_shared. 
  apply shared_in_all.
Qed.

(*Construction used in make_initial_core: put incoming injection
  into foreign component, initialize the other componenet as empty*)
Definition initial_SM (j: meminj) : SM_Injection.
eapply Build_SM_Injection with (myBlocksSrc:=fun b => False)
  (myBlocksTgt:=fun b => False) (frgnInj:=j) 
  (privInj:=fun b => None)(pubInj:=fun b => None).
intros b; intros; auto.
intros. inv H.
intros. auto.
Defined.

Definition sm_inject_incr (j j' : SM_Injection):Prop.
destruct j as [BSrc BTgt frgn pub priv dst locDom frgnDom].
destruct j' as [BSrc' BTgt' frgn' pub' priv' dst' locDom' frgnDom'].
apply (inject_incr frgn frgn' /\ inject_incr pub pub' /\ 
       inject_incr priv priv' /\
       (forall b, BSrc b -> BSrc' b) /\
       (forall b, BTgt b -> BTgt' b)).
Defined.

Definition sm_inject_separated (j j' : SM_Injection) (m1 m2:mem):Prop.
destruct j as [BSrc BTgt frgn pub priv dst locDom frgnDom].
destruct j' as [BSrc' BTgt' frgn' pub' priv' dst' locDom' frgnDom'].
apply (inject_separated frgn frgn' m1 m2 /\ 
       inject_separated pub pub' m1 m2 /\ 
       inject_separated priv priv' m1 m2 /\
       (forall b, ~BSrc b -> BSrc' b -> ~ Mem.valid_block m1 b) /\
       (forall b, ~BTgt b -> BTgt' b -> ~ Mem.valid_block m2 b)).
Defined.

Definition sm_valid (j : SM_Injection) (m1 m2: mem) :=
       (forall b1, DOM j b1 -> Mem.valid_block m1 b1)  
    /\ (forall b2, RNG j b2 -> Mem.valid_block m2 b2).

Definition extend_foreign (mu: SM_Injection)(j:meminj) (m1 m2:mem)
           (INC: inject_incr (shared_of mu) j)  
           (SEP: inject_separated (shared_of mu) j m1 m2)
           (VB: sm_valid mu m1 m2) : SM_Injection.
destruct mu as [BSrc BTgt frgn pub priv dst locDom frgnDom].
eapply Build_SM_Injection with (myBlocksSrc:=BSrc)
  (myBlocksTgt:=BTgt)
  (frgnInj:=fun b => match pub b with 
                       Some p => None
                     | None => j b end)
  (pubInj:=pub)
  (privInj:=priv); trivial.
destruct VB as [Dom Rng].
intros; simpl in *.
  remember (pub b1) as d.
  destruct d; apply eq_sym in Heqd.
    inv H.
  remember (frgn b1) as q.
    destruct q; apply eq_sym in Heqq.
      destruct p. 
      assert (j b1 = Some(b, z0)).
        apply INC. unfold join. rewrite Heqq. trivial.
      rewrite H0 in H. inv H. 
      apply (frgnDom _ _ _ Heqq).
    assert (join frgn pub b1 = None).
      unfold join. rewrite Heqq. rewrite Heqd. trivial.
    destruct (SEP _ _ _ H0 H).
    split; intros N.
      apply H1. apply Dom. left; trivial.
      apply H2. apply Rng. left; trivial.
Defined.

Lemma extend_foreign_prop: forall mu j m1 m2
           (INC: inject_incr (shared_of mu) j)  
           (SEP: inject_separated (shared_of mu) j m1 m2)
           (VB: sm_valid mu m1 m2) ,
   (forall b1 b2 delta, (shared_of mu) b1 = Some(b2,delta) <-> 
          ((as_inj mu) b1 = Some(b2,delta) /\ j b1 = Some(b2,delta)))
   /\ inject_separated (as_inj mu) j m1 m2
   /\ sm_inject_incr mu (extend_foreign _ _ _ _ INC SEP VB)
   /\ sm_inject_separated mu (extend_foreign _ _ _ _ INC SEP VB) m1 m2.
Proof.
  intros.
  destruct mu as [BSrc BTgt frgn pub priv dst locDom frgnDom].
  simpl in *.
  unfold extend_foreign in *; simpl in *.
  split.
  (*first prop*)
    intros.
    split; intros.
      split. unfold join. unfold join in H. 
           remember (frgn b1) as d.
           destruct d. destruct p. trivial.
           rewrite H. trivial.
          apply INC; trivial.
      destruct H.
        unfold join in H. unfold join. 
        remember (frgn b1) as d. 
        destruct d; apply eq_sym in Heqd. 
             destruct p. trivial.
        remember (pub b1) as q.
        destruct q. destruct p. trivial.
        assert (join frgn pub b1 = None).
           unfold join. rewrite Heqd. rewrite Heqq; trivial.
        destruct (SEP _ _ _ H1 H0).
          destruct VB. 
         exfalso. apply H2. apply H4. simpl.  
           left. eapply locDom. unfold join. 
            rewrite H. rewrite <- Heqq. reflexivity.
   (*second prop*)
     split.
       intros b1; intros.
       assert (join frgn pub b1 = None).
         unfold join; unfold join in H.
         remember (frgn b1) as d.
         destruct d. destruct p. inv H.
         remember (pub b1) as q.
         destruct q. destruct p. inv H. trivial.
       apply (SEP _ _ _ H1 H0).
  split. split.
  (*third prop*)
      intros b1; intros.
      destruct (frgnDom _ _ _ H).
      remember (pub b1) as d.
      destruct d.
        apply eq_sym in Heqd.
        destruct p.
        destruct (locDom b1 b z).
          unfold join. rewrite Heqd. trivial.
          contradiction.
        apply INC. unfold join. rewrite H. trivial. 
    split. apply inject_incr_refl. 
    split. apply inject_incr_refl.
    split; trivial.
  split. intros b1; intros.
    remember (pub b1) as d.
    destruct d; apply eq_sym in Heqd.
      inv H0.
    apply (SEP b1 b2 delta); trivial.
      unfold join. rewrite Heqd. rewrite H. trivial.
  split. apply inject_separated_same_meminj.
  split. apply inject_separated_same_meminj.
  split; intuition.
Qed.
        

Module SM_simulation. Section SharedMemory_simulation_inject. 
  Context {F1 V1 C1 G2 C2:Type}
          {Sem1 : @EffectSem (Genv.t F1 V1) C1}
          {Sem2 : @EffectSem G2 C2}
          {ge1: Genv.t F1 V1}
          {ge2: G2}
          {entry_points : list (val * val * signature)}.

  Record SM_simulation_inject := 
  { core_data : Type;
    match_state : core_data -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    (*Same as for coop-simulations*)
    match_memwd: forall d j c1 m1 c2 m2,
          match_state d j c1 m1 c2 m2 -> 
               (mem_wd m1 /\ mem_wd m2);

    match_validblocks: forall d j c1 m1 c2 m2, 
          match_state d j c1 m1 c2 m2 ->
          sm_valid j m1 m2;               

    (*External knowledge is put into pub component*)
    core_initial : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          mem_wd m1 -> mem_wd m2 ->

          Forall2 (val_inject j) vals1 vals2 ->

          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          exists cd, exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_state cd (initial_SM j) c1 m1 c2 m2;

(*Here we distinguish beween "our" and "foreign" block*)
    core_diagram : 
      forall st1 m1 st1' m1', 
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 mu m2,
        match_state cd mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists mu',
          sm_inject_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          (*new condition: corestep evolution only adds to local knowledge*)
          foreign_of mu = foreign_of mu' /\ 
          match_state cd' mu' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);
(*TODO: replace these coresteps by appropriate effsteps, and/or add unchOn conditions*)

    (*Only the shared part is revealed to the environment*)
    core_halted : forall cd mu c1 m1 c2 m2 v1,
      match_state cd mu c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->
      val_valid v1 m1 ->
      exists v2, 
        val_inject (shared_of mu) v1 v2 /\
        halted Sem2 c2 = Some v2 /\
        Mem.inject (shared_of mu) m1 m2 /\ val_valid v2 m2;
        (*Maybe we should additionally require 
            Mem.inject (as_inj mu) m1 m2 and
            val_inject (as_inj mu) v1 v2) ? The latter presumably 
            follows already using shared_in_all*)

    core_at_external : 
      forall cd mu c1 m1 c2 m2 e vals1 ef_sig,
        match_state cd mu c1 m1 c2 m2 ->
        at_external Sem1 c1 = Some (e,ef_sig,vals1) ->
        (forall v1, In v1 vals1 -> val_valid v1 m1) ->
        ( (*The old conditions*)
            Mem.inject (as_inj mu) m1 m2 /\  (*maybe this can now be deleted?*)
            meminj_preserves_globals ge1 (as_inj mu) /\ 
            exists vals2, Forall2 (val_inject (as_inj mu)) vals1 vals2 /\ (*maybe this can now be deleted?*)
            Forall2 (Val.has_type) vals2 (sig_args ef_sig) /\
            at_external Sem2 c2 = Some (e,ef_sig,vals2) /\
            (forall v2, In v2 vals2 -> val_valid v2 m2) /\

          (*new conditions: the shared blocks are leaked to the environment -
             this set must include at least all blocks mentioned by
             the function arguments and the foreign blocks, and must
             be closed under pointer derferencing and arithmetic*)
             Mem.inject (shared_of mu) m1 m2 /\ (*In particular: no pointers from shared to priv or localunmapped  are allowed*)
             Forall2 (val_inject (shared_of mu)) vals1 vals2 /\
             meminj_preserves_globals ge1 (shared_of mu)); (*not sure this is needed ..*)

    core_after_external:
      forall cd mu st1 st2 m1 e vals1 ret1 m1' m2 m2' ret2 ef_sig,
        Mem.inject (as_inj mu) m1 m2->
      forall
        (MS: match_state cd mu st1 m1 st2 m2),
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        (forall v1, In v1 vals1 -> val_valid v1 m1) ->
        meminj_preserves_globals ge1 (as_inj mu) -> 

      forall vals2, 
        Mem.inject (shared_of mu) m1 m2 -> 
        Forall2 (val_inject (shared_of mu)) vals1 vals2 -> 
        meminj_preserves_globals ge1 (shared_of mu) ->

      forall j'
        (INC: inject_incr (shared_of mu) j')  
        (SEP: inject_separated (shared_of mu) j' m1 m2), 
        (*hence inject_separated (as_inj mu) j' m1 m2 holds*)

        Mem.inject j' m1' m2' ->
        val_inject j' ret1 ret2 ->

         mem_forward m1 m1' -> 
(*think about this later         Mem.unchanged_on (loc_unmapped j) m1 m1' ->
         (forall b1 b2 delta ofs, priv b1 = Some(b2,delta) -> U1 b1 ofs) ->?? 
         Mem.unchanged_on U1 m1 m1' ->*)

         mem_forward m2 m2' -> 
(*think about this later         Mem.unchanged_on (loc_out_of_reach j m1) m2 m2' ->
         Mem.unchanged_on (fun b2 ofs => forall b1 delta, lk b <> Some(b2,delta)) m2 m2' ->
         Mem.unchanged_on m2 m2' ->*)

         Val.has_type ret2 (proj_sig_res ef_sig) -> 

         mem_wd m1' -> mem_wd m2' -> 
         val_valid ret1 m1' -> val_valid ret2 m2' ->

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
        exists mu',
          mu' = extend_foreign mu j' m1 m2 INC SEP (match_validblocks _ _ _ _ _ _ MS)

          /\ (*here we combine old knowledge with new knowledge*)
              match_state cd' mu' st1' m1' st2' m2' 

           (*Some conditions that were in fact proven in 
               lemma extends_foreign_prop:
               The common part of mu and j' is exactly (shared_of mu):
           /\ (forall b1 b2 delta, (shared_of mu) b1 = Some(b2,delta) <-> 
                      ((as_inj mu) b1 = Some(b2,delta) /\ j' b1 = Some(b2,delta)))
           /\ inject_separated (as_inj mu) j' m1 m2
           /\ sm_inject_incr mu mu'
           /\ sm_inject_separated mu mu' m1 m2*)
}.

End SharedMemory_simulation_inject. 

Require Import sepcomp.forward_simulations_trans.
Require Import Wellfounded.
Require Import Relations.

Definition compose_sm (j1 j2 : SM_Injection) : SM_Injection.
destruct j1 as [pBL1 pub1 priv1 pBR1 Dist1 dP1].
destruct j2 as [pBL2 pub2 priv2 pBR2 Dist2 dP2].
eapply Build_SM_Injection with
  (privBlocks1:=pBL1)
  (privBlocks2:=pBR2)
  (pubInj:=compose_meminj pub1 pub2)
  (privInj:=compose_meminj priv1 (join pub2 priv2)).
intros b1.
  remember (compose_meminj pub1 pub2 b1) as d.
  destruct d; try (left; reflexivity).
  right. destruct p as [b3 z].
  apply eq_sym in Heqd.
  remember (compose_meminj priv1 (join pub2 priv2) b1) as q.
  destruct q; try reflexivity.
  destruct p as [a3 w].
  apply eq_sym in Heqq.
  destruct (compose_meminjD_Some _ _ _ _ _ Heqd)
     as [b2 [d2 [d3 [PUB1 [PUB2 X]]]]]; subst.
  destruct (compose_meminjD_Some _ _ _ _ _ Heqq)
     as [a2 [w2 [w3 [PRIV1 [PP2 X]]]]]; subst.
  clear Heqd Heqq.
  destruct (Dist1 b1).
    rewrite H in PUB1; congruence.
    rewrite H in PRIV1; congruence.
intros b1 b3 z H.  
  destruct (compose_meminjD_Some _ _ _ _ _ H)
     as [b2 [d2 [d3 [PRIV1 [PP2 X]]]]]; subst.
  clear H.
  split. eapply dP1. apply PRIV1.
Section Eff_sim_trans.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3) 
        epts12 epts23 epts13
        (EPC : entrypoints_compose epts12 epts23 epts13).

Theorem eff_sim_trans: forall 
        (SIM12: @SM_simulation_inject _ _ _ _ _ Sem1 Sem2 g1 g2 epts12)
        (SIM23: @SM_simulation_inject _ _ _ _ _ Sem2 Sem3 g2 g3 epts23),
        @SM_simulation_inject _ _ _ _ _ Sem1 Sem3 g1 g3 epts13.
Proof. (*follows structire of forward_simulations_ytrans.injinj*)
  intros.
  destruct SIM12 
    as [core_data12 match_core12 core_ord12 core_ord_wf12 match_memwd12 
      match_validblock12 core_diagram12 
      core_initial12 core_halted12 core_at_external12 core_after_external12].  
  destruct SIM23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23  match_memwd23 
      match_validblock23 core_diagram23 
      core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Build_SM_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)).
    (match_state := fun d j c1 m1 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists j1, exists j2, 
          X=Some c2 /\ j = compose_sm j1 j2 /\
          match_core12 d1 j1 c1 m1 c2 m2 /\ match_core23 d2 j2 c2 m2 c3 m3 
      end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
 (*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [j12 [j23 [X [J [MC12 MC23]]]]]]]; subst.
  split. apply (match_memwd12 _ _ _ _ _ _ MC12).
  apply (match_memwd23 _ _ _ _ _ _ MC23).
 (*match_validblocks*) 
  intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [j12 [j23 [X [J [MC12 MC23]]]]]]]; subst.
  apply compose_meminjD_Some in H0. 
  destruct H0 as [b11 [ofs11 [ofs12 [Hb [Hb1 Hdelta]]]]]. 
  split. eapply (match_validblock12 _ _ _ _ _ _ MC12); try eassumption.
  eapply (match_validblock23 _ _ _ _ _ _ MC23); try eassumption.
 (*core_diagram*)
  clear core_initial23  core_halted23 core_at_external23 core_after_external23 
    core_initial12  core_halted12 core_at_external12 core_after_external12
    EPC epts12 epts23 epts13.
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [j12 [j23 [X [? [MC12 MC23]]]]]]]; subst.
  eapply (diagram_injinj _ _ _ core_diagram12 _ _ _ core_diagram23 
    match_validblock12 match_validblock23); try eassumption.
 (*initial_core*)
  clear core_diagram23  core_halted23 core_at_external23 core_after_external23 
    core_diagram12  core_halted12 core_at_external12 core_after_external12.
  intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3. 
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). 
  eapply forall_valinject_hastype; eassumption.
  destruct (mem_wd_inject_splitL _ _ _ H1 H2) as [Flat1 XX]; rewrite XX.
  assert (ValInjFlat1 := forall_val_inject_flat _ _ _ H1 _ _ H4).
  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 Flat1 H2 H2 ValInjFlat1 HT) 
    as [d12 [c2 [Ini2 MC12]]].
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3 H4 H5) 
    as [d23 [c3 [Ini3 MC23]]].
  exists (d12,Some c2,d23). exists c3. 
  split; trivial. 
  exists c2. exists m1. exists  (Mem.flat_inj (Mem.nextblock m1)). exists j. 
  split; trivial. split; trivial. split; assumption.
 (*halted*)
  intros. rename c2 into c3. rename m2 into m3.  
  destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [j12 [j23 [X [Y [MC12 MC23]]]]]]]; subst. 
  apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [v2 [ValsInj12 [SH2 [Minj12 VV2]]]].
  apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2; try assumption. 
  destruct SH2 as [v3 [ValsInj23 [SH3 [MInj23 VV3]]]].
  exists v3. split. apply (val_inject_compose _ _ _ _ _ ValsInj12 ValsInj23).
  split. trivial. 
  split. eapply Mem.inject_compose; eassumption.
  assumption.
(*atexternal*)
  intros. rename st2 into st3. rename m2 into m3. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [m2 [j1 [j2 [Y [J [MC12 MC23]]]]]]]. subst.
  apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 [AtExt2 VV2]]]]]].
  apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption. 
  destruct AtExt2 as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 [AtExt3 VV3]]]]]].
  split. eapply Mem.inject_compose; eassumption.
  split. 
  admit. (*
Definition meminj_preserves_globals_ind (globals: (block->Prop)*(block->Prop)) f :=
  (forall b, fst globals b -> f b = Some (b, 0)) /\
  (forall b, snd globals b -> f b = Some (b, 0)) /\
  (forall b1 b2 delta, snd globals b2 -> f b1 = Some (b2, delta) -> b1=b2).

need to prove meminj_preserves_globals g1 (compose_meminj j1 j2) 
          from meminj_preserves_globals g1 j1
          and meminj_preserves_globals g2 j2*)
  exists vals3. 
  split.  eapply forall_val_inject_compose; eassumption.
  split; try assumption.
  split; try assumption.
 (*after_external*) clear core_diagram12 core_initial12 core_halted12 
  core_diagram23 core_initial23 core_halted23. 
  intros. rename st2 into st3. rename m2 into m3. rename ret2 into ret3. rename m2' into m3'. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H0 as [st2 [m2 [j1 [j2 [Y [J [MC12 MC23]]]]]]]. subst.
  rename H1 into AtExt1. rename H2 into VV1.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExt1 VV1) 
   as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 [AtExt2 VV2]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2 VV2) 
   as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 [AtExt3 V3V]]]]]].
  clear core_at_external12 core_at_external23.
  assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). 
  eapply forall_valinject_hastype; eassumption.
  assert (HRet1: Val.has_type ret1 (proj_sig_res ef_sig)). 
  eapply valinject_hastype; eassumption.
  assert (mem_wd m1 /\ mem_wd m2). apply (match_memwd12 _ _ _ _ _ _ MC12). destruct H0 as [WD1 WD2].
  assert (WD3: mem_wd m3). apply (match_memwd23 _ _ _ _ _ _ MC23).
  destruct (MEMAX.interpolate_II _ _ _ MInj12 _ H8 _ _ MInj23 _ H10 _ H6 H4 H5 H9 H11 WD1 H13 WD2 WD3 H14)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Unch22 [Sep12 [Sep23 [Unch222' [Unch2233' WD22']]]]]]]]]]]]]]. 
  subst.
  assert (WD2': mem_wd m2'). apply WD22'. apply WD2. 
  assert (exists ret2, val_inject j12' ret1 ret2 /\ val_inject j23' ret2 ret3 /\
    Val.has_type ret2 (proj_sig_res ef_sig) /\ val_valid ret2 m2'). 
  apply val_inject_split in H7. destruct H7 as [ret2 [injRet12 injRet23]]. 
  exists ret2. split; trivial. split; trivial. 
  split. eapply valinject_hastype; eassumption.
  eapply inject_valvalid; eassumption. 
  destruct H0 as [ret2 [injRet12 [injRet23 [HasTp2 ValV2]]]].
  assert (Unch111': Mem.unchanged_on (loc_unmapped j1) m1 m1').
  split; intros; apply H9; unfold compose_meminj, loc_unmapped in *. 
  rewrite H0. trivial. trivial. 
  intros. rewrite H0. trivial. trivial.
  specialize (core_after_external12 _ _ j12' _ _ _ _ _ ret1 m1' m2 m2' ret2 _ MInj12 MC12 AtExt1
    VV1 PGj1 Incr12 Sep12 MInj12' injRet12 H8 Unch111' Fwd2 Unch22 HasTp2 H13 WD2' H15 ValV2).
  destruct core_after_external12 as [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]].

  specialize (core_after_external23 _ _ j23' _ _ _ _ vals2 ret2 m2' _ m3' ret3 _ MInj23 MC23 
    AtExt2 VV2 PGj2 Incr23 Sep23 MInj23' injRet23 Fwd2 Unch222' H10 Unch2233' H12 WD2'
    H14 ValV2 H16).
  destruct core_after_external23 as [d23' [cc2' [c3' [AftExt22 [AftExt3 MC23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists (d12', Some c2', d23'). exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  exists c2'. exists m2'. exists j12'. exists j23'. auto.
Qed.
  intros.
  inversion SIM12.
  intros SIM12.
  induction SIM12. intros SIM23.
    apply coop_sim_trans_CaseEq; assumption.
    apply coop_sim_trans_CaseExt; assumption.
    apply coop_sim_trans_CaseInj; assumption.
Qed.

End SM_simulation.
*)