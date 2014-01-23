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

  Lemma effstep_corestep: forall M g c m c' m',
      effstep Sem g M c m c' m' -> corestep Sem g c m c' m'. 
  Proof. intros. apply effax1 in H. apply H. Qed.

  Lemma effstep_unchanged: forall M g c m c' m',
        effstep Sem g M c m c' m' -> 
        Mem.unchanged_on (fun b ofs => M b ofs = false) m m'.
  Proof. intros. apply effax1 in H. apply H. Qed.

  Lemma effstep_fwd: forall U c m c' m',
    effstep Sem g U c m c' m' -> mem_forward m m'.
  Proof. intros. destruct Sem.
         eapply corestep_fwd. eapply effax1. apply H.
  Qed.

  Lemma effstep_sub: forall U V c m c' m'
         (UV: forall b ofs, U b ofs = true -> V b ofs = true),
         (effstep Sem g U c m c' m' -> effstep Sem g V c m c' m').
  Proof. intros. eapply (effstep_sub_val _ _ U V). 
         intuition. assumption.
  Qed.

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
    eapply (unchanged_on_trans _ m0 _). 
      eapply mem_unchanged_on_sub; try eassumption.
        intuition. apply orb_false_iff in H. apply H.
      clear FF.
      specialize (unchanged_on_validblock_invariant m0 m' (fun (b : block) (ofs : Z) => FreelistEffect m0 L b ofs = false) (fun (b : block) (ofs : Z) => FreelistEffect m L b ofs = false)).
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

Definition StoreEffectD : forall tv vl b z
      (ST: StoreEffect tv vl b z = true), 
      exists ofs, tv = Vptr b ofs /\ 
                 (Int.unsigned ofs) <= z < (Int.unsigned ofs + Z.of_nat (length vl)).
Proof. intros.
  unfold StoreEffect in ST.
  destruct tv; inv ST.
  exists i.
  destruct (eq_block b0 b); try discriminate. subst. simpl in *.
  split; trivial.
  destruct (zle (Int.unsigned i) z); try discriminate. simpl in *.
  destruct (zlt z (Int.unsigned i + Z.of_nat (length vl))); try discriminate. simpl in *.
  split; trivial.
Qed.

(* Parameter BuiltinEffect : forall {F V: Type} (ge: Genv.t F V) (sg: signature)  *)
(*                     (vargs:list val) (m:mem), block -> Z -> bool. *)

(* Axiom ec_builtinEffectPolymorphic: *)
(*    forall {F V:Type} ef (g : Genv.t F V) vargs m t vres m', *)
(*    external_call ef g vargs m t vres m' -> *)
(*    Mem.unchanged_on (fun b z=> BuiltinEffect g (ef_sig ef) vargs m b z = false) m m'. *)

(* preliminary material for the support of builtins, *)
(* AXIOM BUILTIN: forall (name: ident) (F V: Type) (ge: Genv.t F V) (sg: signature)  *)
(*                     (vargs:list val) *)
(*                        (m:mem) (t:trace) (v: val) (m': mem), *)
(*       extcall_io_sem name sg ge vargs m t v m' -> *)
(*       Mem.unchanged_on (fun b z => BuiltinEffect ge sg vargs m b z = false) m m'. *)

(* Lemma ec_builtinEffectPolymorphic: *)
(*    forall {F V:Type} ef (g : Genv.t F V) vargs m t vres m', *)
(*    external_call ef g vargs m t vres m' -> *)
(*    Mem.unchanged_on (fun b z=> BuiltinEffect g (ef_sig ef) vargs m b z = false) m m'. *)
(* Proof. intros. simpl in H. *)
(*   destruct ef; try (eapply BUILTIN; eassumption). *)
(* Focus 7. simpl in H. inv H. *)
(* Qed. *)
(* Lemma ec_builtinEffectPolymorphic: *)
(*    forall {F V:Type} name sg (g : Genv.t F V) vargs m t vres m', *)
(*    external_call (EF_builtin name sg) g vargs m t vres m' -> *)
(*    Mem.unchanged_on (fun b z=> BuiltinEffect g sg vargs m b z = false) m m'. *)
(* Proof. intros. simpl in H. *)
(*   eapply BUILTIN. eassumption. *)
(* Qed. *)
