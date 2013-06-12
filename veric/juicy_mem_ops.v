Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Import cjoins.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.

Module Type JUICY_MEM_OPS.
Parameter juicy_mem_store
  : juicy_mem -> memory_chunk -> block -> Z -> val -> option juicy_mem.

Parameter juicy_mem_storebytes
  : juicy_mem -> block -> Z -> list memval -> option juicy_mem.

Parameter juicy_mem_alloc
  : juicy_mem -> Z -> Z -> juicy_mem * block.

Parameter juicy_mem_free
  : juicy_mem -> block -> Z -> Z -> option juicy_mem.

Axiom juicy_mem_store_succeeds: forall j j' ch b ofs v,
  juicy_mem_store j ch b ofs v = Some j' 
  -> exists m', store ch (m_dry j) b ofs v = Some m' /\ m' = m_dry j'.

Axiom juicy_mem_alloc_succeeds: forall j j' b lo hi,
  juicy_mem_alloc j lo hi = (j', b) -> (m_dry j', b) = alloc (m_dry j) lo hi.

Axiom juicy_mem_free_succeeds: forall j j' b lo hi, 
  juicy_mem_free j b lo hi = Some j' 
  -> exists m', free (m_dry j) b lo hi = Some m' /\ m' = m_dry j'.
End JUICY_MEM_OPS.

Obligation Tactic := Tactics.program_simpl.

Module JuicyMemOps <: JUICY_MEM_OPS.
Program Definition juicy_mem_store j ch b ofs v: option juicy_mem := 
  if valid_access_dec (m_dry j) ch b ofs Writable 
    then Some (store_juicy_mem j _ ch b ofs v _)
    else None.
Next Obligation.
intros.
apply (proj1_sig (valid_access_store (m_dry j) ch b ofs v H)).
Defined.
Next Obligation.
apply (proj2_sig (valid_access_store (m_dry j) ch b ofs v H)).
Defined.

Lemma juicy_mem_store_succeeds: forall j j' ch b ofs v,
  juicy_mem_store j ch b ofs v = Some j' 
  -> exists m', store ch (m_dry j) b ofs v = Some m' /\ m' = m_dry j'.
Proof.
intros until v; intro H.
unfold juicy_mem_store in H.
destruct (valid_access_dec (m_dry j) ch b ofs Writable) as [H1 | H1].
exists (m_dry j').
split; auto.
inversion H.
simpl.
unfold juicy_mem_store_obligation_1.
destruct (valid_access_store (m_dry j) ch b ofs v H1).
simpl. auto.
inv H.
Qed.

Program Definition juicy_mem_storebytes j b ofs bytes: option juicy_mem := 
  if range_perm_dec (m_dry j) b ofs (ofs + Z_of_nat (length bytes)) Cur Writable
    then Some (storebytes_juicy_mem j _ b ofs bytes _)
    else None.
Next Obligation.
apply (proj1_sig (range_perm_storebytes (m_dry j) b ofs bytes H)).
Defined.
Next Obligation.
apply (proj2_sig (range_perm_storebytes (m_dry j) b ofs bytes H)).
Qed.

Lemma juicy_mem_storebytes_succeeds: forall j j' b ofs bytes,
  juicy_mem_storebytes j b ofs bytes = Some j' ->
  exists m', storebytes (m_dry j) b ofs bytes = Some m' /\ m' = m_dry j'.
Proof.
intros until bytes; intro H.
unfold juicy_mem_storebytes in H.
destruct (range_perm_dec (m_dry j) b ofs (ofs + Z_of_nat (length bytes)) Cur Writable).
exists (m_dry j').
split; auto.
inversion H.
simpl.
unfold juicy_mem_storebytes_obligation_1.
destruct (range_perm_storebytes (m_dry j) b ofs bytes r).
simpl. auto.
inv H.
Qed.


Lemma pshare_sh_bot: forall p, pshare_sh p = Share.bot -> False.
Proof. destruct p; intros. simpl in H. subst x. apply nonunit_nonidentity in n.
apply n. apply bot_identity.
Qed.

Lemma juicy_mem_alloc_aux1:
  forall jm lo hi m' b, alloc (m_dry jm) lo hi = (m',b) ->
        forall ofs, m_phi jm @ (b,ofs) = NO Share.bot.
Proof.
 intros.
 pose proof (juicy_mem_max_access jm (b,ofs)).
 unfold max_access_at in H0.
 simpl in H0. 
 pose proof (alloc_result _ _ _ _ _ H).
 subst b.
 rewrite nextblock_noaccess in H0.
 destruct (m_phi jm @ (nextblock (m_dry jm), ofs)); simpl in H0.
 destruct (eq_dec t Share.bot). subst; auto.
 rewrite perm_of_nonempty in H0 by auto. contradiction.
 destruct (perm_of_sh_pshare t p). rewrite H1 in H0.
 destruct k; try contradiction; xomega.
 xomega. xomega.
Qed.

Transparent alloc.
Lemma after_alloc_contents_cohere:
 forall jm lo hi m' b (H : alloc (m_dry jm) lo hi = (m', b)),
  contents_cohere m'
    (after_alloc lo hi b (m_phi jm) (juicy_mem_alloc_aux1 jm lo hi m' b H)).
Proof.
intros. 
unfold after_alloc; hnf; intros.
rewrite resource_at_make_rmap in H0. unfold after_alloc' in H0.
if_tac in H0.
inv H0; split; auto.
destruct loc as [b' z]; destruct H1; subst b'.
unfold contents_at. inv H; simpl. 
destruct (alloc (m_dry jm) lo hi).
rewrite PMap.gss.
rewrite ZMap.gi; auto.
destruct loc as [b' z].
destruct (eq_dec b b').
subst b'.
elimtype False.
generalize (juicy_mem_access jm (b,z)); intro.
rewrite H0 in H2.
apply alloc_result in H.
unfold access_at in H2.
rewrite nextblock_noaccess in H2.
unfold perm_of_res, perm_of_sh in H2; simpl in H2.
if_tac in H2. subst. if_tac in H2; inv H2.
if_tac in H2; try congruence.
eapply pshare_sh_bot; eauto.
simpl. subst. xomega.
assert (contents_at m' (b',z) = contents_at (m_dry jm) (b',z)).
unfold contents_at. simpl.
inv H. simpl. rewrite PMap.gso; auto.
rewrite H2.
apply (juicy_mem_contents jm _ _ _ _ _ H0).
Qed.

Lemma after_alloc_access_cohere: 
 forall jm lo hi m' b (H : alloc (m_dry jm) lo hi = (m', b)),
 access_cohere m'
  (after_alloc lo hi b (m_phi jm) (juicy_mem_alloc_aux1 jm lo hi m' b H)).
Proof.
intros; hnf; intros.
unfold after_alloc. rewrite resource_at_make_rmap.
unfold after_alloc'.
if_tac.
unfold perm_of_res; simpl.   rewrite perm_of_freeable.
inv H. unfold access_at; simpl. 
   destruct loc as [b' z]; destruct H0; simpl in *; subst b'.
rewrite PMap.gss.
destruct H0.
destruct (zle lo z); try contradiction.
simpl. 
destruct (zlt z hi); try omegaContradiction.
simpl. auto.
destruct loc as [b' z].
destruct (eq_dec b b').
subst b'.
pose proof (juicy_mem_alloc_cohere jm (b,z)).
rewrite H1.
simpl in *.
unfold perm_of_res. simpl. rewrite perm_of_empty.
unfold access_at.
inv H. simpl.
rewrite PMap.gss.
destruct (zle lo z); simpl; auto.
destruct (zlt z hi); simpl; auto.
contradict H0; split; auto. omega.
apply alloc_result in H. subst; simpl; xomega.
replace (access_at m' (b',z)) with (access_at (m_dry jm) (b',z)).
apply (juicy_mem_access jm (b',z)).
unfold access_at.
simpl.
inv H. simpl. rewrite PMap.gso; auto.
Qed.

Lemma after_alloc_max_access_cohere: 
 forall jm lo hi m' b (H : alloc (m_dry jm) lo hi = (m', b)),
 max_access_cohere m'
  (after_alloc lo hi b (m_phi jm) (juicy_mem_alloc_aux1 jm lo hi m' b H)).
Proof.
intros; pose proof I; hnf; intros.
unfold after_alloc. rewrite resource_at_make_rmap.
unfold after_alloc'.
if_tac. simpl; rewrite perm_of_freeable.
destruct loc. destruct H1. subst b0.
unfold max_access_at.
simpl. inv H.
simpl. rewrite PMap.gss.
destruct H2. 
destruct (zle lo z); try contradiction.
simpl. 
destruct (zlt z hi); try omegaContradiction.
simpl.
constructor.
generalize (juicy_mem_max_access jm loc); case_eq (m_phi jm @ loc); intros; auto.
destruct loc as [b' z].
destruct (eq_dec b b').
subst b'.
unfold max_access_at in H3.
simpl in H3.
apply alloc_result in H.
rewrite nextblock_noaccess in H3; auto.
simpl in H3.
revert H3; case_eq (perm_of_sh t Share.bot); intros; try contradiction.
hnf. destruct (max_access_at m' (b, z)); auto.
subst; xomega.
unfold max_access_at.
inv H; simpl. 
rewrite PMap.gso; auto.
replace (max_access_at m' loc) with (max_access_at (m_dry jm) loc); auto.
inv H.
unfold max_access_at. simpl.
destruct k; simpl; try xomega.
apply H3.
unfold max_access_at.
inv H; simpl.
destruct (eq_dec (fst loc) (nextblock (m_dry jm))).
rewrite e. rewrite PMap.gss.
destruct loc as [b z]. simpl in *.
subst b.
destruct (zle lo z).
destruct (zlt z hi).
contradiction H1; split; auto.
omega.
simpl.
apply nextblock_noaccess; xomega.
simpl.
apply nextblock_noaccess; xomega.
rewrite PMap.gso by auto. auto.
pose proof (nextblock_alloc _ _ _ _ _ H).
forget (m_dry jm) as m.
clear - H4 H H3. rewrite H4. xomega.
Qed.

Lemma after_alloc_alloc_cohere:
 forall jm lo hi m' b (H : alloc (m_dry jm) lo hi = (m', b)),
 alloc_cohere m'
  (after_alloc lo hi b (m_phi jm) (juicy_mem_alloc_aux1 jm lo hi m' b H)).
Proof.
intros; hnf; intros.
unfold after_alloc.
rewrite resource_at_make_rmap.
unfold after_alloc'.
destruct loc as [b' z]. simpl in *.
destruct (eq_dec b' b). subst b'.
inv H.
simpl in *. xomegaContradiction.
rewrite if_false.
apply (juicy_mem_alloc_cohere jm (b',z)).
inv H. simpl in *. xomega.
intros [? ?]; subst. xomega.
Qed.

Definition juicy_mem_alloc (jm: juicy_mem) (lo hi: Z) : juicy_mem * block :=
         (mkJuicyMem (fst (alloc (m_dry jm) lo hi))
                     (after_alloc lo hi (snd (alloc (m_dry jm) lo hi)) (m_phi jm) 
                            (juicy_mem_alloc_aux1 _ _ _ _ _ (eq_refl _)))
                     (after_alloc_contents_cohere _ _ _ _ _ (eq_refl _))
                     (after_alloc_access_cohere _ _ _ _ _ (eq_refl _))
                     (after_alloc_max_access_cohere _ _ _ _ _ (eq_refl _))
                     (after_alloc_alloc_cohere _ _ _ _ _ (eq_refl _)), 
           snd (alloc (m_dry jm) lo hi)).

Lemma juicy_mem_alloc_at:
  forall jm lo hi jm' b,
     juicy_mem_alloc jm lo hi = (jm',b) ->
     forall loc, m_phi jm' @ loc = 
       if adr_range_dec (b, lo) (hi - lo) loc
       then YES Share.top pfullshare (VAL Undef) NoneP
       else m_phi jm @ loc.
Proof.
 intros.
 inv H. simpl.
 unfold after_alloc; rewrite resource_at_make_rmap.
 unfold after_alloc'. auto.
Qed.  

Lemma juicy_mem_alloc_level:
 forall jm lo hi jm' b,
   juicy_mem_alloc jm lo hi = (jm', b) -> level jm = level jm'.
Proof.
 unfold juicy_mem_alloc; intros.
 inv H.
 unfold after_alloc; simpl. rewrite level_make_rmap; auto.
Qed.

Lemma juicy_mem_alloc_succeeds: forall j j' b lo hi,
  juicy_mem_alloc j lo hi = (j', b) -> (m_dry j', b) = alloc (m_dry j) lo hi.
Proof.
intros until hi; intro H.
unfold juicy_mem_alloc in H.
inv H.
simpl.
simpl; auto.
Qed.

Program Definition juicy_mem_free j b lo hi: option juicy_mem :=
  if range_perm_dec (m_dry j) b lo hi Cur Freeable
    then Some (free_juicy_mem j _ b lo hi _)
    else None.
Next Obligation.
apply (proj1_sig (range_perm_free (m_dry j) b lo hi H)).
Defined.
Next Obligation.
apply (proj2_sig (range_perm_free (m_dry j) b lo hi H)).
Defined.

Lemma juicy_mem_free_succeeds: forall j j' b lo hi, 
  juicy_mem_free j b lo hi = Some j' 
  -> exists m', free (m_dry j) b lo hi = Some m' /\ m' = m_dry j'.
Proof.
intros until hi; intro H.
unfold juicy_mem_free in H.
destruct (range_perm_dec (m_dry j) b lo hi Cur Freeable) as [H1 | H1].
exists (m_dry j').
split; auto.
inversion H.
unfold juicy_mem_free_obligation_1 in *.
clear H H2.
simpl.
destruct (range_perm_free (m_dry j) b lo hi H1).
simpl in *; subst; auto.
inversion H.
Qed.
End JuicyMemOps.

(* Here we construct an instance of StratifiedSemanticsWithSeparation using
   the juicy mem operations. *)
Module Abs := JuicyMemOps.
Require Import veric.local.

Inductive AbsPrimcom : relation juicy_mem -> Prop :=
| AbsPrimcom_store : forall ch b ofs v, 
  AbsPrimcom (fun j j' => Abs.juicy_mem_store j ch b ofs v = Some j')
| AbsPrimcom_alloc : forall lo hi,
  AbsPrimcom (fun j j' => fst (Abs.juicy_mem_alloc j lo hi) = j')
| AbsPrimcom_free : forall b ofs n,
  AbsPrimcom (fun j j' => Abs.juicy_mem_free j b ofs n = Some j').

Inductive AbsPrimexpr : pfunc juicy_mem val -> Prop :=.

Instance abstract : GenericSemantics juicy_mem AbsPrimcom AbsPrimexpr.

Inductive ConcPrimcom : relation mem -> Prop :=
| ConcPrimcom_store : forall ch b ofs v,
  ConcPrimcom (fun m m' => store ch m b ofs v = Some m')
| ConcPrimcom_alloc : forall lo hi,
  ConcPrimcom (fun m m' => fst (alloc m lo hi) = m')
| ConcPrimcom_free : forall b ofs n,
  ConcPrimcom (fun m m' => free m b ofs n = Some m').

Inductive ConcPrimexpr : pfunc mem val -> Prop :=.

Instance concrete : GenericSemantics mem ConcPrimcom ConcPrimexpr.

Inductive VU : relation juicy_mem -> relation mem -> Prop :=
| VU_store : forall ch b ofs v,
  VU (fun j j' => Abs.juicy_mem_store j ch b ofs v = Some j')
     (fun m m' => store ch m b ofs v = Some m')
| VU_alloc : forall lo hi,
  VU (fun j j' => fst (Abs.juicy_mem_alloc j lo hi) = j')
     (fun m m' => fst (alloc m lo hi) = m')
| VU_free : forall b ofs n,
  VU (fun j j' => Abs.juicy_mem_free j b ofs n = Some j')
     (fun m m' => free m b ofs n = Some m').
  
Inductive GF : pfunc juicy_mem val -> pfunc mem val -> Prop :=.

Lemma PrimexprErasure : forall g f, GF g f -> False. Proof. inversion 1. Qed.

Lemma PrimexprSafety : forall g f, GF g f -> False. Proof. inversion 1. Qed.

Lemma PrimcomErasure : forall v u j j' m m',
  VU v u -> m_dry j = m -> v j j' -> u m m' -> m_dry j' = m'.
Proof.
intros.
inv H.
(* store *)
apply JuicyMemOps.juicy_mem_store_succeeds in H1.
destruct H1 as [? [? ?]]; subst.
rewrite H in H2; inv H2; auto.
(* alloc *)
generalize JuicyMemOps.juicy_mem_alloc_succeeds; intros.
spec H j j' (snd (JuicyMemOps.juicy_mem_alloc j lo hi)) lo hi.
case_eq (JuicyMemOps.juicy_mem_alloc j lo hi); intros.
rewrite H0 in *. spec H; auto. simpl in *.
destruct (alloc (m_dry j) lo hi); simpl in *. inv H; auto.
(* free *)
apply JuicyMemOps.juicy_mem_free_succeeds in H1.
destruct H1 as [? [? ?]].
subst. rewrite H in H2; inv H2; auto.
Qed.

Lemma PrimcomSafety : forall v u j j' m,
  VU v u -> m_dry j = m -> v j j' -> exists m', u m m'.
Proof.
intros.
inv H.
(* store *)
apply JuicyMemOps.juicy_mem_store_succeeds in H1.
destruct H1 as [? [? ?]]; subst.
eexists; eauto.
(* alloc *)
generalize JuicyMemOps.juicy_mem_alloc_succeeds; intros.
spec H j j' (snd (JuicyMemOps.juicy_mem_alloc j lo hi)) lo hi.
case_eq (JuicyMemOps.juicy_mem_alloc j lo hi); intros.
rewrite H0 in *. spec H; auto. simpl in *.
destruct (alloc (m_dry j) lo hi); simpl in *. inv H; auto.
eexists; eauto.
(* free *)
apply JuicyMemOps.juicy_mem_free_succeeds in H1.
destruct H1 as [? [? ?]].
subst. eexists; eauto.
Qed.

Existing Instance abstract.
Existing Instance concrete.

Instance stratsem : @StratifiedSemantics 
  juicy_mem 
  AbsPrimcom
  AbsPrimexpr
  mem
  ConcPrimcom
  ConcPrimexpr
  abstract
  concrete
  m_dry 
  VU 
  GF.
Proof.
constructor.
intros; inv H; split; constructor.
intros; inv H; split; constructor.
apply PrimcomErasure.
apply PrimcomSafety.
intros; elimtype False; eapply PrimexprErasure; eauto.
intros; elimtype False; eapply PrimexprSafety; eauto.
Qed.

Existing Instance stratsem.


Require Import veric.compcert_rmaps.

Inductive RmapPrimexpr : pfunc rmap val -> Prop :=.

Inductive HG : pfunc rmap val -> pfunc juicy_mem val -> Prop :=.

Instance stratsemsep : StratifiedSemanticsWithSeparation m_phi RmapPrimexpr HG.
Proof.
constructor; intros; inv H. 
Qed.

