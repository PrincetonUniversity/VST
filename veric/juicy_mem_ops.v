Require Import VST.veric.juicy_base.
Import cjoins.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.shares.

Module Type JUICY_MEM_OPS.
Parameter juicy_mem_store
  : juicy_mem -> memory_chunk -> block -> Z -> val -> option juicy_mem.

Parameter juicy_mem_storebytes
  : juicy_mem -> block -> Z -> list memval -> option juicy_mem.

Parameter juicy_mem_alloc
  : juicy_mem -> Z -> Z -> juicy_mem * block.

(* See comment below, "this is fixable"

Parameter juicy_mem_free
  : juicy_mem -> block -> Z -> Z -> option juicy_mem.
Axiom juicy_mem_free_succeeds: forall j j' b lo hi,
  juicy_mem_free j b lo hi = Some j'
  -> exists m', free (m_dry j) b lo hi = Some m' /\ m' = m_dry j'.

*)

Axiom juicy_mem_store_succeeds: forall j j' ch b ofs v,
  juicy_mem_store j ch b ofs v = Some j'
  -> exists m', store ch (m_dry j) b ofs v = Some m' /\ m' = m_dry j'.
Axiom juicy_mem_alloc_succeeds: forall j j' b lo hi,
  juicy_mem_alloc j lo hi = (j', b) -> (m_dry j', b) = alloc (m_dry j) lo hi.

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
        forall ofs, m_phi jm @ (b,ofs) = NO Share.bot bot_unreadable.
Proof.
 intros.
 pose proof (juicy_mem_max_access jm (b,ofs)).
 unfold max_access_at in H0.
 simpl in H0.
 pose proof (alloc_result _ _ _ _ _ H).
 subst b.
 destruct jm; simpl in *.
 rewrite JMalloc; auto; simpl.
 xomega.
Qed.

(* Transparent alloc. *)
Lemma after_alloc_contents_cohere:
 forall jm lo hi m' b (H : alloc (m_dry jm) lo hi = (m', b)),
  contents_cohere m'
    (after_alloc lo hi b (m_phi jm) (juicy_mem_alloc_aux1 jm lo hi m' b H)).
Proof.
intros.
unfold after_alloc; hnf; intros.
rewrite resource_at_make_rmap in H0. unfold after_alloc' in H0.
if_tac in H0.
*
inv H0; split; auto.
apply (alloc_dry_updated_on _ _ _ _ _ _ H); auto.
*
destruct (alloc_dry_unchanged_on _ _ _ _ _ b H H1).
pose proof (juicy_mem_access jm loc).
rewrite H0 in H4. rewrite H4 in H3.
spec H3.
clear.
unfold perm_of_res, perm_of_sh; simpl.
if_tac. if_tac. congruence. congruence. rewrite if_true by auto. congruence.
destruct (juicy_mem_contents jm _ _ _ _ _ H0).
split; auto.
rewrite <- H3; auto.
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
*
unfold perm_of_res; simpl.   rewrite perm_of_freeable.
apply (alloc_dry_updated_on _ _ _ _ _ _ H); auto.
*
destruct (alloc_dry_unchanged_on _ _ _ _ _ b H H0).
pose proof (juicy_mem_access jm loc).
congruence.
Qed.

Lemma after_alloc_max_access_cohere:
 forall jm lo hi m' b (H : alloc (m_dry jm) lo hi = (m', b)),
 max_access_cohere m'
  (after_alloc lo hi b (m_phi jm) (juicy_mem_alloc_aux1 jm lo hi m' b H)).
Proof.

intros; pose proof I; hnf; intros.
unfold after_alloc. rewrite resource_at_make_rmap.
unfold after_alloc'.
if_tac.
*
 simpl; rewrite perm_of_freeable.
 destruct loc. destruct H1. subst b0.
 unfold max_access_at.
 rewrite (alloc_access_same _ _ _ _ _ H) by omega.
 constructor.
*
  assert (HH:= juicy_mem_max_access jm loc).

    eapply perm_order''_trans; eauto.
    unfold max_access_at in *.
    destruct loc as [b' z].
    rewrite (alloc_access_other _ _ _ _ _ H); auto.

    destruct ((access_at m' (b', z) Max)); [apply perm_refl |constructor].
    destruct (eq_block b b').
    right. assert (~(lo <= z < lo + (hi - lo))).
    { intros HHH; apply H1. split; auto. }
    xomega.
    left; auto.
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
rewrite if_false.
apply (juicy_mem_alloc_cohere jm loc).
rewrite (nextblock_alloc _ _ _ _ _ H) in H0.
zify. omega.
destruct loc as [b' z']; simpl in *; intros [? ?]; subst b'.
pose proof (alloc_result _ _ _ _ _ H).
pose proof (nextblock_alloc _ _ _ _ _ H).
rewrite <- H1 in H3.
rewrite H3 in H0.
clear - H0.
zify; omega.
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
       then YES Share.top readable_share_top (VAL Undef) NoneP
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

(* This is fixable, as long as we replace range_perm_dec
  with something based on the PERM argument of free_juicy_mem ...
Program Definition juicy_mem_free j b lo hi: option juicy_mem :=
  if range_perm_dec (m_dry j) b lo hi Cur Freeable
    then Some (free_juicy_mem j _ b lo hi _ _)
    else None.
Next Obligation.
apply (proj1_sig (range_perm_free (m_dry j) b lo hi H)).
Defined.
Next Obligation.
apply (proj2_sig (range_perm_free (m_dry j) b lo hi H)).
Defined.
Next Obligation.
pose proof (juicy_mem_access j (b,ofs)).
specialize (H ofs).
spec H; [ omega | ].
hnf in H. unfold access_at in H2.
simpl in *.
destruct ((mem_access (m_dry j)) !! b ofs Cur); try contradiction.
destruct p; inv H.
inv H.
hnf in H.

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
*)

End JuicyMemOps.


(* Here we construct an instance of StratifiedSemanticsWithSeparation using
   the juicy mem operations. *)
Module Abs := JuicyMemOps.
Require Import VST.veric.local.

Inductive AbsPrimcom : relation juicy_mem -> Prop :=
| AbsPrimcom_store : forall ch b ofs v,
  AbsPrimcom (fun j j' => Abs.juicy_mem_store j ch b ofs v = Some j')
| AbsPrimcom_alloc : forall lo hi,
  AbsPrimcom (fun j j' => fst (Abs.juicy_mem_alloc j lo hi) = j')
(*
| AbsPrimcom_free : forall b ofs n,
  AbsPrimcom (fun j j' => Abs.juicy_mem_free j b ofs n = Some j').
*).
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
(*| VU_free : forall b ofs n,
  VU (fun j j' => Abs.juicy_mem_free j b ofs n = Some j')
     (fun m m' => free m b ofs n = Some m')*).

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
specialize (H j j' (snd (JuicyMemOps.juicy_mem_alloc j lo hi)) lo hi).
case_eq (JuicyMemOps.juicy_mem_alloc j lo hi); intros.
rewrite H0 in *. spec H; auto. simpl in *.
destruct (alloc (m_dry j) lo hi); simpl in *. inv H; auto.
(* free *)
(*apply JuicyMemOps.juicy_mem_free_succeeds in H1.
destruct H1 as [? [? ?]].
subst. rewrite H in H2; inv H2; auto.
*)
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
specialize (H j j' (snd (JuicyMemOps.juicy_mem_alloc j lo hi)) lo hi).
case_eq (JuicyMemOps.juicy_mem_alloc j lo hi); intros.
rewrite H0 in *. spec H; auto. simpl in *.
destruct (alloc (m_dry j) lo hi); simpl in *. inv H; auto.
eexists; eauto.
(* free *)
(*apply JuicyMemOps.juicy_mem_free_succeeds in H1.
destruct H1 as [? [? ?]].
subst. eexists; eauto.
*)
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

Require Import VST.veric.compcert_rmaps.

Inductive RmapPrimexpr : pfunc rmap val -> Prop :=.

Inductive HG : pfunc rmap val -> pfunc juicy_mem val -> Prop :=.

Instance stratsemsep : StratifiedSemanticsWithSeparation m_phi RmapPrimexpr HG.
Proof.
constructor; intros; inv H.
Qed.

(*Lenb: moved alloc_juicy_variables, juicy_mem_alloc_core, and alloc_juicy_variables_e to veric/semax_call.v*)