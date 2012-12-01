Load loadpath.
Require Import veric.base.
Require Import veric.Address.
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

Program Definition juicy_mem_alloc j lo hi: juicy_mem * block :=
  (alloc_juicy_mem j lo hi (fst (alloc (m_dry j) lo hi)) (snd (alloc (m_dry j) lo hi)) _, snd (alloc (m_dry j) lo hi)).

Lemma juicy_mem_alloc_succeeds: forall j j' b lo hi,
  juicy_mem_alloc j lo hi = (j', b) -> (m_dry j', b) = alloc (m_dry j) lo hi.
Proof.
intros until hi; intro H.
unfold juicy_mem_alloc in H.
inv H.
simpl.
destruct (alloc (m_dry j) lo hi); simpl; auto.
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

