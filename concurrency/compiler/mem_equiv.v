Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.

Require Import VST.concurrency.lib.setoid_help.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.Clight_bounds.
Require Import VST.concurrency.common.permissions.
(* Require Import VST.concurrency.lib.Coqlib3. *)

Import FunctionalExtensionality.
Import Logic.
Import Basics.
Import BinInt.

Set Bullet Behavior "Strict Subproofs".



(** *Extension to rewrite library:*)
(*    We add partially reflexive relations:
    https://coq.inria.fr/refman/addendum/generalized-rewriting.html#rewriting-and-non-reflexive-relations
 *)


Class PartReflexive {A:Type} (P: A -> Prop) R:=
  { PReflex: forall x : A, P x -> R x x }.
Lemma part_reflexive_proper_proxy {A P} {R: relation A}
      `(PartReflexive A P R) (x : A) : P x -> ProperProxy R x.
  intros. eapply H; auto.
Qed.
(* This ensures that when ProperProxy is ebing resolved,
   partial reflexivity is considered
 *)
Hint Extern 3 (ProperProxy ?R _) => 
not_evar R; class_apply @part_reflexive_proper_proxy;
  try typeclasses eauto; eauto
                         : typeclass_instances.


(* We present two more relations that help take advantage of the above.*)
Inductive trieq {A : Type} (x : A) : A -> A -> Prop :=
| triew_refl: trieq x x x.
Hint Resolve (triew_refl).
Instance trieq_PartReflexive: forall A (x:A), PartReflexive (eq x) (trieq x).
Proof. constructor; intros; subst; constructor. Qed.
Global Instance Symmetric_trieq:
  forall {A} (x:A), Symmetric (trieq x).
Proof.
  intros. intros ???H; inversion H; constructor. Qed.
Global Instance Transitive_trieq:
  forall {A} (x:A), Transitive (trieq x).
Proof.
  intros. intros ??? H1 H2.
  inversion H1; inversion H2. constructor.
Qed. 

Definition eq_P {A : Type} (P:A -> Prop) (x y: A) : Prop := 
  (x = y) /\ P x.
Instance eq_P_PartReflexive: forall {A P}, PartReflexive P (@eq_P A P).
Proof. constructor; intros; subst; constructor; auto. Qed.
Global Instance Symmetric_eq_P:
  forall {A P}, Symmetric (@eq_P A P).
Proof.
  intros. intros ???H; inversion H; subst; constructor; auto. Qed.
Global Instance Transitive_eq_P:
  forall {A P}, Transitive (@eq_P A P).
Proof.
  intros. intros ??? H1 H2.
  inversion H1; inversion H2; subst. constructor; auto.
Qed. 

(* End rewrite extension*)




Ltac rewrite_getPerm_goal:=
  match goal with
  | [|- context[(?f ?m) !! ?b ?ofs ?k] ] =>
    replace ((f m) !! b ofs k) with (permission_at m b ofs k)
      by reflexivity;
    match k with
    | Cur => rewrite <- getCurPerm_correct
    | Max => rewrite <- getMaxPerm_correct
    end
  end.
Ltac rewrite_getPerm_hyp:=
  match goal with
  | [H: context[(?f ?m) !! ?b ?ofs ?k]|- _ ] =>
    replace ((f m) !! b ofs k) with (permission_at m b ofs k) in H
      by reflexivity;
    match k with
    | Cur => rewrite <- getCurPerm_correct in H
    | Max => rewrite <- getMaxPerm_correct in H
    end
  end.
Ltac rewrite_getPerm := first [rewrite_getPerm_goal|rewrite_getPerm_hyp].



Definition access_map_equiv (a1 a2: access_map): Prop :=
  forall b, a1 !! b =  a2 !! b.
Instance access_map_equiv_Equivalence: Equivalence access_map_equiv.
Proof.
  constructor; try constructor; intros ?; intros.
  - unfold access_map_equiv in *; auto.
  - unfold access_map_equiv in *; etransitivity; auto.
Qed.


Ltac destruct_address_range b ofs b0 ofs0 n:=
  let Hrange:= fresh "Hrange" in
  let Hneq:= fresh "Hneq" in
  destruct (Coqlib.peq b b0) as [Hneq | Hneq];
  [subst b0;
   destruct (Intv.In_dec ofs0
                         (ofs, ofs + BinInt.Z.of_nat(n))%Z )
     as [Hrange | Hrange]
  | ].


Instance setPermBlock_access_map_equiv:
  Proper (eq ==> eq ==> eq ==>
             access_map_equiv ==> eq_P (lt 0) ==>  access_map_equiv)
         (setPermBlock ).
Proof.
  proper_intros; inversion H3; subst.
  intros b; extensionality ofs.
  destruct_address_range y0 y1 b ofs y3.
  - unfold Intv.In in *; simpl in *.
    repeat rewrite setPermBlock_same; auto.
  - eapply Intv.range_notin in Hrange; simpl; try omega.
    repeat rewrite setPermBlock_other_1; auto.
    rewrite H2; auto.
  - subst.
    repeat rewrite setPermBlock_other_2; auto.
    rewrite H2; auto.
Qed.

Definition Max_equiv (m1 m2: mem): Prop :=
  access_map_equiv (getMaxPerm m1) (getMaxPerm m2).

Global Instance Equivalenc_Max_equiv:
  Equivalence Max_equiv.
Proof.
  econstructor.
  - intros??; reflexivity.
  - intros ????. symmetry; auto.
  - intros ??????. etransitivity; eauto.
Qed.
Definition Cur_equiv (m1 m2: mem): Prop :=
  access_map_equiv (getCurPerm m1) (getCurPerm m2).
Global Instance Equivalenc_Cur_equiv:
  Equivalence Cur_equiv.
Proof.
  econstructor.
  - intros??; reflexivity.
  - intros ????. symmetry; auto.
  - intros ??????. etransitivity; eauto.
Qed.

Lemma restr_Max_equiv:
  forall {p m}
         (Hlt: permMapLt p (getMaxPerm m)),
    Max_equiv (restrPermMap Hlt) m.
Proof. intros ????.
       extensionality ofs.
       rewrite getMaxPerm_correct.
       apply restrPermMap_Max.
Qed.

Definition content_equiv (m1 m2: mem):=
  forall b ofs,
    ZMap.get ofs (Mem.mem_contents m1) !! b =
    ZMap.get ofs (Mem.mem_contents m2) !! b.
Global Instance Equivalenc_content_equiv:
  Equivalence content_equiv.
Proof.
  econstructor.
  - intros??; reflexivity.
  - intros ????. symmetry; auto.
  - intros ??????. etransitivity; eauto.
Qed.
Lemma restr_content_equiv:
  forall {p m} Hlt,
    content_equiv (@restrPermMap p m Hlt) m.
Proof. intros ?????; reflexivity. Qed.

Record mem_equiv (m1 m2: mem): Prop :=
  { cur_eqv:> Cur_equiv m1 m2;
    max_eqv:> Max_equiv m1 m2;
    content_eqv:>
               content_equiv m1 m2 ;
    nextblock_eqv:> Mem.nextblock m1 = Mem.nextblock m2 }.

Global Instance Equivalence_mem_equiv:
  Equivalence mem_equiv.
Proof.
  econstructor.
  - intros ?; econstructor; reflexivity.
  - intros ?? H; inversion H; econstructor; symmetry; auto.
  - intros ??? H1 H2. inversion H1; inversion H2.
    econstructor; etransitivity; eauto.
Qed.

Instance Proper_perm_max:
  Proper (Max_equiv ==> eq ==> eq ==> (trieq Max) ==> eq ==> iff) Mem.perm.
Proof.
  proper_iff; proper_intros; subst.
  inversion H2; subst.
  unfold Max_equiv in *.
  unfold Mem.perm in *;
    repeat rewrite_getPerm.
  rewrite <- H; auto.
Qed.
Instance Proper_perm_cur:
  Proper (Cur_equiv ==> eq ==> eq ==> (trieq Cur) ==> eq ==> iff) Mem.perm.
Proof.
  proper_iff; proper_intros; subst.
  inversion H2; subst.
  unfold Cur_equiv in *.
  unfold Mem.perm in *;
    repeat rewrite_getPerm.
  - rewrite <- H; auto.
Qed.

Instance Proper_perm:
  Proper (mem_equiv ==> eq ==> eq ==> eq ==> eq ==> iff) Mem.perm.
Proof.
  proper_iff; proper_intros; subst.
  destruct y2; [rewrite <- (max_eqv _ _ H)| erewrite <- (cur_eqv _ _ H)];
    assumption.
Qed.
Instance Proper_perm_Max:
  Proper (Max_equiv ==> eq ==> eq ==> trieq Max ==> eq ==> iff) Mem.perm.
Proof.
  proper_iff; unfold Mem.perm; proper_intros; subst.
  inversion H2; subst.
  repeat rewrite_getPerm; auto. 
  rewrite <- H; assumption.
Qed.

Instance range_perm_mem_equiv:
  Proper (mem_equiv ==> eq ==>  eq ==>  eq ==>  eq ==>  eq ==> iff) Mem.range_perm.
Proof.
  proper_iff; proper_intros; subst.
  unfold Mem.range_perm in *; intros.
  rewrite <- H. eapply H5; auto.
Qed.
Instance range_perm_mem_equiv_Max:
  Proper (Max_equiv ==> eq ==>  eq ==>  eq ==>  trieq Max  ==>  eq ==> iff) Mem.range_perm.
Proof.
  proper_iff; proper_intros; subst.
  inversion H3; subst.
  unfold Mem.range_perm in *; intros.
  rewrite <- H. eapply H5; auto.
Qed.
Instance range_perm_mem_equiv_Cur:
  Proper (Cur_equiv ==> eq ==>  eq ==>  eq ==>  trieq Cur  ==>  eq ==> iff) Mem.range_perm.
Proof.
  proper_iff; proper_intros; subst.
  inversion H3; subst.
  unfold Mem.range_perm in *; intros.
  rewrite <- H. eapply H5; auto.
Qed.

Instance mem_inj_equiv:
  Proper ( eq ==> mem_equiv ==> mem_equiv ==> iff) Mem.mem_inj.
Proof.
  proper_iff. proper_intros; subst.
  econstructor; intros.
  - rewrite <- H1.
    rewrite <- H0 in H3.
    eapply H2; eauto.
  - eapply H2; eauto.
    rewrite H0; eauto.
  - rewrite <- H0 in H3.
    destruct H0; destruct H1.
    unfold content_equiv in *.
    rewrite <- content_eqv0.
    rewrite <- content_eqv1.
    eapply H2; eauto.
Qed.

Instance Proper_nextblock:
  Proper (mem_equiv ==> Logic.eq) Mem.nextblock.
Proof. intros ???. erewrite nextblock_eqv; auto. Qed.

Instance Proper_valid_block:
  Proper (mem_equiv ==> Logic.eq ==> Logic.eq) Mem.valid_block.
Proof.
  intros ??????.
  subst; unfold Mem.valid_block.
  rewrite H; reflexivity.
Qed.


Instance Proper_no_overlap_max_equiv:
  Proper (Logic.eq ==> Max_equiv ==> iff)
         Mem.meminj_no_overlap.
Proof.
  unfold Mem.meminj_no_overlap.
  proper_iff. proper_intros; subst.
  eapply H1; unfold  Mem.perm in *; eauto.
  - repeat rewrite_getPerm.
    rewrite H0; auto.
  - repeat rewrite_getPerm.
    rewrite H0; auto.
Qed.


Instance Proper_no_overlap_mem_equiv:
  Proper (eq ==> mem_equiv ==> iff) Mem.meminj_no_overlap.
Proof.
  proper_iff. proper_intros; subst.
  eapply Proper_no_overlap_max_equiv; eauto.
  symmetry; apply H0.
Qed.

Instance mem_inject_equiv:
  Proper  ( eq ==> mem_equiv ==> mem_equiv ==> iff) Mem.inject.
Proof.
  proper_iff.
  intros ?????  Heqv1 ?? Heqv2 Hinj; subst.
  symmetry in Heqv1, Heqv2.
  econstructor.
  - rewrite Heqv1, Heqv2. eapply Hinj.
  - intros ?.
    rewrite Heqv1. eapply Hinj.
  - intros ???.
    rewrite Heqv2. eapply Hinj.
  - rewrite Heqv1. apply Hinj.
  - intros. eapply Hinj; eauto.
    rewrite <- Heqv1; auto.
  - intros ???????.
    rewrite Heqv2, Heqv1.
    apply Hinj; auto.
Qed.

Instance permMapLt_equiv:
  Proper (access_map_equiv ==> access_map_equiv ==> iff)
         permMapLt.
Proof. proper_iff. intros ?????? HH ??; rewrite <- H, <- H0; auto. Qed.

Lemma getCur_restr:
  forall perm m (Hlt: permMapLt perm (getMaxPerm m)),
    access_map_equiv
      (getCurPerm (restrPermMap Hlt))  perm.
Proof.
  unfold getCurPerm, access_map_equiv.
  intros; simpl.
  rewrite PMap.gmap.
  Import FunctionalExtensionality.
  extensionality ofs; simpl.
  unfold PMap.get; simpl.
  rewrite PTree.gmap.
  destruct ((snd (Mem.mem_access m)) ! b) eqn:HH.
  - reflexivity.
  - simpl.
    specialize (Hlt b ofs).
    rewrite getMaxPerm_correct in Hlt;
      unfold permission_at in Hlt.
    unfold PMap.get in Hlt.
    rewrite HH in Hlt.
    rewrite Clight_bounds.Mem_canonical_useful in Hlt.
    simpl in Hlt.
    destruct ( (snd perm) ! b).
    + destruct (o ofs); first [contradiction | auto].
    + destruct (fst perm ofs); first [contradiction | auto].
Qed.
Lemma getMax_restr:
  forall perm m (Hlt: permMapLt perm (getMaxPerm m)),
    access_map_equiv
      (getMaxPerm (restrPermMap Hlt))  (getMaxPerm m) .
Proof. intros; intros ?; eapply getMax_restr. Qed.


Lemma restrPermMap_equiv:
  forall perm1 perm2 m1 m2
         Hlt1 Hlt2,
    mem_equiv m1 m2 ->
    access_map_equiv perm1 perm2 ->
    mem_equiv (@restrPermMap perm1 m1 Hlt1)
              (@restrPermMap perm2 m2 Hlt2).
Proof.
  intros. inversion H.
  econstructor.
  - unfold Cur_equiv; do 2 rewrite getCur_restr; auto.
  - unfold Max_equiv; intros ?.
    do 2 rewrite getMax_restr; auto.
  - simpl; eauto.
  - simpl. auto.
Qed.
Lemma restrPermMap_idempotent:
  forall perm0 perm1 m1 Hlt0 Hlt1 Hlt2, 
    mem_equiv (@restrPermMap perm1 m1 Hlt1)
              (@restrPermMap perm1 (@restrPermMap perm0 m1 Hlt0) Hlt2).
Proof.
  intros; econstructor.
  - unfold Cur_equiv; do 2 rewrite getCur_restr; reflexivity.
  - unfold Max_equiv; intros ?.
    do 3 rewrite getMax_restr; auto.
  - simpl; eauto.
    etransitivity; try eapply restr_content_equiv.
    etransitivity; try eapply (restr_content_equiv Hlt2).
  - simpl; eapply nextblock_eqv; reflexivity.
Qed.
Arguments restrPermMap_idempotent {_ _ _} _ _.

Lemma useful_permMapLt_trans:
  forall {perm m perm0} Hlt0,
    permMapLt perm (getMaxPerm m) ->
    permMapLt perm (getMaxPerm (@restrPermMap perm0 m Hlt0)).

Proof. unfold permMapLt; intros. rewrite getMax_restr; eauto. Qed.

Lemma restrPermMap_idempotent':
  forall perm0 perm1 m1 Hlt0 Hlt1 , 
    mem_equiv (@restrPermMap perm1 m1 Hlt1)
              (@restrPermMap perm1 (@restrPermMap perm0 m1 Hlt0)
                             (useful_permMapLt_trans Hlt0 Hlt1)).
Proof. intros; eapply restrPermMap_idempotent. Qed.

Lemma restr_proof_irr_equiv:
  forall m perm Hlt Hlt',
    mem_equiv (@restrPermMap m perm Hlt) (@restrPermMap m perm Hlt').
  intros. replace Hlt with Hlt'.
  - reflexivity. 
  - apply Axioms.proof_irr.
Qed.


Instance valid_access_Proper:
  Proper (mem_equiv  ==> Logic.eq ==> Logic.eq  ==>
                     Logic.eq ==> Logic.eq ==> iff) Mem.valid_access.
Proof.
  unfold Mem.valid_access.
  setoid_help.proper_iff; setoid_help.proper_intros; subst.
  rewrite <- H; auto.
Qed.
Instance load_Proper:
  Proper (Logic.eq ==> mem_equiv ==> Logic.eq ==> Logic.eq  ==> Logic.eq) Mem.load.
Proof.
  setoid_help.proper_intros; subst.
  Transparent Mem.load.
  unfold Mem.load.
  destruct (Mem.valid_access_dec x0 y y1 y2 Readable) as [v|v];
    rewrite H0 in v;
    destruct (Mem.valid_access_dec y0 y y1 y2 Readable);
    (* solve the impossible ones*)
    try solve[contradict v; auto].
  - destruct  H0. do 2 f_equal.
    clear - content_eqv0 y1 y2.
    revert y2 y1.
    induction (size_chunk_nat y); auto; intros.
    simpl.  f_equal; eauto.
  - reflexivity.
Qed.

Instance loadv_Proper:
  Proper (Logic.eq ==> mem_equiv ==> Logic.eq  ==> Logic.eq) Mem.loadv.
Proof. intros ??? ??? ???; subst.
       destruct y1; auto.
       eapply load_Proper; auto.
Qed.


Lemma cur_equiv_restr_mem_equiv:
  forall (m:mem) p
    (Hlt: permMapLt p (getMaxPerm m)),
    access_map_equiv p (getCurPerm m) ->
    mem_equiv (restrPermMap Hlt) m.
Proof.
  intros. constructor; eauto.
  - unfold Cur_equiv. etransitivity; eauto.
    eapply getCur_restr.
  - eapply getMax_restr.
  - eapply restr_content_equiv.
Qed.
Lemma mem_access_max_equiv:
  forall m1 m2, Mem.mem_access m1 =  Mem.mem_access m2 ->
           Max_equiv m1 m2.
Proof. intros ** ?; unfold getMaxPerm; simpl.
       rewrite H; reflexivity.
Qed.
Lemma mem_access_cur_equiv:
  forall m1 m2, Mem.mem_access m1 = Mem.mem_access m2 ->
           Cur_equiv m1 m2.
Proof. intros ** ?; unfold getCurPerm; simpl.
       rewrite H; reflexivity.
Qed.

Lemma Cur_equiv_restr:
  forall p1 p2 m1 m2 Hlt1 Hlt2,
    access_map_equiv p1 p2 ->
    Cur_equiv (@restrPermMap p1 m1 Hlt1)
              (@restrPermMap p2 m2 Hlt2).
Proof. unfold Cur_equiv; intros.
       do 2 rewrite getCur_restr; assumption. Qed.
Lemma Max_equiv_restr:
  forall p1 p2 m1 m2 Hlt1 Hlt2,
    Max_equiv m1 m2 ->
    Max_equiv (@restrPermMap p1 m1 Hlt1)
              (@restrPermMap p2 m2 Hlt2).
Proof. unfold Max_equiv; intros.
       do 2 rewrite getMax_restr; assumption. Qed.

Lemma store_max_eq:
  forall cnk  m b ofs v m',
    Mem.store cnk  m b ofs v = Some m' ->
    getMaxPerm m = getMaxPerm m'.
Proof.
  intros.
  Transparent Mem.store.
  unfold Mem.store in H; simpl in *.
  destruct (Mem.valid_access_dec m cnk b ofs Writable); try discriminate.
  inversion H. reflexivity.
Qed.
Lemma store_max_equiv:
  forall sz m b ofs v m',
    Mem.store sz m b ofs v = Some m' ->
    Max_equiv m m'.
Proof.
  intros. intros ?.
  erewrite store_max_eq; eauto.
Qed.