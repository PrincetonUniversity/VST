Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.lib.Coqlib3.
Require Import VST.concurrency.common.permissions. Import permissions.
Import BinNums.

Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.
Require Import VST.concurrency.common.bounded_maps.

Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.compiler.pair.
Require Import VST.concurrency.lib.setoid_help.

Ltac unify_injection:=
  match goal with
    [H: ?mu ?x = _,H0: ?mu ?x = _ |- _] =>
    match type of mu with
    | meminj => rewrite H in H0; invert H0
    | block -> option (block * Z) => rewrite H in H0; invert H0
    end
  end.
Local Ltac unify_mapping:=
  match goal with
    [H: ?a !! ?x ?y = Some _ ,
        H0: ?a !! ?x ?y = _ |- _] => rewrite H in H0
  | [H: ?a !! ?x ?y = None ,
        H0: ?a !! ?x ?y = _ |- _] => rewrite H in H0
  | [H: ?a !! ?x ?y = Some _ ,
        H0: _ = ?a !! ?x ?y |- _] => rewrite H in H0
  | [H: ?a !! ?x ?y = None ,
        H0: _ = ?a !! ?x ?y |- _] => rewrite H in H0
  end.

Definition inject_lock' size mu (b_lock:block) (ofs_lock: Z) (m1 m2:mem):=
  exists b_lock' delt,
    mu b_lock = Some (b_lock', delt) /\ 
    ( forall ofs0,
        Intv.In ofs0 (ofs_lock, (ofs_lock + size)%Z) ->
        memval_inject mu
                      (ZMap.get ofs0 (Mem.mem_contents m1) !! b_lock)
                      (ZMap.get (ofs0 + delt)%Z
                                (Mem.mem_contents m2) !! b_lock')).

Definition inject_lock := inject_lock' LKSIZE.
Lemma inject_lock_morphism':
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==>
                   content_equiv ==> content_equiv ==> Basics.impl) inject_lock.
Proof.
  intros ??????????????? (b' & delt & Hinj & HH) ; subst.
  repeat (econstructor; eauto).
  intros ? H. eapply HH in H.
  rewrite <- H2, <- H3; assumption.
Qed.
Instance inject_lock_morphism:
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==>
                   content_equiv ==> content_equiv ==> iff) inject_lock.
Proof. split; eapply inject_lock_morphism'; eauto; symmetry; auto. Qed.

Definition inject_lock_simpl
           size mu (b_lock:block) (ofs_lock: Z) (m1 m2:mem):=
  forall b_lock' delt,
    mu b_lock = Some (b_lock', delt) -> 
    ( forall ofs0,
        Intv.In ofs0 (ofs_lock, (ofs_lock + size)%Z) ->
        memval_inject mu
                      (ZMap.get ofs0 (Mem.mem_contents m1) !! b_lock)
                      (ZMap.get (ofs0 + delt)%Z
                                (Mem.mem_contents m2) !! b_lock')).
Lemma inject_lock_simplification:
  forall n mu b_lock ofs_lock m1 m2,
    inject_lock' n mu b_lock ofs_lock m1 m2 ->
    inject_lock_simpl n mu b_lock ofs_lock m1 m2.
Proof. intros. destruct H as (? &? &?&HH).
       unfold inject_lock_simpl; intros.
       rewrite H in H0; inversion H0; subst.
       eauto.
Qed.


Definition option_implication {A B} (oa:option A) (ob: option B):=
  match oa, ob with | Some _, None => False | _, _ => True end.
Definition map_option_implication {A B} (m1:PTree.t A) (m2:PTree.t B):=
  forall b, option_implication (m1 ! b) (m2 ! b).

Definition at_least_Some {A} (x:option A):=
  option_implication (Some tt) x.

Lemma at_least_Some_trivial:
  forall {A} x y, x = Some y -> @at_least_Some A x.
Proof. intros; subst; constructor. Qed.

Lemma at_least_Some_perm_Cur:
  forall m1 b1 ofs,
    at_least_Some ((getCurPerm m1) !! b1 ofs) <->
    Mem.perm m1 b1 ofs Cur Nonempty.
Proof.
  intros *. rewrite getCurPerm_correct; auto.
  unfold at_least_Some,Mem.perm, permission_at in *.
  destruct ((Mem.mem_access m1) !! b1 ofs Cur);
    split; intros; auto; constructor.
Qed.
Lemma at_least_Some_perm_Max:
  forall m1 b1 ofs,
    at_least_Some ((getMaxPerm m1) !! b1 ofs) <->
    Mem.perm m1 b1 ofs Max Nonempty.
Proof.
  intros *. rewrite getMaxPerm_correct; auto.
  unfold at_least_Some,Mem.perm, permission_at in *.
  destruct ((Mem.mem_access m1) !! b1 ofs Max);
    split; intros; auto; constructor.
Qed.
Definition perm_image (f:meminj) (a1: access_map): Prop:=
  forall b1 ofs, at_least_Some (a1 !! b1 ofs) ->
            exists b2 delta, f b1 = Some (b2, delta).
Instance proper_perm_image:
  Proper (Logic.eq ==> access_map_equiv ==> iff) perm_image.
Proof.
  unfold perm_image.
  setoid_help.proper_iff; setoid_help.proper_intros; subst.
  rewrite <- H0 in *; eauto.
Qed.
(* The injection maps to every visible location *)
Definition perm_surj (mu:meminj) (a1 a2: access_map):=
  forall b2 ofs_delt,
    at_least_Some (a2 !! b2 ofs_delt) ->
    exists b1 ofs delt, mu b1 = Some (b2, delt) /\
                   ofs_delt = ofs + delt /\
                   a2 !! b2 ofs_delt = a1 !! b1 ofs.



(* The injection maps all visible locations*)



Definition access_map_injected (f:meminj) (pmap1 pmap2: access_map):=
  forall (b1 b2 : block) (delt ofs: Z),
    f b1 = Some (b2, delt) ->
    Mem.perm_order'' (pmap2 !! b2 (ofs+delt)%Z) (pmap1 !! b1 ofs).

Lemma access_map_injected_getMaxPerm:
  forall f m1 m2,
    Mem.inject f m1 m2 ->
    access_map_injected f (getMaxPerm m1) (getMaxPerm m2).
  intros. intros ?????.
  do 2 rewrite getMaxPerm_correct.
  destruct (permission_at m1 b1 ofs Max) eqn:HH.
  - rewrite <- mem_lemmas.po_oo.
    eapply Mem.mi_perm; eauto.
    + apply H.
    + unfold Mem.perm.
      unfold permission_at in HH; rewrite HH.
      simpl. apply perm_refl.
  - apply event_semantics.po_None.
Qed.
Lemma access_map_injected_getCurPerm:
  forall f m1 m2,
    Mem.inject f m1 m2 ->
    access_map_injected f (getCurPerm m1) (getCurPerm m2).
  intros. intros ?????.
  do 2 rewrite getCurPerm_correct.
  destruct (permission_at m1 b1 ofs Cur) eqn:HH.
  - rewrite <- mem_lemmas.po_oo.
    eapply Mem.mi_perm; eauto.
    + apply H.
    + unfold Mem.perm.
      unfold permission_at in HH;
        rewrite HH.
      simpl.
      apply perm_refl.
  - apply event_semantics.po_None.
Qed.

Lemma setPermBlock_inject_permMapLt':
  forall n (NZ: (0 < n)%nat)
    (m1 m2 : mem) 
    (mu : meminj) cur_perm1 cur_perm2 max_perm1 max_perm2
    (b : block) ofs P,
    permMapLt (setPermBlock P b (ofs) cur_perm1 n)
              max_perm1 ->
    Mem.inject mu m1 m2 ->
    access_map_injected mu max_perm1 max_perm2 -> 
    forall (b' : block) (delt : Z),
      mu b = Some (b', delt) ->
      permMapLt cur_perm2 max_perm2 ->
      permMapLt (setPermBlock P b' (ofs + delt)
                              cur_perm2 n) max_perm2.
Proof.
  intros; intros b0 ofs0.
  destruct (base.block_eq_dec b' b0);
    [destruct (Intv.In_dec ofs0 ((ofs + delt)%Z, (ofs + delt + (Z.of_nat n))%Z))|
    ].
  - subst. unfold Intv.In in i; simpl in *.
    rewrite setPermBlock_same; auto.
    replace ofs0 with ((ofs0 - delt) + delt)%Z by omega.
    eapply juicy_mem.perm_order''_trans.
    2:{ unfold permMapLt in H.
        specialize (H b (ofs0 - delt)%Z).
        rewrite setPermBlock_same in H; auto; try omega.
        eauto. }    
    + eapply H1; auto.
  - subst; rewrite setPermBlock_other_1; eauto.
    + eapply Intv.range_notin in n0; auto; simpl.  clear -NZ.
      assert ( 0 < Z.of_nat n).
      { replace 0 with (Z.of_nat 0) by reflexivity.
        eapply Nat2Z.inj_lt; auto. }
      omega.
  - subst; rewrite setPermBlock_other_2; eauto.
Qed.
Lemma setPermBlock_inject_permMapLt:
  forall n (NZ: (0 < n)%nat)
    (m1 m2 : mem) 
    (mu : meminj) cur_perm1 cur_perm2 max_perm1 max_perm2
    (b : block) ofs P,
    permMapLt (setPermBlock P b (ofs) cur_perm1 n)
              max_perm1 ->
    Mem.inject mu m1 m2 ->
    access_map_injected mu max_perm1 max_perm2 -> 
    forall (b' : block) (delt : Z),
      mu b = Some (b', delt) ->
      permMapLt cur_perm2 max_perm2 ->
      permMapLt (setPermBlock P b' (ofs + delt)
                              cur_perm2 n) max_perm2.
Proof.
  intros ??. eapply setPermBlock_inject_permMapLt'; assumption.
Qed.






























(* bounded_maps*)


Lemma setPermBlock_extensionality:
  forall perm b ofs perm_map1 perm_map2 n,
    (0 < n)%nat ->
    (forall b0, perm_map1 !! b0 = perm_map2 !! b0) -> 
    forall b0, (setPermBlock perm b ofs perm_map1 n) !! b0=
          (setPermBlock perm b ofs perm_map2 n) !! b0.
Proof.
  intros.
  extensionality ofs0.
  destruct_address_range b ofs b0 ofs0 n.
  - do 2 (rewrite setPermBlock_same; auto).
  - eapply Intv.range_notin in Hrange;
      try (simpl; omega).
    do 2 (erewrite setPermBlock_other_1; auto).
    rewrite (H0 b); auto.
  - do 2 (rewrite setPermBlock_other_2; auto).
    rewrite H0; auto.
Qed.

(* New permissions*)



(* Permissions *)
Global Instance perm_preimage_setoid:
  Proper (Logic.eq ==> access_map_equiv ==>
                   access_map_equiv ==> iff) perm_surj.
Proof.
  proper_iff. proper_intros; subst.
  unfold perm_surj in *; intros ?? HH.
  rewrite <- H1 in HH.
  eapply H2 in HH.
  destruct HH as (?&?&?&?&?&?); subst.
  do 3 econstructor. repeat (split; eauto).
  rewrite <- H1, <- H0; auto.
Qed.

Lemma access_map_injected_morphism':
  Proper (Logic.eq ==> access_map_equiv  ==> access_map_equiv ==> Basics.impl)
         access_map_injected.
Proof.
  intros ????????? HH ?????; subst.
  rewrite <- H1, <- H0. eapply HH; eauto.
Qed.
Instance access_map_injected_morphism:
  Proper (Logic.eq ==> access_map_equiv  ==> access_map_equiv ==> Logic.iff)
         access_map_injected.
Proof. split; eapply access_map_injected_morphism'; auto; symmetry; auto. Qed.


Lemma permMapLt_extensional1:
  forall p1 p2 p3,
    (forall b, p2 !! b = p3 !! b) -> 
    permMapLt p1 p2 -> permMapLt p1 p3.
Proof. intros; intros ??. rewrite <- H. eapply H0. Qed.
Lemma permMapLt_extensional2:
  forall p1 p2 p3,
    (forall b, p1 !! b = p2 !! b) -> 
    permMapLt p1 p3 -> permMapLt p2 p3.
Proof. intros; intros ??. rewrite <- H. eapply H0. Qed.


Definition mi_perm_perm (f:meminj) perm1 perm2:=
  forall (b1 b2 : block) (delta ofs : Z)(p : permission),
    f b1 = Some (b2, delta) ->
    Mem.perm_order' (perm1 !! b1 ofs) p ->
    Mem.perm_order' (perm2 !! b2 (ofs + delta)) p.
Instance proper_mi_perm_perm:
  Proper (Logic.eq ==> access_map_equiv ==> access_map_equiv ==> iff)
         mi_perm_perm.
Proof.
  unfold mi_perm_perm.
  setoid_help.proper_iff;
    setoid_help.proper_intros; subst.
  rewrite <- H1. eapply H2; eauto.
  rewrite H0; eassumption.
Qed.
Definition mi_memval_perm (f:meminj) (perm1:access_map) cont1 cont2:=
  forall b1 b2 delta ofs,
    f b1 = Some (b2, delta) ->
    Mem.perm_order' (perm1 !! b1 ofs) Readable ->
    memval_inject f (ZMap.get ofs cont1 !! b1)
                  (ZMap.get (ofs + delta) cont2 !! b2).
Instance proper_mi_memval_perm:
  Proper (Logic.eq ==> access_map_equiv ==>
                   Logic.eq ==> Logic.eq ==> iff)
         mi_memval_perm.
Proof.
  unfold mi_memval_perm.
  setoid_help.proper_iff;
    setoid_help.proper_intros; subst.
  eapply H3; auto.
  rewrite H0; assumption.
Qed.
Lemma mem_inj_restr:
  forall mu m1 m2 perm1 perm2,
  forall (Hlt1: permMapLt perm1 (getMaxPerm m1))
    (Hlt2: permMapLt perm2 (getMaxPerm m2)),
    mi_perm_perm mu perm1 perm2 ->
    mi_memval_perm mu perm1 (Mem.mem_contents m1) (Mem.mem_contents m2) ->
    Mem.mem_inj mu m1 m2 ->
    Mem.mem_inj mu (restrPermMap Hlt1) (restrPermMap Hlt2).
Proof.
  intros * Hmi_perm Hmi_align H; econstructor.
  - unfold Mem.perm; intros.
    destruct k; repeat rewrite_getPerm.
    + (* Max *)
      rewrite getMax_restr in *.
      eapply H with (k:=Max) in H0;
        unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
    + rewrite getCur_restr in *.
      eapply Hmi_perm; eassumption.
  - intros * ?. 
    rewrite restr_Max_equiv.
    eapply H; eassumption.
  - intros *; simpl.
    unfold Mem.perm.
    rewrite_getPerm.
    rewrite getCur_restr.
    apply Hmi_align.
Qed.

Definition mi_perm_inv_perm f perm1 perm2 m1:=
  forall (b1 : block) (ofs : Z) (b2 : block) 
    (delta : Z) (p : permission),
    f b1 = Some (b2, delta) ->
    Mem.perm_order' (perm2 !! b2 (ofs + delta)) p ->
    Mem.perm_order' (perm1 !! b1 ofs) p
    \/ ~ Mem.perm m1 b1 ofs Max Nonempty.

Instance proper_mi_perm_inv_perm:
  Proper (Logic.eq ==> access_map_equiv ==> access_map_equiv ==>
                   Max_equiv ==> iff) mi_perm_inv_perm.
Proof.
  unfold mi_perm_inv_perm.
  setoid_help.proper_iff;
    setoid_help.proper_intros; subst.
  rewrite <- H0, <- H2.
  eapply H3; eauto.
  rewrite H1; assumption.
Qed.
Lemma inject_restr:
  forall mu m1 m2 perm1 perm2,
  forall (Hlt1: permMapLt perm1 (getMaxPerm m1))
    (Hlt2: permMapLt perm2 (getMaxPerm m2)),
    mi_perm_perm mu perm1 perm2 ->
    mi_memval_perm mu perm1 (Mem.mem_contents m1) (Mem.mem_contents m2) ->
    mi_perm_inv_perm mu perm1 perm2 m1 ->
    Mem.inject mu m1 m2 ->
    Mem.inject mu (restrPermMap Hlt1) (restrPermMap Hlt2).
Proof.
  intros * Hmi_perm Hmi_align Hmi_perm_inv; econstructor.
  - apply mem_inj_restr; try assumption. apply H.
  - intros ? Hnot_valid; apply H.
    eauto using restrPermMap_valid.
  - intros.
    eapply restrPermMap_valid. eapply H. eassumption.
  - rewrite restr_Max_equiv. apply H.
  - intros. rewrite restr_Max_equiv in H1.
    eapply H; eauto.
  - intros until delta.
    intros [] *.
    + repeat rewrite restr_Max_equiv.
      eapply H; eauto.
    + unfold Mem.perm; repeat rewrite_getPerm.
      repeat rewrite getCur_restr;
        rewrite getMax_restr.
      rewrite getMaxPerm_correct.
      eapply Hmi_perm_inv.
Qed.



Lemma setPermBlock_mi_perm_Cur:
  forall (mu : meminj) (m1 m2 : mem) (b b' : block) (ofs delt : Z) 
    (n : nat),
    (0 < n)%nat ->
    forall (Hno_overlap:Mem.meminj_no_overlap mu m1)
      (Hlt1 : permMapLt (setPermBlock (Some Writable)
                                      b ofs (getCurPerm m1) n) (getMaxPerm m1))
      (Hlt2 : permMapLt (setPermBlock (Some Writable)
                                      b' (ofs + delt) (getCurPerm m2) n)
                        (getMaxPerm m2)),
      mu b = Some (b', delt) ->
      Mem.mem_inj mu m1 m2 ->
      forall (b1 b2 : block) (delta ofs0 : Z) (p : permission),
        mu b1 = Some (b2, delta) ->
        Mem.perm_order' ((getCurPerm (restrPermMap Hlt1)) !! b1 ofs0) p ->
        Mem.perm_order' ((getCurPerm (restrPermMap Hlt2)) !! b2 (ofs0 + delta)%Z) p.
Proof.
  intros mu m1 m2 b b' ofs delt n Neq
         Hno_overlap Hlt1 Hlt2 H0 H1 b1 b2 delta ofs0 p H2 H3.
  
  rewrite getCur_restr in *.
  destruct_address_range b1 ofs b ofs0 n.
  - rewrite setPermBlock_same in H3; auto.
    rewrite H2 in H0; inversion H0; subst.
    rewrite setPermBlock_same; auto.
    unfold Intv.In in Hrange; simpl in Hrange.
    omega.
  - eapply Intv.range_notin in Hrange;
      try (simpl; omega).
    erewrite setPermBlock_other_1 in H3; auto.
    rewrite H2 in H0; inversion H0; subst.
    erewrite setPermBlock_other_1; auto.
    + rewrite getCurPerm_correct in *.
      eapply H1; eauto.
    + destruct Hrange; simpl in *; [left | right]; omega.
      
  - rewrite setPermBlock_other_2 in H3; auto.
    
    pose proof (Classical_Prop.classic
                  (Mem.perm_order'' (Some p) (Some Nonempty))) as [HH|HH].
    2: { destruct p; try solve[contradict HH; constructor]. }
    
    assert (HNoneempty:Mem.perm m1 b1 ofs0 Max Nonempty).
    { unfold Mem.perm. rewrite mem_lemmas.po_oo in *.
      eapply juicy_mem.perm_order''_trans; eauto.
      eapply juicy_mem.perm_order''_trans; eauto.
      rewrite getCurPerm_correct.
      eapply Mem.access_max. }

    assert (Hrange_no_overlap := Hneq).
    eapply setPermBLock_no_overlap in Hrange_no_overlap; eauto.
    
    destruct Hrange_no_overlap as [H | [H H']]; eauto.
    
    --  erewrite setPermBlock_other_2; auto.
        rewrite getCurPerm_correct.
        eapply H1; eauto.
        unfold Mem.perm. rewrite_getPerm; auto.
    -- subst; erewrite setPermBlock_other_1; auto.
       rewrite getCurPerm_correct.
       eapply H1; eauto.
       unfold Mem.perm. rewrite_getPerm; auto.
       eapply Intv.range_notin in H'; auto.
       simpl; omega.
Qed.

Lemma setPermBlock_mem_inj:
  forall mu m1 m2 b b' ofs delt n,
    (0 < n)%nat ->
    forall (Hinject_lock: inject_lock' (Z.of_nat n) mu b ofs m1 m2)
      (Hno_overlap:Mem.meminj_no_overlap mu m1)
      (Hlt1: permMapLt
               (setPermBlock (Some Writable) b ofs
                             (getCurPerm m1)
                             n) (getMaxPerm m1))
      
      (Hlt2: permMapLt
               (setPermBlock (Some Writable) b' (ofs + delt)
                             (getCurPerm m2)
                             n) (getMaxPerm m2)),
      mu b = Some (b', delt) ->
      Mem.mem_inj mu m1 m2 ->
      Mem.mem_inj mu (restrPermMap Hlt1) (restrPermMap Hlt2).
Proof.
  intros; econstructor.
  - unfold Mem.perm; intros.
    destruct k.
    + repeat rewrite_getPerm.
      rewrite getMax_restr in *.
      rewrite getMaxPerm_correct in *.
      eapply H1; eauto.
    + repeat rewrite_getPerm.
      eapply setPermBlock_mi_perm_Cur; eauto.
  - intros.
    eapply H1; eauto.
    unfold Mem.range_perm, Mem.perm in *.
    intros.
    specialize (H3 _ H4).
    repeat rewrite_getPerm.
    rewrite getMax_restr in H3; eauto.
  - intros; simpl.
    unfold Mem.perm in *. 
    repeat rewrite_getPerm.
    rewrite getCur_restr in H3.
    destruct_address_range b ofs b1 ofs0 n.

    + eapply inject_lock_simplification; eauto.

    + eapply H1; auto.
      rewrite setPermBlock_other_1 in H3; auto.
      unfold Mem.perm; rewrite_getPerm; auto.
      eapply Intv.range_notin in Hrange; simpl; auto.
      omega.
      
    + eapply H1; auto.
      rewrite setPermBlock_other_2 in H3; auto.
      unfold Mem.perm; rewrite_getPerm; auto.
Qed.

(* Last case for Mem.inject,
                       using setPermBlock with Cur
                       Helper lemma for setPermBlock_mem_inject
 *)
Lemma setPermBlock_mi_perm_inv_Cur:
  forall b1 b1' ofs delt1 m1 m2 n mu,
    (0 < n)%nat -> 
    forall (Hlt1: permMapLt
               (setPermBlock (Some Writable)
                             b1 ofs (getCurPerm m1) n)
               (getMaxPerm m1))
      (Hlt2: permMapLt
               (setPermBlock (Some Writable)
                             b1' (ofs + delt1) (getCurPerm m2) n)
               (getMaxPerm m2))
      (Hinject:Mem.inject mu m1 m2),
      mu b1 = Some (b1', delt1) -> 
      forall b2 b2' ofs0 delt2 p,
        let m1_restr := (restrPermMap Hlt1) in
        let m2_restr := (restrPermMap Hlt2) in
        mu b2 = Some (b2', delt2) ->
        Mem.perm m2_restr b2' (ofs0 + delt2) Cur p ->
        Mem.perm m1_restr b2 ofs0 Cur p \/
        ~ Mem.perm m1_restr b2 ofs0 Max Nonempty.
Proof.
  intros.
  unfold Mem.perm in *.
  repeat rewrite_getPerm.
  subst m1_restr m2_restr; rewrite getCur_restr in *.
  rewrite getMax_restr.
  (* try to do it backwards: destruct source blocks first*)
  destruct_address_range
    b1 (ofs)%Z b2 (ofs0)%Z n.
  - rewrite H0 in H1; inversion H1; subst.
    rewrite setPermBlock_same.
    2: { unfold Intv.In in *; auto. }
    rewrite setPermBlock_same in H2.
    2: { unfold Intv.In in *; simpl in *; omega. } 
    auto.
  - rewrite H0 in H1; inversion H1; subst.
    rewrite setPermBlock_other_1.
    2: { eapply Intv.range_notin in Hrange; eauto.
         simpl; omega. }
    rewrite setPermBlock_other_1 in H2.
    2: { eapply Intv.range_notin in Hrange; eauto;
         simpl in *; omega. }
    rewrite getCurPerm_correct, getMaxPerm_correct in *.
    eapply Hinject; eauto.
  - pose proof (Classical_Prop.classic
                  (Mem.perm_order' ((getMaxPerm m1) !! b2 ofs0) Nonempty))
      as [HH|HH]; try eauto.
    rewrite setPermBlock_other_2; eauto.
    rewrite getCurPerm_correct, getMaxPerm_correct in *.
    eapply Hinject; eauto.
    unfold Mem.perm in *; rewrite_getPerm.
    
    (* now destruct the addresses for the target blocks*)
    destruct_address_range
      b1' (ofs+delt1)%Z b2' (ofs0 + delt2)%Z n.
    + exploit (@range_no_overlap mu m1 b2 b1' b1 b1');
        try apply Hneq; eauto.
      * eapply Hinject.
      * eapply setPermBlock_range_perm in Hlt1.
        eapply range_perm_trans; eauto.
        constructor.
      * intros [?|[? ?]].
        -- contradict H3; auto.
        -- contradict H4; eassumption.
    + rewrite setPermBlock_other_1 in H2; eauto.
      eapply Intv.range_notin in Hrange; simpl in *; omega.
    + rewrite setPermBlock_other_2 in H2; eauto.
Qed.

Lemma setPermBlock_mem_inject:
  forall mu m1 m2 b b' ofs delt LKSIZE_nat,
    (0 < LKSIZE_nat)%nat ->
    forall (Hinject_lock: inject_lock' (Z.of_nat LKSIZE_nat) mu b ofs m1 m2)
      (Hlt1: permMapLt
               (setPermBlock (Some Writable) b ofs
                             (getCurPerm m1)
                             LKSIZE_nat) (getMaxPerm m1))
      
      (Hlt2: permMapLt
               (setPermBlock (Some Writable) b' (ofs + delt)
                             (getCurPerm m2)
                             LKSIZE_nat) (getMaxPerm m2)),
      mu b = Some (b', delt) ->
      Mem.inject mu m1 m2 ->
      Mem.inject mu (restrPermMap Hlt1) (restrPermMap Hlt2).
Proof.
  intros.
  intros; econstructor.
  - eapply setPermBlock_mem_inj; auto; eapply H1.
  - intros ?; rewrite restrPermMap_valid.
    eapply H1. 
  - intros. apply restrPermMap_valid.
    eapply H1; eauto.
  - pose proof (restr_Max_equiv Hlt1).
    eapply Proper_no_overlap_max_equiv; eauto.
    eapply H1.
  - intros ????? ?. 
    eapply H1; eauto.
    pose proof (restr_Max_equiv Hlt1) as HH.
    destruct H3 as [H3|H3];
      eapply (Proper_perm_max) in H3;
      try (symmetry; apply restr_Max_equiv);
      try eassumption;
      try solve[econstructor];
      auto.
  - intros.
    pose proof (restr_Max_equiv Hlt1) as HH1.
    pose proof (restr_Max_equiv Hlt2) as HH2.
    destruct k.
    + eapply (Proper_perm_max) in H3;
        try (symmetry; apply restr_Max_equiv);
        try eassumption;
        eauto.
      eapply H1 in H3; eauto.
      destruct H3 as [H3|H3].
      * left; eapply Proper_perm_max;
          try eassumption;
          try solve[econstructor];
          auto.
      * right; intros ?; apply H3.
        eapply (Proper_perm_max) in H4;
          try eassumption; eauto.
        symmetry; apply restr_Max_equiv.
    + eapply setPermBlock_mi_perm_inv_Cur; eauto.
Qed.
Lemma setPermBlock_mem_inject_lock:
  forall mu m1 m2 b b' ofs delt LKSIZE_nat,
    (0 < LKSIZE_nat)%nat ->
    forall (Hinject_lock: inject_lock' (Z.of_nat LKSIZE_nat) mu b ofs m1 m2)
           (Hlt1: permMapLt
                    (setPermBlock (Some Writable) b ofs
                                  (getCurPerm m1)
                                  LKSIZE_nat) (getMaxPerm m1))
           
           (Hlt2: permMapLt
                    (setPermBlock (Some Writable) b' (ofs + delt)
                                  (getCurPerm m2)
                                  LKSIZE_nat) (getMaxPerm m2)),
      mu b = Some (b', delt) ->
      Mem.inject mu m1 m2 ->
      Mem.inject mu (restrPermMap Hlt1) (restrPermMap Hlt2).
Proof.
  intros; econstructor.
  - eapply setPermBlock_mem_inj; auto;
      eapply H1.
  - intros ?.
    rewrite restrPermMap_valid.
    eapply H1. 
  - intros. apply restrPermMap_valid.
    eapply H1; eauto.
  - 
    
    pose proof (restr_Max_equiv Hlt1).
    eapply Proper_no_overlap_max_equiv; eauto.
    eapply H1.
  - intros ?????.
    

    intros ?.
    eapply H1; eauto.

    pose proof (restr_Max_equiv Hlt1) as HH.
    destruct H3 as [H3|H3];
      eapply (Proper_perm_max) in H3;
      try (symmetry; apply restr_Max_equiv);
      try eassumption;
      try solve[econstructor];
      auto.

  - intros.
    pose proof (restr_Max_equiv Hlt1) as HH1.
    pose proof (restr_Max_equiv Hlt2) as HH2.
    destruct k.
    + eapply (Proper_perm_max) in H3;
        try (symmetry; apply restr_Max_equiv);
        try eassumption;
        eauto.
      eapply H1 in H3; eauto.
      destruct H3 as [H3|H3].
      * left; eapply Proper_perm_max;
          try eassumption;
          try solve[econstructor];
          auto.
      * right; intros ?; apply H3.
        eapply (Proper_perm_max) in H4;
          try eassumption; eauto.
        symmetry; apply restr_Max_equiv.
    + eapply setPermBlock_mi_perm_inv_Cur; eauto.
Qed.

(* HERE no overlap *) 
Definition maps_no_overlap {A} (f:meminj) (p1 p2: PMap.t (Z -> option A)):=
  forall (b1 b1' : block) (delta1 : Z) (b2 b2' : block) (delta2 ofs1 ofs2 : Z),
    b1 <> b2 ->
    f b1 = Some (b1', delta1) ->
    f b2 = Some (b2', delta2) ->
    at_least_Some (p1 !! b1 ofs1) ->
    at_least_Some  (p2 !! b2 ofs2) ->
    b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Definition map_no_overlap {A} (f:meminj) p:=
  @maps_no_overlap A f p p.

Lemma meminj_no_overlap_maps_no_overlap:
  forall m mu,
    Mem.meminj_no_overlap mu m <->
    map_no_overlap mu (getMaxPerm m).
Proof.
  intros.
  unfold Mem.meminj_no_overlap, map_no_overlap, maps_no_overlap.
  split; intros HH **; exploit HH; eauto.
  all: try apply at_least_Some_perm_Max; auto.
Qed.

(* Move to Self_simulation*)
Lemma at_least_perm_order:
  forall x, at_least_Some x <-> Mem.perm_order' x Nonempty.
Proof.
  intros; unfold at_least_Some, Mem.perm_order'.
  destruct x; split; simpl; auto.
  intros; apply perm_any_N.
Qed.
Lemma no_overlap_mem_perm:
  forall mu m1, 
    Mem.meminj_no_overlap mu m1 ->
    map_no_overlap mu (getMaxPerm m1).
Proof.
  intros * H ? **; eapply H; eauto;
    unfold Mem.perm; rewrite_getPerm;
      apply  at_least_perm_order; assumption.
Qed.
Definition map_no_overlap_range (f:meminj) (perm: access_map):=
  forall (b1 b1' : block) (delta1 : Z) (b2 b2' : block) (delta2 ofs1 ofs2 SZ : Z),
    0 < SZ ->
    b1 <> b2 ->
    f b1 = Some (b1', delta1) ->
    f b2 = Some (b2', delta2) ->
    Mem.perm_order' (perm !! b1 ofs1) Nonempty ->
    (forall ofs2', 0 <= ofs2' < SZ ->
                   Mem.perm_order' (perm !! b2 (ofs2 + ofs2')) Nonempty) ->
    b1' <> b2' \/ ~ Intv.In (ofs1 + delta1) (ofs2 + delta2, ofs2 + delta2 + SZ).

Lemma perm_no_over_point_to_range:
  forall f p,
    map_no_overlap f p ->
    map_no_overlap_range f p.
Proof.
  intros ** ? **.
  destruct (base.block_eq_dec b1' b2');
    auto; (* solevs the case b1' <> b2' *) subst.
  remember ((ofs1 + delta1)-(ofs2 + delta2)) as ofs2'.
  right; intros [LEFT RIGHT]; simpl in *.
  exploit (H5 (ofs2')).
  { subst; omega. }
  intros Hperm.
  exploit H; eauto; try apply at_least_perm_order; eauto.
  intros [? | Hcontra]; try congruence.
  apply Hcontra. subst.
  omega.
Qed.


Lemma set_perm_block_mi_perm_perm:
  forall (mu:meminj) b ofs p p_max perm1 perm2 LS b' delt
    (HLSpos: 0 < Z.of_nat LS),
    map_no_overlap mu p_max ->
    mu b = Some (b', delt) ->
    permMapLt perm1 p_max ->
    (forall ofs2' : Z,
        0 <= ofs2' < Z.of_nat LS ->
        Mem.perm_order' (p_max !! b (ofs + ofs2')) Nonempty) ->
    mi_perm_perm mu perm1 perm2 ->
    mi_perm_perm mu
                 (setPermBlock p b ofs perm1 LS)
                 (setPermBlock p b' (ofs + delt) perm2 LS).
Proof.
  intros ** ? * Hinj.
  pose proof (H2 0 ltac:(omega)).
  unfold Mem.perm_order'.
  destruct_address_range b ofs b1 ofs0 LS.
  - unify_injection.
    repeat rewrite (@setPermBlock_same); auto.
    unfold Intv.In in *; simpl in *; omega.
  - unify_injection.
    repeat rewrite (@setPermBlock_other_1).
    apply H3; auto.
    eapply Intv.range_notin in Hrange; simpl in *; omega.
    eapply Intv.range_notin in Hrange; simpl in *; omega.
  - rewrite (@setPermBlock_other_2); auto.
    destruct (base.block_eq_dec b' b2); try subst.  
    2: { rewrite (@setPermBlock_other_2); auto.
         eapply H3; auto . }
    + match_case; try solve[intros HH; inv HH].
      exploit H; eauto; try apply at_least_perm_order; eauto.
      eapply perm_order_trans211; eauto.
      rewrite Heqo; constructor.
      
      intros [?| ?].
      * congruence.
      * rewrite (@setPermBlock_other_1).
        intros. eapply H3; eauto.
        rewrite Heqo; auto.
        eapply (Intv.range_notin _ (ofs + delt, ofs + delt + _ )).
        2: simpl; omega.
        apply not_eq_sym in Hneq.
        exploit perm_no_over_point_to_range; eauto.
        eapply perm_order_trans211; eauto.
        rewrite Heqo; constructor.
        intros [?|?]; auto.
Qed.

Lemma inject_mi_perm_inv_perm_Max:
  forall f m1 m2,
    Mem.inject f m1 m2 ->
    mi_perm_inv_perm f (getMaxPerm m1)
                     (getMaxPerm m2) m1.
Proof.
  intros ** ? **.
  eapply Mem.mi_perm_inv with (k:=Max) in H; eauto;
    unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
Qed.
Lemma inject_mi_perm_inv_perm_Cur:
  forall f m1 m2,
    Mem.inject f m1 m2 ->
    mi_perm_inv_perm f (getCurPerm m1)
                     (getCurPerm m2) m1.
Proof.
  intros ** ? **.
  eapply Mem.mi_perm_inv with (k:=Cur) in H; eauto;
    unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
Qed.
Lemma mi_inj_mi_memval_perm:
  forall f m1 m2,
    Mem.mem_inj f m1 m2 ->
    mi_memval_perm f (getCurPerm m1)
                   (Mem.mem_contents m1) (Mem.mem_contents m2).
Proof.
  intros ** ? **.
  eapply Mem.mi_memval in H; eauto;
    unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
Qed.
Lemma mi_inj_mi_perm_perm_Max:
  forall f m1 m2,
    Mem.mem_inj f m1 m2 ->
    mi_perm_perm f (getMaxPerm m1) (getMaxPerm m2).
Proof.
  intros ** ? **.
  eapply Mem.mi_perm with(k:=Max) in H; eauto;
    unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
Qed.
Lemma mi_inj_mi_perm_perm_Cur:
  forall f m1 m2,
    Mem.mem_inj f m1 m2 ->
    mi_perm_perm f (getCurPerm m1) (getCurPerm m2).
Proof.
  intros ** ? **.
  eapply Mem.mi_perm with(k:=Cur) in H; eauto;
    unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
Qed.




Record virtue:=
  { virtueThread:
      PTree.t (Z -> option (option permission)) *
      PTree.t (Z -> option (option permission));
    virtueLP: access_map * access_map }.




Definition pair21 {A B C} (f: A -> B -> C) (aa:Pair A) (b: B): Pair C :=
  pair1 (fun a => f a b) aa.
Hint Unfold pair21: pair.
Definition pair21_prop {A B} (f: A -> B -> Prop) (aa:Pair A) (b: B):Prop :=
  pair1_prop (fun a => f a b) aa.
Hint Unfold pair21_prop: pair.
Definition permMapLt_pair1:= pair21_prop permMapLt.
Hint Unfold permMapLt_pair1: pair.

(*Take just the tree*)

Definition sub_map_snd {A A' B} (a:A'* _) b:=
  @sub_map A B (snd a) b. 
Record sub_map_virtue (v:virtue)(m:access_map):=
  { virtueThread_sub_map:
      pair21_prop sub_map (virtueThread v) (snd m);
    virtueLP_sub_map:
      map_empty_def (fst (virtueLP v)) /\
      map_empty_def (snd (virtueLP v)) /\
      pair21_prop sub_map_snd (virtueLP v) (snd m)
  }.

Definition sub_map_pair {A B} :=
  (pair21_prop (@sub_map A B)).

(*  *)
Definition writable_lock b ofs perm1 m1:=
  permMapLt (setPermBlock (Some Writable) b ofs perm1 LKSIZE_nat) (getMaxPerm m1).

Lemma LKSIZE_nat_pos: (0 < LKSIZE_nat)%nat.
Proof.
  replace 0%nat with (Z.to_nat 0)%Z by reflexivity.
  unfold LKSIZE_nat, LKSIZE.
  rewrite size_chunk_Mptr.
  destruct Archi.ptr64;
    eapply Z2Nat.inj_lt; eauto; try omega.
Qed.
Hint Resolve LKSIZE_nat_pos.
Lemma writable_lock_inject:
  forall b1 ofs cperm1 cperm2 m1 m2 f  b2 delt LKS,  
    (0 < LKS)%nat ->
    writable_lock b1 ofs cperm1 m1 ->
    Mem.inject f m1 m2 ->
    f b1 = Some (b2, delt) ->
    permMapLt cperm2 (getMaxPerm m2) ->
    writable_lock b2 (ofs + delt)%Z cperm2 m2.
Proof.
  intros.
  eapply setPermBlock_inject_permMapLt; simpl in *; eauto.
  apply access_map_injected_getMaxPerm; auto.
Qed.

Instance writable_lock_proper:
  Proper (Logic.eq ==> Logic.eq ==>
                   access_map_equiv ==> Max_equiv ==> iff) writable_lock.
Proof.
  setoid_help.proper_iff;
    setoid_help.proper_intros; subst.
  unfold writable_lock in *.
  unfold Max_equiv in *.
  rewrite <- H1, <- H2; auto.
Qed.
Lemma writable_lock_inject_restr:
  forall b1 ofs cperm1 cperm2 m1 m2 f  b2 delt LKS,  
    (0 < LKS)%nat ->
    writable_lock b1 ofs cperm1 m1 ->
    forall p1 p2 Hlt1 Hlt2,
      Mem.inject f (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2) ->
      f b1 = Some (b2, delt) ->
      permMapLt cperm2 (getMaxPerm m2) ->
      writable_lock b2 (ofs + delt)%Z cperm2 m2.
Proof.
  intros.
  erewrite <- restr_Max_equiv.
  erewrite <- restr_Max_equiv in H0.
  eapply writable_lock_inject; eauto.
  rewrite getMax_restr; auto.
Qed.
Lemma writable_lock_perm:
  forall b ofs perm m,
    writable_lock b ofs perm m ->
    forall ofs2,
      0 <= ofs2 < LKSIZE ->
      Mem.perm m b (ofs+ofs2) Max Writable.
Proof.
  unfold writable_lock, Mem.perm; intros.
  specialize (H b (ofs+ofs2)).
  rewrite_getPerm.
  eapply perm_order_trans211; eauto.
  rewrite setPermBlock_same; try solve [constructor].
  unfold LKSIZE_nat; rewrite Z2Nat.id;
    omega.
Qed.
Definition permMapJoin_pair:= pair3_prop permMapJoin.
Hint Unfold permMapJoin_pair: pair.

Definition is_empty_map (am:access_map):=
  forall b ofs, am !! b ofs = None.
Definition empty_doublemap:=
  pair1_prop is_empty_map.
Hint Unfold empty_doublemap: pair.


Lemma is_empty_map_is_canon:
  forall perms,
    is_empty_map perms ->
    isCanonical perms.
Proof.
  unfold is_empty_map, isCanonical; destruct perms as (deflt, perms).
  induction perms.
  - simpl. intros H; specialize (H 1%positive).
    extensionality ofs.
    unfold PMap.get in *; eauto.
  - simpl in *.
    intros. eapply IHperms1.
    intros.
    specialize (H (xO b) ofs). simpl in *.
    unfold PMap.get in *.
    simpl in *; auto.
Qed.


Lemma empty_map_useful:
  (* Transforms empty_doublemap into the 
               form used by step *)
  forall am, empty_doublemap am <->
             forall b ofs, (fst am) !! b ofs = None /\ (snd am) !! b ofs = None.
Proof. split; intros HH; split; try intros ??; eapply HH. Qed.

Definition map_no_overlap' {A} (f:meminj) (perm: PMap.t (Z -> option A)):=
  forall (b1 b1' : block) (delta1 : Z) (b2 b2' : block) (delta2 ofs1 ofs2 : Z),
    b1 <> b2 ->
    f b1 = Some (b1', delta1) ->
    f b2 = Some (b2', delta2) ->
    at_least_Some (perm !! b1 ofs1) ->
    at_least_Some  (perm !! b2 ofs2) ->
    b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Definition maps_no_overlap_contra {A} (mu:meminj)
           (p p': PMap.t (Z -> option A)):=
  forall b1 b1' b2 delt delt',
    mu b1 = Some(b2, delt) ->
    mu b1' = Some(b2, delt') ->
    forall ofs ofs',
      at_least_Some (p !! b1 ofs) ->
      at_least_Some (p' !! b1' ofs') ->
      ofs + delt = ofs' + delt' ->
      b1 = b1' /\ ofs = ofs' /\ delt = delt' .
Definition map_no_overlap_contra {A} (mu:meminj) (p: PMap.t (Z -> option A)):=
  maps_no_overlap_contra mu p p.
Lemma no_overlapp_iff:
  forall A mu p1 p2,
    @maps_no_overlap A mu p1 p2 <-> maps_no_overlap_contra mu p1 p2.
Proof.
  intros; unfold maps_no_overlap_contra, maps_no_overlap.
  split; intros H **.
  - destruct (base.block_eq_dec b1 b1').
    + subst; eauto. rewrite H0 in H1; inv H1.
      repeat split; eauto. omega.
    + exploit H; eauto; intros [?|  ?].
      * contradict H5; reflexivity.
      * contradict H5; assumption.
  - destruct (base.block_eq_dec b1' b2'); eauto.
    destruct (Z.eq_dec (ofs1 + delta1) (ofs2 + delta2)); eauto.
    subst; exploit (H b1 b2); eauto.
    intros (?&?&?); subst.
    contradict H0; reflexivity.
Qed.        
Lemma  no_overlapp_iff':
  forall {A} mu p,
    @map_no_overlap A mu p <-> maps_no_overlap_contra mu p p.
Proof.
  unfold map_no_overlap; intros.
  eapply no_overlapp_iff.
Qed.
Definition perm_inj (f:meminj) (a1 a2: access_map): Prop:=
  forall b1 ofs, at_least_Some (a1 !! b1 ofs) ->
            (* Mem.perm_order' (a1 !! b1 ofs) (Nonempty) -> *)
            exists b2 delta,
              f b1 = Some (b2, delta) /\
              a1 !! b1 ofs = a2 !! b2 (ofs + delta).
Definition perfect_image (f:meminj) (a1 a2: access_map): Prop:=
  forall b1 b2 delt,
    f b1 = Some (b2, delt) ->
    forall ofs, a1 !! b1 ofs = a2 !! b2 (ofs + delt).
(* TODO: change the names 
             perm_inj -> perm_inj
             perm_surj -> perm_surj
             pimage -> pimage  
             p_image -> prem_inj
             ppre_perfect_image -> prem_surj
 *)

Record perm_perfect_image mu a1 a2:=
  { (* pimage: perfect_image mu a1 a2; *) (* Too strong*)
    p_image: perm_inj mu a1 a2;
    ppre_perfect_image: perm_surj mu a1 a2}.
(*Arguments pimage {_ _ _}. *)
Arguments p_image {_ _ _}.
Arguments ppre_perfect_image {_ _ _}.

Local Ltac exploit_p_image H:=
  let b:=fresh "b" in
  let delt:=fresh "delt" in
  let Hinj:=fresh "Hinj" in
  destruct
    (p_image H _ _ ltac:(eapply at_least_Some_trivial; eauto))
    as (b&delt&Hinj&?); subst.
Local Ltac exploit_ppre_image H:=
  let b:=fresh "b" in
  let ofs:=fresh "ofs" in
  let delt:=fresh "delt" in
  let Hinj:=fresh "Hinj" in
  destruct
    (ppre_perfect_image H _ _ ltac:(eapply at_least_Some_trivial; eauto))
    as (b&ofs&delt&Hinj&?&?); subst.
Local Ltac exploit_perfect_image H:=
  first [exploit_p_image H | exploit_ppre_image H]. (*
            progress (try (exploit_p_image H); try (exploit_ppre_image H)). *) 
Local Ltac exploit_no_overlap_perm H:=
  (* TODO: remove coqlib*)
  ( eapply no_overlapp_iff in H;
    exploit H;
    try (eapply at_least_Some_trivial; eauto);
    eauto;
    intros ?; destruct_and; subst
  ).


Lemma permMapJoin_inject:
  forall mu a1 a2 b1 b2 c1 c2,
    maps_no_overlap mu a1 b1 ->
    maps_no_overlap mu b1 c1 ->
    maps_no_overlap mu c1 a1 ->
    perm_perfect_image mu a1 a2 ->
    perm_perfect_image mu b1 b2 ->
    perm_perfect_image mu c1 c2 ->
    permMapJoin a1 b1 c1 ->
    permMapJoin a2 b2 c2.
Proof.
  intros * H12 H23 H31 Ha Hb Hc HH ??.
  destruct (a2 !! b ofs) eqn:AA; 
    destruct (b2 !! b ofs) eqn:BB; 
    destruct (c2 !! b ofs) eqn:CC;
    try exploit_perfect_image Ha;
    try exploit_perfect_image Hb;
    try exploit_perfect_image Hc;
    repeat unify_mapping;
    
    (* use no_pverlap_mem to set which blocks and ofsets are equal*)
    
    try (exploit_no_overlap_perm H12);
    try (exploit_no_overlap_perm H23);
    try (exploit_no_overlap_perm H31);
    !goal (permjoin_def.permjoin _ _ _);
    

    (* inistantiate hypothesis wiith permMapJoin *)
    try (match goal with
         |[H: mu ?b = _, _:Some _ = ?a !! ?b ?ofs |-_] => specialize (HH b ofs)
         end;
         (*rewriite the values ini the joiin*)
         repeat match goal with
                | [ H: Some _ = _ |- _] => rewrite <- H in HH
                end; auto);
    

    
    (*destruct the parts that are not mapped*)
    repeat match type of HH with
             context[?a !! ?b ?ofs] =>
             destruct (a !! b ofs) eqn:?
           end; try eassumption;

      (* map the ones that are not mapped yet (and show a contradictoni)*)
      try exploit_perfect_image Ha;
      try exploit_perfect_image Hb;
      try exploit_perfect_image Hc;
      repeat unify_injection;
      repeat unify_mapping;
      try discriminate.
  - !goal (permjoin_def.permjoin None None None).
    constructor.
Qed.


Definition perm_perfect_image_pair mu:=
  pair2_prop (perm_perfect_image mu).
Hint Unfold perm_perfect_image_pair: pair.

Definition maps_no_overlap_pair {A} mu:=
  pair2_prop (@maps_no_overlap A mu).
Hint Unfold maps_no_overlap_pair: pair.

Definition permMapLt_pair2:= pair2_prop permMapLt.
Hint Unfold permMapLt_pair2: pair.

Lemma permMapJoin_lt_pair1:
  forall p1 p2 p3 (Hjoin: permMapJoin_pair p1 p2 p3), permMapLt_pair2 p1 p3.
Proof. solve_pair; eapply permMapJoin_lt. Qed.


Lemma permMapJoin_lt_pair2:
  forall p1 p2 p3
    (Hjoin: permMapJoin_pair p1 p2 p3), permMapLt_pair2 p2 p3.
Proof.
  solve_pair;intros.
  eapply permMapJoin_comm in H;
    eapply permMapJoin_lt; eauto.
Qed.

Lemma permMapJoin_pair_inject:
  forall mu a1 a2 b1 b2 c1 c2,
    maps_no_overlap_pair mu a1 b1 -> 
    maps_no_overlap_pair mu b1 c1 ->
    maps_no_overlap_pair mu c1 a1 ->
    perm_perfect_image_pair mu a1 a2 ->
    perm_perfect_image_pair mu b1 b2 ->
    perm_perfect_image_pair mu c1 c2 ->
    permMapJoin_pair a1 b1 c1 ->
    permMapJoin_pair a2 b2 c2.
Proof.
  intros ?; solve_pair.
  apply permMapJoin_inject.
Qed.

Definition permMapLt_pair pp1 p2:=
  permMapLt_pair2 pp1 (pair0 p2).
Hint Unfold permMapLt_pair: pair.
Instance permMapLt_pair_proper : 
  Proper (Logic.eq ==> access_map_equiv ==> iff) permMapLt_pair.
Proof.
  setoid_help.proper_iff;
    setoid_help.proper_intros; subst.
  split; simpl; rewrite <- H0; eapply H1.
Qed.

Lemma permMapLt_trans:
  transitive _ permMapLt.
Proof. unfold permMapLt; intros ? **.
       eapply mem_lemmas.po_trans; eauto.
Qed.
Lemma permMapLt_pair_trans211:
  forall pa pb c,
    permMapLt_pair2 pa pb ->
    permMapLt_pair pb c ->
    permMapLt_pair pa c.
Proof.
  unfold permMapLt_pair; intros;
    eapply impr_rel_trans; eauto.
  eapply permMapLt_trans.
Qed.

Lemma maps_no_overlap_under_mem:
  forall mu a1 a2 m,
    Mem.meminj_no_overlap mu m ->
    permMapLt a1 (getMaxPerm m) ->
    permMapLt a2 (getMaxPerm m) ->
    maps_no_overlap mu a1 a2.
Proof.
  intros **. eapply no_overlapp_iff;
               intros ????????????.
  destruct (base.block_eq_dec b1 b1').
  - subst; unify_injection.
    repeat (split; auto); omega.
  - exfalso.
    exploit H; eauto; unfold Mem.perm.
    + try (rewrite_getPerm_goal; eapply perm_order_trans211).
      2: eapply at_least_perm_order; exact H4.
      apply H0.
    + try (rewrite_getPerm_goal; eapply perm_order_trans211).
      2: eapply at_least_perm_order; exact H5.
      apply H1.
    + intros [?| ?]; tauto.
Qed.
Lemma maps_no_overlap_under_mem_pair:
  forall mu a1 a2 m,
    Mem.meminj_no_overlap mu m ->
    permMapLt_pair a1 (getMaxPerm m) ->
    permMapLt_pair a2 (getMaxPerm m) ->
    maps_no_overlap_pair mu a1 a2.
Proof.
  intros; split;
    eapply maps_no_overlap_under_mem; eauto;
      first [eapply H0 | eapply H1].
Qed.

Lemma permMapJoin_pair_comm:
  forall AA BB CC,
    permMapJoin_pair AA BB CC ->
    permMapJoin_pair BB AA CC.
Proof. solve_pair; apply permMapJoin_comm. Qed.

Lemma permMapLt_pair_trans:
  transitive _ permMapLt_pair2.
Proof. unfold transitive; solve_pair.
       eapply permMapLt_trans.
Qed.


(* subsumed is different than sub_map:
         submap is that the STRUCTURE of the tree is the same
         subsumed is that it can join to it:
         subsumed x y: exists z. x + z = y.
 *)
Inductive subsumed: option permission -> option permission -> Prop:=
| subsumedNone: forall x, subsumed None x
| subsumedNENE: subsumed (Some Nonempty) (Some Nonempty)
| subsumedNER: subsumed (Some Nonempty) (Some Readable)
| subsumedNEW: subsumed (Some Nonempty) (Some Writable)
| subsumedRR: subsumed (Some Readable) (Some Readable)
| subsumedRW: subsumed (Some Readable) (Some Writable).


Lemma subsumed_order:
  forall b c, subsumed b c -> Mem.perm_order'' c b.
Proof. intros b c H; destruct b, c; inv H; constructor. Qed.

Lemma subsume_same_join:
  forall x y, subsumed x y <->
         permjoin_def.permjoin y x y.
Proof.
  intros x y; split;
    intros HH; inversion HH; subst; constructor.
Qed.


Inductive option_join :
  option (option permission) ->
  option permission ->
  option permission -> Prop :=
| NoneJoin: forall l c,
    subsumed l c -> (* why subsumed? *)
    option_join None l c
| SomeJoin: forall a b c,
    permjoin_def.permjoin a b c ->
    option_join (Some a) b c.

Definition delta_map_join
           (A: delta_map)
           (B: access_map)
           (C: access_map):=
  forall b ofs,
    option_join (dmap_get A b ofs)
                (B !! b ofs)
                (C !! b ofs).
Definition delta_map_join_pair:= pair3_prop delta_map_join.
Hint Unfold delta_map_join_pair: pair.


Lemma compute_map_join:
  forall A B C,
    delta_map_join A B C <->
    permMapJoin
      (computeMap C A) B C.
Proof.
  split;
    intros ** b ofs.
  
  { !goal(permjoin_def.permjoin _ _ _).
    specialize (H b ofs); inversion H; subst.
    - unfold dmap_get, PMap.get in H0; simpl in *.
      destruct (A ! b) eqn:Ab.
      + destruct (o ofs) eqn:oofs; try inversion H0.
        erewrite computeMap_2; eauto.
        eapply subsume_same_join; auto.
      + erewrite computeMap_3; eauto.
        eapply subsume_same_join; auto. 
    - unfold dmap_get, PMap.get in H0; simpl in *.
      destruct (A ! b) eqn:HH; try solve[inversion H0].
      erewrite computeMap_1.
      1, 2: eauto.
      destruct (o ofs) eqn:HH'; inversion H0; auto. }
  
  { !goal (option_join _ _ _ ).
    destruct (dmap_get A b ofs) eqn:HH.
    - eapply dmap_get_copmute_Some in HH.
      rewrite <- HH.
      econstructor; eauto.
    - eapply dmap_get_copmute_None in HH.
      econstructor.
      specialize (H b ofs).
      rewrite HH in H.
      eapply subsume_same_join; assumption.
  }
Qed.
Lemma compute_map_join_fwd:
  forall A B C,
    delta_map_join A B C ->
    permMapJoin
      (computeMap C A) B C.
Proof. intros; apply compute_map_join; assumption. Qed.
Lemma compute_map_join_bkw:
  forall A B C,
    permMapJoin
      (computeMap C A) B C ->
    delta_map_join A B C.
Proof. intros; apply compute_map_join; assumption. Qed.


Definition computeMap_pair:= pair2 computeMap.
Hint Unfold computeMap_pair: pair.
Lemma compute_map_join_pair:
  forall AA BB CC,
    delta_map_join_pair AA BB CC <->
    permMapJoin_pair
      (computeMap_pair CC AA) BB CC.
Proof. solve_pair; apply compute_map_join. Qed.
Lemma compute_map_join_fwd_pair:
  forall AA BB CC,
    delta_map_join_pair AA BB CC ->
    permMapJoin_pair
      (computeMap_pair CC AA) BB CC.
Proof. solve_pair; apply compute_map_join_fwd. Qed.
Lemma compute_map_join_bkw_pair:
  forall AA BB CC,
    permMapJoin_pair
      (computeMap_pair CC AA) BB CC ->
    delta_map_join_pair AA BB CC.
Proof. solve_pair; apply compute_map_join_bkw. Qed.
(* Definition at_least_Some {A} (x:option A):=
        option_implication (Some tt) x. *)
Definition perm_inj_dmap f dm1 dm2:=
  forall b1 ofs,
    at_least_Some (dmap_get dm1 b1 ofs) ->
    exists b2 delta,
      f b1 = Some (b2, delta) /\
      (dmap_get dm1 b1 ofs) = (dmap_get dm2 b2 (ofs + delta)).
Definition dmap_preimage f dm1 dm2:=
  forall b2 ofs_delt,
    at_least_Some (dmap_get dm2 b2 ofs_delt) ->
    exists (b1 : block) (ofs delt : Z),
      f b1 = Some (b2, delt) /\
      ofs_delt = ofs + delt /\
      (dmap_get dm2 b2 ofs_delt) = (dmap_get dm1 b1 ofs).
Definition perfect_image_dmap (f:meminj) (a1 a2: delta_map): Prop:=
  forall b1 b2 delt,
    f b1 = Some (b2, delt) ->
    forall ofs, dmap_get a1 b1 ofs = dmap_get a2 b2 (ofs + delt).
Record perm_perfect_image_dmap (mu : meminj) (a1 a2 : delta_map) : Prop
  := { p_image_dmap : perm_inj_dmap mu a1 a2;
       ppre_perfect_image_dmap : dmap_preimage mu a1 a2 }.
Arguments p_image_dmap {_ _ _}.
Arguments ppre_perfect_image_dmap {_ _ _}.
Definition perm_perfect_image_dmap_pair f:=
  pair2_prop (perm_perfect_image_dmap f).
Hint Unfold perm_perfect_image_dmap_pair: pair.

Inductive opt_rel {A}  (r: relation A): relation (option A):=
| SomeOrder:forall a b, r a b -> opt_rel r (Some a) (Some b)
| NoneOrder: forall p, opt_rel r p None.
Lemma perm_order_from_dmap:
  forall dmap b (ofs : Z) p,
    dmap_get  dmap b ofs  = Some (Some p) ->
    opt_rel Mem.perm_order''  (dmap_get  dmap b ofs)
            (Some (Some Nonempty)).
Proof. intros * H; rewrite H; repeat constructor. Qed.
Lemma perm_order_from_dmap':
  forall dmap b (ofs : Z) p,
    dmap_get  dmap b ofs  = Some p ->
    at_least_Some (dmap_get  dmap b ofs).
Proof. intros * H; rewrite H;  destruct p; repeat constructor. Qed.
Local Ltac exploit_p_image_dmap H:=
  let b:=fresh "b" in
  let delt:=fresh "delt" in
  let Hinj:=fresh "Hinj" in
  destruct
    (p_image_dmap H _ _ ltac:(eapply perm_order_from_dmap'; eauto))
    as (b&delt&Hinj&?); subst.
Local Ltac exploit_ppre_image_dmap H:=
  let b:=fresh "b" in
  let ofs:=fresh "ofs" in
  let delt:=fresh "delt" in
  let Hinj:=fresh "Hinj" in
  destruct
    (ppre_perfect_image_dmap H _ _ ltac:(eapply perm_order_from_dmap'; eauto))
    as (b&ofs&delt&Hinj&?&?); subst.
Local Ltac exploit_perfect_image_dmap H:=
  first [exploit_p_image_dmap H| exploit_ppre_image_dmap H].


Lemma no_overlap_contrapositive_iff:
  forall f m,
    Mem.meminj_no_overlap f m <->
    map_no_overlap_contra f (getMaxPerm m).
Proof.
  intros *; etransitivity .
  - eapply meminj_no_overlap_maps_no_overlap.
  - eapply no_overlapp_iff.
Qed.
Definition deltaMapLt2 (dmap: delta_map) (pmap : access_map) : Prop :=
  forall b ofs,
    opt_rel
      Mem.perm_order''
      (Some (Maps.PMap.get b pmap ofs))
      (dmap_get dmap b ofs).

Definition almost_perfect_image mu (max a1 a2: access_map):=
  forall b1 b2 delt,
    mu b1 = Some (b2, delt) ->
    forall ofs, at_least_Some (max !! b1 ofs) ->
                a1 !! b1 ofs = a2 !! b2 (ofs + delt).
Lemma injection_perfect_image:
  forall mu m1 m2,
    Mem.inject mu m1 m2 ->
    almost_perfect_image mu (getMaxPerm m1) (getCurPerm m1) (getCurPerm m2).
Proof.
  intros * Hinj ??? Hmu ? Hmax.
  dup Hmu as Hmu'.
  pose proof (Mem.mi_perm_inv _ _ _ Hinj) as H1.
  assert (H2:
            forall p,
              Mem.perm m2 b2 (ofs + delt) Cur p ->
              Mem.perm m1 b1 ofs Cur p \/ ~ Mem.perm m1 b1 ofs Max Nonempty).
  { intros ?; eapply H1; eauto. } clear H1.
  assert (Hr: forall p,
             Mem.perm m2 b2 (ofs + delt) Cur p ->
             Mem.perm m1 b1 ofs Cur p).
  { intros ? HHH. eapply H2 in HHH. destruct HHH; auto.
    contradict H. unfold Mem.perm.
    repeat rewrite getMaxPerm_correct in *; unfold permission_at in *.
    rewrite mem_lemmas.po_oo; auto.
    eapply at_least_perm_order; assumption.
    
  } clear H2.
  assert (Hl: forall p,
             Mem.perm m1 b1 ofs Cur p ->
             Mem.perm m2 b2 (ofs + delt) Cur p).
  { intros ?. eapply Mem.mi_perm; eauto; try apply Hinj. }

  unfold_getPerm.
  eapply at_least_perm_order in Hmax.
  
  match goal with
    |- ?L = ?R =>
    destruct L as [pl|] eqn:LHS;
      destruct R as [pr|] eqn:RHS; auto;
        try (specialize (Hl pl);
             unfold Mem.perm in Hl;
             unfold_getCurPerm;
             rewrite LHS in *
             ;specialize (Hl ltac:(simpl; eapply perm_refl))
            );
        try (specialize (Hr pr);
             unfold Mem.perm in Hr;
             unfold_getCurPerm;
             rewrite RHS in *;
             specialize (Hr ltac:(eapply perm_refl))
            );
        try rewrite LHS in *;
        try rewrite RHS in *;
        try solve[inv Hl];
        try solve [inv Hr]
  end.
  - simpl in *; clear - Hr Hl.
    destruct pl, pr; auto;
      inversion Hr; inversion Hl.
Qed.

Lemma r_dmap_join_lt:
  forall A B C,
    delta_map_join A B C->
    permMapLt B C.
Proof.
  intros ??? H b ofs. specialize (H b ofs).
  inv H.
  - apply subsumed_order; assumption.
  - apply permjoin_def.permjoin_order in H1 as [? ?]; auto.
Qed.
Definition dmap_vis_filtered (dmap:delta_map) (m:mem) :=
  forall b ofs p,
    dmap_get dmap b ofs = Some p ->
    Mem.perm m b ofs Max Nonempty. 

Lemma delta_map_join_inject:
  forall m f A1 A2 B1 B2 C1 C2,
    Mem.meminj_no_overlap f m ->
    dmap_vis_filtered A1 m ->
    (*deltaMapLt2 A1 (getMaxPerm m) ->
              permMapLt B1  (getMaxPerm m) -> *)
    permMapLt C1  (getMaxPerm m) ->
    perm_perfect_image_dmap f A1 A2 ->
    perm_perfect_image f B1 B2 ->
    almost_perfect_image f (getMaxPerm m) C1 C2 ->
    (* perm_perfect_image f C1 C2 -> *)
    delta_map_join A1 B1 C1 ->
    delta_map_join A2 B2 C2.
Proof.
  intros * Hno_overlap Hfilter HltC  HppiA HppiB HppiC Hjoin b2 ofs_delta.
  assert (HltB : permMapLt B1 (getMaxPerm m)).
  { intros b ofs. eapply perm_order''_trans.
    - eapply HltC.
    - revert b ofs.
      apply r_dmap_join_lt with A1; assumption. }
  
  (* Ltacs for this goal *)
  

  Local Ltac rewrite_double:=
    match goal with
    | [ H: ?L = ?R, H0: ?L = Some _  |- _ ] =>
      rewrite H0 in H; try rewrite <- H in *; symmetry in H
    | [ H: ?R = ?L, H0: ?L = Some _  |- _ ] =>
      rewrite H0 in H; try rewrite H in *
    | [ H: ?L = ?R, H0: ?L = None  |- _ ] =>
      rewrite H0 in H; try rewrite <- H in *; symmetry in H
    | [ H: ?R = ?L, H0: ?L = None  |- _ ] =>
      rewrite H0 in H; try rewrite H in *
    end.
  
  Ltac auto_exploit_pimage :=
    match goal with
    | [ H: perm_perfect_image_dmap _ _ _ |- _ ] =>
      exploit_perfect_image_dmap H; clear H
    | [ H: perm_perfect_image _ _ _ |- _ ] => 
      exploit_perfect_image H; clear H
    end ; repeat rewrite_double. 
  
  
  (* Case analysis on first term*)
  match goal with
  | [ |- option_join _ ?B _ ] => destruct B as [o|] eqn:HB2 
  end.
  - (*B2 -> Some *)
    Note B2_Some.
    auto_exploit_pimage.
    dup Hinj as Hinj'.
    assert (Hmax: Mem.perm_order' ((getMaxPerm m) !! b ofs) Nonempty).
    { eapply perm_order_trans211.
      specialize (HltB b ofs).
      eapply HltB. rewrite H0; constructor.
    }

    (* new try*)
    destruct (dmap_get A2 b2 (ofs + delt)) eqn:HA2.
    + exploit (ppre_perfect_image_dmap HppiA); eauto.
      { rewrite HA2; constructor. }
      intros; normal. rewrite HA2 in H2.

      assert (x = b).
      { destruct (base.block_eq_dec x b); auto.
        exploit Hno_overlap; eauto.
        unfold Mem.perm. rewrite_getPerm; eauto. 
        intros [HH | HH]; contradict HH; auto.
      }

      subst; unify_injection.
      assert (x0 = ofs) by omega; subst.
      
      specialize (Hjoin b ofs).
      rewrite <- H2, H0 in Hjoin.
      inv Hjoin. constructor.
      exploit HppiC; eauto.
      eapply at_least_perm_order; eassumption.
      intros <-; auto.

    + specialize (Hjoin b ofs).
      destruct (dmap_get A1 b ofs) eqn:HA1.
      * exploit (p_image_dmap HppiA); eauto.
        { rewrite HA1. constructor. }
        intros; normal. unify_injection.
        rewrite HA1, HA2 in H1; congruence.
      * rewrite H0 in Hjoin. 
        inv Hjoin. constructor.
        exploit HppiC; eauto.
        eapply at_least_perm_order; eassumption.
        intros <-; auto.
        
        
  - match goal with
    | [ |- option_join ?A _ _ ] => destruct A as [o|] eqn:HA2 
    end.
    + auto_exploit_pimage.
      specialize (Hjoin b ofs).
      assert (HB1:B1 !! b ofs = None).
      { match goal with
          |- ?L = ?R => destruct L eqn:HB1 end; auto.
        auto_exploit_pimage.
        inv Hinj.
        rewrite_double; auto. }
      rewrite H0, HB1 in Hjoin.
      inv Hjoin. assert ((C1 !! b ofs) = o) by (inv H1; auto).
      constructor.
      exploit HppiC; eauto.
      * eapply at_least_perm_order.
        rewrite mem_lemmas.po_oo. 
        eapply Hfilter in H0.
        unfold Mem.perm in H0.
        rewrite_getPerm; eauto.
      * intros <-; auto.
    + do 2 constructor.
Qed.

Definition deltaMapLt2_pair1:= pair21_prop deltaMapLt2.
Hint Unfold deltaMapLt2_pair1: pair.
Definition dmap_vis_filtered_pair:= pair21_prop dmap_vis_filtered.
Hint Unfold dmap_vis_filtered_pair: pair.
Definition almost_perfect_image_pair f max_perm:=
  pair2_prop (almost_perfect_image f max_perm).
Hint Unfold almost_perfect_image_pair: pair.
Lemma delta_map_join_inject_pair (m:mem) f:
  forall A1 A2 B1 B2 C1 C2,
    Mem.meminj_no_overlap f m ->
    dmap_vis_filtered_pair A1 m ->
    (*deltaMapLt2_pair1 A1 (getMaxPerm m) ->
              permMapLt_pair1 B1 (getMaxPerm m) -> *)
    permMapLt_pair C1 (getMaxPerm m) ->
    perm_perfect_image_dmap_pair f A1 A2 ->
    perm_perfect_image_pair f B1 B2 ->
    almost_perfect_image_pair f (getMaxPerm m) C1 C2 -> 
    delta_map_join_pair A1 B1 C1 ->
    delta_map_join_pair A2 B2 C2.
Proof. solve_pair; eapply delta_map_join_inject. Qed.



Lemma easy_mem_eq:
  forall m1 m2,
    Mem.mem_contents m1 = Mem.mem_contents m2 ->
    Mem.mem_access m1 = Mem.mem_access m2 ->
    Mem.nextblock m1 = Mem.nextblock m2 ->
    m1 = m2.
Proof.
  intros. destruct m1, m2; simpl in *.
  subst. f_equal;
           apply Axioms.proof_irr.
Qed.


Lemma sub_map_implictaion:
  forall {A B} x y,
    @sub_map A B x y ->
    forall b, option_implication (x ! b) (y ! b).
Proof.
  intros *.
  unfold sub_map; intros HH b.
  eapply strong_tree_leq_spec in HH.
  - instantiate(1:=b) in HH.
    unfold option_implication.
    repeat match_case; auto.
  - constructor.
Qed.
Lemma option_implication_trans:
  forall {A B C} a b c,
    @option_implication A B a b ->
    @option_implication B C b c ->
    @option_implication A C a c.
Proof.
  unfold option_implication.
  intros *; repeat match_case.
Qed.

Lemma no_overla_perm_mem:
  forall {A} mu m perm,
    (forall (b : positive) (ofs : Z),
        option_implication
          (perm !! b ofs)
          ((getMaxPerm m) !! b ofs)) ->
    Mem.meminj_no_overlap mu m ->
    @map_no_overlap A mu perm.
Proof.
  intros ** ? **.
  eapply H0; eauto.
  + specialize (H b1 ofs1).
    unfold Mem.perm; rewrite_getPerm.
    unfold option_implication in *.
    repeat match_case in H.
    constructor.
    inversion H4.
  + specialize (H b2 ofs2).
    unfold Mem.perm; rewrite_getPerm.
    unfold option_implication in *.
    repeat match_case in H.
    constructor.
    inversion H5. 
Qed.
Lemma canon_mem_access:
  forall m1 ofs k, fst (Mem.mem_access m1) ofs k = None.
Proof.
  intros.
  destruct k.
  - pose proof (Max_isCanonical m1).
    unfold getMaxPerm in *.
    unfold isCanonical in *; simpl in *.
    match type of H with
      ?a = ?b => remember a as A eqn:HH;
                  assert (A ofs = b ofs) by (rewrite H;auto);
                  subst A; auto
    end.
    
  - pose proof (Cur_isCanonical m1).
    unfold getMaxPerm in *.
    unfold isCanonical in *; simpl in *.
    match type of H with
      ?a = ?b => remember a as A eqn:HH;
                  assert (A ofs = b ofs) by (rewrite H;auto);
                  subst A; auto
    end.
Qed.

Definition isCanonical' {A} (pmap: PMap.t (Z-> option A)):=
  fst pmap = (fun _ : Z => None).
Lemma option_implication_injection:
  forall {A} mu m1 m2 b1 b2 ofs (perm:PMap.t (Z -> option A) ) o delta
    (Hcanon: isCanonical' perm)
    (Hdmap: perm !! b1 ofs = Some o)
    (Himpl: option_implication
              (perm !! b1 ofs)
              ((getMaxPerm m1) !! b1 ofs))
    (Hmi_inj:Mem.mem_inj mu m1 m2),
    mu b1 = Some (b2, delta) ->
    option_implication
      (snd perm) ! b1 (snd (getMaxPerm m2)) ! b2.
Proof.
  intros.
  unfold PMap.get in *; simpl in *.
  repeat match_case in Hdmap.
  2: { rewrite Hcanon in Hdmap. congruence. } 
  eapply option_implication_trans.
  - instantiate(1:= (snd (getMaxPerm m1)) ! b1).
    unfold option_implication,PMap.get,getMaxPerm in *.
    simpl. 
    rewrite Hdmap in Himpl.
    repeat match_case; auto.
    repeat match_case in Himpl; auto.
    rewrite canon_mem_access in Heqo2.
    congruence.
  - pose proof (Mem.mi_perm
                  _ _ _ Hmi_inj b1 b2 delta
                  ofs Max Nonempty H); eauto.
    unfold Mem.perm in *.
    repeat rewrite_getPerm.
    rewrite Hdmap in *.
    unfold PMap.get in *.
    repeat match_case in Himpl.
    2:{ rewrite canon_mem_access in *; inv Himpl. }
    rewrite PTree.gmap1.
    repeat match_case in H0; simpl; auto.
    + unfold getMaxPerm in Heqo3; simpl in *.
      rewrite PTree.gmap1 in  Heqo3.
      rewrite  Heqo3; auto.
    + rewrite PTree.gmap1 in  Heqo1.
      unfold getMaxPerm in *; simpl in *.
      rewrite PTree.gmap1 in *.
      destruct ((snd (Mem.mem_access m1)) ! b1) eqn:HH;
        simpl in *; inv Heqo1; inv Heqo2.
      unfold option_implication in *.
      rewrite canon_mem_access in H0.
      match_case in Himpl.
      exploit H0; try (intros HHH; inv HHH).
      constructor.
      
Qed.
Lemma option_implication_injection_dmap:
  forall mu m1 m2 b1 b2 ofs dmap o delta
    (Hdmap: dmap_get dmap b1 ofs = Some o)
    (Himpl: option_implication
              (dmap_get dmap b1 ofs)
              ((getMaxPerm m1) !! b1 ofs))
    (Hmi_inj:Mem.mem_inj mu m1 m2),
    mu b1 = Some (b2, delta) ->
    option_implication
      dmap ! b1 (snd (getMaxPerm m2)) ! b2.
Proof.
  intros.
  exploit (@option_implication_injection (option permission)); eauto.
  reflexivity.
Qed.
Lemma option_implication_fst:
  forall {A B} (perm1 perm2:PMap.t (A -> option B)),
    (forall b ofs,
        option_implication (perm1 !! b ofs) (perm2 !! b ofs)) ->
    forall ofs, option_implication ((fst perm1) ofs) ((fst perm2) ofs).
Proof.
  intros *.
  pose proof (finite_ptree (snd perm1)).
  pose proof (finite_ptree (snd perm2)).
  normal_hyp.
  remember (Pos.max (x0 + 1) (x+1)) as bound.
  intros.
  specialize (H1 bound ofs). unfold PMap.get in *.
  rewrite H, H0 in H1; auto; xomega.
Qed.
Lemma option_impl_isCanon:
  forall perm m1,
    (forall (b : positive) (ofs : Z),
        option_implication (perm !! b ofs) ((getMaxPerm m1) !! b ofs)) ->
    isCanonical perm.
Proof.
  intros * Himpl; unfold.
  extensionality ofs.
  eapply option_implication_fst in Himpl.
  instantiate(1:= ofs) in Himpl.
  rewrite Max_isCanonical in Himpl.
  unfold option_implication in Himpl. match_case in Himpl.
Qed.
Definition option_implication_dmap_access (dmap:delta_map)(map: access_map) :=
  forall b ofs, option_implication (dmap_get dmap b ofs) (map !! b ofs).
Definition option_implication_dmap_access_pair :=
  pair21_prop option_implication_dmap_access.
Hint Unfold option_implication_dmap_access_pair: pair.
Definition option_implication_access (a1 a2: access_map) :=
  forall b ofs, option_implication (a1 !! b ofs) (a2 !! b ofs).
Definition option_implication_access_pair :=
  pair21_prop option_implication_access.
Hint Unfold option_implication_access_pair: pair.




Definition dmap_valid (m:mem) (dm:delta_map) :=
  forall b ofs p,
    dmap_get dm b ofs = Some p ->
    Mem.valid_block m b.
Definition dmap_valid_pair m:=
  pair1_prop (dmap_valid m).
Hint Unfold dmap_valid_pair: pair.

Definition map_valid (m:mem) (am:access_map) :=
  forall b ofs p,
    am !! b ofs = Some p ->
    Mem.valid_block m b.

Definition map_valid_pair m:= pair1_prop (map_valid m).
Hint Unfold map_valid_pair: pair.

Lemma sub_map_valid:
  forall m (a:access_map),
    (fun a => sub_map (snd a) (snd (getMaxPerm m))) a ->
    map_valid m a.
Proof.
  intros ** ? **.
  unfold sub_map in H.
  eapply strong_tree_leq_spec in H; try constructor.
  instantiate (1:=b) in H.
(*
                        eapply map_get_Some in H0;
                          destruct H0 as [f [H0 ?]].
                        rewrite H0 in H.
                        destruct ((snd (getMaxPerm m)) ! b) eqn:HH1; try solve[ inversion H].
                        specialize (H ofs ltac:(rewrite H1; auto)).
                        destruct (o ofs) eqn:HH2; try solve[inversion H].
                        assert ((getMaxPerm m) !! b ofs = Some p0).
                        { unfold PMap.get; rewrite HH1; assumption. }
                        rewrite getMaxPerm_correct in H2.
                        unfold permission_at in H2.

                        destruct (mem_lemmas.valid_block_dec m b); auto.
                        eapply m in n.
                        rewrite H2 in n; congruence.*)
Admitted.
Lemma sub_map_valid_pair:
  forall m (aa:Pair access_map),
    pair1_prop
      (fun a => sub_map (snd a) (snd (getMaxPerm m))) aa ->
    map_valid_pair m aa.
Proof.
  intros m; solve_pair. eapply sub_map_valid.
Qed.

Lemma join_dmap_valid:
  forall m (a:delta_map),
    sub_map a (snd (getMaxPerm m)) ->
    dmap_valid m a.
Proof.
  intros ** ? **.
  
  unfold sub_map in H.
  eapply strong_tree_leq_spec in H; try constructor.
  instantiate (1:=b) in H.
  eapply dmap_get_Some in H0;
    destruct H0 as [f [H0 ?]].
  rewrite H0 in H.
  destruct ((snd (getMaxPerm m)) ! b) eqn:HH1; try solve[ inversion H].
  specialize (H ofs ltac:(rewrite H1; auto)).
  destruct (o ofs) eqn:HH2; try solve[inversion H].
  assert ((getMaxPerm m) !! b ofs = Some p0).
  { unfold PMap.get; rewrite HH1; assumption. }
  rewrite getMaxPerm_correct in H2.
  unfold permission_at in H2.

  destruct (mem_lemmas.valid_block_dec m b); auto.
  eapply m in n.
  rewrite H2 in n; congruence.
Qed.
Lemma join_dmap_valid_pair:
  forall m (aa:Pair delta_map),
    pair1_prop
      (fun a => sub_map a (snd (getMaxPerm m))) aa ->
    dmap_valid_pair m aa.
Proof.
  intros ?; solve_pair. apply join_dmap_valid.
Qed.




Record perm_perfect_virtue f (angel1 angel2:virtue):=
  { permp: perm_perfect_image_pair f (virtueLP angel1) (virtueLP angel2);
    pperm_dmap: perm_perfect_image_dmap_pair
                  f (virtueThread angel1) (virtueThread angel2)
  }.


Lemma delta_map_join_inject_pair' (m:mem) f:
  forall angel1 angel2 C1 C2
    (Hvirtue_inject: perm_perfect_virtue f angel1 angel2),
    Mem.meminj_no_overlap f m ->
    dmap_vis_filtered_pair (virtueThread angel1) m ->
    permMapLt_pair C1 (getMaxPerm m) ->
    almost_perfect_image_pair f (getMaxPerm m) C1 C2 -> 
    delta_map_join_pair (virtueThread angel1) (virtueLP angel1) C1 ->
    delta_map_join_pair (virtueThread angel2) (virtueLP angel2) C2.
Proof.
  intros; destruct Hvirtue_inject.
  eapply delta_map_join_inject_pair; eauto.
Qed.

Lemma perm_surj_compute:
  forall (f:meminj) perm1 perm2 dmap1 dmap2,
    perm_surj f perm1 perm2 ->
    perm_perfect_image_dmap f dmap1 dmap2 ->
    perm_surj f (computeMap perm1 dmap1) (computeMap perm2 dmap2).
Proof.
  unfold perm_surj; intros.
  destruct (dmap_get dmap2 b2 ofs_delt) eqn:HH.
  - exploit (ppre_perfect_image_dmap H0).
    { rewrite HH; constructor. }
    intros (?&?&?&?&?&?).
    repeat (econstructor; eauto).
    rewrite HH in H4; symmetry in H4.
    eapply dmap_get_copmute_Some in HH.
    eapply dmap_get_copmute_Some in H4.
    rewrite HH, H4; reflexivity.
  - eapply dmap_get_copmute_None in HH as HH';
      rewrite HH' in H1.
    eapply H in H1 as (b1&ofs&delt&?&?&?).
    repeat (econstructor; eauto).
    rewrite HH', H3.
    symmetry.
    destruct (dmap_get dmap1 b1 ofs) eqn: HH1.
    + revert HH; subst ofs_delt.
      intros.
      destruct (dmap_get dmap1 b1 ofs) eqn:Heq1.
      { exploit (p_image_dmap H0).
        rewrite Heq1; repeat constructor.
        intros; normal. unify_injection. inv HH1.
        rewrite Heq1 in H4. rewrite <- H4 in HH; congruence. }
      congruence.
      
    + eapply dmap_get_copmute_None; eassumption.
Qed.

Lemma injection_full_nextblock:
  forall f m m',
    Mem.nextblock m = Mem.nextblock m' ->
    Events.injection_full f m ->
    Events.injection_full f m'.
Proof.
  intros ** ? **.
  eapply H0. unfold Mem.valid_block.
  rewrite H; auto.
Qed.



Lemma permMapLt_setPermBlock2:
  forall op b ofs perm1 perm2 sz,
    (0 < sz)%nat-> 
    permMapLt perm1 perm2 ->
    permMapLt (setPermBlock op b ofs perm1 sz)
              (setPermBlock op b ofs perm2 sz).
Proof.
  intros ** b0 ofs0.
  destruct_address_range b ofs b0 ofs0 sz.
  - do 2 (rewrite setPermBlock_same; auto); apply po_refl.
  - eapply Intv.range_notin in Hrange;
      try (simpl; omega).
    do 2 (erewrite setPermBlock_other_1; auto).
  - do 2 (rewrite setPermBlock_other_2; auto).
Qed.

Lemma inject_almost_perfect:
  forall f m1 m2,
    Mem.inject f m1 m2 ->
    almost_perfect_image f
                         (getMaxPerm m1) (getCurPerm m1) (getCurPerm m2).
Admitted.
Lemma almost_perfect_image_proper:
  Proper (Logic.eq ==> access_map_equiv
                   ==> access_map_equiv
                   ==> access_map_equiv
                   ==> iff) almost_perfect_image.
Proof.
  setoid_help.proper_iff;
    setoid_help.proper_intros; subst.
  intros ? **.
  rewrite <- H0, <- H1, <- H2  in *; auto.
Qed.


Lemma inject_almost_perfect_pair
  : forall (f : meminj) (m1 m2 : mem)
      p11 p12 p21 p22 Hlt11 Hlt12 Hlt21 Hlt22,
    Mem.inject f (@restrPermMap p12 m1 Hlt12) (@restrPermMap p22 m2 Hlt22) ->
    Mem.inject f (@restrPermMap p11 m1 Hlt11) (@restrPermMap p21 m2 Hlt21) ->
    almost_perfect_image_pair f (getMaxPerm m1) (p11,p12) (p21,p22). 
Proof.
  constructor; simpl.
  - eapply inject_almost_perfect in H0.
    eapply almost_perfect_image_proper; eauto.
    + symmetry. eapply getMax_restr.
    + symmetry. eapply getCur_restr.
    + symmetry. eapply getCur_restr.
  - eapply inject_almost_perfect in H.
    eapply almost_perfect_image_proper; eauto.
    + symmetry. eapply getMax_restr.
    + symmetry. eapply getCur_restr.
    + symmetry. eapply getCur_restr.
Qed.

Lemma sub_map_filtered:
  forall m a,
    sub_map a (snd (getMaxPerm m)) ->
    dmap_vis_filtered a m.
Proof.
  unfold dmap_vis_filtered, Mem.perm.
  
  intros. 
  intros; eapply sub_map_lt in H.
  instantiate(1:=b) in H.
  rewrite_getPerm.
  unfold PMap.get.
  unfold dmap_get, PMap.get in H0.
  simpl in H0.
  match_case in H0.
  destruct ((snd (getMaxPerm m)) ! b) eqn:HMax;
    try solve[inv H].
  simpl in H.
  exploit H.
  - destruct (o ofs) eqn:HH; try congruence.
    rewrite HH; auto.
  - intros HH; destruct (o0 ofs); inv HH.
    constructor.
Qed.
Lemma sub_map_filtered_pair:
  forall m a,
    pair21_prop sub_map a (snd (getMaxPerm m)) ->
    dmap_vis_filtered_pair a m.
Proof. intros m; solve_pair.
       eapply sub_map_filtered. Qed.


Definition permMapLt_range (perms:access_map) b lo hi p:=
  forall ofs : Z, lo <= ofs < hi ->
             Mem.perm_order'' (perms !! b ofs) p.

(*Lookup : 
                setPermBlock_range_perm  *)
Lemma permMapLt_setPermBlock:
  forall perm1 perm2 op b ofs sz,
    permMapLt_range perm2 b ofs (ofs + Z.of_nat sz) op  ->
    permMapLt perm1 perm2 ->
    permMapLt (setPermBlock op b ofs perm1 sz) perm2.
Proof. Admitted.
Lemma permMapLt_range_mem:
  forall perm b lo hi p m,
    permMapLt_range perm b lo hi (Some p) ->
    forall (Hlt:permMapLt perm (getMaxPerm m)),
      Mem.range_perm (restrPermMap Hlt) b lo hi Cur p.
Proof.
  unfold Mem.range_perm, Mem.perm; intros.
  rewrite_getPerm. rewrite getCur_restr.
  eapply H; assumption.
Qed.

Definition setPermBlock_pair b ofs:=
  pair3 (fun p => setPermBlock p b ofs).
Hint Unfold setPermBlock_pair: pair.
Definition setPermBlock_var_pair b ofs size:=
  pair2 (fun p pmap => setPermBlock_var p b ofs pmap size).
Hint Unfold setPermBlock_var_pair: pair.

Lemma permMapLt_computeMap:
  forall c a b,
    deltaMapLt2 b c ->
    permMapLt a c ->
    permMapLt (computeMap a b) c.
Proof.
  intros ** ??.
  destruct (dmap_get b b0 ofs) eqn:HH.
  - erewrite dmap_get_copmute_Some; try eassumption.
    unfold deltaMapLt2 in *.
    specialize (H b0 ofs). rewrite HH in H.
    inv H; auto.
  - erewrite dmap_get_copmute_None; try eassumption.
    eapply H0.
Qed.
Lemma permMapLt_computeMap_pair:
  forall c a b,
    deltaMapLt2_pair1 b c ->
    permMapLt_pair a c ->
    permMapLt_pair (computeMap_pair a b) c.
Proof.
  intros ?. solve_pair. apply permMapLt_computeMap.
Qed.

Lemma permMapLt_computeMap':
  forall c a b,
    permMapLt (computeMap a b) c ->
    deltaMapLt2 b c.
Proof.
  intros ** ??.
  specialize (H b0 ofs).
  destruct (dmap_get b b0 ofs) eqn:HH.
  - erewrite dmap_get_copmute_Some in H; try eassumption.
    constructor; auto.
  - constructor.
Qed.
Lemma permMapLt_computeMap_pair':
  forall c a b,
    permMapLt_pair (computeMap_pair a b) c ->
    deltaMapLt2_pair1 b c.
Proof.
  intros ?.
  solve_pair. eapply permMapLt_computeMap'.
Qed.

Lemma permMapLt_empty_pair:
  forall a, permMapLt_pair (pair0 empty_map) a.
Proof.
  intros ?. solve_pair; apply empty_LT.
Qed.

Definition permMapLt_range_pair perm b lo hi:=
  pair1_prop  (permMapLt_range perm b lo hi).
Hint Unfold permMapLt_range_pair: pair.

Lemma permMapLt_setPermBlock_pair:
  forall perm2 b ofs sz perm1 op,
    permMapLt_range_pair perm2 b ofs (ofs + Z.of_nat sz) op  ->
    permMapLt_pair perm1 perm2 ->
    permMapLt_pair (setPermBlock_pair b ofs op perm1 (pair0 sz)) perm2.
Proof.
  intros ? ? ? ?; solve_pair.
  intros; eapply permMapLt_setPermBlock; assumption.
Qed.
Lemma permMapLt_range_pair_left:
  forall a b lo hi perm1 perm2,
    permMapLt_range a b lo hi perm1 ->
    Mem.perm_order'' perm1 perm2 ->
    permMapLt_range_pair a b lo hi (perm1, perm2).
Proof.
Admitted.
Lemma permMapLt_range_pair_right:
  forall a b lo hi perm1 perm2,
    permMapLt_range a b lo hi perm2 ->
    Mem.perm_order'' perm2 perm1 ->
    permMapLt_range_pair a b lo hi (perm1, perm2).
Proof.
Admitted.

Ltac permMapLt_range_pair_simpl:=
  first [eapply permMapLt_range_pair_left; [|constructor]
        |eapply permMapLt_range_pair_right; [|constructor]].
Lemma permMapLt_range_trans:
  forall perms1 perms2 b lo hi perm,
    permMapLt_range perms1  b lo hi perm ->
    permMapLt perms1 perms2 ->                                
    permMapLt_range perms2  b lo hi perm.
Proof.
Admitted.
Lemma range_mem_permMapLt:
  forall b lo hi p m,
    Mem.range_perm m b lo hi Cur p ->
    permMapLt_range (getCurPerm m) b lo hi (Some p).
Proof.
Admitted.

Lemma make_mem_eq:
  forall m m',
    Mem.mem_contents m = Mem.mem_contents m' ->
    Mem.mem_access m = Mem.mem_access m' ->
    Mem.nextblock m = Mem.nextblock m' ->
    m = m'.
Proof.
  intros ??.
  destruct m, m'; simpl.
  intros **; subst.
  assert (access_max = access_max0).
  { apply Axioms.proof_irr. }
  assert (nextblock_noaccess = nextblock_noaccess0).
  { apply Axioms.proof_irr. }
  assert (contents_default = contents_default0).
  { apply Axioms.proof_irr. }
  intros **; subst.
  reflexivity.
Qed.
Lemma restrPermMap_equiv_eq:
  forall perm perm' m m' Hlt Hlt',
    access_map_equiv perm perm' ->
    m = m' ->
    @restrPermMap perm  m  Hlt =
    @restrPermMap perm' m' Hlt'.
Proof.
  intros. subst m.
  unfold restrPermMap.
  eapply make_mem_eq; simpl; auto.
  remember (snd (Mem.mem_access m')) as T.
  f_equal.
  unfold PTree.map.
  remember 1%positive as i eqn:HH.
  clear HH; revert i; clear -H.
  induction T; auto.
  intro; simpl.
  f_equal; eauto.
  destruct o; f_equal.
  extensionality ofs.
  extensionality k.
  destruct k; auto.
  erewrite H; reflexivity.
Qed.

Lemma mem_is_restr_eq:
  forall m, m = restrPermMap (cur_lt_max m).
Proof.
  intros.
  pose proof (Clight_bounds.Mem_canonical_useful m) as Hbound.
  destruct m; simpl in *.
  eapply easy_mem_eq; try reflexivity.
  simpl. simpl.
  clear - Hbound.
  destruct mem_access; f_equal; simpl.
  - extensionality ofs.
    extensionality k.
    destruct k; auto.
  - match goal with
      |- context[
            PTree.map ?access _
          ] => replace access with
        (fun b f ofs k => match k with
                       | Max => f ofs Max
                       | Cur => (o, t) !! b ofs Cur
                       end)
        
    end.
    2: { extensionality b.
         extensionality f.
         extensionality ofs.
         extensionality k.
         destruct k; auto.
         symmetry; apply getCurPerm_correct.
    }
    rewrite trivial_ptree_map; auto.
    intros.
    extensionality ofs.
    extensionality k.
    destruct k; auto.
    unfold PMap.get; simpl.
    rewrite H; reflexivity.
Qed.

Instance sub_map_virtue_proper:
  Proper (Logic.eq ==> access_map_equiv ==> iff) sub_map_virtue.
Admitted.