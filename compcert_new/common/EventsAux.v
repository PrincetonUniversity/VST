
Require Import String.
Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.

Require Import Maps.


Require Import Morphisms.
Require Import Setoid.
Require Import RelationClasses.


Lemma Forall2_impl:
  forall {A B} (r1 r2:A-> B -> Prop) l1 l2, (forall a b, r1 a b -> r2 a b) ->
                                  Forall2 r1 l1 l2 -> Forall2 r2 l1 l2.
Proof.
  intros until l1; induction l1.
  - intros * ? H; inv H; constructor.
  - intros * ? H; inv H; constructor; eauto.
Qed.

(* New strong injection. This relation is injective! *)
Inductive inject_strong (mi : meminj) : val -> val -> Prop :=
  inject_int : forall i : int, inject_strong mi (Vint i) (Vint i)
| inject_long : forall i : int64, inject_strong mi (Vlong i) (Vlong i)
| inject_float : forall f : float, inject_strong mi (Vfloat f) (Vfloat f)
| inject_single : forall f : float32, inject_strong mi (Vsingle f) (Vsingle f)
| inject_ptr : forall (b1 : block) (ofs1 : ptrofs) (b2 : block) (ofs2 : ptrofs) (delta : Z),
    mi b1 = Some (b2, delta) ->
    ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta) ->
    inject_strong mi (Vptr b1 ofs1) (Vptr b2 ofs2)
| val_inject_undef : inject_strong mi Vundef Vundef.
Inductive memval_inject_strong (f : meminj) : memval -> memval -> Prop :=
  memval_inject_byte_str : forall n : byte, memval_inject_strong f (Byte n) (Byte n)
| memval_inject_frag_str : forall (v1 v2 : val) (q : quantity) (n : nat),
    inject_strong f v1 v2 ->
    memval_inject_strong f (Fragment v1 q n) (Fragment v2 q n)
| memval_inject_undef_str : memval_inject_strong f Undef Undef.

Definition list_memval_inject mu:= Forall2 (memval_inject mu).
Definition list_memval_inject_strong mu:= Forall2 (memval_inject_strong mu).
Lemma memval_inject_strong_weak:
  forall f v1 v2, memval_inject_strong f v1 v2 ->  memval_inject f v1 v2.
Proof. intros * HH; inv HH; econstructor; auto. inv H; econstructor; eauto. Qed.
Lemma list_memval_inject_strong_weak:
  forall f vals1 vals2, list_memval_inject_strong f vals1 vals2 ->
                   list_memval_inject f vals1 vals2.
Proof. intros *; eapply Forall2_impl; apply memval_inject_strong_weak. Qed.

(*Injection for block ranges*)
Inductive inject_hi_low (mu:meminj): (block * Z * Z) -> (block * Z * Z) -> Prop:=
| HiLow: forall b1 b2 hi low delt,
    mu b1 = Some(b2, delt) ->
    inject_hi_low mu (b1, hi, low) (b2, hi+delt, low+delt).
Definition list_inject_hi_low mu := Forall2 (inject_hi_low mu).

(*
  Delta Permission Maps:
  A change in memory permissions.
  - They have the same shape as the memories
  - they return [None], if the permission doesn't change at that location
  - return [Some perm], if the new permission is [perm].
 *)

Definition delta_map := PTree.t (Z -> option (option permission)).
Definition dmap_get (dm:delta_map) b ofs:=
  PMap.get b (fun _ => None, dm) ofs.
Definition inject_Z_map {A} (delt: Z) (f1 f2: (Z -> option A)): Prop:=
  forall ofs p, f1 ofs = Some p -> f1 ofs = f2 (ofs+ delt).

Record inject_delta_map (mu: meminj)(dpm1 dpm2: delta_map): Prop:=
  { DPM_image: (*All permissions changed are mapped*)
      forall b1 ofs p,
        dmap_get dpm1 b1 ofs = Some p -> 
        exists b2 delt, mu b1 = Some (b2, delt) /\
                   dmap_get dpm2 b2 (ofs + delt) = Some p
    ;DPM_preimage:
       forall b2 ofs2 p,
         dmap_get dpm2 b2 ofs2 = Some p ->
         exists b1 ofs1 delt,
           mu b1 = Some(b2, delt) /\
           dmap_get dpm1 b1 ofs1 = Some p /\ 
           ofs2 = ofs1 + delt
  }.

(** *Relations that are monotonic w.r.t. injections*)
Definition inj_monotone{A} (R:meminj -> A -> A-> Prop):Prop:=
  forall (a b:A) f f',  R f a b -> inject_incr f f' -> R f' a b.
Lemma Forall2_incr:
  forall {A} (R: meminj -> A -> A -> Prop),
    inj_monotone R ->
    inj_monotone (fun j => Forall2 (R j)).
Proof.
  intros A R HR; unfold inj_monotone.
  induction a; intros ? ? ? HH; inv HH; intros; constructor; eauto.
Qed.
Create HintDb inj_mono. Hint Resolve Forall2_incr: inj_mono.
Ltac inj_mono_tac:=
  match goal with
    [|- inj_monotone ?R ] =>
    (* If it's a list try the list lemma *)
    try (eapply Forall2_incr; eauto with  inj_mono);
    intros ???? ?HR ?Hincr; inv HR;
    try solve[econstructor; eauto with inj_mono]
  | _ => fail "Expected goal: inj_monotone ?R" 
  end.
Lemma inj_delta_map_mono: inj_monotone inject_delta_map.
Proof. inj_mono_tac. econstructor.
       + intros. exploit DPM_image0; eauto.
         intros (?&?&?&?).
         repeat (econstructor; eauto).
       + intros; exploit DPM_preimage0; eauto.
         intros (?&?&?&?&?&?).
         repeat (econstructor; eauto).
Qed.
Hint Resolve inj_delta_map_mono: inj_mono.

(** * Relations that compose with injections *)
Definition composes_inj {A} (R: meminj -> A -> A ->Prop):=
  forall j12 j23 x1 x2 x3, R j12 x1 x2 -> R j23 x2 x3 -> R (compose_meminj j12 j23) x1 x3.
Create HintDb compose_inj.
Lemma Forall2_compose:
  forall {A} (R: meminj -> A -> A -> Prop),
    composes_inj R -> composes_inj (fun j => Forall2 (R j)).
Proof.
  intros ** ?? ls. induction ls; intros * H0 H1;
                     inv H0; inv H1; constructor; eauto.
Qed.
Hint Resolve Forall2_compose: compose_inj.
Ltac composition_arithmetic:=
  (* Solves the Ptrofs.add... goal that results from 
       injecting a pointer twice: the offsets are added 
       in two different ways *)
  rewrite Ptrofs.add_assoc; decEq;
  unfold Ptrofs.add; apply Ptrofs.eqm_samerepr; auto with ints.
Ltac composed_injections_injection_case j12 j23:=
  match goal with
  |[ H12: j12 _ = Some _, H23: j23 _ = Some _ |-
     context[compose_meminj j12 j23] ] =>
   econstructor;
   try (unfold compose_meminj; rewrite H12; rewrite H23); eauto;
   try composition_arithmetic; eauto with compose_inj
  end.
Ltac composed_injections:=
  match goal with
  |[|- composes_inj ?R] =>
   let H1:= fresh "H1" in let H2:= fresh "H2" in 
                          intros j12 j23  ??? H1 H2;
                          inv H1; auto; inv H2; auto;
                          try solve[econstructor; eauto with compose_inj];
                          try composed_injections_injection_case j12 j23
  | _ => fail "Not the shape expected"
  end.
Ltac rewrite_compose_meminj:=
  match goal with
  |[ H12: ?j12 _ = Some _, H23: ?j23 _ = Some _ |-
     context[compose_meminj ?j12 ?j23]
   ] => unfold compose_meminj; rewrite H12, H23
  end.


Lemma inject_delta_map_compose: composes_inj inject_delta_map.
Proof. intros ? **.
       inv H; inv H0.
       constructor.
       - intros; exploit  DPM_image0; eauto.
         intros (?&?&?&?).
         exploit  DPM_image1; eauto.
         intros (?&?&?&?).
         repeat (econstructor; eauto).
         unfold compose_meminj;
           rewrite H0, H2; reflexivity.
         rewrite <- H3. f_equal. omega.
       - intros; exploit  DPM_preimage1; eauto.
         intros (?&?&?&?&?&?).
         exploit  DPM_preimage0; eauto.
         intros (?&?&?&?&?&?).
         repeat (econstructor; eauto).
         unfold compose_meminj; rewrite H3, H0; reflexivity.
         subst; eauto; omega.
Qed.
Hint Resolve inject_delta_map_compose: compose_inj.

Lemma inject_hi_low_compose: composes_inj inject_hi_low.
Proof. composed_injections; do 2 rewrite Zplus_assoc_reverse.
       econstructor; rewrite_compose_meminj; reflexivity. Qed.
Hint Resolve inject_hi_low_compose:compose_inj. 
Lemma list_inject_hi_low_compose: composes_inj list_inject_hi_low.
Proof. eauto with compose_inj. Qed.
Hint Resolve list_inject_hi_low_compose:compose_inj. 



(** *Strong interpolation:
    An injection relation, induced by a composed meminj,
    can be split into a strong one and a regular one.
 *)
Definition strong_interpolation {A} (R: meminj -> A -> A -> Prop)
           (R_strong: meminj -> A -> A -> Prop):=
  forall v1 v3 j12 j23, R (compose_meminj j12 j23) v1 v3 ->
                   exists v2,  R_strong j12 v1 v2 /\ R j23 v2 v3.
Create HintDb str_interp.
Ltac case_compose_meminj:=
  match goal with
  | [ H: compose_meminj ?f1 ?f2 ?b = Some _  |- _ ] =>
    unfold compose_meminj in H; repeat match_case in H;
    subst;
    try match goal with
        | [ H: Some _ = Some _ |- _ ] => inv H
        end
  end.
(* apply a strong interpolation lemma in a hypothesis*)
Lemma list_str_interpol:
  forall {A} (R R_str: meminj -> A -> A -> Prop) ,
    strong_interpolation R R_str ->
    strong_interpolation (fun f => Forall2 (R f))
                         (fun f => Forall2 (R_str f)).
Proof.
  intros.
  unfold strong_interpolation.
  induction v1; intros.
  - inv H0; do 3 econstructor. 
  - inv H0.
    exploit IHv1; eauto. intros (?&?&?).
    exploit H; eauto. intros (?&?&?).
    do 3 econstructor; eauto.
Qed.
Lemma str_interpol_cut:
  forall A R R_str,
    @strong_interpolation A R R_str -> 
    @strong_interpolation A R R_str.
Proof. eauto. Qed.
Ltac use_interpolations_in_hyps:=
  match goal with
  | [ H: ?R (compose_meminj ?j12 ?j23) _ _ |- _ ] =>
    eapply (@str_interpol_cut _ R) in H;
    [ destruct H as (?&?&?) | solve[eauto with str_interp]]
  end.
Ltac str_interp:=
  match goal with
    [|- strong_interpolation ?R ?R_Str] =>
    (* try if it's a list*)
    try (eapply list_str_interpol;
         eauto with str_interp);
    intros ???? ?HR; inv HR;
    try case_compose_meminj;
    (* exploit one interpolation from the hypothesis *)
    repeat use_interpolations_in_hyps;
    (*try easy cases *)
    try solve[ do 3 econstructor];
    try solve[repeat (econstructor; eauto with str_interp)]
  end.

Ltac destruct_dmap_get:=
  match goal with
  | H: dmap_get ?v1 ?b1 ?ofs = Some ?p |- _ =>
    let HH:= fresh in
    assert(HH:=H); unfold dmap_get,PMap.get in HH;
    simpl in HH; match_case in HH
  end.

(* We convert delta_maps into lists (delta_lists) to prove the interpolation *)
Notation delta_list:= (list (block * (Z -> option (option permission)))).
Definition flat_dm (dm:delta_map): delta_list:= PTree.elements dm.
Definition unflat_dm (dm:delta_list):delta_map:= PTree_Properties.of_list dm.
Record inject_delta_map_flat' (mu : meminj) (dpm1 dpm2 : delta_list) : Prop
  := Build_inject_delta_map_flat'
       { DPM_image_flat' : forall (b1 : positive) (ofs : Z)
                             (p : option permission) f,
           In (b1,f) dpm1 ->
           f ofs = Some p ->
           exists (b2 : block) (delt : Z) f2,
             mu b1 = Some (b2, delt) /\
             In (b2,f2) dpm2 /\
             f2 (ofs + delt) = Some p;
         DPM_preimage_flat' : forall (b2 : positive) (ofs2 : Z)
                                (p : option permission) f2,
             In (b2,f2) dpm2 -> 
             f2 (ofs2) = Some p ->
             exists (b1 : block) (ofs1 delt : Z) f1,
               mu b1 = Some (b2, delt) /\
               In (b1,f1) dpm1 /\
               f1 ofs1 = Some p /\
               ofs2 = ofs1 + delt}.
Record inject_delta_map_flat (mu : meminj) (dpm1 dpm2 : delta_list) : Prop
  := Build_inject_delta_map_flat
       { DPM_image_flat : forall (b1 : positive) (ofs : Z)
                            (p : option permission) f,
           In (b1,f) dpm1 ->
           f ofs = Some p ->
           exists (b2 : block) (delt : Z) f2,
             mu b1 = Some (b2, delt) /\
             In (b2,f2) dpm2 /\
             f2 (ofs + delt) = Some p;
         DPM_preimage_flat : forall (b2 : positive) (ofs2 : Z)
                               (p : option permission) f2,
             In (b2,f2) dpm2 -> 
             f2 (ofs2) = Some p ->
             exists (b1 : block) (ofs1 delt : Z) f1,
               mu b1 = Some (b2, delt) /\
               In (b1,f1) dpm1 /\
               f1 ofs1 = Some p /\
               ofs2 = ofs1 + delt;
         non_repeat: list_norepet (map fst (dpm2))}.
Lemma inject_delta_map_flaten:
  forall dm1 dm2 f,
    inject_delta_map f dm1 dm2 ->
    inject_delta_map_flat f (flat_dm dm1) (flat_dm dm2).
Proof.
  intros * [Himg Hpre]; 
    unfold dmap_get, PMap.get,flat_dm in *; simpl in *;
      econstructor.
  - intros. exploit Himg.
    erewrite PTree.elements_complete; eauto.
    intros (?&?&?&?). match_case in H2.
    repeat (econstructor; eauto).
    apply PTree.elements_correct; auto.
  - intros. exploit Hpre.
    erewrite PTree.elements_complete; eauto.
    intros (?&?&?&?&?&?). match_case in H2.
    repeat (econstructor; eauto).
    apply PTree.elements_correct; auto.
  - apply PTree.elements_keys_norepet.
Qed.
Lemma of_list_norepet':
  forall (A : Type) (l : list (PTree.elt * A)) ,
    list_norepet (map fst l) ->
    forall (k : PTree.elt) (v : A),
      In (k, v) l -> (PTree_Properties.of_list l) ! k = Some v.
Proof. intros; eapply PTree_Properties.of_list_norepet; auto. Qed.
Lemma inject_delta_map_unflaten:
  forall dm1 dm2 f,
    list_norepet (map fst dm1) ->
    list_norepet (map fst dm2) ->
    inject_delta_map_flat f dm1 dm2 ->
    inject_delta_map f (unflat_dm dm1) (unflat_dm dm2).
Proof.
  intros * Hnr1 Hnr2 [Himg Hpre]; 
    unfold dmap_get, PMap.get,unflat_dm in *; simpl in *.
  pose proof (of_list_norepet' _ _ Hnr1) as Hcorrec1.
  pose proof (of_list_norepet' _ _ Hnr2) as Hcorrec2.

  econstructor.
  - intros; destruct_dmap_get. exploit Himg; eauto.
    eapply PTree_Properties.in_of_list; eauto.
    intros (?&?&?&?&?&?). 
    repeat (econstructor; eauto).
    unfold dmap_get, PMap.get,unflat_dm in *; simpl in *.
    erewrite Hcorrec2; eauto.
  - intros; destruct_dmap_get. exploit Hpre; eauto.
    eapply PTree_Properties.in_of_list; eauto.
    intros (?&?&?&?&?&?&?&?). 
    repeat (econstructor; eauto).
    unfold dmap_get, PMap.get,unflat_dm in *; simpl in *.
    erewrite Hcorrec1; eauto.
Qed.

Definition project_block (j12:meminj) b_fb: (block * (Z -> option (option permission))):=
  (match j12 (fst b_fb) with
   | Some (b2, delt) => (b2, fun ofs => (snd b_fb) (ofs - delt))
   | None => (1%positive, fun _ => None)
   end).
(* Prove interpolation for repeating lists*)
Lemma inject_delta_interpolation_flat':
  strong_interpolation inject_delta_map_flat' inject_delta_map_flat'.
Proof.
  intros dm1 dm2 ?? HH.
  exists (map (project_block j12) dm1); split; constructor; intros.
  - (* image d1 d2 *)
    exploit DPM_image_flat'; eauto.
    intros (?&?&?&?&?&?).
    unfold compose_meminj in H1; repeat match_case in H1; inv H1; subst.
    eapply (in_map (project_block j12)) in H.
    unfold project_block in H; simpl in H. rewrite Heqo in H.
    do 4 econstructor; eauto; split; eauto.
    simpl. replace (ofs + z- z) with ofs by omega; auto.
  - (*preimage 12 *)
    eapply list_in_map_inv in H; destruct H as ((?&?)&?&?).
    unfold project_block in H; simpl in *.
    repeat match_case in H; subst; inv H; eauto; try congruence.
    exploit DPM_image_flat'; eauto.
    intros (?&?&?&?&?&?).
    repeat (econstructor; eauto). omega.
  - (* image d2 d3 *)
    eapply list_in_map_inv in H; destruct H as ((?&?)&?&?).
    unfold project_block in H; simpl in *.
    repeat match_case in H; subst; inv H; eauto; try congruence.
    exploit DPM_image_flat'; eauto.
    intros (?&?&?&?&?&?).
    unfold compose_meminj in H. rewrite Heqo0 in H.
    repeat match_case in H; inv H; subst.
    repeat (econstructor; eauto).
    rewrite <- H3; f_equal; omega.
  -(* image d3 d2 *)
    exploit DPM_preimage_flat'; eauto.
    intros (?&?&?&?&?&?&?&?).
    unfold compose_meminj in H1; repeat match_case in H1; inv H1; subst.
    (* Basically the first case again*)
    eapply (in_map (project_block j12)) in H2.
    unfold project_block in H2; simpl in H2.
    rewrite Heqo in H2. fold project_block in H2.
    do 4 eexists; split; eauto.
    split. eapply H2.
    instantiate(1:=x0+z).
    split.
    rewrite <- H3; f_equal; omega.
    omega.
Qed.

(* make a list into a non repeating list*)
Definition update_fn {A B} (f1 f2:A -> option B) (x:A): option B :=
  if f1 x then f1 x else f2 x.
Fixpoint update_node_list b fb (dm:delta_list) {struct dm} : delta_list :=
  match dm with
  | nil => (b,fb)::nil
  | (b',fb')::tl => if peq b b' then
                     (b, update_fn fb fb')::tl
                   else (b',fb')::(update_node_list b fb tl)
  end.
Definition add_node_list (node:block * (Z -> option (option permission))) (dm:delta_list):delta_list:=
  let (b, fb):= node in update_node_list b fb dm.
Lemma add_node_list_fst:
  forall b fb dm,
    map fst (add_node_list (b,fb) dm) =
    if (in_dec peq) b (map fst dm) then
      (map fst dm)
    else (map fst dm) ++ b::nil.
Proof.
  induction dm.
  - reflexivity.
  - simpl. repeat match_case; subst; eauto.
    + simpl. simpl in n. clear - n; contradict n; auto.
    + simpl. simpl in *. f_equal.
      rewrite IHdm. destruct  o0; subst. (exfalso; apply n; auto).
      match_case; eauto.
    + simpl in *.
      f_equal. rewrite IHdm. match_case. exfalso; apply n0; auto.
Qed.

Definition de_doubling (dm:delta_list):delta_list:=
  fold_right add_node_list nil dm.
Set Nested Proofs Allowed.

Lemma de_doubling_norepeat_fst: forall dm, list_norepet (map fst (de_doubling dm)). 
Proof.
  induction dm.
  - constructor.
  - simpl.
    destruct a; rewrite add_node_list_fst.
    match_case.
    apply list_norepet_append_commut; simpl.
    constructor; eauto.
Qed.
Lemma de_doubling_norepeat: forall dm, list_norepet (de_doubling dm). 
Proof.
  intros. pose proof (de_doubling_norepeat_fst dm).
  remember (de_doubling dm) as L. clear dm HeqL.
  induction L; inv H; constructor; eauto.
  intros HH; apply H2, in_map; auto.
Qed.

Lemma update_node_list_notin:
  forall dm b fb, ~ In b (map fst dm) ->
             update_node_list b fb dm = dm ++ (b,fb)::nil.
Proof.
  induction dm.
  - reflexivity.
  - intros. simpl in H.
    apply Decidable.not_or in H; destruct H.
    unfold update_node_list; simpl in *.
    match_case; simpl in *; subst.
    match_case. f_equal.
    eapply IHdm; auto.
Qed.

Lemma in_map_fst:
  forall {A B} l (a:A) (b:B),
    In (a,b) l ->
    In a (map fst l).
Proof.
  intros. replace a with (fst (a,b)) by reflexivity.
  apply in_map. simpl; auto.
Qed.
Lemma update_node_list_neq':
  forall dm b b' fb fb',
    b <> b' ->
    In (b, fb) (update_node_list b' fb' dm) ->
    In (b, fb) dm .
Proof.
  induction dm.
  - simpl; intros. inv H0; inv H1; congruence.
  - intros. simpl. unfold update_node_list in H0.
    do 2 (match_case in H0; subst).
    + inv H0; auto. inv H1; congruence.
    + inv H0; eauto.
Qed.

Lemma de_double_in:
  forall b dm,
    In b (map fst (de_doubling dm)) -> In b (map fst dm).
Proof.
  induction dm.
  - intros HH; inv HH.
  - intros; simpl. simpl in H.
    destruct a as (b'&fb').
    destruct (peq b' b); eauto.
    right. eapply IHdm.
    simpl in H.
    eapply list_in_map_inv in H as ((?&?)&?&?).
    eapply in_map_fst.
    subst; eapply update_node_list_neq'; eauto.
Qed.
Lemma update_node_list_in:
  forall dm b fb fb',
    In (b,fb') dm ->
    list_norepet (map fst dm) -> 
    In (b, update_fn fb fb')  (update_node_list b fb dm).
Proof.
  induction dm.
  intros. inv H.
  intros. inv H.
  - simpl. match_case.
    constructor; eauto.
  - simpl. repeat match_case; subst.
    + simpl in H0. inv H0.
      exfalso; apply H3. replace b0 with (fst (b0,fb')) by reflexivity.
      apply in_map; auto.
    + right; simpl.
      apply IHdm; eauto.
      simpl in H0; inv H0; auto.
Qed.
Lemma update_node_list_neq:
  forall dm b b' fb fb',
    b <> b' ->
    In (b, fb) dm ->
    In (b, fb) (update_node_list b' fb' dm).
Proof.
  induction dm.
  - simpl; intros. inv H0.
  - intros. simpl. do 2 (match_case; subst).
    + constructor 2. inv H0; auto.
      inv H1; congruence.
    + inv H0; auto.
      * constructor 1; auto. 
      * constructor 2; auto.
Qed.
Lemma de_doubling_sep1:
  forall dm b,
    In b (map fst dm) ->
    In (b, fold_right (fun b_fb base => if peq (fst b_fb) b then
                                       update_fn (snd b_fb) base 
                                     else base) (fun _ => None) dm) (de_doubling dm).
Proof.
  induction dm.
  - intros. inv H.
  - destruct a. simpl; intros.
    destruct ((in_dec peq) b (map fst dm)); swap 1 2.
    + destruct H; eauto. 2: exfalso; apply n; eauto.
      subst. subst. match_case. clear e Heqs.
      match goal with
        |- context[update_fn _ ?X] =>
        replace X with (fun _ : Z => @None (option permission))
      end.
      
      2: { clear -n. induction dm. simpl. reflexivity.
           destruct a; simpl. match_case; subst.
           - exfalso; apply n; constructor; reflexivity.
           - eapply IHdm. intros HH; apply n. constructor 2; auto. }

      rewrite update_node_list_notin; eauto.
      eapply in_app; right; constructor. f_equal.
      apply Axioms.extensionality; intros x; simpl.
      unfold update_fn; match_case; eauto.
      intros HH; eapply n.
      revert HH.
      
      eapply de_double_in.
    + match_case; subst.
      * eapply update_node_list_in.
        eapply IHdm; auto.
        eapply de_doubling_norepeat_fst.
      * eapply update_node_list_neq; auto.
Qed.

Definition equiv_one_side (dm1 dm2:delta_list): Prop:=
  forall b1 fb1 ofs p,
    In (b1,fb1) dm1 ->
    fb1 ofs = Some p ->
    exists fb1',  
      In (b1,fb1') dm2 /\
      fb1' ofs = Some p.
Definition equiv_delta (dm1 dm2:delta_list): Prop:=
  equiv_one_side dm1 dm2 /\
  equiv_one_side dm2 dm1.

Instance delta_list_equiv_Equivalence: Equivalence equiv_delta.
Proof.
  econstructor.
  - constructor; intros ? **; repeat (econstructor; eauto).
  - constructor; eapply H.
  - intros ? **; econstructor; intros ?**.
    + inv H. exploit H3; eauto.
      clear - H0; intros (?&?&?).
      eapply H0; eauto.
    + inv H0. exploit H4; eauto.
      clear - H; intros (?&?&?).
      eapply H; eauto.
Qed.

Definition benevolent_repeat (dm:delta_list):=
  (forall b1 fb1 fb2 p1 p2 ofs,
      In (b1,fb1) dm -> 
      In (b1,fb2) dm ->
      fb1 ofs = Some p1 ->
      fb2 ofs = Some p2 ->
      p1 = p2).
Lemma de_doubling_correct1:
  forall dm,
    benevolent_repeat dm ->
    equiv_one_side dm (de_doubling dm).
Proof.
  unfold equiv_one_side, benevolent_repeat.
  intros dm; remember (length dm) as n eqn:Hlen; revert dm Hlen.
  induction n.
  - intros. destruct dm; inv Hlen. inv H0.
  - intros. clear Hlen IHn.
    econstructor; split.
    + eapply de_doubling_sep1. replace b1 with (fst (b1, fb1)) by reflexivity.
      apply in_map; auto.
    + clear - H H0 H1. 
      induction dm; simpl. inv H0.
      destruct a; simpl in *. match_case; subst.
      * destruct H0.
        -- inv H0; unfold update_fn; rewrite H1; reflexivity.
        -- unfold update_fn; match_case.
           ++ f_equal. eapply H.
              left; eauto.
              right; eauto.
              all: eauto.
           ++ eapply IHdm; eauto.
      * destruct H0. inv H0; congruence.
        eapply IHdm; eauto.
Qed.

Lemma add_node_in_neq:
  forall l b b' fb fb',
    In (b, fb) (add_node_list (b',fb') l) ->
    b <> b' -> In (b, fb) l.
Proof.
  induction l.
  - intros; inv H; auto. inv H1; congruence.
  - intros. simpl in H. repeat match_case in H; subst; simpl.
    + right. inv H; eauto. inv H1; congruence.
    + simpl in *. inv H; eauto.
Qed.
Lemma add_node_in_eq:
  forall l b fb fb' fb3,
    In (b, fb) (add_node_list (b,fb') l) ->
    list_norepet (map fst l) ->
    In (b, fb3) l ->
    fb = update_fn fb' fb3.
Proof.
  induction l.
  - intros. simpl in H; inv H; try solve[exfalso; auto].
  - intros. inv H1.
    + simpl in *.
      match_case in H; subst.
      inv H.
      * inv H1; auto.
      * inv H0. exfalso; eapply H3.
        eapply in_map_fst.
        eauto.
    + eapply IHl; eauto.
      * inv H0. simpl in H.
        repeat match_case in H.
        -- subst. simpl in *. inv H.
           ++ exfalso; apply H4. eapply in_map_fst; eauto.
           ++ exfalso; apply H4. eapply in_map_fst; eauto.
        -- inv H. inv H0; congruence.
           apply H0.
      * inv H0; auto.
Qed.
Lemma de_doubling_correct2:
  forall dm,
    benevolent_repeat dm ->
    equiv_one_side (de_doubling dm) dm.
Proof.
  unfold equiv_one_side, benevolent_repeat.
  induction dm; intros. inv H0.
  simpl in H0.
  destruct a. simpl in *.
  destruct (peq b b1).
  - subst.
    destruct (in_dec peq b1 (map fst (de_doubling dm))).
    + eapply list_in_map_inv in i as ((?&?)&?&?); subst.
      simpl in *. exploit add_node_in_eq. eapply H0. all: eauto.
      * eapply de_doubling_norepeat_fst.
      * intros. subst. unfold update_fn in H1; match_case in H1.
        -- inv H1. repeat (econstructor; eauto).
        -- exploit IHdm; eauto. intros (F&?&?).
           repeat (econstructor; eauto).
    + rewrite update_node_list_notin in H0; eauto.
      apply in_app in H0; destruct H0.
      * exfalso; eapply n. replace b1 with (fst (b1,fb1)) by reflexivity.
        apply in_map; eauto.
      * inv H0; inv H2. repeat (econstructor; eauto).
  - eapply add_node_in_neq in H0; auto.
    exploit IHdm; eauto. intros (F&?&?).
    repeat (econstructor; eauto).
Qed.
Lemma de_doubling_correct:
  forall dm,
    benevolent_repeat dm ->
    equiv_delta dm (de_doubling dm).
Proof.
  intros; econstructor;
    [eapply de_doubling_correct1| eapply de_doubling_correct2]; eauto.
Qed.

Instance inject_delta_map_flat_proper:
  Proper (Logic.eq ==> equiv_delta ==> equiv_delta ==> iff) inject_delta_map_flat'.
Proof.
  intros ??? ??? ???; subst; split; intros HH.
  - econstructor; intros.
    + inv H0. exploit H4; eauto.
      clear - HH H1.
      intros (?&?&?).
      exploit DPM_image_flat'; eauto.
      intros (?&?&?&?&?&?). inv H1.
      exploit H5; eauto; intros (?&?&?).
      repeat (econstructor; eauto).
      
    + inv H1. exploit H4; eauto.
      clear - HH H0.
      intros (?&?&?).
      exploit DPM_preimage_flat'; eauto.
      intros (?&?&?&?&?&?&?&?). inv H0.
      exploit H6; eauto; intros (?&?&?).
      repeat (econstructor; eauto).
  - symmetry in H0; symmetry in H1.
    econstructor; intros.
    + inv H0. exploit H4; eauto.
      clear - HH H1.
      intros (?&?&?).
      exploit DPM_image_flat'; eauto.
      intros (?&?&?&?&?&?). inv H1.
      exploit H5; eauto; intros (?&?&?).
      repeat (econstructor; eauto).
      
    + inv H1. exploit H4; eauto.
      clear - HH H0.
      intros (?&?&?).
      exploit DPM_preimage_flat'; eauto.
      intros (?&?&?&?&?&?&?&?). inv H0.
      exploit H6; eauto; intros (?&?&?).
      repeat (econstructor; eauto).
Qed.
Lemma nonrepet_in_fst:
  forall {A B} l (a:A) (b b':B),
    list_norepet (map fst l) ->
    In (a, b) l ->
    In (a, b') l ->
    b = b'.
Proof.
  intros.
  eapply in_split in H0 as (?&?&?); subst.
  rewrite map_app in H.
  eapply list_norepet_app in H as (?&?&?).
  apply in_app in H1; inv H1.
  -  simpl in H2; exploit H2.
     + eapply in_map_fst; eauto.
     + econstructor; auto.
     + reflexivity.
     + intros HH; inv HH.
  - inv H0; eauto. inv H3; eauto. inv H0; auto.
    exfalso; apply H5. eapply in_map_fst; eauto.
Qed.
Lemma inject_delta_interpolation_flat:
  strong_interpolation inject_delta_map_flat inject_delta_map_flat.
Proof.
  intros dm1 dm3 **.
  exploit inject_delta_interpolation_flat'.
  { inv H; econstructor; eauto. }

  intros (dm2'&?&?).
  exists (de_doubling dm2').
  assert (benevolent_repeat dm2').
  { Lemma inject_benevolent:
      forall j dm1 dm2,
        inject_delta_map_flat' j dm1 dm2 ->
        list_norepet (map fst dm2) ->
        benevolent_repeat dm1.
    Proof.
      intros * H Hnr ? **.
      exploit DPM_image_flat'; eauto.
      clear H3 H1.
      exploit DPM_image_flat'; eauto.
      clear - Hnr.
      intros (?&?&?&?&?&?) (?&?&?&?&?&?).
      rewrite H in H2; inv H2.
      replace x1 with x4 in H1.
      - rewrite H1 in H4; inv H4; auto.
      - clear - H0 H3 Hnr.
        eapply nonrepet_in_fst; eauto.
    Qed.
    eapply inject_benevolent; eauto.
    apply H. }
  
  erewrite (de_doubling_correct dm2') in H0; auto.
  erewrite (de_doubling_correct dm2') in H1; auto.
  assert (list_norepet (map fst (de_doubling dm2'))) by apply de_doubling_norepeat_fst.

  inv H0; inv H1; split; econstructor; eauto.
  eapply H.
Qed.

Definition delta_map_equiv: relation delta_map:=
  fun dm1 dm2 => forall b, dm1 ! b = dm2 ! b.
Instance delta_map_equiv_Equivalence: Equivalence delta_map_equiv.
Proof.
  econstructor.
  - constructor.
  - intros ?? H; unfold delta_map_equiv; auto.
  - intros ??; unfold delta_map_equiv; auto.
    intros; etransitivity; eauto.
Qed.
(* Better using Proper, but don't want to import all the machinery *)
Lemma inject_delta_map_proper':
  forall dm1 dm1' dm2 dm2' f,
    delta_map_equiv dm1 dm1' ->
    delta_map_equiv dm2 dm2' ->
    inject_delta_map f dm1 dm2 ->
    inject_delta_map f dm1' dm2'.
Proof.
  intros * Heq1 Heq2 [Himg Hpre].
  econstructor; intros; unfold dmap_get, PMap.get in *; simpl in *.
  - exploit Himg. erewrite Heq1; eauto.
    intros (?&?&?&?).
    repeat (econstructor; eauto).
    rewrite <- Heq2; auto.
  - exploit Hpre. erewrite Heq2; eauto.
    intros (?&?&?&?&?&?).
    repeat (econstructor; eauto).
    rewrite <- Heq1; auto.
Qed.

Instance inject_delta_map_proper:
  Morphisms.Proper (Logic.eq ==> delta_map_equiv ==> delta_map_equiv ==> iff) inject_delta_map.
Proof.
  intros ??? ??? ???; subst.
  split; eapply inject_delta_map_proper'; eauto.
  all: unfold delta_map_equiv; eauto.
Qed.


Lemma flat_unflat_equiv:
  forall dm, delta_map_equiv dm (unflat_dm (flat_dm dm)).
Proof. unfold unflat_dm, flat_dm. intros ??.
       symmetry; eapply PTree_Properties.of_list_elements. Qed.

Lemma inject_delta_interpolation: strong_interpolation inject_delta_map inject_delta_map.
Proof.
  intros v1 **.
  eapply inject_delta_map_flaten in H.
  exploit inject_delta_interpolation_flat; eauto.
  intros (dm2&?&?). eexists (unflat_dm dm2); split.
  - erewrite flat_unflat_equiv.
    eapply inject_delta_map_unflaten; eauto.
    + eapply PTree.elements_keys_norepet.
    + eapply H0.
  - erewrite (flat_unflat_equiv v3).
    eapply inject_delta_map_unflaten; eauto.
    + eapply H0.
    + eapply PTree.elements_keys_norepet.
Qed.
Hint Resolve inject_delta_interpolation: str_interp.



(** *Determinism in relations *)
Definition deterministic {A B} (R: A -> B -> Prop):=
  forall a b b', R a b -> R a b' -> b = b'.
Lemma determ_cut:
  forall A B R, @deterministic A B R -> deterministic R. Proof. eauto. Qed.
Lemma  Forall2_determ:
  forall {A B} (R: A -> B -> Prop),
    deterministic R ->
    deterministic (Forall2 R).
Proof.
  unfold deterministic;
    intros. revert b' H1.
  induction H0; intros.
  - inv H1; auto.
  - inv H2; f_equal.
    + eapply H; eassumption.
    + eapply IHForall2; assumption.
Qed.
Create HintDb determ. Hint Resolve Forall2_determ: determ.

Ltac different_results:=
  match goal with
    [H: ?a = _, H0: ?a = _ |- _]=>
    rewrite H in H0; inv H0
  end.
Ltac determ_hyp:=
  match goal with
    [H: ?R ?a ?b, H0: ?R ?a ?b' |- _] =>
    replace b with b' in * by (eapply determ_cut; eauto with determ);
    auto; clear H0
  end.
Ltac solve_determ:=
  match goal with
    [|- forall j,  deterministic ?R ] =>
    let H:= fresh in let H0:=fresh in
                     eauto with determ;
                     intros ?? * H H0; inv H; inv H0;
                     repeat different_results;
                     repeat determ_hyp;
                     eauto
  end.
Lemma inject_delta_map_determ:
  forall (f12 : meminj), deterministic (inject_delta_map f12).  
Proof. solve_determ.
Admitted.
Hint Resolve inject_delta_map_determ: determ.



(** *Some trivial hints added to the database. *)
Hint Immediate inject_incr_refl.
