From mathcomp.ssreflect Require Import ssreflect seq ssrbool
        ssrnat ssrfun eqtype seq fintype finfun.

Set Implicit Arguments.
Require Import VST.msl.Coqlib2.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permjoin_def.
Require Import compcert.common.Memory.
Require Import compcert.common.Values. (*for val*)
Require Import compcert.lib.Integers.
Require Export compcert.lib.Maps.
Require Import Coq.ZArith.ZArith.
From VST.veric Require Import shares juicy_mem juicy_mem_lemmas.
Require Import VST.msl.msl_standard.
Require Import FunInd.
Import cjoins.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

Lemma po_refl: forall p, Mem.perm_order'' p p.
Proof.
  destruct p; [apply perm_refl| simpl]; auto.
Qed.

Lemma perm_order_antisym :
  forall p p'
    (Hlt: Mem.perm_order'' p p')
    (Hgt: Mem.perm_order'' p' p),
    p = p'.
Proof.
  intros.
  unfold Mem.perm_order'' in *.
  destruct p as [p|], p' as [p'|];
    try destruct p; try destruct p';
    auto;
    try (by inversion Hgt); try (by inversion Hlt).
Qed.

Definition access_map := Maps.PMap.t (Z -> option permission).
Definition delta_map := Maps.PTree.t (Z -> option (option permission)).

Section permMapDefs.

  Definition empty_map : access_map :=
    (fun z => None, Maps.PTree.empty (Z -> option permission)).

  Lemma empty_map_spec: forall b ofs,
      Maps.PMap.get b empty_map ofs = None.
        intros. unfold empty_map, Maps.PMap.get.
        rewrite Maps.PTree.gempty; reflexivity.
  Qed.

  Definition permission_at (m : mem) (b : block) (ofs : Z) (k : perm_kind) :=
    Maps.PMap.get b (Mem.mem_access m) ofs k.

  (** Coherence between permissions. This is used for the relation between data
  and lock permissions*)
  (** Note: p1 should be data permission and p2 lock permission*)
  Definition perm_coh (p1 p2 : option permission) :=
    match p1 with
    | Some Freeable | Some Writable | Some Readable =>
                                      match p2 with
                                      | None => True
                                      | _ => False
                                      end
    | Some Nonempty | None =>
                      match p2 with
                      | Some Freeable => False
                      | _ => True
                      end
    end.

  Lemma perm_coh_lower:
    forall p1 p2 p3 p4
      (Hpu: perm_coh p1 p2)
      (Hperm2: Mem.perm_order'' p2 p4)
      (Hperm1: Mem.perm_order'' p1 p3),
      perm_coh p3 p4.
  Proof.
    intros.
    destruct p2 as [p|];
      try (destruct p); simpl in Hperm2;
      destruct p4 as [p|];
      try (destruct p); inversion Hperm2; subst;
      destruct p1 as [p|];
      try (destruct p); simpl in Hpu, Hperm1; try (now exfalso);
      destruct p3; try inversion Hperm1; subst; simpl; auto.
    destruct p; auto.
  Qed.

  Lemma perm_coh_not_freeable:
    forall p p',
      perm_coh p p' ->
      p' <> Some Freeable.
  Proof.
    intros.
    destruct p as [p|];
      try (destruct p); simpl in H;
      destruct p'; try (by exfalso);
      intro Hcontra; try discriminate.
    inversion Hcontra; subst; auto.
    inversion Hcontra; subst; auto.
  Qed.

  Lemma perm_coh_empty_1:
    forall p,
      perm_coh p None.
  Proof.
    intros.
    destruct p as [p|];
      try (destruct p); simpl;
      auto.
  Qed.

  Lemma perm_coh_empty_2:
    forall p : option permission,
      Mem.perm_order'' (Some Writable) p ->
      perm_coh None p.
  Proof.
    intros p H.
    destruct p; try destruct p; try solve[inversion H];
    constructor.
  Qed.

  Lemma perm_of_glb_not_Freeable: forall sh,
      ~ perm_of_sh (Share.glb Share.Rsh sh) = Some Freeable.
  Proof.
    intros ??%perm_of_sh_Freeable_top%glb_Rsh_not_top; auto.
  Qed.

  Lemma perm_coh_self: forall res,
      perm_coh (perm_of_res res)
               (perm_of_res_lock res).
        destruct res; simpl; auto.
        - apply perm_coh_empty_1.
        - destruct k; try apply perm_coh_empty_1; simpl.
            destruct (perm_of_sh (Share.glb Share.Rsh sh)) eqn: ?; auto.
            destruct p0; auto.
            eapply perm_of_glb_not_Freeable; eauto.
  Qed.


  Lemma perm_coh_joins:
    forall a b, joins a b ->
           perm_coh (perm_of_res a) (perm_of_res_lock b).
  Proof.
    intros a b H.
    destruct H as [c H].
    inversion H; subst; simpl.
    - apply perm_coh_empty_1.
    - apply perm_coh_empty_1.
    - destruct k; try apply perm_coh_empty_1.
      + destruct (perm_of_sh (Share.glb Share.Rsh sh2)) eqn:AA;
        destruct (eq_dec sh1 Share.bot) eqn:BB;
        try destruct p0;
        try constructor.
        * apply perm_of_sh_Freeable_top in AA; inversion AA; subst.
          exfalso; eapply glb_Rsh_not_top; eauto.
        * apply perm_of_sh_Freeable_top in AA; inversion AA; subst.
          exfalso; eapply glb_Rsh_not_top; eauto.
    - destruct k; try apply perm_coh_empty_1.
      + destruct (perm_of_sh (Share.glb Share.Rsh sh2)) eqn:AA;
        destruct (eq_dec sh1 Share.bot) eqn:BB;
        try destruct p0;
        try constructor.
        * apply perm_of_sh_Freeable_top in AA; inversion AA; subst.
          exfalso; eapply glb_Rsh_not_top; eauto.
        * apply perm_of_sh_Freeable_top in AA; inversion AA; subst.
          exfalso; eapply glb_Rsh_not_top; eauto.
    - constructor.
  Qed.

  
  Lemma po_join_sub_lock:
  forall r1 r2 ,
    join_sub r2 r1 ->
    Mem.perm_order'' (perm_of_res_lock r1) (perm_of_res_lock r2).
  Proof.
  intros.
  destruct H as [x H].
  inversion H; subst; simpl; try constructor.
  - destruct k; simpl; auto;
      apply juicy_mem_lemmas.po_join_sub_sh; eexists;
        eapply compcert_rmaps.join_glb_Rsh; eassumption.
  - apply event_semantics.po_None.
    
  - destruct k; simpl; auto;
      apply juicy_mem_lemmas.po_join_sub_sh; eexists;
        eapply compcert_rmaps.join_glb_Rsh; eassumption.
    
Qed.


  Definition permMapCoherence (pmap1 pmap2 : access_map) :=
    forall b ofs, perm_coh (pmap1 !! b ofs) (pmap2 !! b ofs).

  Lemma permCoh_empty: forall r,
      (forall b ofs, Mem.perm_order'' (Some Writable) (r !! b ofs)) ->
      permMapCoherence empty_map r.
        intros r H b ofs.
        rewrite empty_map_spec.
        specialize (H b ofs).
        apply perm_coh_empty_2; assumption.
  Qed.

  Lemma permCoh_empty': forall x,
      permMapCoherence x empty_map.
  Proof.
    intros x b ofs.
    rewrite empty_map_spec.
    apply perm_coh_empty_1.
  Qed.

  Lemma perm_of_res_lock_not_Freeable:
    forall r,
      Mem.perm_order'' (Some Writable) (perm_of_res_lock r).
  Proof.
    destruct r; try constructor; destruct k ; simpl; auto.
    - destruct (perm_of_sh (Share.glb Share.Rsh sh)) eqn:HH; auto.
      destruct p0; try constructor.
      apply perm_of_sh_Freeable_top in HH; inversion HH.
          exfalso; eapply glb_Rsh_not_top; eauto.
  Qed.

  (* Some None represents the empty permission. None is used for
  permissions that conflict/race. *)

  Definition perm_union (p1 p2 : option permission) : option (option permission) :=
    match p1,p2 with
      | None, _ => Some p2
      | _, None => Some p1
      | Some p1', Some p2' =>
        match p1', p2' with
          | Freeable, _ => None
          | _, Freeable => None
          | Nonempty, _ => Some p2
          | _, Nonempty => Some p1
          | Writable, _ => None
          | _, Writable => None
          | Readable, Readable => Some (Some Readable)
        end
    end.

  Lemma perm_union_comm :
    forall p1 p2,
      perm_union p1 p2 = perm_union p2 p1.
  Proof.
    intros. destruct p1 as [p1|];
      destruct p2 as [p2|];
    try destruct p1, p2; simpl in *; reflexivity.
  Defined.

  Lemma perm_union_result : forall p1 p2 pu (Hunion: perm_union p1 p2 = Some pu),
                              pu = p1 \/ pu = p2.
  Proof.
    intros. destruct p1 as [p1|]; destruct p2 as [p2|];
            try destruct p1, p2; simpl in Hunion; try discriminate;
            try inversion Hunion; subst; auto.
  Defined.

  Lemma perm_union_ord : forall p1 p2 pu (Hunion: perm_union p1 p2 = Some pu),
                           Mem.perm_order'' pu p1 /\ Mem.perm_order'' pu p2.
  Proof.
    intros. destruct p1 as [p1|]; destruct p2 as [p2|];
            try destruct p1, p2; simpl in Hunion; try discriminate;
            try inversion Hunion; subst; unfold Mem.perm_order''; split; constructor.
  Defined.

  Lemma perm_union_lower:
    forall p1 p2 p3
      (Hpu: exists pu, perm_union p1 p2 = Some pu)
      (Hperm: Mem.perm_order'' p2 p3),
    exists pu, perm_union p1 p3 = Some pu.
  Proof.
    intros.
    destruct p2 as [p|].
    destruct p; simpl in Hperm;
    destruct Hpu as [pu Hpu];
    destruct p1 as [p|]; try destruct p; simpl in Hpu;
    try congruence;
    destruct p3; inversion Hperm; simpl; eexists; eauto.
    simpl in Hperm.
    destruct p3; simpl in *; tauto.
  Qed.

  Lemma perm_union_lower_2:
    forall p1 p2 p3 p4
      (Hpu: exists pu, perm_union p1 p2 = Some pu)
      (Hperm: Mem.perm_order'' p1 p3)
      (Hperm': Mem.perm_order'' p2 p4),
    exists pu, perm_union p3 p4 = Some pu.
  Proof.
    intros.
    destruct p2 as [p2|]; simpl in Hperm;
      destruct p4 as [p4|];
      destruct p1 as [p1 |];
      destruct p3 as [p3|];
      try (destruct p1);
      simpl in *; inversion Hperm; subst;
        destruct Hpu; try (discriminate);
          try (destruct p2; inversion Hperm'; subst);
          try (discriminate); try (by exfalso);
            eexists; eauto.
  Qed.


  Inductive not_racy : option permission -> Prop :=
  | empty : not_racy None.

  Inductive racy : option permission -> Prop :=
  | freeable : racy (Some Freeable).

  Lemma not_racy_union :
    forall p1 p2 (Hnot_racy: not_racy p1),
    exists pu, perm_union p1 p2 = Some pu.
  Proof. intros. destruct p2 as [o |]; [destruct o|]; inversion Hnot_racy; subst;
                 simpl; eexists; reflexivity.
  Qed.

  Lemma no_race_racy : forall p1 p2 (Hracy: racy p1)
                              (Hnorace: exists pu, perm_union p1 p2 = Some pu),
                         not_racy p2.
  Proof.
    intros.
    destruct p2 as [o|]; [destruct o|];
    inversion Hracy; subst;
    simpl in *; inversion Hnorace;
    (discriminate || constructor).
  Qed.

  Lemma perm_order_clash:
    forall p p'
      (Hreadable: Mem.perm_order' p Readable)
      (Hwritable: Mem.perm_order' p' Writable),
      ~ exists pu, perm_union p p' = Some pu.
  Proof.
    intros. intro Hcontra.
    destruct p as [p0|], p' as [p0'|];
      try destruct p0;
      try destruct p0';
      simpl in *;
      destruct Hcontra as [pu H];
      try inversion H;
      try (by inversion Hwritable);
      try (by inversion Hreadable).
  Qed.

  Lemma perm_order_incompatible:
    forall p p'
      (Hreadable: Mem.perm_order'' p (Some Readable))
      (Hwritable: Mem.perm_order'' p' (Some Writable)),
      perm_union p p' = None.
  Proof.
    intros.
    destruct p as [p0|], p' as [p0'|];
      try destruct p0;
      try destruct p0';
      simpl in *; try (reflexivity);
      try (by inversion Hwritable);
      try (by inversion Hreadable).
  Qed.

  Definition perm_max (p1 p2 : option permission) : option permission :=
    match p1,p2 with
      | Some Freeable, _ => p1
      | _, Some Freeable => p2
      | Some Writable, _ => p1
      | _, Some Writable => p2
      | Some Readable, _ => p1
      | _, Some Readable => p2
      | Some Nonempty, _ => p1
      | _, Some Nonempty => p2
      | None, None => None
    end.

  Lemma perm_max_comm :
    forall p1 p2,
      perm_max p1 p2 = perm_max p2 p1.
  Proof.
    intros. destruct p1 as [p1|];
      destruct p2 as [p2|];
    try destruct p1, p2; simpl in *; reflexivity.
  Defined.

  Lemma perm_max_result : forall p1 p2 pu (Hmax: perm_max p1 p2 = pu),
                            pu = p1 \/ pu = p2.
  Proof.
    intros. destruct p1 as [p1|]; destruct p2 as [p2|];
            try destruct p1, p2; simpl in Hmax; try rewrite Hmax; auto.
    destruct p1; auto. destruct p2; auto.
  Defined.

  Lemma perm_max_ord : forall p1 p2 pu (Hmax: perm_max p1 p2 = pu),
                           Mem.perm_order'' pu p1 /\ Mem.perm_order'' pu p2.
  Proof.
    intros. destruct p1 as [p1|]; destruct p2 as [p2|];
            try destruct p1; try destruct p2; simpl in Hmax;
            try discriminate; subst; unfold Mem.perm_order'';
    split; constructor.
  Defined.

  Definition getMaxPerm (m : mem) : access_map :=
    Maps.PMap.map (fun f => fun ofs => f ofs Max) (Mem.mem_access m).

  Definition getCurPerm (m : mem) : access_map :=
    Maps.PMap.map (fun f => fun ofs => f ofs Cur) (Mem.mem_access m).

  Definition getPermMap (m : mem) : Maps.PMap.t (Z -> perm_kind -> option permission) :=
    Mem.mem_access m.

  Lemma getCur_Max : forall m b ofs,
                       Mem.perm_order'' (Maps.PMap.get b (getMaxPerm m) ofs)
                                        (Maps.PMap.get b  (getCurPerm m) ofs).
  Proof.
    intros.
    assert (Hlt:= Mem.access_max m b ofs).
    unfold Mem.perm_order'' in *.
    unfold getMaxPerm, getCurPerm.
    do 2 rewrite Maps.PMap.gmap.
    auto.
  Qed.

  Lemma getMaxPerm_correct :
    forall m b ofs,
      Maps.PMap.get b (getMaxPerm m) ofs = permission_at m b ofs Max.
  Proof.
    intros. unfold getMaxPerm. by rewrite Maps.PMap.gmap.
  Qed.

  Lemma getCurPerm_correct :
    forall m b ofs,
      Maps.PMap.get b (getCurPerm m) ofs = permission_at m b ofs Cur.
  Proof.
    intros. unfold getCurPerm. by rewrite Maps.PMap.gmap.
  Qed.


  Definition permDisjoint p1 p2:=
    exists pu : option permission,
      perm_union p1 p2 = Some pu.

   Lemma permDisjoint_None: forall p,
      permDisjoint None p.
  Proof. intros p. exists p; reflexivity. Qed.

  Lemma permDisjoint_comm: forall p1 p2,
      permDisjoint p1 p2 -> permDisjoint p2 p1.
  Proof. intros p1 p2.
         unfold permDisjoint, perm_union.
         destruct p1 as [p3|]; destruct p2 as [p4|];
         try destruct p3, p4; intros [k H]; exists k; inversion H;
         reflexivity.
  Qed.

  Lemma permDisjointLT: forall a b c,
      permDisjoint a c ->
      Mem.perm_order'' a b ->
      permDisjoint b c.
        intros a b c H1 H2.
        destruct a, b; try solve[inversion H2];
        try solve[exists c; reflexivity].
        simpl in H2.
        destruct H1 as [k H1].
        inversion H2; subst.
        - exists k; assumption.
        - destruct c; inversion H1.
          exists (Some p0); reflexivity.
        - destruct c; inversion H1.
          destruct p; inversion H0.
          exists (Some Readable); reflexivity.
        - exists (Some Readable); reflexivity.
        - destruct c; inversion H1;
          try solve[exists (Some Nonempty); reflexivity].
          destruct p; inversion H0; try(destruct p0; inversion H3);
          try solve[exists (Some Nonempty); reflexivity];
          try solve[exists (Some Readable); reflexivity];
          try solve[exists (Some Writable); reflexivity].
  Qed.

  (* Lemma join_sh_permDisjoint: forall rsh1 rsh2 rsh3 (sh1 sh2 sh3: pshare),
      join rsh1 rsh2 rsh3 ->
      join sh1 sh2 sh3 ->
      permDisjoint (perm_of_sh (Share.glb Share.Rsh sh1))) (perm_of_sh (Share.glb Share.Rsh sh1))).
  Proof.
    intros rsh1 rsh2 rsh3 sh1 sh2 sh3.
    intros H1.
    intros H2.
    move: (perm_of_sh_pshare rsh1 sh1) (perm_of_sh_pshare rsh2 sh2) =>
    [] p1 HH1 [] p2 HH2.
    rewrite HH1 HH2 /permDisjoint /=.
    destruct p1.
    - apply perm_of_sh_Freeable_top in HH1; inversion HH1; subst.
      destruct sh1.
      unfold join, Join_pshare, Join_lift in H2.
      simpl in H2.
      simpl in H3; subst x.
      apply pshare_join_full_false4 in H2.
      exfalso; assumption.
    - move: HH1.
      unfold perm_of_sh.
      repeat if_tac; try solve[intros HH; inversion HH].
      destruct sh1.
      unfold join, Join_pshare, Join_lift in H2.
      simpl in H2.
      simpl in H; subst x.
      apply pshare_join_full_false4 in H2.
      exfalso; assumption.
    - move: HH1.
      unfold perm_of_sh.
      repeat if_tac; try solve[intros HH; inversion HH].
      destruct p2; try solve[eexists; reflexivity].
      + apply perm_of_sh_Freeable_top in HH2; inversion HH2; subst.
        destruct sh2.
        unfold join, Join_pshare, Join_lift in H2.
        simpl in H2.
        simpl in H5; subst x.
        apply pshare_join_full_false3 in H2.
        exfalso; assumption.
      + move: HH2.
        unfold perm_of_sh.
        repeat if_tac; try solve[intros HH; inversion HH].
        destruct sh2.
        unfold join, Join_pshare, Join_lift in H2.
        simpl in H2.
        simpl in H3; subst x.
        apply pshare_join_full_false3 in H2.
        exfalso; assumption.
    - destruct p2; try solve[eexists; reflexivity].
      apply perm_of_sh_Freeable_top in HH2; inversion HH2; subst.
      destruct sh2.
      unfold join, Join_pshare, Join_lift in H2.
      simpl in H2.
      simpl in H3; subst x.
      apply pshare_join_full_false3 in H2.
      exfalso; assumption.
  Qed.
   *)
  (*The new version of the above*)
  Ltac if_simpl:=
    repeat match goal with
           | [ H: ?X = true |- context[if ?X then _ else _] ] => rewrite H; simpl 
           | [ H: ?X = false |- context[if ?X then _ else _] ] => rewrite H; simpl 
           | [ H: ?X = left _ |- context[match ?X with left _ => _ | right _ => _ end] ]=>
             rewrite H; simpl 
           | [ H: ?X = right _ |- context[match ?X with left _ => _ | right _ => _ end] ]=>
             rewrite H; simpl 
           | [ H: (@is_left _ _ ?X) = true |-
               context [match ?X with left _ => _ | right _ => _ end ]] => destruct X; inversion H
           | [ H: (@is_left _ _ ?X) = false |-
               context [match ?X with left _ => _ | right _ => _ end ]] => destruct X; inversion H
           end.

  Ltac permDisj_solve:= eexists; simpl; reflexivity.
  
  Lemma join_sh_permDisjoint:
        forall sh1 sh2,
          joins sh1 sh2 ->
          permDisjoint (perm_of_sh sh1) (perm_of_sh sh2).
  
    Ltac joins_sh_contradiction_onside:=
      match goal with
      | [ H: joins ?sh1 ?sh2,
             W1: writable_share ?sh1,
                 W2: writable_share ?sh2 |- _ ] =>
        exfalso; eapply writable_not_join_writable; eassumption
      | [ H: joins ?sh1 ?sh2,
             W1: writable_share ?sh1,
                 W2: readable_share ?sh2 |- _ ] =>
        exfalso; eapply writable_not_join_readable; eassumption
      | [ H: joins Share.top ?sh2,
             H0: ?sh2 <> Share.bot |- _ ] =>
        exfalso; eapply H0; eapply only_bot_joins_top; eassumption
      end.
    Ltac joins_sh_contradiction:=
      first[ joins_sh_contradiction_onside |
             match goal with
             | [ H: joins ?sh1 ?sh2 |- _ ] =>
               eapply joins_comm in H
             end; joins_sh_contradiction_onside].
  Proof.
    (*intros.
        unfold perm_of_sh.
        destruct (writable_share_dec sh1).
          
        - pose proof (writable_not_join_writable H w).
          pose proof (writable_not_join_readable H w).
          destruct (writable_share_dec sh2); try contradiction.
          destruct (readable_share_dec sh2); try contradiction.
          destruct (eq_dec sh1 Share.top).
          + subst. apply only_bot_joins_top in H; subst.
            destruct (eq_dec Share.bot Share.bot); try contradiction.
            eexists; reflexivity.
          + destruct (eq_dec sh2 Share.bot); eexists; reflexivity.
        - destruct (readable_share_dec sh1).
          pose proof (readable_not_join_writable H r). 
          pose proof (readable_not_join_readable H r). 
          destruct ( writable_share_dec sh2); try contradiction.
          destruct (readable_share_dec sh2); try contradiction.
          destruct (eq_dec sh2 Share.bot); eexists; reflexivity.*)
    intros.

    functional induction (perm_of_sh sh1) using perm_of_sh_ind;
      functional induction (perm_of_sh sh2) using perm_of_sh_ind;
      try permDisj_solve;
      joins_sh_contradiction.
    Qed.
 
  (*HERE*)
  Lemma joins_permDisjoint: forall r1 r2,
      joins r1 r2 ->
      permDisjoint (perm_of_res r1) (perm_of_res r2).
  Proof.
(*
    intros.
    destruct H as [X H]; inversion H; simpl;
      try permDisj_solve.
    - destruct (eq_dec sh1 Share.bot); destruct (eq_dec sh2 Share.bot);
      try permDisj_solve.
    - destruct k; destruct (eq_dec sh2 Share.bot); try solve[eexists; reflexivity].
      + eapply permDisjoint_comm. apply permDisjoint_None.
      + subst; unfold perm_of_sh.
        destruct (writable_share_dec sh1).
          destruct (eq_dec sh1 Share.top); simpl;
            try permDisj_solve.
        * inversion RJ; subst.
          rewrite Share.glb_commute in H0.
          rewrite Share.glb_top in H0; contradiction.
        * destruct (readable_share_dec sh1); try contradiction.
          permDisj_solve.
    - unfold permDisjoint.
      destruct k; destruct (eq_dec sh1 Share.bot); try permDisj_solve.
      subst; unfold perm_of_sh.
      destruct (writable_share_dec sh2).
      * destruct (eq_dec sh2 Share.top);
          try permDisj_solve.
        subst; inversion RJ.
        rewrite Share.glb_top in H0; contradiction.
      * destruct (readable_share_dec sh2);
          try permDisj_solve.
        destruct (eq_dec sh2 Share.bot); 
          try permDisj_solve.
    - destruct k; try permDisj_solve.

      Restart.

      (*Explicit consturction of cases and induction*)

      Inductive perm_of_res_cases (r : compcert_rmaps.RML.R.resource):=
        | NO_bot: forall sh Psh, r = compcert_rmaps.RML.R.NO sh Psh ->
                  is_left (eq_dec sh Share.bot) = true ->
                  perm_of_res_cases r
        | NO_nbot: forall sh Psh, r = compcert_rmaps.RML.R.NO sh Psh ->
                   is_left (eq_dec sh Share.bot) = false ->
                  perm_of_res_cases r
        | YES_VAL_Freeable: forall sh Psh k Pk v, r = compcert_rmaps.RML.R.YES sh Psh k Pk ->
                   k = compcert_rmaps.VAL v ->
                    is_left (writable_share_dec sh) = true ->
                    is_left (eq_dec sh Share.top) = true ->
                   perm_of_res_cases r
        | YES_VAL_Writable: forall sh Psh k Pk v, r = compcert_rmaps.RML.R.YES sh Psh k Pk ->
                   k = compcert_rmaps.VAL v ->
                    is_left (writable_share_dec sh) = true ->
                    is_left (eq_dec sh Share.top) = false ->
                   perm_of_res_cases r
        | YES_VAL_Readable: forall sh Psh k Pk v, r = compcert_rmaps.RML.R.YES sh Psh k Pk ->
                   k = compcert_rmaps.VAL v ->
                    is_left (writable_share_dec sh) = false ->
                    is_left (readable_share_dec sh)  = true ->
                   perm_of_res_cases r
        | YES_LK: forall sh Psh k Pk v, r = compcert_rmaps.RML.R.YES sh Psh k Pk ->
                   k = compcert_rmaps.LK v ->
                   perm_of_res_cases r
        | YES_CT: forall sh Psh k Pk v, r = compcert_rmaps.RML.R.YES sh Psh k Pk ->
                   k = compcert_rmaps.CT v ->
                   perm_of_res_cases r
        | YES_FUN: forall sh Psh k Pk x1 x2, r = compcert_rmaps.RML.R.YES sh Psh k Pk ->
                   k = compcert_rmaps.FUN x1 x2 ->
                   perm_of_res_cases r
        | IS_PURE: forall P Q, r = compcert_rmaps.RML.R.PURE P Q ->
                          perm_of_res_cases r.
      (* Print perm_of_res_cases_ind. *)

      Restart.
      
      intros.
      (* Print perm_of_res_ind.*)
      Functional Scheme perm_of_res_ind := Induction for perm_of_res Sort Prop.
      Functional Scheme perm_of_sh_ind := Induction for perm_of_sh Sort Prop.

      functional induction (perm_of_res r1) using perm_of_res_ind; simpl; subst;
        unfold perm_of_sh; if_simpl; subst;
      functional induction (perm_of_res r2) using perm_of_res_ind; simpl; subst;
        unfold perm_of_sh; if_simpl; subst;
          try permDisj_solve.
      
      functional induction (perm_of_sh sh0) using perm_of_sh_ind; simpl; subst;
        unfold perm_of_sh; if_simpl; subst;
          try permDisj_solve.

      Restart.
      *)

      intros.
      
       Ltac join_sh_contradiction:=
        match goal with
        | [ H: @join Share.t _ _ _ _ |- _ ] => apply join_joins in H
        end;
      joins_sh_contradiction.
      functional induction (perm_of_res_explicit r1) using perm_of_res_expl_ind;
        simpl;subst;
        unfold perm_of_sh; if_simpl; subst;
          functional induction (perm_of_res_explicit r2) using perm_of_res_expl_ind;
          simpl; subst;
        unfold perm_of_sh; if_simpl; subst;
          try permDisj_solve;
          inversion H; inversion H0; subst;
      try join_sh_contradiction.
      
  Qed.                                    
  
  
  
  Ltac glb_contradictions:=
    repeat match goal with
           | [ H: writable_share_dec _ = _ |- _ ] => clear H
           end;
    match goal with
    | [ H:  Share.glb Share.Rsh ?sh = Share.top  |- _ ] =>
      exfalso; eapply glb_Rsh_not_top; eassumption
    | [ H: writable_share (Share.glb Share.Rsh ?sh) |- _ ] =>
      eapply writable_right in H
    end; join_sh_contradiction.
  
  Lemma joins_permDisjoint_lock: forall r1 r2,
      joins r1 r2 ->
      permDisjoint (perm_of_res_lock r1) (perm_of_res_lock r2).
  Proof.
    intros.
    
    functional induction (perm_of_res_lock_explicit r1) using perm_of_res_lock_expl_ind;
      simpl; subst;
        unfold perm_of_sh; if_simpl; subst;
    functional induction (perm_of_res_lock_explicit r2) using perm_of_res_lock_expl_ind;
          simpl; subst;
            unfold perm_of_sh; if_simpl; subst;
              try permDisj_solve;
          inversion H; inversion H0; subst;
            try glb_contradictions.
  Qed.
  
  (*Lemma permDisjoint_sub: forall r1 r2 p,
      join_sub r2 r1 ->
      permDisjoint (perm_of_res r1) p ->
      permDisjoint (perm_of_res r2) p.
  Proof.*)

  (*Lemma join_permDisjoint: forall r1 r2 r3 p,
      join r1 r2 r3 ->
      permDisjoint (perm_of_res r1) p ->
      permDisjoint (perm_of_res r2) p ->
      permDisjoint (perm_of_res r3) p.
Proof.*)

  Definition permMapsDisjoint (pmap1 pmap2 : access_map) : Prop :=
    forall b ofs, exists pu,
      perm_union ((Maps.PMap.get b pmap1) ofs)
                 ((Maps.PMap.get b pmap2) ofs) = Some pu.

  Definition permMapsDisjoint2 (pmap pmap': access_map * access_map) :=
    permMapsDisjoint pmap.1 pmap'.1 /\
    permMapsDisjoint pmap.2 pmap'.2.

  Lemma permDisjoint_permMapsDisjoint: forall r1 r2,
      (forall b ofs, permDisjoint (r1 !! b ofs) (r2 !! b ofs))->
      permMapsDisjoint r1 r2.
        intros. intros b ofs. apply H.
  Qed.

  Lemma permMapsDisjoint_permDisjoint: forall r1 r2 b ofs,
      permMapsDisjoint r1 r2 ->
      permDisjoint (r1 !! b ofs) (r2 !! b ofs).
        intros. destruct  (H b ofs) as [k H'].
        exists k; assumption.
  Qed.

  Lemma empty_disjoint':
    forall pmap,
      permMapsDisjoint empty_map pmap.
        intros pmap b ofs. exists (pmap !! b ofs). rewrite empty_map_spec; reflexivity.
  Qed.
  Lemma empty_disjoint:
    permMapsDisjoint empty_map
                     empty_map.
      unfold permMapsDisjoint.
      unfold empty_map; intros; simpl.
      unfold Maps.PMap.get; simpl.
      rewrite Maps.PTree.gempty; simpl.
      exists None; reflexivity.
  Qed.

  Lemma permMapsDisjoint_comm :
    forall pmap1 pmap2
      (Hdis: permMapsDisjoint pmap1 pmap2),
      permMapsDisjoint pmap2 pmap1.
  Proof.
    unfold permMapsDisjoint in *.
    intros. destruct (Hdis b ofs) as [pu Hpunion].
    rewrite perm_union_comm in Hpunion.
    eexists; eauto.
  Qed.

  Lemma permMapsDisjoint2_comm:
    forall pmaps pmaps',
      permMapsDisjoint2 pmaps pmaps' <-> permMapsDisjoint2 pmaps' pmaps.
  Proof.
    intros.
    split; intros (? & ?); split;
      eauto using permMapsDisjoint_comm.
  Qed.

  Lemma disjoint_norace:
    forall (mi mj : mem) (b : block) (ofs : Z)
      (Hdisjoint: permMapsDisjoint (getCurPerm mi) (getCurPerm mj))
      (Hpermj: Mem.perm mj b ofs Cur Readable)
      (Hpermi: Mem.perm mi b ofs Cur Writable),
      False.
  Proof.
    intros.
    unfold Mem.perm, Mem.perm_order' in *.
    unfold permMapsDisjoint, getCurPerm in Hdisjoint. simpl in Hdisjoint.
    destruct (Hdisjoint b ofs) as [pu Hunion].
    clear Hdisjoint.
    do 2 rewrite Maps.PMap.gmap in Hunion.
    destruct (Maps.PMap.get b (Mem.mem_access mj) ofs Cur) as [pj|] eqn:Hpj;
      auto.
    destruct (Maps.PMap.get b (Mem.mem_access mi) ofs Cur) as [pi|] eqn:Hpi;
      auto.
    inversion Hpermi; inversion Hpermj; subst; simpl in Hunion;
    discriminate.
  Qed.

  Definition isCanonical (pmap : access_map) := pmap.1 = fun _ => None.
  Import Maps.
  Definition TreeMaxIndex {A} (t:Maps.PTree.t A): positive:=
    compcert.lib.Coqlib.list_fold_left (fun a => [eta Pos.max a.1]) 1%positive (Maps.PTree.elements t) .
  Lemma fold_max_monoton: forall  {A} (ls: seq.seq (positive * A)), forall i,
        (Coqlib.list_fold_left (fun a => [eta Pos.max a.1]) i ls >= i)%positive.
  Proof.
    induction ls.
    - simpl. intros; apply Pos.le_ge; apply Pos.le_refl.
    - intros. simpl.
      destruct (Pos.max_spec a.1 i) as [LT | GE].
      + destruct LT as [LT MAX]; rewrite MAX.
        apply IHls.
      + destruct GE as [GE MAX]; rewrite MAX.
        apply Pos.le_ge. apply (Pos.le_trans _ a.1); try assumption.
        apply Pos.ge_le; apply IHls.
  Qed.
  Lemma fold_max_monoton': forall  {A} (ls: seq.seq (positive * A)), forall i j,
        (i >= j)%positive ->
        (compcert.lib.Coqlib.list_fold_left (fun a => [eta Pos.max a.1]) i ls >=
         compcert.lib.Coqlib.list_fold_left (fun a => [eta Pos.max a.1]) j ls)%positive.
  Proof.
    induction ls.
    - auto.
    - intros. simpl.
      destruct (Pos.max_spec a.1 i) as [LTi | GEi];
      destruct (Pos.max_spec a.1 j) as [LTj | GEj];
      try destruct LTi as [LTi MAXi]; try destruct LTj as [LTj MAXj];
      try destruct GEi as [GEi MAXi]; try destruct GEj as [GEj MAXj];
      try rewrite MAXi; try rewrite MAXj; simpl.
      + apply IHls; assumption.
      + apply IHls. apply Pos.le_ge. apply Pos.lt_le_incl; assumption.
      + pose (contra:= Pos.le_lt_trans  _ _ _ GEi LTj).
        apply Pos.ge_le in H. apply Pos.le_nlt in H. contradict H; assumption.
      + apply Pos.le_ge. apply Pos.le_refl.
  Qed.
  Lemma TreeMaxIndex_help: forall {A} (ls: seq.seq (positive * A)), forall i v,
        In (i, v) ls -> (compcert.lib.Coqlib.list_fold_left (fun a => [eta Pos.max a.1])
                                              1%positive ls >= i)%positive.
  Proof.
    induction ls.
    - intros. inversion H.
    - intros. simpl in H.
      destruct H as [eq | ineq].
      + subst a. simpl.
        rewrite Pos.max_1_r.
        apply fold_max_monoton.
      +  simpl. rewrite Pos.max_1_r.
         pose (ineq':=ineq).
         apply IHls in ineq'.
         apply Pos.le_ge.
         apply (Pos.le_trans _ (compcert.lib.Coqlib.list_fold_left
                                  (fun a0 : positive * A => [eta Pos.max a0.1])
                                  1%positive ls)).
         * apply Pos.ge_le. eapply IHls.
           eassumption.
         * apply Pos.ge_le. apply fold_max_monoton'.
           apply Pos.le_ge; apply Pos.le_1_l.
  Qed.

  Lemma max_works: forall A (t:PTree.t A) m, (m > TreeMaxIndex t)%positive ->
                                        t ! m = None.
  Proof.
    intros. destruct (t ! m) eqn: GET; try reflexivity.
    apply PTree.elements_correct in GET.
    unfold TreeMaxIndex in H. simpl in H.
    apply TreeMaxIndex_help in GET.
    apply Pos.ge_le in GET. apply Pos.le_nlt in GET.
    contradict GET. apply Pos.gt_lt; assumption.
  Qed.

  Lemma Cur_isCanonical: forall m, isCanonical (getCurPerm m).
        unfold isCanonical. intros.
        pose (BigNumber:= Pos.max (Pos.succ( TreeMaxIndex (getCurPerm m).2) ) (Mem.nextblock m)).
        assert (HH: (BigNumber >= (Pos.succ ( TreeMaxIndex (getCurPerm m).2)))%positive )
          by (unfold BigNumber; apply Pos.le_ge; apply Pos.le_max_l).
        apply Pos.ge_le in HH; apply Pos.le_succ_l in HH.
        apply Pos.lt_gt in HH; eapply max_works in HH.
        extensionality x.
        pose (property:= Mem.nextblock_noaccess m BigNumber x Cur).
        rewrite <- property.
        - replace ((Mem.mem_access m) !! BigNumber x Cur) with
          (permission_at m BigNumber x Cur); try reflexivity.
          rewrite <- getCurPerm_correct.
          unfold PMap.get.
          rewrite HH.
          reflexivity.
        - apply Pos.le_nlt. unfold BigNumber. apply Pos.le_max_r.
  Qed.

  Lemma Max_isCanonical: forall m, isCanonical (getMaxPerm m).
        unfold isCanonical. intros.
        pose (BigNumber:= Pos.max (Pos.succ( TreeMaxIndex (getMaxPerm m).2) ) (Mem.nextblock m)).
        assert (HH: (BigNumber >= (Pos.succ ( TreeMaxIndex (getMaxPerm m).2)))%positive )
          by (unfold BigNumber; apply Pos.le_ge; apply Pos.le_max_l).
        apply Pos.ge_le in HH; apply Pos.le_succ_l in HH.
        apply Pos.lt_gt in HH; eapply max_works in HH.
        extensionality x.
        pose (property:= Mem.nextblock_noaccess m BigNumber x Max).
        rewrite <- property.
        - replace ((Mem.mem_access m) !! BigNumber x Max) with
          (permission_at m BigNumber x Max); try reflexivity.
          rewrite <- getMaxPerm_correct.
          unfold PMap.get.
          rewrite HH.
          reflexivity.
        - apply Pos.le_nlt. unfold BigNumber. apply Pos.le_max_r.
  Qed.

  Definition permMapLt (pmap1 pmap2 : access_map) : Prop :=
    forall b ofs,
      Mem.perm_order'' (Maps.PMap.get b pmap2 ofs)
                       (Maps.PMap.get b pmap1 ofs).

  Lemma empty_LT: forall pmap,
             permMapLt empty_map pmap.
               intros pmap b ofs.
               rewrite empty_map_spec.
               destruct (pmap !! b ofs); simpl; exact I.
  Qed.

  Lemma canonical_lt :
    forall p' m
      (Hlt: permMapLt p' (getMaxPerm m)),
      isCanonical p'.
  Proof.
    intros.
    assert (Hcan:= Max_isCanonical m).
    unfold isCanonical in *.
    unfold permMapLt in *.
    remember (Pos.max (Pos.succ(TreeMaxIndex
                                  (getMaxPerm m).2) ) (Mem.nextblock m)) as b.
    remember (Pos.max (Pos.succ(TreeMaxIndex p'.2)) b) as b'.
    assert (Hb: ((Pos.succ ( TreeMaxIndex (getMaxPerm m).2)) <= b)%positive )
      by (subst; apply Pos.le_max_l).
    assert (Hm: (b' >= (Pos.succ ( TreeMaxIndex (getMaxPerm m).2)))%positive).
    { subst b'. apply Pos.le_ge. eapply Pos.le_trans; eauto.
      apply Pos.le_max_r.
    }
    assert (Hp': (b' >= (Pos.succ ( TreeMaxIndex p'.2)))%positive).
    { subst b'. apply Pos.le_ge. apply Pos.le_max_l.
    }
    apply Pos.ge_le in Hm; apply Pos.le_succ_l in Hm.
    apply Pos.lt_gt in Hm; eapply max_works in Hm.
    apply Pos.ge_le in Hp'; apply Pos.le_succ_l in Hp'.
    apply Pos.lt_gt in Hp'; eapply max_works in Hp'.
    extensionality ofs.
    assert (H:= Mem.nextblock_noaccess m b' ofs Max).
    assert (Hinvalid: ~ compcert.lib.Coqlib.Plt b' (Mem.nextblock m)).
    { clear - Heqb Heqb'.
      subst. intros Hcontra.
      unfold compcert.lib.Coqlib.Plt in Hcontra.
      apply Pos.max_lub_lt_iff in Hcontra. destruct Hcontra as [? Hcontra].
      apply Pos.max_lub_lt_iff in Hcontra. destruct Hcontra as [? Hcontra].
        by apply Pos.lt_irrefl in Hcontra.
    }
    specialize (H Hinvalid).
    specialize (Hlt b' ofs).
    rewrite getMaxPerm_correct in Hlt Hm.
    unfold permission_at in *. rewrite H in Hlt. simpl in Hlt.
    unfold Maps.PMap.get in Hlt.
    rewrite Hp' in Hlt.
    destruct (p'.1 ofs); tauto.
  Qed.

   Lemma invalid_block_empty:
    forall pmap m
      (Hlt: permMapLt pmap (getMaxPerm m)),
    forall b, ~ Mem.valid_block m b ->
         forall ofs,
           pmap !! b ofs = None.
  Proof.
    intros.
    apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in H.
    specialize (Hlt b ofs).
    rewrite getMaxPerm_correct in Hlt.
    unfold permission_at in Hlt.
    rewrite H in Hlt. simpl in Hlt.
    destruct (pmap !! b ofs); [by exfalso | reflexivity].
  Qed.

  Definition setPerm (p : option permission) (b : block)
             (ofs : Z) (pmap : access_map) : access_map :=
    Maps.PMap.set b (fun ofs' => if compcert.lib.Coqlib.zeq ofs ofs' then
                                p
                              else
                                Maps.PMap.get b pmap ofs')
                  pmap.

   Fixpoint setPermBlock (p : option permission) (b : block)
           (ofs : Z) (pmap : access_map) (length: nat): access_map :=
    match length with
      0 => pmap
    | S len =>
      setPerm p b (ofs + (Z_of_nat len))%Z (setPermBlock p b ofs pmap len)
    end.

  Lemma setPermBlock_same:
    forall p b ofs ofs' pmap sz
      (Hofs: (ofs <= ofs' < ofs + (Z.of_nat sz))%Z),
      (Maps.PMap.get b (setPermBlock p b ofs pmap sz)) ofs' = p.
  Proof. intros.
         generalize dependent ofs'.
         induction sz; simpl in *; intros.
         - unfold setPerm.
           exfalso. destruct Hofs. omega.
         - unfold setPerm.
           rewrite PMap.gss.
           destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat sz) ofs');
             first by (subst; reflexivity).
           simpl.
           eapply IHsz.
           destruct Hofs.
           split; auto.
           clear - H0 n.
           zify. omega.
  Qed.

  Lemma setPermBlock_other_1:
    forall p b ofs ofs' pmap sz
      (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat sz))%Z),
      (Maps.PMap.get b (setPermBlock p b ofs pmap sz)) ofs' =
      Maps.PMap.get b pmap ofs'.
  Proof. intros.
         generalize dependent ofs'.
         induction sz; simpl in *; intros; unfold setPerm.
         - reflexivity.
         - rewrite Maps.PMap.gss.
           destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat sz) ofs') as [Hcontra | ?].
           subst. exfalso.
           destruct Hofs; zify; omega.
           simpl. eapply IHsz.
           destruct Hofs; auto.
           right.
           zify. omega.
  Qed.

  Lemma setPermBlock_other_2:
    forall p b b' ofs ofs' pmap sz,
      b <> b' ->
      (Maps.PMap.get b' (setPermBlock p b ofs pmap sz)) ofs' =
      Maps.PMap.get b' pmap ofs'.
  Proof. intros.
         induction sz;
           simpl;
           auto.
         rewrite Maps.PMap.gso; auto.
  Qed.

  Lemma setPermBlock_or:
    forall p b ofs sz pmap b' ofs',
      (setPermBlock p b ofs pmap sz) !! b' ofs' = p \/
      (setPermBlock p b ofs pmap sz) !! b' ofs' = pmap !! b' ofs'.
  Proof.
    induction sz; intros.
    - simpl. right; reflexivity.
    - simpl.
      unfold setPerm.
      destruct (Pos.eq_dec b b').
      + subst.
        erewrite Maps.PMap.gss by eauto.
        destruct (Z.eq_dec (ofs + Z.of_nat sz) ofs').
        * subst.
          left.
          erewrite if_true
            by (now apply compcert.lib.Coqlib.proj_sumbool_is_true).
          reflexivity.
        * erewrite if_false
            by (apply Bool.negb_true_iff; now apply proj_sumbool_is_false).
          eauto.
      + erewrite Maps.PMap.gso by eauto.
        eauto.
  Qed.

  Fixpoint setPermBlock_var (fp : nat -> option permission) (b : block)
           (ofs : Z) (pmap : access_map) (length: nat): access_map :=
    match length with
      0 => pmap
    | S len =>
      setPerm (fp length) b (ofs + (Z_of_nat len))%Z
              (setPermBlock_var fp b ofs pmap len)
    end.

  Lemma setPermBlock_var_other_2:
    forall p b b' ofs ofs' pmap sz,
      b <> b' ->
      (Maps.PMap.get b' (setPermBlock_var p b ofs pmap sz)) ofs' =
      Maps.PMap.get b' pmap ofs'.
  Proof.
    intros.
    induction sz;
      simpl;
      auto.
    rewrite Maps.PMap.gso; auto.
  Qed.

   Lemma setPermBlock_var_other_1:
    forall p b ofs ofs' pmap sz
      (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat sz))%Z),
      (Maps.PMap.get b (setPermBlock_var p b ofs pmap sz)) ofs' =
      Maps.PMap.get b pmap ofs'.
  Proof.
    intros.
    generalize dependent ofs'.
    induction sz; simpl in *; intros; unfold setPerm.
    - reflexivity.
    - rewrite Maps.PMap.gss.
      destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat sz) ofs') as [Hcontra | ?].
      subst. exfalso.
      destruct Hofs; zify; omega.
      simpl. eapply IHsz.
      destruct Hofs; auto.
      right.
      zify. omega.
  Qed.

  Lemma setPermBlock_var_same:
    forall p b ofs ofs' pmap sz
      (Hofs: (ofs <= ofs' < ofs + (Z.of_nat sz))%Z),
      (Maps.PMap.get b (setPermBlock_var p b ofs pmap sz)) ofs' =
      p (compcert.lib.Coqlib.nat_of_Z (ofs' - ofs +1)).
  Proof.
    intros.
    generalize dependent ofs'.
    induction sz; simpl in *; intros.
    - unfold setPerm.
      exfalso. destruct Hofs. omega.
    - unfold setPerm.
      rewrite PMap.gss.
      destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat sz) ofs'); simpl.
      + f_equal. rewrite -e.
        replace (ofs + Z.of_nat sz - ofs +1 )%Z with (Z.of_nat sz + 1)%Z; try omega.
        rewrite compcert.lib.Coqlib.nat_of_Z_plus; simpl; try omega.
        rewrite compcert.lib.Coqlib.nat_of_Z_of_nat Pos2Nat.inj_1; omega.
      + apply IHsz; split; try omega.
        move : Hofs n=> [] l.
        rewrite Zpos_P_of_succ_nat.
        intros; omega.
  Qed.

  Lemma setPermBlock_setPermBlock_var:
    forall b ofs sz pmap p,
      setPermBlock p b ofs pmap sz =
      setPermBlock_var (fun _ => p) b ofs pmap sz.
  Proof.
    intros b ofs sz.
    generalize dependent ofs.
    induction sz; intros.
    - reflexivity.
    - simpl.
      rewrite IHsz.
      reflexivity.
  Qed.



  (*Lemma setPermBlock_var_or:
    forall p b ofs sz pmap b' ofs',
      (setPermBlock_var p b ofs pmap sz) !! b' ofs' = p \/
      (setPermBlock_var p b ofs pmap sz) !! b' ofs' = pmap !! b' ofs'.
  Proof.
    induction sz; intros.
    - simpl. right; reflexivity.
    - simpl.
      unfold setPerm.
      destruct (Pos.eq_dec b b').
      + subst.
        erewrite Maps.PMap.gss by eauto.
        destruct (Z.eq_dec (ofs + Z.of_nat sz) ofs').
        * subst.
          left.
          erewrite if_true
            by (now apply compcert.lib.Coqlib.proj_sumbool_is_true).
          reflexivity.
        * erewrite if_false
            by (apply Bool.negb_true_iff; now apply proj_sumbool_is_false).
          eauto.
      + erewrite Maps.PMap.gso by eauto.
        eauto.
  Qed. *)



  Lemma permMapCoherence_increase:
    forall pmap pmap' b ofs sz_nat sz
      (Hsz: sz = Z.of_nat (sz_nat))
      (Hcoh: permMapCoherence pmap pmap')
      (Hreadable: forall ofs', Intv.In ofs' (ofs, ofs + sz)%Z ->
                          Mem.perm_order' (pmap' !! b ofs') Readable),
      permMapCoherence pmap (setPermBlock (Some Writable) b ofs pmap' sz_nat).
  Proof.
    intros.
    intros b' ofs'.
    specialize (Hcoh b' ofs').
    destruct (Pos.eq_dec b b') as [Heq | Hneq].
    - subst.
      destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat sz_nat)%Z).
      + specialize (Hreadable _ i).
        erewrite setPermBlock_same by eauto.
        destruct (pmap' !! b' ofs') as [p|]; simpl in *;
          try (by exfalso);
          destruct p; inversion Hreadable; subst;
            destruct (pmap !! b' ofs') as [p1|];
            try (destruct p1); simpl in *; auto.
      + destruct sz_nat; first by (simpl; eauto).
        erewrite setPermBlock_other_1
          by (eapply Intv.range_notin in n;
              simpl; eauto; zify; omega).
        assumption.
    - erewrite setPermBlock_other_2 by eauto.
      assumption.
  Qed.

  (*setPermBlock with a function*)
  Fixpoint setPermBlockFunc (fp : Z -> option permission) (b : block)
           (ofs : Z) (pmap : access_map) (length: nat): access_map :=
    match length with
      0 => pmap
    | S len =>
      setPerm (fp (ofs + (Z_of_nat len))%Z) b (ofs + (Z_of_nat len))%Z (setPermBlockFunc fp b ofs pmap len)
    end.

  Lemma setPermBlockFunc_same:
    forall fp b ofs ofs' pmap sz
      (Hofs: (ofs <= ofs' < ofs + (Z.of_nat sz))%Z),
      (Maps.PMap.get b (setPermBlockFunc fp b ofs pmap sz)) ofs' = fp ofs'.
  Proof.
    intros.
    generalize dependent ofs'.
    induction sz; simpl in *; intros.
    - unfold setPerm.
      exfalso. destruct Hofs. omega.
    - unfold setPerm.
      rewrite PMap.gss.
      destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat sz) ofs');
        first by (subst; reflexivity).
      simpl.
      eapply IHsz.
      destruct Hofs.
      split; auto.
      clear - H0 n.
      zify. omega.
  Qed.

  Lemma setPermBlockFunc_other_1:
    forall fp b ofs ofs' pmap sz
      (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat sz))%Z),
      (Maps.PMap.get b (setPermBlock fp b ofs pmap sz)) ofs' =
      Maps.PMap.get b pmap ofs'.
  Proof.
    intros.
    generalize dependent ofs'.
    induction sz; simpl in *; intros; unfold setPerm.
    - reflexivity.
    - rewrite Maps.PMap.gss.
      destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat sz) ofs') as [Hcontra | ?].
      subst. exfalso.
      destruct Hofs; zify; omega.
      simpl. eapply IHsz.
      destruct Hofs; auto.
      right.
      zify. omega.
  Qed.

  Lemma setPermBlockFunc_other_2:
    forall fp b b' ofs ofs' pmap sz,
      b <> b' ->
      (Maps.PMap.get b' (setPermBlock fp b ofs pmap sz)) ofs' =
      Maps.PMap.get b' pmap ofs'.
  Proof.
    intros.
    induction sz;
      simpl;
      auto.
    rewrite Maps.PMap.gso; auto.
  Qed.

  Lemma setPermBlock_coherent:
    forall pmap pmap' b ofs sz
      (Hcoh: permMapCoherence pmap pmap')
      (Hnonempty: forall ofs', Intv.In ofs' (ofs, ofs + Z.of_nat sz)%Z ->
                          ~ Mem.perm_order' (pmap !! b ofs') Readable),
      permMapCoherence pmap (setPermBlock (Some Writable) b ofs pmap' sz).
  Proof.
    intros.
    intros b' ofs'.
    specialize (Hcoh b' ofs').
    destruct (Pos.eq_dec b b').
    - subst.
      destruct (Intv.In_dec ofs' (ofs, (ofs + Z.of_nat sz)%Z)).
      + erewrite setPermBlock_same by eauto.
        specialize (Hnonempty _ i).
        destruct (pmap !! b' ofs') as [p|] eqn:Hpmap'; simpl; auto;
          destruct p; simpl in Hnonempty; eauto using perm_order.
      + destruct sz;
          first by (simpl; assumption).
        erewrite setPermBlock_other_1.
        assumption.
        apply Intv.range_notin in n; eauto.
        simpl. rewrite Zpos_P_of_succ_nat. omega.
    - erewrite setPermBlock_other_2 by eauto.
      assumption.
  Qed.

  (** Apply a [delta_map] to an [access_map]*)
  Definition computeMap (pmap : access_map) (delta : delta_map) : access_map :=
    (pmap.1,
     @Maps.PTree.combine (Z -> option permission) (Z -> option (option permission))
                         (Z -> option permission)
                         (fun p1 pd => match pd, p1 with
                                    | Some pd', Some p1' =>
                                      Some (fun z => match pd' z with
                                                    Some pd'' => pd''
                                                  | _ => p1' z
                                                  end)
                                    | Some pd', None =>
                                      Some (fun z => match pd' z with
                                                    Some pd'' => pd''
                                                  | _ => pmap.1 z
                                                  end)
                                    | None, _ => p1
                                    end)
                         pmap.2 delta).

  (** If the [delta_map] changes the [access_map] at a specific [address] *)
  Lemma computeMap_1 :
    forall (pmap : access_map) (dmap : delta_map) b ofs df (p : option permission),
      Maps.PTree.get b dmap = Some df ->
      df ofs = Some p ->
      Maps.PMap.get b (computeMap pmap dmap) ofs = p.
  Proof.
    intros pmap dmap b ofs df p Hdmap Hdf.
    unfold computeMap, Maps.PMap.get. simpl.
    rewrite Maps.PTree.gcombine; try reflexivity.
    rewrite Hdmap.
    destruct ((pmap.2) ! b);
      by rewrite Hdf.
  Qed.

  (** If the [delta_map] changes the [access_map] at this [block] but not at this [offset] *)
  Lemma computeMap_2 :
    forall (pmap : access_map) (dmap : delta_map) b ofs df,
      Maps.PTree.get b dmap = Some df ->
      df ofs = None ->
      Maps.PMap.get b (computeMap pmap dmap) ofs = Maps.PMap.get b pmap ofs.
  Proof.
    intros pmap dmap b ofs df Hdmap Hdf.
    unfold computeMap, Maps.PMap.get. simpl.
    rewrite Maps.PTree.gcombine; try reflexivity.
    rewrite Hdmap.
    destruct ((pmap.2) ! b);
      by rewrite Hdf.
  Qed.

  (** If the [delta_map] does not change the [access_map] at this [block] *)
  Lemma computeMap_3 :
    forall (pmap : access_map) (dmap : delta_map) b ofs,
      Maps.PTree.get b dmap = None ->
      Maps.PMap.get b (computeMap pmap dmap) ofs = Maps.PMap.get b pmap ofs.
  Proof.
    intros pmap dmap b ofs Hdmap.
    unfold computeMap, Maps.PMap.get. simpl.
    rewrite Maps.PTree.gcombine; try reflexivity.
    rewrite Hdmap.
      by reflexivity.
  Qed.

  Import Maps BlockList.

  Definition maxF (f : Z -> perm_kind -> option permission) :=
    fun ofs k => match k with
              | Max => Some Freeable
              | Cur => f ofs k
              end.

  Definition allF (f : Z -> perm_kind -> option permission) :=
    fun (_ : Z) (_ : perm_kind) => Some Freeable.

  Fixpoint PList (f : (Z -> perm_kind -> option permission) ->
                      Z -> perm_kind -> option permission)
           l m : list (positive * (Z -> perm_kind -> option permission)) :=
    match l with
      | nil => nil
      | x :: l =>
        (Pos.of_nat x, f (PMap.get (Pos.of_nat x) m)) :: (PList f l m)
  end.

  Lemma PList_app :
    forall l m x f,
      (PList f l m) ++ ((Pos.of_nat x,
                                f (PMap.get (Pos.of_nat x) m)) :: nil) =
      PList f (l ++ (x :: nil)) m.
  Proof.
    intro l. induction l; intros.
    reflexivity.
    simpl. apply f_equal.
    auto.
  Qed.

  Lemma PList_cons :
    forall f l m x,
      (Pos.of_nat x, f (PMap.get (Pos.of_nat x) m)) :: (PList f l m) =
      PList f (x :: l) m.
  Proof.
    reflexivity.
  Qed.

  Lemma PList_correct :
    forall f l m k v
           (HInl: List.In k l)
           (HInMap: List.In (Pos.of_nat k, v) (PTree.elements m.2)),
      List.In (Pos.of_nat k, f v) (PList f l m).
  Proof.
    intros f l m. induction l; intros; inversion HInl.
    - subst. simpl. apply PTree.elements_complete in HInMap.
      unfold PMap.get. rewrite HInMap. now left.
    - simpl. right. auto.
  Qed.

  Lemma PList_mkBlock_complete :
    forall f k v m n
           (Hk: k > 0)
           (HIn1: List.In (Pos.of_nat k, v) (PList f (mkBlockList n) m)),
      List.In k (mkBlockList n).
  Proof.
    intros.
    induction n.
    simpl in *. auto.
    destruct n. simpl in HIn1. auto.
    rewrite <- mkBlockList_unfold' in HIn1.
    rewrite <- PList_cons in HIn1.
    apply List.in_inv in HIn1.
    destruct HIn1 as [Heq | HIn1].
    assert (Heqn: Pos.of_nat (S n) = Pos.of_nat k) by (inversion Heq; auto).
    apply Nat2Pos.inj_iff in Heqn.
    subst. simpl; auto.
    auto. intro Hcontra. subst. auto.
    rewrite <- mkBlockList_unfold'.
    right. auto.
  Qed.

  Lemma PList_mkBlock_det :
    forall n f k v v' m
           (HIn1: List.In (Pos.of_nat k, v) (PList f (mkBlockList n) m))
           (HIn2: List.In (Pos.of_nat k, v') (PList f (mkBlockList n) m)),
      v = v'.
  Proof.
    intros n. induction n.
    - simpl. intros. exfalso. auto.
    - intros.
      destruct n. simpl in HIn1. exfalso; auto.
      destruct n. simpl in HIn1, HIn2.
      destruct HIn1 as [HIn1 | HIn1];
        destruct HIn2 as [HIn2 | HIn2];
        inversion HIn1; inversion HIn2; now subst.
      rewrite <- mkBlockList_unfold' in HIn1, HIn2.
      rewrite <- PList_cons in HIn1, HIn2.
      apply List.in_inv in HIn1.
      apply List.in_inv in HIn2.
      destruct HIn1 as [Heq1 | HIn1].
      + destruct HIn2 as [Heq2 | HIn2].
        inversion Heq1; inversion Heq2. reflexivity.
        assert (Heq:Pos.of_nat (S (S n)) =
                    Pos.of_nat k /\ f (m !! (Pos.of_nat (S (S n)))) = v)
          by (inversion Heq1; auto).
        destruct Heq as [HEqk Hv].
        rewrite <- HEqk in HIn2.
        exfalso.
        clear Hv HEqk Heq1 IHn v k.
        apply PList_mkBlock_complete in HIn2.
        eapply mkBlockList_not_in in HIn2; eauto. auto.
      + destruct HIn2 as [Heq | HIn2].
        assert (Heq':Pos.of_nat (S (S n)) = Pos.of_nat k) by (inversion Heq; auto).
        rewrite <- Heq' in HIn1.
        apply PList_mkBlock_complete in HIn1; auto.
        apply mkBlockList_not_in in HIn1; auto. now exfalso.
        eauto.
  Qed.

  Fixpoint canonicalPTree (l : list (positive * (Z -> perm_kind -> option permission))) :=
    match l with
      | nil => PTree.empty _
      | x :: l =>
        PTree.set (fst x) (snd x) (canonicalPTree l)
    end.

  Lemma canonicalPTree_elements :
    forall l x
           (Hin: List.In x (PTree.elements (canonicalPTree l))),
      List.In x l.
  Proof.
    intro l.
    induction l; intros; auto.
    simpl.
    simpl in Hin.
    unfold PTree.elements in Hin.
    destruct x as [p o].
    apply PTree.elements_complete in Hin.
    destruct (Pos.eq_dec a.1 p).
    - subst. rewrite PTree.gss in Hin. inversion Hin; subst.
      left.  destruct a; reflexivity.
    - rewrite PTree.gso in Hin; auto.
      apply PTree.elements_correct in Hin. right. auto.
  Qed.

  Lemma canonicalPTree_get_complete :
    forall l m k f fn
           (HGet: (canonicalPTree (PList fn l m)) ! k = Some f),
      List.In (k, f) (PList fn l m).
  Proof.
    intro l. induction l.
    simpl. intros. rewrite PTree.gempty in HGet. discriminate.
    intros.
    rewrite <- PList_cons in HGet.
    apply PTree.elements_correct in HGet.
    apply canonicalPTree_elements in HGet.
    destruct (List.in_inv HGet) as [Heq | Hin].
    inversion Heq; subst. simpl; auto.
    auto.
  Qed.

  Lemma canonicalPTree_get_sound :
    forall n m k fn
           (Hk: k > 0)
           (Hn: n > 1)
           (HGet: (canonicalPTree (PList fn (mkBlockList n) m)) ! (Pos.of_nat k) = None),
      ~ List.In k (mkBlockList n).
  Proof.
    intros.
    destruct n. simpl; auto.
    induction n. simpl; auto.
    intro HIn.
    rewrite <- mkBlockList_unfold' in HGet, HIn.
    destruct (List.in_inv HIn) as [? | HIn']; subst.
    rewrite <- PList_cons in HGet.
    unfold canonicalPTree in HGet. fold canonicalPTree in HGet.
    rewrite PTree.gss in HGet. discriminate.
    destruct n. simpl in *; auto.
    apply IHn. auto. rewrite <- PList_cons in HGet.
    unfold canonicalPTree in HGet. fold canonicalPTree in HGet.
    apply mkBlockList_range in HIn'.
    assert (k <> S (S n)). destruct HIn'. intros Hcontra; subst. auto.
    rewrite ltnn in H. auto.
    rewrite PTree.gso in HGet.
    assumption.
    intros HContra.
    unfold fst in HContra.
    apply Nat2Pos.inj_iff in HContra. auto. intros ?; subst; auto.
    intros ?; subst. discriminate.
    assumption.
  Qed.

  Definition canonicalPMap fn n m : Maps.PMap.t (Z -> perm_kind -> option permission) :=
    let l := mkBlockList n in
    (fun _ _ => None, canonicalPTree (PList fn l m)).

  Lemma canonicalPMap_sound :
    forall k n m fn
           (Hk : k > 0)
           (Hkn : k < n),
      fn (m !! (Pos.of_nat k)) = (canonicalPMap fn n m) !! (Pos.of_nat k).
  Proof.
    intros.
    unfold PMap.get.
    destruct (((canonicalPMap fn n m).2) ! (Pos.of_nat k)) as [f|] eqn:HGet.
    - apply PTree.elements_correct in HGet.
      unfold canonicalPMap in HGet.  simpl in HGet.
      destruct ((m.2) ! (Pos.of_nat k)) eqn:HGet'.
      + apply PTree.elements_correct in HGet'.
        apply canonicalPTree_elements in HGet.
        apply PList_correct with (f := fn) (l := mkBlockList n) in HGet'.
        eapply PList_mkBlock_det; eauto.
        apply PList_mkBlock_complete in HGet. assumption.
        assumption.
      + apply PTree.elements_complete in HGet.
        apply canonicalPTree_get_complete in HGet.
        induction (mkBlockList n). simpl in HGet. by exfalso.
        simpl in HGet. destruct HGet as [Heq | Hin].
        inversion Heq; subst.
        unfold PMap.get. rewrite <- H0 in HGet'. rewrite HGet'. reflexivity.
        auto.
    - unfold canonicalPMap in HGet. simpl in HGet.
      apply canonicalPTree_get_sound in HGet.
      destruct n. exfalso. auto. destruct n. exfalso. ssromega.
      exfalso. apply HGet. apply mkBlockList_include; auto.
      assumption. clear HGet.
      eapply leq_ltn_trans; eauto.
  Qed.

  Lemma canonicalPMap_default :
    forall n k m fn
           (Hkn : k >= n),
      (canonicalPMap fn n m) !! (Pos.of_nat k) = fun _ _ => None.
  Proof.
    intro. induction n; intros. unfold canonicalPMap. simpl.
    unfold PMap.get.
    rewrite PTree.gempty. reflexivity.
    assert (Hkn': n <= k) by ssromega.
    unfold canonicalPMap.
    destruct n. simpl. unfold PMap.get. simpl. rewrite PTree.gempty. reflexivity.
    unfold PMap.get.
    rewrite <- mkBlockList_unfold'. rewrite <- PList_cons.
    unfold canonicalPTree.
    rewrite PTree.gso. fold canonicalPTree.
    specialize (IHn _ m fn Hkn').
    unfold canonicalPMap, PMap.get, snd in IHn.
    destruct ((canonicalPTree (PList fn (mkBlockList n.+1) m)) ! (Pos.of_nat k)); auto.
    unfold fst. intros HContra. apply Nat2Pos.inj_iff in HContra; subst; ssromega.
  Qed.

  Definition setMaxPerm (m : mem) : mem.
  Proof.
    refine (Mem.mkmem (Mem.mem_contents m)
                      (canonicalPMap maxF (Pos.to_nat (Mem.nextblock m))
                                     (Mem.mem_access m))
                      (Mem.nextblock m) _ _ _).
      { intros.
        replace b with (Pos.of_nat (Pos.to_nat b)) by (rewrite Pos2Nat.id; done).
        destruct (leq (Pos.to_nat (Mem.nextblock m)) (Pos.to_nat b)) eqn:Hbn.
          by rewrite canonicalPMap_default.
          erewrite <- canonicalPMap_sound. simpl.
          match goal with
          | [|- match ?Expr with _ => _ end] => destruct Expr
          end; constructor.
          apply/ltP/Pos2Nat.is_pos.
          ssromega. }
      { intros b ofs k H.
        replace b with (Pos.of_nat (Pos.to_nat b)) by (rewrite Pos2Nat.id; done).
        erewrite canonicalPMap_default. reflexivity.
        apply Pos.le_nlt in H.
        apply/leP.
        now apply Pos2Nat.inj_le.
      }
      { apply Mem.contents_default. }
  Defined.

  Lemma setMaxPerm_Max :
    forall m b ofs,
      (Mem.valid_block m b ->
       permission_at (setMaxPerm m) b ofs Max = Some Freeable) /\
      (~Mem.valid_block m b ->
       permission_at (setMaxPerm m) b ofs Max = None).
  Proof.
    intros.
    assert (Hb : b = Pos.of_nat (Pos.to_nat b))
      by (by rewrite Pos2Nat.id).
    split.
    { intros Hvalid. unfold permission_at,  setMaxPerm. simpl.
      rewrite Hb.
      rewrite <- canonicalPMap_sound.
      reflexivity.
      assert (H := Pos2Nat.is_pos b). ssromega.
      apply Pos2Nat.inj_lt in Hvalid. ssromega.
    }
    { intros Hinvalid.
      unfold permission_at, setMaxPerm. simpl.
      rewrite Hb.
      rewrite canonicalPMap_default. reflexivity.
      apply Pos.le_nlt in Hinvalid.
      apply Pos2Nat.inj_le in Hinvalid. ssromega.
    }
  Qed.

   Lemma setMaxPerm_MaxV :
    forall m b ofs,
      Mem.valid_block m b ->
       permission_at (setMaxPerm m) b ofs Max = Some Freeable.
  Proof.
    intros;
    assert (Hmax := setMaxPerm_Max m b ofs);
    destruct Hmax; auto.
  Qed.

  Lemma setMaxPerm_MaxI :
    forall m b ofs,
      ~ Mem.valid_block m b ->
      permission_at (setMaxPerm m) b ofs Max = None.
  Proof.
    intros;
    assert (Hmax := setMaxPerm_Max m b ofs);
    destruct Hmax; auto.
  Qed.

  Lemma setMaxPerm_Cur :
    forall m b ofs,
      permission_at (setMaxPerm m) b ofs Cur = permission_at m b ofs Cur.
  Proof.
    intros. unfold setMaxPerm, permission_at. simpl.
    assert (Hb : b = Pos.of_nat (Pos.to_nat b))
      by (by rewrite Pos2Nat.id).
    rewrite Hb.
    destruct (compcert.lib.Coqlib.plt b (Mem.nextblock m)) as [Hvalid | Hinvalid].
    rewrite <- canonicalPMap_sound. reflexivity.
    assert (H := Pos2Nat.is_pos b). ssromega.
    apply Pos2Nat.inj_lt in Hvalid. ssromega.
    rewrite canonicalPMap_default.
    apply Mem.nextblock_noaccess with (ofs := ofs) (k := Cur) in Hinvalid.
    rewrite <- Hb.
    rewrite Hinvalid. reflexivity.
    apply Pos.le_nlt in Hinvalid.
    apply Pos2Nat.inj_le in Hinvalid. ssromega.
  Qed.

  Definition makeCurMax_map (mem_access:PMap.t (Z -> perm_kind -> option permission)):
    PMap.t (Z -> perm_kind -> option permission):=
    PMap.map (fun f => fun z k => f z Max) mem_access.


  Definition makeCurMax (m:mem): mem.
  apply (Mem.mkmem (Mem.mem_contents m)
                   (makeCurMax_map (Mem.mem_access m))
                   (Mem.nextblock m)).
  - intros. unfold makeCurMax_map; simpl. rewrite PMap.gmap.
    apply po_refl.
  - intros. unfold makeCurMax_map; simpl. rewrite PMap.gmap.
    apply Mem.nextblock_noaccess; assumption.
  - intros; apply Mem.contents_default.
  Defined.

  Lemma makeCurMax_correct :
    forall m b ofs k,
      permission_at m b ofs Max = permission_at (makeCurMax m) b ofs k.
  Proof.
    intros.
    unfold permission_at, makeCurMax, makeCurMax_map.
    simpl;
      by rewrite Maps.PMap.gmap.
  Qed.

  Lemma makeCurMax_valid :
    forall m b,
      Mem.valid_block m b <-> Mem.valid_block (makeCurMax m) b.
  Proof.
    intros;
    unfold Mem.valid_block, makeCurMax; simpl;
      by auto.
  Qed.

  Definition restrPermMap p' m (Hlt: permMapLt p' (getMaxPerm m)) : mem.
  Proof.
    refine ({|
               Mem.mem_contents := Mem.mem_contents m;
               Mem.mem_access :=
                 (fun ofs k =>
                    match k with
                      | Cur => None
                      | Max => fst (Mem.mem_access m) ofs k
                    end, Maps.PTree.map (fun b f =>
                                           fun ofs k =>
                                             match k with
                                               | Cur =>
                                                 (Maps.PMap.get b p') ofs
                                               | Max =>
                                                 f ofs Max
                                             end) (Mem.mem_access m).2);
               Mem.nextblock := Mem.nextblock m;
               Mem.access_max := _;
               Mem.nextblock_noaccess := _;
               Mem.contents_default := Mem.contents_default m |}).
    - unfold permMapLt in Hlt.
      assert (Heq: forall b ofs, Maps.PMap.get b (getMaxPerm m) ofs =
                            Maps.PMap.get b (Mem.mem_access m) ofs Max).
      { unfold getMaxPerm. intros.
        rewrite Maps.PMap.gmap. reflexivity. }
      intros.
      specialize (Hlt b ofs).
      specialize (Heq b ofs).
      unfold getMaxPerm in Hlt.
      unfold Maps.PMap.get in *. simpl in *.
      rewrite Maps.PTree.gmap; simpl.
      match goal with
        | [|- context[match compcert.lib.Coqlib.option_map ?Expr1 ?Expr2  with _ => _ end]] =>
          destruct (compcert.lib.Coqlib.option_map Expr1 Expr2) as [f|] eqn:?
      end; auto; unfold compcert.lib.Coqlib.option_map in Heqo.
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; try discriminate.
      + inversion Heqo; subst; clear Heqo.
        rewrite Heq in Hlt. auto.
      + unfold Mem.perm_order''. by destruct ((Mem.mem_access m).1 ofs Max).
    - intros b ofs k Hnext.
    - unfold permMapLt in Hlt.
      assert (Heq: forall b ofs, Maps.PMap.get b (getMaxPerm m) ofs =
                            Maps.PMap.get b (Mem.mem_access m) ofs Max).
      { unfold getMaxPerm. intros.
        rewrite Maps.PMap.gmap. reflexivity. }
      specialize (Hlt b ofs).
      specialize (Heq b ofs).
      unfold Maps.PMap.get in *.
      simpl in *.
      rewrite Maps.PTree.gmap; simpl.
      assert (H := Mem.nextblock_noaccess m).
      specialize (H b). unfold Maps.PMap.get in H.
      match goal with
        | [|- context[match compcert.lib.Coqlib.option_map ?Expr1 ?Expr2  with _ => _ end]] =>
          destruct (compcert.lib.Coqlib.option_map Expr1 Expr2) as [f|] eqn:?
      end; auto; unfold compcert.lib.Coqlib.option_map in Heqo;
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:Heqo2; try discriminate.
      inversion Heqo. subst f. clear Heqo.
      destruct k; auto.
      rewrite Heq in Hlt.
      specialize (H ofs Max). rewrite H in Hlt; auto.
      unfold Mem.perm_order'' in Hlt. destruct (Maps.PTree.get b p'.2).
      destruct (o0 ofs); tauto.
      destruct (p'.1 ofs); tauto.
      rewrite H; auto. destruct k; auto.
  Defined.

Lemma restrPermMap_irr:
      forall p1 p2 m1 m2
        (P1: permMapLt p1 (getMaxPerm m1))
        (P2: permMapLt p2 (getMaxPerm m2)),
        p1 = p2 -> m1 = m2 ->
        restrPermMap P1 = restrPermMap P2.
    Proof.
      intros; subst.
      replace P1 with P2.
      reflexivity.
      apply proof_irrelevance.
    Qed.
    Lemma restrPermMap_ext:
      forall p1 p2 m
        (P1: permMapLt p1 (getMaxPerm m))
        (P2: permMapLt p2 (getMaxPerm m)),
        (forall b, (p1 !! b) = (p2 !! b)) ->
        restrPermMap P1 = restrPermMap P2.
    Proof.
      intros; subst.
      remember (restrPermMap P1) as M1.
      remember (restrPermMap P2) as M2.
      assert (Mem.mem_contents M1 = Mem.mem_contents M2) by
          (subst; reflexivity).
      assert (Mem.nextblock M1 = Mem.nextblock M2) by
          (subst; reflexivity).
      assert (Mem.mem_access M1 = Mem.mem_access M2).
      {
        subst. simpl.
        f_equal. f_equal.
        simpl.
        do 4 (apply functional_extensionality; intro).
        destruct x2; try rewrite H; reflexivity.
      }
      subst.
      destruct (restrPermMap P1);
        destruct (restrPermMap P2); simpl in *.
      subst. f_equal;
      apply proof_irrelevance.
    Qed.

  Lemma restrPermMap_nextblock :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)),
      Mem.nextblock (restrPermMap Hlt) = Mem.nextblock m.
  Proof.
    intros. unfold restrPermMap. reflexivity.
  Qed.

  Lemma restrPermMap_valid :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)) b,
      Mem.valid_block (restrPermMap Hlt) b <-> Mem.valid_block m b.
  Proof.
    intros. unfold Mem.valid_block. rewrite restrPermMap_nextblock.
      by split.
  Qed.

  Lemma restrPermMap_contents :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)),
      contents_at (restrPermMap Hlt) = contents_at m.
  Proof.
    intros. unfold restrPermMap. reflexivity.
  Qed.

  Lemma restrPermMap_max :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)),
      max_access_at (restrPermMap Hlt) = max_access_at m.
  Proof.
    intros.
    unfold max_access_at; simpl. unfold Memory.access_at.
    extensionality loc; simpl.
    unfold Maps.PMap.get at 1; simpl.
    rewrite Maps.PTree.gmap.
    unfold Maps.PMap.get at 2; simpl.
    destruct (((Mem.mem_access m).2) ! (loc.1)) eqn:AA; reflexivity.
  Qed.

  Lemma getMax_restr :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)) b,
      (getMaxPerm (restrPermMap Hlt)) !!  b = (getMaxPerm m) !! b.
  Proof.
    intros.
    unfold getMaxPerm.
    unfold Maps.PMap.get.
    simpl. do 2 rewrite Maps.PTree.gmap1.
    unfold compcert.lib.Coqlib.option_map.
    rewrite Maps.PTree.gmap.
    unfold compcert.lib.Coqlib.option_map.
    simpl.
    destruct ((Mem.mem_access m).2 ! b);
      by auto.
  Qed.

  Lemma restrPermMap_irr' : forall p' p'' m
                             (Hlt : permMapLt p' (getMaxPerm m))
                             (Hlt': permMapLt p'' (getMaxPerm m))
                             (Heq_new: p' = p''),
                             restrPermMap Hlt = restrPermMap Hlt'.
  Proof.
    intros. subst.
    apply f_equal. by apply proof_irr.
  Qed.

  Lemma restrPermMap_disjoint_inv:
    forall (mi mj m : mem) (pi pj : access_map)
      (Hltj: permMapLt pj (getMaxPerm m))
      (Hlti: permMapLt pi (getMaxPerm m))
      (Hdisjoint: permMapsDisjoint pi pj)
      (Hrestrj: restrPermMap Hltj = mj)
      (Hrestri: restrPermMap Hlti = mi),
      permMapsDisjoint (getCurPerm mi) (getCurPerm mj).
  Proof.
    intros. rewrite <- Hrestri. rewrite <- Hrestrj.
    unfold restrPermMap, getCurPerm, permMapsDisjoint. simpl in *.
    intros b ofs.
    do 2 rewrite Maps.PMap.gmap.
    clear Hrestrj Hrestri.
    unfold permMapLt, Mem.perm_order'' in *.
    specialize (Hltj b ofs); specialize (Hlti b ofs).
    unfold getMaxPerm in *; simpl in *.
    rewrite Maps.PMap.gmap in Hlti, Hltj.
    unfold permMapsDisjoint, Maps.PMap.get in *; simpl in *.
    do 2 rewrite Maps.PTree.gmap. unfold compcert.lib.Coqlib.option_map.
    specialize (Hdisjoint b ofs).
    assert (Hnone: (Mem.mem_access m).1 ofs Max = None)
      by (assert (Hcan_m := Max_isCanonical m);
           unfold isCanonical in Hcan_m; simpl in Hcan_m;
            by apply equal_f with (x:=ofs) in Hcan_m).
    destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; auto.
    rewrite Hnone in Hlti, Hltj;
      destruct (Maps.PTree.get b pi.2)
      as [f1 |] eqn:?;
                destruct (Maps.PTree.get b pj.2) as [f2|] eqn:?;
      repeat match goal with
               | [H: match ?Expr with _ => _ end |- _] => destruct Expr
             end; tauto.
  Qed.

  Lemma restrPermMap_correct :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m))
      b ofs,
      permission_at (restrPermMap Hlt) b ofs Max =
      Maps.PMap.get b (getMaxPerm m) ofs /\
      permission_at (restrPermMap Hlt) b ofs Cur =
      Maps.PMap.get b p' ofs.
  Proof.
    intros.
    assert (Hcan_p' := canonical_lt Hlt).
    assert (Hcan_m := Max_isCanonical m).
    unfold restrPermMap, getMaxPerm, permission_at. simpl.
    rewrite Maps.PMap.gmap. split;
      unfold permMapLt in Hlt; specialize (Hlt b ofs);
      unfold Maps.PMap.get; simpl; rewrite Maps.PTree.gmap;
      unfold compcert.lib.Coqlib.option_map; simpl;
      destruct (Maps.PTree.get b (Mem.mem_access m).2) eqn:?; auto.
    unfold Maps.PMap.get in Hlt.
    unfold isCanonical in *.
    destruct (Maps.PTree.get b p'.2) eqn:?; [| by rewrite Hcan_p'].
    rewrite Hcan_m in Hlt.
    unfold getMaxPerm in Hlt. rewrite Maps.PTree.gmap1 in Hlt.
    unfold compcert.lib.Coqlib.option_map in Hlt.
    rewrite Heqo in Hlt. simpl in Hlt.
    destruct (o ofs); tauto.
  Qed.

  Corollary restrPermMap_Cur :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)) b ofs,
      permission_at (restrPermMap Hlt) b ofs Cur =
      Maps.PMap.get b p' ofs.
  Proof.
    intros.
    assert (Heq := restrPermMap_correct Hlt b ofs).
    by destruct Heq.
  Qed.

  Corollary restrPermMap_Max :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m)) b ofs,
      permission_at (restrPermMap Hlt) b ofs Max =
      Maps.PMap.get b (getMaxPerm m) ofs.
  Proof.
    intros.
    assert (Heq := restrPermMap_correct Hlt b ofs).
      by destruct Heq.
  Qed.


  Lemma restrPermMap_can : forall (p : access_map) (m m': mem)
                             (Hlt: permMapLt p (getMaxPerm m))
                             (Hrestrict: restrPermMap Hlt = m'),
      isCanonical (getCurPerm m').
  Proof.
    intros. subst.
    unfold restrPermMap, getCurPerm, isCanonical in *. simpl in *.
    auto.
  Defined.

  Lemma restrPermMap_can_max : forall (p : access_map) (m m': mem)
                                 (Hlt: permMapLt p (getMaxPerm m))
                                 (Hrestrict: restrPermMap Hlt = m'),
      isCanonical (getMaxPerm m').
  Proof.
    intros. subst.
    assert (Hcanonical := Max_isCanonical m).
    unfold restrPermMap, getMaxPerm, isCanonical in *. simpl in *.
    auto.
  Defined.

  Definition erasePerm (m : mem) : mem.
  Proof.
    refine (Mem.mkmem (Mem.mem_contents m)
                      (canonicalPMap allF (Pos.to_nat (Mem.nextblock m))
                                     (Mem.mem_access m))
                      (Mem.nextblock m) _ _ _).
      { intros.
        replace b with (Pos.of_nat (Pos.to_nat b)) by (rewrite Pos2Nat.id; done).
        destruct (leq (Pos.to_nat (Mem.nextblock m)) (Pos.to_nat b)) eqn:Hbn.
          by rewrite canonicalPMap_default.
          erewrite <- canonicalPMap_sound. simpl.
          constructor.
          apply/ltP/Pos2Nat.is_pos.
          ssromega. }
      { intros b ofs k H.
        replace b with (Pos.of_nat (Pos.to_nat b)) by (rewrite Pos2Nat.id; done).
        erewrite canonicalPMap_default. reflexivity.
        apply Pos.le_nlt in H.
        apply/leP.
        now apply Pos2Nat.inj_le.
      }
      { apply Mem.contents_default. }
  Defined.

  Lemma erasePerm_Perm :
    forall m b ofs k ,
      (Mem.valid_block m b ->
       permission_at (erasePerm m) b ofs k = Some Freeable) /\
      (~Mem.valid_block m b ->
       permission_at (erasePerm m) b ofs k = None).
  Proof.
    intros.
    assert (Hb : b = Pos.of_nat (Pos.to_nat b))
      by (by rewrite Pos2Nat.id).
    split.
    { intros Hvalid. unfold permission_at,  setMaxPerm. simpl.
      rewrite Hb.
      rewrite <- canonicalPMap_sound.
      reflexivity.
      assert (H := Pos2Nat.is_pos b). ssromega.
      apply Pos2Nat.inj_lt in Hvalid. ssromega.
    }
    { intros Hinvalid.
      unfold permission_at, setMaxPerm. simpl.
      rewrite Hb.
      rewrite canonicalPMap_default. reflexivity.
      apply Pos.le_nlt in Hinvalid.
      apply Pos2Nat.inj_le in Hinvalid. ssromega.
    }
  Qed.

   Lemma erasePerm_V :
    forall m b ofs k,
      Mem.valid_block m b ->
       permission_at (erasePerm m) b ofs k = Some Freeable.
  Proof.
    intros;
    assert (Hperm := erasePerm_Perm m b ofs k);
    destruct Hperm; auto.
  Qed.

  Lemma erasePerm_I :
    forall m b ofs k,
      ~ Mem.valid_block m b ->
      permission_at (erasePerm m) b ofs k = None.
  Proof.
    intros;
    assert (Hperm := erasePerm_Perm m b ofs k);
    destruct Hperm; auto.
  Qed.

   Definition decay m_before m_after := forall b ofs,
      (~Mem.valid_block m_before b ->
       Mem.valid_block m_after b ->
       (forall k, Maps.PMap.get b (Mem.mem_access m_after) ofs k = Some Freeable)
       \/ (forall k, Maps.PMap.get b (Mem.mem_access m_after) ofs k = None)) /\
      (Mem.valid_block m_before b ->
       (forall k,
           (Maps.PMap.get b (Mem.mem_access m_before) ofs k = Some Freeable /\
            Maps.PMap.get b (Mem.mem_access m_after) ofs k = None)) \/
       (forall k, Maps.PMap.get b (Mem.mem_access m_before) ofs k =
             Maps.PMap.get b (Mem.mem_access m_after) ofs k)).

   Definition strong_decay m_before m_after := forall b ofs,
       (~Mem.valid_block m_before b ->
       Mem.valid_block m_after b ->
       (forall k, Maps.PMap.get b (Mem.mem_access m_after) ofs k = Some Freeable)
       \/ (forall k, Maps.PMap.get b (Mem.mem_access m_after) ofs k = None)) /\
      (Mem.valid_block m_before b ->
       (forall k, Maps.PMap.get b (Mem.mem_access m_before) ofs k =
             Maps.PMap.get b (Mem.mem_access m_after) ofs k)).

   Lemma strong_decay_implies_decay:
     forall m m',
       strong_decay m m' ->
       decay m m'.
   Proof.
     intros.
     intros b ofs.
     destruct (H b ofs);
       intros;
       now auto.
   Qed.

  Lemma decay_refl:
    forall m,
      decay m m.
  Proof.
    intros m b ofs.
    split; intros; first by exfalso.
    right; auto.
  Qed.

  Lemma decay_trans :
    forall m m' m'',
      (forall b, Mem.valid_block m b -> Mem.valid_block m' b) ->
      decay m m' ->
      decay m' m'' ->
      decay m m''.
  Proof.
    intros m m' m'' Hvblocks H H0.
    unfold decay in *.
    intros b ofs.
    specialize (H b ofs).
    specialize (H0 b ofs).
    destruct H, H0.
    split.
    - intros Hinvalid Hvalid''.
      destruct (valid_block_dec m' b) as [Hvalid' | Hinvalid'];
        eauto.
      specialize (H Hinvalid Hvalid').
      specialize (H2 Hvalid').
      destruct H2.
      right. intros k; destruct (H2 k); eauto.
      destruct H;
        [left | right]; intros k; specialize (H k);
        specialize (H2 k); rewrite <- H2; auto.
    - intros Hvalid.
      clear H.
      specialize (H1 Hvalid).
      specialize (Hvblocks _ Hvalid).
      specialize (H2 Hvblocks).
      destruct H2 as [H2 | H2], H1 as [H1 | H1].
      + left; intros k; destruct (H1 k); destruct (H2 k);
        eauto.
      + left; intros k; specialize (H1 k); destruct (H2 k);
        rewrite H1; eauto.
      + left; intros k; destruct (H1 k); specialize (H2 k);
        rewrite <- H2; eauto.
      + right; intros k; specialize (H1 k); specialize (H2 k);
        rewrite H1; rewrite H2; eauto.
  Qed.

  Definition permMapJoin (pmap1 pmap2 pmap3: access_map) :=
    forall b ofs,
      permjoin ((pmap1 !! b) ofs) ((pmap2 !! b) ofs) ((pmap3 !! b) ofs).

  Lemma permMapJoin_order:
    forall p1 p2 p3
      (Hjoin: permMapJoin p1 p2 p3),
    forall b ofs,
      Mem.perm_order'' (p3 !! b ofs) (p1 !! b ofs) /\
      Mem.perm_order'' (p3 !! b ofs) (p2 !! b ofs).
  Proof.
    intros.
    specialize (Hjoin b ofs);
      auto using permjoin_order.
  Qed.

  Lemma permMapLt_invalid_block:
    forall pmap m b ofs
      (Hlt: permMapLt pmap (getMaxPerm m))
      (Hinvalid: ~ Mem.valid_block m b),
      (pmap !! b ofs) = None.
  Proof.
    intros.
    apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
    specialize (Hlt b ofs).
    rewrite getMaxPerm_correct in Hlt.
    unfold permission_at in Hlt.
    rewrite Hinvalid in Hlt.
    simpl in Hlt. destruct (pmap !! b ofs);
                    [by exfalso | auto].
  Qed.

  Lemma perm_order_valid_block:
    forall pmap m b ofs p
      (Hperm: Mem.perm_order'' (pmap !! b ofs) (Some p))
      (Hlt: permMapLt pmap (getMaxPerm m)),
      Mem.valid_block m b.
  Proof.
    intros.
    destruct (valid_block_dec m b);
      auto.
    eapply permMapLt_invalid_block with (ofs := ofs) in n;
      eauto.
    rewrite n in Hperm.
    simpl in Hperm.
      by exfalso.
  Qed.

  Definition perm_order''_dec : forall (op op' : option permission),
      {Mem.perm_order'' op op'} + {~ Mem.perm_order'' op op'}.
  Proof.
    intros.
    destruct op, op'; simpl; auto.
    eapply Mem.perm_order_dec.
  Defined.

  Definition perm_eq_dec: forall (op op' : option permission),
      {op = op'} + {~ op = op'}.
  Proof.
    intros; destruct op as [op|], op' as [op'|]; simpl; auto;
    try (destruct op, op'); auto;
    right; intros Hcontra; discriminate.
  Defined.

End permMapDefs.

Require Import VST.concurrency.common.core_semantics.
Require Import compcert.lib.Coqlib.

Lemma storebytes_decay:
  forall m loc p vl m', Mem.storebytes m loc p vl = Some m' -> decay m m'.
Proof.
intros.
hnf; intros.
split; intros.
contradiction (Mem.storebytes_valid_block_2 _ _ _ _ _ H _ H1).
right.
intros.
rewrite (Mem.storebytes_access _ _ _ _ _ H); auto.
Qed.

Lemma alloc_decay:
  forall m lo hi m1 b1, Mem.alloc m lo hi = (m1,b1) -> decay m m1.
Proof.
intros.
hnf; intros.
split; intros.
destruct (eq_block b1 b).
subst.
destruct (Memory.range_dec lo ofs hi).
left.
intros.
Transparent Mem.alloc.
unfold Mem.alloc in H.
inv H.
simpl. rewrite PMap.gss.
destruct (zle lo ofs); try omega.
destruct (zlt ofs hi); try omega; auto.
right.
intros.
inv H; simpl.
rewrite PMap.gss.
destruct (zle lo ofs); try omega;
destruct (zlt ofs hi); try omega; auto.
contradiction H0.
pose proof (Mem.valid_block_alloc_inv _ _ _ _ _ H b H1).
destruct H2. subst. contradiction n; auto.
auto.
right.
intros.
assert (b1<>b).
intro. subst.
contradiction (Mem.fresh_block_alloc _ _ _ _ _ H).
destruct ((Mem.mem_access m1) !! b ofs k) eqn:?H.
destruct (semantics_lemmas.alloc_access_inv _ _ _ _ _ H _ _ _ _ H2).
destruct H3; congruence.
destruct H3; auto.
apply (semantics_lemmas.alloc_access_inv_None _ _ _ _ _ H _ _ _ H2).
Opaque Mem.alloc.
Qed.

Lemma free_decay: forall m b lo hi m', Mem.free m b lo hi = Some m' -> decay m m'.
Proof.
intros.
hnf; intros.
destruct (eq_block b b0).
subst b0.
split; intros.
contradiction H0.
eapply Mem.valid_block_free_2; eauto.
Transparent Mem.free.
unfold Mem.free in H.
if_tac in H; inv H.
destruct (Memory.range_dec lo ofs hi) as [?H|?H].
specialize (H1 _ H).
left.
intros.
hnf in H1.
destruct ((Mem.mem_access m) !! b ofs Cur) eqn:H2; try contradiction.
assert (p=Freeable) by (destruct p; inv H1; auto). subst p; clear H1.
split.
destruct k; auto.
pose proof (Mem.access_max m b ofs).
rewrite H2 in H1.
destruct ((Mem.mem_access m) !! b ofs Max); inv H1; auto.
simpl.
rewrite PMap.gss.
destruct (zle lo ofs); try omega.
destruct (zlt ofs hi); try omega.
simpl. auto.
right.
intros.
simpl.
rewrite PMap.gss.
destruct (zle lo ofs); destruct (zlt ofs hi); try omega; auto.
split.
intros.
contradiction H0.
eapply Mem.valid_block_free_2; eauto.
intros.
right.
intros.
unfold Mem.free in H.
destruct (Mem.range_perm_dec m b lo hi Cur Freeable).
inv H.
simpl.
rewrite PMap.gso; auto.
inv H.
Opaque Mem.free.
Qed.


Lemma msem_decay: 
  forall C (Sem: MemSem C) c m c' m',
   corestep (csem Sem)  c m c' m' ->
  decay m m'.
Proof.
  intros.
 apply corestep_mem in H.
 induction H.
 eapply storebytes_decay; eauto.
 eapply alloc_decay; eauto.
 revert m H; induction l; simpl; intros. inv H. apply decay_refl.
 destruct a as [[? ?] ?].
 destruct (Mem.free m b z z0) eqn:?; inv H.
 apply IHl in H1.
 apply decay_trans with m0; auto.
 eapply Mem.valid_block_free_1; eauto.
 eapply free_decay; eauto.
 apply decay_trans with m''; auto.
 apply semantics_lemmas.mem_step_nextblock' in H.
 apply semantics_lemmas.mem_step_nextblock' in H0.
 pose proof (Pos.le_trans _ _ _ H H0).
 intros.
 red in H2|-*.
  unfold Plt in *.
  eapply Pos.lt_le_trans; eauto.
Qed.

    
