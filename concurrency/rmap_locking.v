Require Import Coq.Strings.String.
Require Import Coq.ZArith.Zpower.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import msl.seplog.
Require Import veric.shares.
Require Import veric.compcert_rmaps.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.SeparationLogic.
Require Import veric.res_predicates.
Require Import veric.juicy_mem.
Require Import floyd.field_at.
Require Import floyd.reptype_lemmas.
Require Import sepcomp.Address.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import veric.coqlib4.
Require Import floyd.type_induction.
Require Import concurrency.permjoin.
Require Import concurrency.sync_preds_defs.
Require Import concurrency.semax_conc_pred.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

Lemma data_at_unfolding CS sh b ofs phi :
  readable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) 4 noattr) (Vptr b ofs)) phi ->
  forall loc,
    adr_range (b, Int.intval ofs) 4%Z loc ->
    exists p v,
      phi @ loc =
      YES sh p
        (VAL v) NoneP.
Proof.
  intros Readable [A [B wob]].
  destruct wob as (phi0 & phi123 & j0 & s0 & wob); simpl in *.
  destruct wob as (phi1 & phi23 & j1 & s1 & wob); simpl in *.
  destruct wob as (phi2 & phi3 & j2 & s2 & s3); simpl in *.
  rewrite seplog.sepcon_emp in s3.
  unfold mapsto_memory_block.at_offset in *.
  simpl in *.
  unfold nested_field_lemmas.nested_field_offset in *. simpl in *.
  unfold reptype_lemmas.unfold_reptype in *. simpl in *.
  unfold reptype_lemmas.default_val in *.
  simpl in *.
  unfold SeparationLogic.mapsto in *.
  simpl in *.
  unfold SeparationLogic.mapsto in *.
  if_tac in s3. 2:tauto.
  destruct s0 as [([], _) | (_, (v0, (vs0 & C0 & D0)))].
  destruct s1 as [([], _) | (_, (v1, (vs1 & C1 & D1)))].
  destruct s2 as [([], _) | (_, (v2, (vs2 & C2 & D2)))].
  destruct s3 as [([], _) | (_, (v3, (vs3 & C3 & D3)))].
  rewrite reptype_lemmas.int_add_repr_0_r in *. simpl in *.
  intros (b', ofs').
  specialize (D0 (b', ofs')).
  specialize (D1 (b', ofs')).
  specialize (D2 (b', ofs')).
  specialize (D3 (b', ofs')).
  simpl in *.
  intros (<-, range).
  destruct (adr_range_dec _ _ _) as [(_, a0) | n0] in D0; swap 1 2. {
    rewrite reptype_lemmas.int_add_repr_0_r in *. simpl in *.
    destruct n0. split; auto.
  }
  Local Ltac t ofs z :=
    exfalso;
    rewrite reptype_lemmas.int_add_repr_0_r in *; simpl in *;
    destruct (Int.unsigned_add_either ofs (Int.repr z)) as [R|R];
    [ rewrite Int.unsigned_repr_eq in *;
      unfold Z.modulo in *; simpl in *;
      omega
    | rewrite Int.unsigned_repr_eq in *;
      unfold Z.modulo in *; simpl in *;
      unfold Int.modulus, two_power_nat, Int.wordsize, Wordsize_32.wordsize in *;
      simpl in *; omega ].
  destruct (adr_range_dec _ _ _) as [(_, a1) | n1] in D1. t ofs 4%Z.
  destruct (adr_range_dec _ _ _) as [(_, a2) | n2] in D2. t ofs 8%Z.
  destruct (adr_range_dec _ _ _) as [(_, a3) | n3] in D3. t ofs 12%Z.
  apply resource_at_join with (loc := (b, ofs')) in j0.
  apply resource_at_join with (loc := (b, ofs')) in j1.
  apply resource_at_join with (loc := (b, ofs')) in j2.
  rewrite <-(@join_unit2_e resource _ _ _ _ _ D3 j2) in j1.
  rewrite <-(@join_unit2_e resource _ _ _ _ _ D2 j1) in j0.
  rewrite <-(@join_unit2_e resource _ _ _ _ _ D1 j0).
  destruct D0 as (p, ->). exists p.
  eexists.
  f_equal.
Qed.

Ltac app_pred_unfold :=
  match goal with
    H : context[app_pred (exist ?F ?f ?p) ?phi] |- _ =>
    change (app_pred (exist F f p) phi) with (f phi) in H; cbv beta in H
  | |- context[app_pred (exist ?F ?f ?p) ?phi] =>
    change (app_pred (exist F f p) phi) with (f phi); cbv beta
  end.

Lemma mapsto_unfold sh z b ofs phi loc :
  readable_share sh ->
  app_pred (mapsto sh (Tpointer Tvoid noattr) (offset_val (4 * z) (Vptr b ofs)) Vundef) phi ->
  if adr_range_dec (b, Int.unsigned (Int.add ofs (Int.repr (4 * z)))) 4%Z loc then
    exists p v,
      phi @ loc =
      YES sh p (VAL v) NoneP
  else
    identity (phi @ loc).
Proof.
  unfold mapsto.
  simpl (access_mode _).
  unfold type_is_volatile in *.
  if_tac. now intros _ [].
  unfold offset_val.
  if_tac. 2:tauto.
  intros _ [[[]] | [[] (v2 & bl & wob & Sat)]].
  specialize (Sat loc).
  unfold jam in *.
  app_pred_unfold.
  cbv beta in Sat.
  change (size_chunk Mint32) with 4%Z in Sat.
  if_tac.
  destruct Sat as (p & Sat). exists p.
  unfold yesat_raw in *.
  app_pred_unfold.
  rewrite Sat.
  eexists.
  f_equal.
  unfold NoneP; simpl.
  unfold "oo"; simpl.
  unfold noat in *.
  apply Sat.
Qed.

Lemma data_at_unfold_readable CS sh b ofs phi length :
  readable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) (Z.of_nat length) noattr) (Vptr b ofs)) phi ->
  forall loc,
    if adr_range_dec (b, Int.intval ofs) (4 * Z.of_nat length)%Z loc then
      exists p v,
        phi @ loc =
        YES
          sh p (VAL v) NoneP
    else
      identity (phi @ loc).
Proof.
  intros Readable.
  intros [(_ & _ & _ & _ & bound1 & bound2 & align & _) [_ H]].
  change (4 | Int.unsigned ofs) in align.
  replace _ with (4 * Z.of_nat length < Int.modulus)%Z in bound1 by (unfold sizeof; repeat f_equal; zify; omega).
  change (Int.unsigned ofs + 4 * Z.max 0 (Z.of_nat length) <= Int.modulus)%Z in bound2.
  replace _ with (Int.unsigned ofs + 4 * Z.of_nat length <= Int.modulus)%Z in bound2 by (f_equal; zify; omega).

  simpl in H.
  unfold mapsto_memory_block.at_offset in *.
  simpl in H.
  unfold reptype_lemmas.unfold_reptype in *.
  unfold reptype_lemmas.reptype in *.
  unfold reptype_lemmas.reptype_gen in *.
  simpl in H.
  unfold nested_field_lemmas.nested_field_type in *.
  simpl in H.
  unfold reptype_lemmas.default_val in *.
  simpl in H.
  unfold nested_field_lemmas.nested_field_offset in *.
  simpl in H.
  rewrite <-Zminus_0_l_reverse in H.
  assert (H' :
            app_pred
              (aggregate_pred.rangespec
                 0 (Z.to_nat (Z.of_nat length))
                 (fun (i : Z) (v : val) =>
                    SeparationLogic.mapsto
                      sh (Tpointer Tvoid noattr)
                      (expr.offset_val (4 * i)%Z v)
                      Vundef) (Vptr b (Int.add ofs (Int.repr 0)))) phi).
  {
    exact_eq H. repeat (f_equal || extensionality). rewrite Nat2Z.id; auto.
    unfold sublist.Znth. if_tac; auto.
    generalize (Z.to_nat (x - 0)).
    clear bound1 bound2.
    induction length; intros [|n]; simpl; auto.
  }

  clear H. revert H'.
  rewrite Nat2Z.id in *.
  rewrite int_add_repr_0_r in *.
  replace (Int.intval ofs) with (Int.intval (Int.add ofs (Int.repr (4 * 0))))
    by (rewrite int_add_repr_0_r; reflexivity).

  assert (bound3 : (Int.unsigned ofs + (4 * 0) + 4 * Z.of_nat length <= Int.modulus)%Z) by omega.
  remember 0%Z as z; assert (z0 : 0 <= z) by omega; clear Heqz.
  assert (RR : forall z,
             (match z with 0 => 0 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0 end = 4 * z)%Z)
    by reflexivity.

  assert (AA : forall P, (b = b /\ P) <-> P) by (intros; tauto).
  revert z z0 bound3 phi.
  induction length.
  - intros z z0 bound3 phi SAT (b', ofs'). simpl.
    if_tac.
    + simpl in *. omega.
    + apply resource_at_identity, SAT.
  - intros z z0 bound3 phi (phi1 & phi2 & j & SAT1 & SAT2) loc.
    specialize (IHlength ltac:(zify;omega)).
    specialize (IHlength ltac:(zify;omega)).
    specialize (IHlength (Z.succ z)).
    specialize (IHlength ltac:(zify;omega)).
    specialize (IHlength ltac:(zify;omega)).
    specialize (IHlength phi2 SAT2 loc).
    assert (E4 : 4 * z mod Int.modulus = (4 * z)). {
      rewrite Zdiv.Zmod_small; auto.
      split; try omega.
      change Int.modulus with 4294967296%Z in *.
      destruct (Int.size_interval_1 ofs).
      zify.
      omega.
    }
    if_tac.
    + if_tac in IHlength.
      * destruct IHlength as (p & v & E).
        exists p, v.
        apply resource_at_join with (loc := loc) in j.
        rewrite E in j.
        cut (identity (phi1 @ loc)).
        { intros I1. generalize (join_unit1_e _ _ I1 j).
          intros <-; reflexivity. }
        apply mapsto_unfold with (loc := loc) in SAT1; auto.
        if_tac in SAT1. 2:tauto.
        exfalso.
        clear -H0 H1 H AA bound1 bound2.
        destruct loc as (b', ofs').
        unfold adr_range in *.
        assert (b' = b) by intuition; subst b'.
        repeat rewrite AA in *.
        repeat rewrite RR in *.
        rewrite Z.mul_succ_r in *.
        remember (4 * z)%Z as a.
        change Int.intval with Int.unsigned in *.
        rewrite <-coqlib3.add_repr in *.
        rewrite <-Int.add_assoc in *.
        remember (Int.add ofs (Int.repr a)) as i; clear Heqi.
        destruct (Int.unsigned_add_either i (Int.repr 4)) as [E | E].
        -- rewrite E in *.
           rewrite Int.unsigned_repr_eq in *.
           change (4 mod Int.modulus)%Z with 4%Z in *.
           omega.
        -- rewrite E in *.
           rewrite Int.unsigned_repr_eq in *.
           change (4 mod Int.modulus)%Z with 4%Z in *.
           change Int.modulus with 4294967296%Z in *.
           unfold Z.div in *; simpl in bound1.
           zify.
           omega.
      * apply resource_at_join with (loc := loc) in j.
        pose proof (join_unit2_e _ _ IHlength j) as E.
        rewrite <-E in *. clear SAT2 E j IHlength.
        apply mapsto_unfold with (loc := loc) in SAT1; auto.
        if_tac in SAT1. auto.
        destruct loc as (b', ofs').
        unfold adr_range in *.
        exfalso.
        assert (b' = b) by intuition; subst b'.
        rewrite AA in *.
        replace (4 * Z.of_nat (S length))%Z with (4 + 4 * Z.of_nat length)%Z in *.
        2:simpl (Z.of_nat); zify; omega.
        replace (4 * Z.succ z)%Z with (4 + 4 * z)%Z in *.
        2:zify; omega.
        rewrite <-coqlib3.add_repr in *.
        rewrite <-Int.add_assoc in *.
        rewrite (Int.add_commut ofs) in H0.
        rewrite Int.add_assoc in *.
        remember (Int.add ofs (Int.repr (4 * z))) as a(* ; clear Heqa *).
        change Int.intval with Int.unsigned in *.
        rewrite Int.unsigned_add_carry in *.
        unfold Int.add_carry in *.
        rewrite Int.unsigned_repr_eq in *.
        change (4 mod Int.modulus)%Z with 4%Z in *.
        remember (Int.unsigned a) as c(* ; clear Heqc a *).
        if_tac [If|If] in H0.
        -- change (Int.unsigned Int.zero) with 0%Z in *.
           omega.
        -- subst c a.
           (* clear -If bound3. *)
           rewrite Int.unsigned_add_carry in *.
           unfold Int.add_carry in *.
           if_tac [If2|If2] in If.
           ++ change (Int.unsigned Int.zero) with 0%Z in *.
              change (Int.unsigned Int.one) with 1%Z in *.
              rewrite Int.unsigned_repr_eq in *.
              rewrite E4 in *.
              change Int.modulus with 4294967296%Z in *.
              omega.
           ++ change (Int.unsigned Int.zero) with 0%Z in *.
              change (Int.unsigned Int.one) with 1%Z in *.
              rewrite Int.unsigned_repr_eq in *.
              change Int.modulus with 4294967296%Z in *.
              omega.
    + apply mapsto_unfold with (loc := loc) in SAT1; auto.
      if_tac in SAT1.
      * exfalso.
        destruct loc as (b', ofs').
        unfold adr_range in *.
        assert (b' = b) by intuition; subst b'.
        rewrite AA in *.
        clear SAT1 IHlength SAT2 j phi2.
        rewrite Int.unsigned_add_carry in *.
        unfold Int.add_carry in *.
        rewrite Int.unsigned_repr_eq, E4 in *.
        if_tac in H0.
        -- change (Int.unsigned Int.zero) with 0%Z in *.
           change Int.modulus with 4294967296%Z in *.
           destruct (Int.size_interval_1 ofs).
           zify.
           omega.
        -- change (Int.unsigned Int.zero) with 0%Z in *.
           change Int.modulus with 4294967296%Z in *.
           destruct (Int.size_interval_1 ofs).
           zify.
           omega.
      * if_tac in IHlength.
        -- exfalso. clear SAT1 SAT2 phi phi1 phi2 IHlength j.
           destruct loc as (b', ofs').
           unfold adr_range in *.
           assert (b' = b) by intuition; subst b'.
           rewrite AA in *.
           replace (4 * Z.succ z)%Z with (4 + 4 * z)%Z in *.
           2:zify; omega.
           rewrite <-coqlib3.add_repr in *.
           rewrite <-Int.add_assoc in *.
           rewrite (Int.add_commut ofs) in H1.
           rewrite Int.add_assoc in *.
           remember (Int.add ofs (Int.repr (4 * z))) as a.
           change Int.intval with Int.unsigned in *.
           rewrite Int.unsigned_add_carry in *.
           unfold Int.add_carry in *.
           rewrite Int.unsigned_repr_eq in *.
           change (4 mod Int.modulus)%Z with 4%Z in *.
           remember (Int.unsigned a) as c.
           if_tac [If|If] in H1.
           ++ change (Int.unsigned Int.zero) with 0%Z in *.
              change Int.modulus with 4294967296%Z in *.
              zify.
              omega.
           ++ change (Int.unsigned Int.zero) with 0%Z in *.
              change (Int.unsigned Int.one) with 1%Z in *.
              change Int.modulus with 4294967296%Z in *.
              zify.
              subst a c.
              rewrite Int.unsigned_add_carry in *.
              unfold Int.add_carry in *.
              if_tac [If2|If2] in If.
              ** change (Int.unsigned Int.zero) with 0%Z in *.
                 change (Int.unsigned Int.one) with 1%Z in *.
                 rewrite Int.unsigned_repr_eq in *.
                 change Int.modulus with 4294967296%Z in *.
                 rewrite E4 in *.
                 omega.
              ** change (Int.unsigned Int.zero) with 0%Z in *.
                 change (Int.unsigned Int.one) with 1%Z in *.
                 rewrite Int.unsigned_repr_eq in *.
                 change Int.modulus with 4294967296%Z in *.
                 omega.
        -- apply resource_at_join with (loc := loc) in j.
           generalize (join_unit1_e _ _ SAT1 j).
           intros <-; auto.
Qed.

(*
Lemma writable_unique_right sh :
  writable_share sh ->
  forall p, mk_lifted (Share.unrel Share.Rsh sh) p = pfullshare.
Proof.
  intros Hw.
  unfold pfullshare.
  rewrite writable_share_right; auto.
  intros p; f_equal; apply proof_irr.
Qed.*)

Lemma data_at_unfold CS sh b ofs phi length :
  forall (Hw: writable_share sh),
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) (Z.of_nat length) noattr) (Vptr b ofs)) phi ->
  forall loc,
    if adr_range_dec (b, Int.intval ofs) (4 * Z.of_nat length)%Z loc then
      exists v, phi @ loc = YES sh (writable_readable_share Hw) (VAL v) NoneP
    else
      identity (phi @ loc).
Proof.
  intros Hw Hat.
  pose proof writable_readable_share Hw as Hr.
  pose proof data_at_unfold_readable _ _ _ _ _ _ Hr Hat as H.
  intros loc; spec H loc.
  if_tac; auto.
  destruct H as (p, H).
  exact_eq H; repeat (extensionality || f_equal).
  apply proof_irr.
Qed.

Lemma data_at_unfold_weak CS sh b ofs phi z z' loc :
  readable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) z noattr) (Vptr b ofs)) phi ->
  adr_range (b, Int.intval ofs) z' loc ->
  z' <= 4 * z ->
  exists p v,
    phi @ loc =
    YES
      sh p 
      (VAL v) NoneP.
Proof.
  intros R AT range L.
  pose proof data_at_unfold_readable CS sh b ofs phi (Z.to_nat z) R as H.
  assert (z0 : 0 <= z). {
    destruct AT as [(_ & bound & _) _].
    change ((0 <=? z) && true = true) in bound.
    apply Zle_bool_imp_le.
    destruct (0 <=? z); auto.
  }
  assert_specialize H. {
    intros.
    exact_eq AT; repeat f_equal.
    rewrite Coqlib.nat_of_Z_eq; omega.
  }
  specialize (H loc).
  if_tac [If|If] in H; auto.
  destruct If.
  destruct loc as (b', ofs'); clear -range z0 L.
  unfold adr_range in *.
  destruct range as (<- & A & B).
  split; auto.
  split; auto.
  rewrite Coqlib.nat_of_Z_eq; omega.
Qed.

Definition rmap_makelock phi phi' loc R length :=
  (level phi = level phi') /\
  (forall x, ~ adr_range loc length x -> phi @ x = phi' @ x) /\
  (forall x,
      adr_range loc length x ->
      exists val sh Psh,
        phi @ x = YES sh Psh (VAL val) NoneP /\
        writable_share sh /\
        phi' @ x =
        if eq_dec x loc then
          YES sh Psh (LK length) (pack_res_inv (approx (level phi) R))
        else
          YES sh Psh (CT (snd x - snd loc)) NoneP).

(* rmap_freelock phi phi' is ALMOST rmap_makelock phi' phi but we
specify that the VAL will be the dry memory's *)
Definition rmap_freelock phi phi' m loc R length :=
  (level phi = level phi') /\
  (forall x, ~ adr_range loc length x -> phi @ x = phi' @ x) /\
  (forall x,
      adr_range loc length x ->
      exists sh Psh,
        phi' @ x = YES sh Psh (VAL (contents_at m x)) NoneP /\
        writable_share sh /\
        phi @ x =
        if eq_dec x loc then
          YES sh Psh (LK length) (pack_res_inv (approx (level phi) R))
        else
          YES sh Psh (CT (snd x - snd loc)) NoneP).

Definition makelock_f phi loc R length : address -> resource :=
  fun x =>
    if adr_range_dec loc length x then
      match phi @ x with
      | YES sh sh' (VAL _) _ =>
        if eq_dec x loc then
          YES sh sh' (LK length) (pack_res_inv (approx (level phi) R))
        else
          YES sh sh' (CT (snd x - snd loc)) NoneP
      | YES _ _ _ _
      | PURE _ _
      | NO _ _ => NO Share.bot bot_unreadable
      end
    else
      phi @ x.

Definition freelock_f phi m loc length : address -> resource :=
  fun x =>
    if adr_range_dec loc length x then
      match phi @ x with
      | YES sh sh' (LK _) _ => YES sh sh' (VAL (contents_at m x)) NoneP
      | YES sh sh' (CT _) _ => YES sh sh' (VAL (contents_at m x)) NoneP
      | YES _ _ _ _
      | PURE _ _
      | NO _ _ => NO Share.bot bot_unreadable
      end
    else
      phi @ x.

Local Ltac pfulltac := try solve [exfalso; eapply join_pfullshare; eauto].

Lemma rmap_makelock_join phi1 phi1' loc R length phi2 phi :
  0 < length ->
  rmap_makelock phi1 phi1' loc R length ->
  join phi1 phi2 phi ->
  exists phi',
    rmap_makelock phi phi' loc R length /\
    join phi1' phi2 phi'.
Proof.
  intros Hpos (Hlev & Hsame & Hchanged) j.
  assert (L1 : level phi1 = level phi) by (eapply join_level; eauto).

  pose proof make_rmap (makelock_f phi loc R length) as Hphi'.

  (* the makelock_f function is valid *)
  assert_specialize Hphi'. {
    clear Hphi'.
    pose proof rmap_valid phi as V.
    unfold "oo", makelock_f in *.
    intros b ofs.
    pose proof j as j0.
    eapply resource_at_join with (loc := (b, ofs)) in j0.
    if_tac [r|nr].
    - destruct (Hchanged (b, ofs) r) as (val & sh & Rsh & E & Wsh & E').
      rewrite E in j0.
      inv j0; pfulltac.
      if_tac [e|ne].
      + simpl.
        intros i Hi.
        if_tac [ri|nri].
        * destruct (Hchanged (b, ofs + i) ri) as (vali & shi & Rshi & Ei & Wshi& Ei').
          pose proof j as ji.
          eapply resource_at_join with (loc := (b, ofs + i)) in ji.
          rewrite Ei in ji.
          inv ji; pfulltac.
          if_tac.
          -- assert (ofs = ofs + i) by congruence. omega.
          -- simpl. repeat f_equal; try omega.
             
             eapply join_readable_part; eauto.
        * destruct nri.
          subst loc; split; auto. omega.
      + simpl.
        destruct loc as (b', ofs').
        destruct r as (->, r). assert (ofs <> ofs') by congruence.
        exists length; split. simpl in *; omega.
        simpl.
        replace (ofs - (ofs - ofs')) with ofs' by omega.
        if_tac [r'|nr'].
        * spec Hchanged (b, ofs') r'.
          destruct Hchanged as (val' & sh' & Eq & Eq').
          pose proof j as j'.
          eapply resource_at_join with (loc := (b, ofs')) in j'.
          rewrite Eq in j'.
          inv j'; pfulltac.
          if_tac; tauto.
        * destruct nr'; split; auto.
          split; auto; omega.
    - spec V b ofs.
      destruct (phi @ (b, ofs)) as [t | t p [] p0 | k p] eqn:Ephi; simpl in V |- *; auto.
      + intros i ri. spec V i ri.
        if_tac [ri'|nri]; [ | easy ].
        exfalso.
        spec Hchanged (b, ofs + i) ri'.
        destruct Hchanged as (val & sh & E & E').
        pose proof j as ji.
        eapply resource_at_join with (loc := (b, ofs + i)) in ji.
        rewrite E in ji.
        revert V.
        inv ji; simpl; congruence.
      + if_tac [rz|nrz]; [ | easy ].
        exfalso.
        spec Hchanged (b, ofs - z) rz.
        destruct V as (?&?&V).
        destruct Hchanged as (?&?&?&?).
        pose proof j as jz.
        eapply resource_at_join with (loc := (b, ofs - z)) in jz.
        rewr (phi1 @ (b, ofs - z)) in jz.
        revert V.
        inv jz; simpl; congruence.
  }

  specialize (Hphi' (level phi1)).

  (* the makelock_f function is stable under approximation at level phi1 *)
  assert_specialize Hphi'. {
    pose proof approx_oo_approx as AA.
    unfold "oo", makelock_f in *.
    extensionality x.
    replace (level phi1) with (level phi); auto.
    pose proof resource_at_approx phi x.
    if_tac; [if_tac | ]; destruct (phi @ x) as [t | t p [] p0 | k p] eqn:E; auto.
    unfold pack_res_inv in *; simpl.
    do 2 f_equal.
    extensionality tt.
    etransitivity; swap 1 2.
    rewrite <-(AA (level phi)). reflexivity.
    reflexivity.
  }

  destruct Hphi' as (phi' & Hlev' & Ephi').
  exists phi'.

  (* the new rmap indeed joins *)
  assert (j' : join phi1' phi2 phi'). {
    apply resource_at_join2.
    - apply join_level in j. destruct j; congruence.
    - apply join_level in j. destruct j; congruence.
    - intros x; rewrite Ephi'.
      eapply resource_at_join with (loc := x) in j.
      unfold makelock_f.
      if_tac [r|nr].
      + spec Hchanged x r.
        destruct Hchanged as (val & sh & E & E').
        rewrite E in j. rewrite E'.
        rewrite L1 in *.
        if_tac [e|ne].
        * inv j.
          -- constructor. auto.
          -- exfalso; eapply join_pfullshare. eauto.
        * inv j.
          -- constructor. auto.
          -- exfalso; eapply join_pfullshare. eauto.
      + spec Hsame x nr.
        congruence.
  }

  split; auto.
  split. apply join_level in j. destruct j; congruence.
  split.
  + intros x nr. spec Hsame x nr.
    eapply resource_at_join with (loc := x) in j.
    eapply resource_at_join with (loc := x) in j'.
    eapply join_eq. apply j. rewrite <-Hsame in j'. eapply j'.
  + intros x r. spec Hchanged x r.
    destruct Hchanged as (val & sh & E & E').
    exists val.
    eapply resource_at_join with (loc := x) in j.
    eapply resource_at_join with (loc := x) in j'.
    rewrite E in j.
    rewrite E' in j'.
    rewrite L1 in *.
    if_tac [e|ne].
    * inv j; inv j'; try solve [exfalso; eapply join_pfullshare; eauto].
      eexists; split; f_equal.
      assert (rsh0 = rsh2) by congruence; subst.
      eapply join_eq; eauto.
    * inv j; inv j'; try solve [exfalso; eapply join_pfullshare; eauto].
      eexists; split; f_equal.
      assert (rsh0 = rsh2) by congruence; subst.
      eapply join_eq; eauto.
Qed.

Lemma rmap_freelock_join phi1 phi1' m loc R length phi2 phi :
  0 < length ->
  rmap_freelock phi1 phi1' m loc R length ->
  join phi1 phi2 phi ->
  exists phi',
    rmap_freelock phi phi' m loc R length /\
    join phi1' phi2 phi'.
Proof.
  intros Hpos (Hlev & Hsame & Hchanged) j.
  assert (L1 : level phi1 = level phi) by (eapply join_level; eauto).

  pose proof make_rmap (freelock_f phi m loc length) as Hphi'.

  (* the freelock_f function is valid *)
  assert_specialize Hphi'. {
    clear Hphi'.
    pose proof rmap_valid phi as V.
    pose proof rmap_valid phi as V'.
    unfold "oo", freelock_f in *.
    intros b ofs.
    pose proof j as j0.
    eapply resource_at_join with (loc := (b, ofs)) in j0.
    if_tac [r|nr].
    - destruct (Hchanged (b, ofs) r) as (sh & E' & E).
      rewrite E in j0.
      if_tac [e|ne] in E.
      + inv j0; pfulltac.
        constructor.
      + inv j0; pfulltac.
        constructor.
    - spec Hsame (b, ofs) nr.
      spec V b ofs.
      destruct (phi @ (b, ofs)) as [ ? | ? ? [ | | | ] | ] eqn:E1; simpl in *; auto.
      + intros i ii; spec V i ii.
        if_tac [ri|nri]; simpl; try congruence. exfalso.
        spec Hchanged (b, ofs + i) ri.
        destruct Hchanged as (sh & _ & Ei).
        if_tac in Ei.
        * subst loc.
          eapply resource_at_join with (loc := (b, ofs + i)) in j.
          rewr (phi1 @ (b, ofs + i)) in j.
          inv j; rewr (phi @ (b, ofs + i)) in V; simpl in V; congruence.
        * eapply resource_at_join with (loc := (b, ofs + i)) in j.
          rewr (phi1 @ (b, ofs + i)) in j.
          inv j; rewr (phi @ (b, ofs + i)) in V; simpl in V.
          -- destruct loc as (b', ofs'). destruct ri as [<- ri]. simpl in *.
             assert (Hi : ofs + i - ofs' = i) by congruence.
             assert (ofs' = ofs) by omega. subst ofs'.
             apply nr. split. auto. split. omega. omega.
          -- destruct loc as (b', ofs'). destruct ri as [<- ri]. simpl in *.
             assert (Hi : ofs + i - ofs' = i) by congruence.
             assert (ofs' = ofs) by omega. subst ofs'.
             apply nr. split. auto. split. omega. omega.
      + pose proof V as V''. destruct V'' as (n & rn & Ez). exists n; split; auto.
        if_tac [rz|nrz]; simpl; try congruence. exfalso.
        spec Hchanged (b, ofs - z) rz.
        destruct Hchanged as (sh & _ & Ei).
        if_tac in Ei.
        * subst loc. apply nr. split; auto. split. omega. cut (n = length). omega.
          eapply resource_at_join with (loc := (b, ofs - z)) in j.
          rewr (phi1 @ (b, ofs - z)) in j.
          inv j; destruct (phi @ (b, ofs - z)) as [ ? | ? ? [ | | | ] | ] eqn:E'; simpl in *; breakhyps.
        * eapply resource_at_join with (loc := (b, ofs - z)) in j.
          rewr (phi1 @ (b, ofs - z)) in j.
          destruct (phi @ (b, ofs - z)) as [ ? | ? ? [ | | | ] | ] eqn:E'; simpl in *; auto.
          all: inv j; simpl in *; breakhyps.
  }

  specialize (Hphi' (level phi1)).

  (* the freelock_f function is stable under approximation at level phi1 *)
  assert_specialize Hphi'. {
    pose proof approx_oo_approx as AA.
    unfold "oo", freelock_f in *.
    extensionality x.
    replace (level phi1) with (level phi); auto.
    pose proof resource_at_approx phi x.
    if_tac; destruct (phi @ x) as [t | t p [] p0 | k p] eqn:E; auto.
  }

  destruct Hphi' as (phi' & Hlev' & Ephi').
  exists phi'.

  (* the new rmap indeed joins *)
  assert (j' : join phi1' phi2 phi'). {
    apply resource_at_join2.
    - apply join_level in j. destruct j; congruence.
    - apply join_level in j. destruct j; congruence.
    - intros x; rewrite Ephi'.
      eapply resource_at_join with (loc := x) in j.
      unfold freelock_f.
      if_tac [r|nr].
      + spec Hchanged x r.
        destruct Hchanged as (sh & E' & E).
        rewrite E in j. rewrite E'.
        rewrite L1 in *.
        if_tac [e|ne] in E.
        * inv j.
          -- constructor. auto.
          -- exfalso; eapply join_pfullshare. eauto.
        * inv j.
          -- constructor. auto.
          -- exfalso; eapply join_pfullshare. eauto.
      + spec Hsame x nr.
        congruence.
  }

  split; auto.
  split. apply join_level in j. destruct j; congruence.
  split.
  + intros x nr. spec Hsame x nr.
    eapply resource_at_join with (loc := x) in j.
    eapply resource_at_join with (loc := x) in j'.
    eapply join_eq. apply j. rewrite <-Hsame in j'. eapply j'.
  + intros x r. spec Hchanged x r.
    destruct Hchanged as (sh & E' & E).
    eapply resource_at_join with (loc := x) in j.
    eapply resource_at_join with (loc := x) in j'.
    rewrite E in j.
    rewrite E' in j'.
    rewrite L1 in *.
    if_tac [e|ne].
    * inv j; inv j'; try solve [exfalso; eapply join_pfullshare; eauto].
      eexists; split; f_equal.
      eapply join_eq; eauto.
      assert (rsh0 = rsh2) by congruence; subst. auto.
    * inv j; inv j'; try solve [exfalso; eapply join_pfullshare; eauto].
      eexists; split; f_equal.
      assert (rsh0 = rsh2) by congruence; subst.
      eapply join_eq; eauto.
Qed.

(* TODO those definitions are also in sync_preds_defs, see if we can
include without changing the dep DAG too badly *)

(* The TT branch of the jam below might seem too weak, but we already
keep enough control over joining with other rmaps that it should be
enough *)

Definition LKspec_ext (R: pred rmap) lksize : spec :=
   fun (rsh sh: Share.t) (l: AV.address)  =>
    allp (jam (adr_range_dec l lksize)
              (jam (eq_dec l)
                   (yesat (SomeP rmaps.Mpred (fun _ => R)) (LK lksize) rsh sh)
                   (CTat l rsh sh))
              (fun _ => TT)).

Definition LK_at R lksize sh :=
  LKspec_ext R lksize (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh).

Lemma data_at_rmap_makelock CS sh b ofs R phi length :
  0 < length ->
  writable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) length noattr) (Vptr b ofs)) phi ->
  exists phi',
    rmap_makelock phi phi' (b, Int.unsigned ofs) R (4 * length) /\
    LK_at R (4 * length) sh (b, Int.unsigned ofs) phi'.
Proof.
  intros Hpos Hwritable Hat.
  destruct (Z_of_nat_complete length) as (n, Hn). omega.
  rewrite Hn in Hat.
  pose proof data_at_unfold _ _ _ _ _ _ Hwritable Hat as Hbefore.
  rewrite <-Hn in *. clear n Hn.

  pose proof make_rmap (makelock_f phi (b, Int.unsigned ofs) R (4 * length)) as Hphi'.

  assert_specialize Hphi'. {
    intros b' ofs'.
    remember (4 * length) as n.
    clear Hphi'.
    unfold "oo", makelock_f in *.
    change compcert_rmaps.R.AV.valid with AV.valid in *.
    change compcert_rmaps.R.res_option with res_option in *.
    change compcert_rmaps.R.resource_fmap with resource_fmap in *.
    change compcert_rmaps.R.resource_at with resource_at in *.
    change compcert_rmaps.R.approx with approx in *.
    (* pose proof Hbefore (b, Int.unsigned ofs) as E1. *)
    if_tac [r|nr].
    - pose proof Hbefore as E1.
      specialize (E1 (b', ofs')).
      if_tac in E1. 2:tauto.
      destruct E1 as (v, ->).
      if_tac [e|ne]; simpl.
      + intros i ri.
        injection e as -> ->.
        if_tac [?|nri].
        * specialize (Hbefore (b, Int.unsigned ofs + i)).
          if_tac in Hbefore. 2:tauto.
          destruct Hbefore as (v', ->).
          if_tac [ei|nei]; simpl; auto.
          -- injection ei as Ei. omega.
          -- repeat f_equal. omega.
        * exfalso.
          apply nri; split; auto.
          omega.
      + exists n. split.
        * unfold adr_range in *.
          destruct r as (<-, r).
          assert (ofs' <> Int.unsigned ofs) by congruence.
          omega.
        * unfold adr_range in *.
          destruct r as (<-, r).
          replace (ofs' - (ofs' - Int.unsigned ofs)) with (Int.unsigned ofs) by omega.
          specialize (Hbefore (b, Int.unsigned ofs)).
          unfold Int.unsigned in *.
          if_tac. 2:now range_tac.
          destruct Hbefore as (v', ->).
          if_tac; simpl. easy.
          congruence.
    - specialize (Hbefore (b', ofs')).
      if_tac in Hbefore.
      tauto.
      apply empty_NO in Hbefore.
      breakhyps; rewr (phi @ (b', ofs')); simpl; auto.
  }

  specialize (Hphi' (level phi)).

  assert_specialize Hphi'. {
    pose proof approx_oo_approx as AA.
    unfold "oo", makelock_f in *.
    extensionality x.
    pose proof resource_at_approx phi x.
    if_tac; [if_tac | ]; destruct (phi @ x) as [t | t p [] p0 | k p] eqn:E; auto.
    unfold pack_res_inv in *; simpl.
    do 2 f_equal.
    extensionality tt.
    etransitivity; swap 1 2.
    rewrite <-(AA (level phi)). reflexivity.
    reflexivity.
  }

  destruct Hphi' as (phi' & Hlev & Ephi').
  exists phi'.
  split.
  - split3.
    + auto.
    + rewrite Ephi'.
      intros x nr; unfold makelock_f.
      if_tac; tauto.
    + rewrite Ephi'.
      intros x r; unfold makelock_f.
      if_tac. 2:tauto.
      spec Hbefore x.
      if_tac in Hbefore. 2:tauto.
      destruct Hbefore as (val & ->).
      exists val, (Share.unrel Share.Lsh sh).
      split; reflexivity.
  - intros x.
    remember (4 * length) as n.
    simpl.
    unfold Int.unsigned in *.
    specialize (Hbefore x).
    rewrite Ephi'. unfold makelock_f.
    if_tac. 2:easy.
    destruct Hbefore as (v, ->).
    if_tac; subst.
    + eexists.
      if_tac. 2:tauto.
      f_equal.
      symmetry.
      apply writable_unique_right, Hwritable.
      unfold pack_res_inv in *.
      f_equal. extensionality. f_equal. auto.
    + eexists.
      if_tac. congruence.
      f_equal.
      symmetry.
      apply writable_unique_right, Hwritable.
      Unshelve. all:rewrite <-readable_share_unrel_Rsh; apply writable_readable_share; auto.
Qed.

Lemma nat_of_Z_nonzero z n: n <> O -> nat_of_Z z = n -> z = Z.of_nat n.
Proof.
  intros nz <-.
  symmetry; apply Coqlib.nat_of_Z_eq. unfold Z.ge.
  destruct z; simpl in *; congruence.
Qed.

Lemma lock_inv_rmap_freelock CS sh b ofs R phi m :
  (4 | Int.unsigned ofs) ->
  Int.unsigned ofs + 4 <= Int.modulus ->
  writable_share sh ->
  app_pred (@lock_inv sh (Vptr b ofs) R) phi ->
  exists phi',
    rmap_freelock phi phi' m (b, Int.unsigned ofs) R 4 /\
    app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) 1 noattr) (Vptr b ofs)) phi'.
Proof.
  intros Halign Hbound Hwritable Hli.
  destruct Hli as (? & ? & E & Hli). injection E as <- <- .

  pose proof make_rmap (freelock_f phi m (b, Int.unsigned ofs) 4) as Hphi'.

  assert_specialize Hphi'. {
    intros b' ofs'.
    clear Hphi'.
    unfold "oo", freelock_f in *.
    change compcert_rmaps.R.AV.valid with AV.valid in *.
    change compcert_rmaps.R.res_option with res_option in *.
    change compcert_rmaps.R.resource_fmap with resource_fmap in *.
    change compcert_rmaps.R.resource_at with resource_at in *.
    change compcert_rmaps.R.approx with approx in *.
    (* pose proof Hbefore (b, Int.unsigned ofs) as E1. *)
    if_tac [r|nr].
    - pose proof Hli as E1.
      unfold lock_inv in *.
      specialize (E1 (b', ofs')). simpl in E1.
      if_tac in E1. 2:tauto.
      if_tac [e|ne] in E1; destruct E1 as (p, ->); constructor.
    - spec Hli (b', ofs'). simpl in Hli.
      if_tac [r'|nr'] in Hli. tauto.
      apply identity_NO in Hli.
      destruct Hli as [-> | (? & ? & ->)]; simpl; constructor.
  }

  specialize (Hphi' (level phi)).

  assert_specialize Hphi'. {
    pose proof approx_oo_approx as AA.
    unfold "oo", freelock_f in *.
    extensionality x.
    pose proof resource_at_approx phi x.
    repeat if_tac; destruct (phi @ x) as [t | t p [] p0 | k p] eqn:E; auto.
  }

  destruct Hphi' as (phi' & Hlev & Ephi').
  exists phi'.
  split.
  - split3.
    + auto.
    + rewrite Ephi'.
      intros x nr; unfold freelock_f.
      if_tac; tauto.
    + rewrite Ephi'.
      intros x r; unfold freelock_f.
      if_tac. 2:tauto.
      spec Hli x. simpl in Hli.
      if_tac in Hli. 2:tauto.
      if_tac in Hli; destruct Hli as (p, ->); simpl.
      * exists (Share.unrel Share.Lsh sh); split; f_equal.
        -- apply writable_unique_right, Hwritable.
        -- if_tac; f_equal; try apply writable_unique_right, Hwritable; try congruence.
      * exists (Share.unrel Share.Lsh sh); split; f_equal.
        -- apply writable_unique_right, Hwritable.
        -- if_tac; f_equal; try apply writable_unique_right, Hwritable; try congruence.
  - split; [repeat split|]. assumption. assumption.
    split. reflexivity. simpl. rewrite seplog.sepcon_emp.
    unfold mapsto_memory_block.at_offset in *.
    simpl.
    rewrite int_add_repr_0_r.
    change (app_pred (mapsto sh (Tpointer Tvoid noattr) (Vptr b (Int.add ofs (Int.repr 0))) Vundef) phi').
    rewrite int_add_repr_0_r.
    unfold mapsto in *; simpl.
    pose proof writable_readable_share Hwritable as Hr.
    if_tac. 2:tauto. right. split; [reflexivity|].
    eexists _, (_ :: _ :: _ :: _ :: nil); split.
    { repeat split; assumption. }
    intros x. spec Hli x. simpl in *. unfold lksize.LKSIZE in *.
    rewrite Ephi'. unfold freelock_f.
    if_tac [r|nr]. 2:assumption.
    rewrite writable_share_right; auto. exists top_share_nonunit.
    if_tac [<-|ne] in Hli.
    * destruct Hli as (p & ->). f_equal. now apply writable_unique_right; auto.
      simpl.
      replace (Int.unsigned ofs - Int.unsigned ofs) with 0 by omega; simpl.
      reflexivity.
    * destruct Hli as (p & ->). f_equal. now apply writable_unique_right; auto.
      destruct x as (b', ox); simpl in r; destruct r as (<-, r); simpl.
      assert (A : forall a b c, a - b = c -> a = b + c) by (intros; omega).
      destruct (nat_of_Z (ox - Int.unsigned ofs)) as [|[|[|[|[|]]]]] eqn:Ez; auto.
      { apply juicy_mem_lemmas.Zminus_lem in Ez. subst ox; auto. apply r. }
      all: apply nat_of_Z_nonzero in Ez; auto; apply A in Ez; subst ox.
      all: try reflexivity.
      -- simpl in r; omega.
      -- simpl in r; zify; omega.
Qed.

Lemma rmap_makelock_unique phi phi1 phi2 loc R len :
  rmap_makelock phi phi1 loc R len ->
  rmap_makelock phi phi2 loc R len ->
  phi1 = phi2.
Proof.
  intros (L1 & out1 & in1) (L2 & out2 & in2).
  apply rmap_ext. congruence.
  intros x.
  destruct (adr_range_dec loc len x) as [r | nr].
  - spec in1 x r. spec in2 x r. if_tac in in1; breakhyps.
  - spec out1 x nr. spec out2 x nr. congruence.
Qed.

Lemma rmap_freelock_unique phi phi1 phi2 m loc R len :
  rmap_freelock phi phi1 m loc R len ->
  rmap_freelock phi phi2 m loc R len ->
  phi1 = phi2.
Proof.
  intros (L1 & out1 & in1) (L2 & out2 & in2).
  apply rmap_ext. congruence.
  intros x.
  destruct (adr_range_dec loc len x) as [r | nr].
  - spec in1 x r. spec in2 x r. if_tac in in1; breakhyps.
  - spec out1 x nr. spec out2 x nr. congruence.
Qed.

Definition pures_same phi1 phi2 := forall loc k pp, phi1 @ loc = PURE k pp <-> phi2 @ loc = PURE k pp.

Lemma rmap_freelock_pures_same phi phi' m loc R length :
  rmap_freelock phi phi' m loc R length ->
  pures_same phi phi'.
Proof.
  intros (lev & before & after); intros l.
  destruct (adr_range_dec loc length l) as  [r|n].
  - spec after l r. destruct after as (sh & -> & ->). if_tac; intros; split; congruence.
  - spec before l n. rewrite before. tauto.
Qed.

Lemma rmap_makelock_pures_same phi phi' loc R length :
  rmap_makelock phi phi' loc R length ->
  pures_same phi phi'.
Proof.
  intros (lev & before & after); intros l.
  destruct (adr_range_dec loc length l) as  [r|n].
  - spec after l r. destruct after as (val & sh & -> & ->). if_tac; intros; split; congruence.
  - spec before l n. rewrite before. tauto.
Qed.

Require Import veric.juicy_mem.

Definition noyes phi := forall x sh rsh k pp, phi @ x <> YES sh rsh k pp.

Definition getYES_aux (phi : rmap) (loc : address) : resource :=
  match phi @ loc with
    YES sh rsh k pp => YES Share.bot rsh k pp
  | NO sh => NO Share.bot
  | PURE k pp => PURE k pp
  end.

Definition getNO_aux (phi : rmap) (loc : address) : resource :=
  match phi @ loc with
    YES sh rsh k pp => NO sh
  | NO sh => NO sh
  | PURE k pp => PURE k pp
  end.

Program Definition getYES (phi : rmap) := proj1_sig (make_rmap (getYES_aux phi) _ (level phi) _).
Next Obligation.
  intros phi.
  pose proof juicy_mem.phi_valid phi as V.
  intros b ofs. spec V b ofs.
  unfold getYES_aux, "oo" in *.
  destruct (phi @ _); simpl in *; auto.
  destruct k; auto.
  - intros i ri; spec V i ri. destruct (phi @ _); auto.
  - destruct (phi @ _); auto.
Qed.
Next Obligation.
  intros phi.
  pose proof resource_at_approx phi as V.
  extensionality l. spec V l.
  unfold getYES_aux, "oo" in *.
  destruct (phi @ _); simpl in *; auto.
  congruence.
Qed.

Program Definition getNO (phi : rmap) := proj1_sig (make_rmap (getNO_aux phi) _ (level phi) _).
Next Obligation.
  intros phi.
  pose proof juicy_mem.phi_valid phi as V.
  intros b ofs. spec V b ofs.
  unfold getNO_aux, "oo" in *.
  destruct (phi @ _); simpl in *; auto.
Qed.
Next Obligation.
  intros phi.
  pose proof resource_at_approx phi as V.
  extensionality l. spec V l.
  unfold getNO_aux, "oo" in *.
  destruct (phi @ _); simpl in *; auto.
Qed.

Lemma getYES_getNO_join phi : join (getYES phi) (getNO phi) phi.
Proof.
  apply resource_at_join2; try apply level_make_rmap.
  unfold getYES, getNO; do 2 rewrite resource_at_make_rmap.
  unfold getYES_aux, getNO_aux; intros loc.
  destruct (phi @ loc); constructor; apply bot_join_eq.
Qed.

Lemma noyes_getNO phi : noyes (getNO phi).
Proof.
  intros l.
  unfold getNO; rewrite resource_at_make_rmap; unfold getNO_aux.
  destruct (phi @ _); congruence.
Qed.

Section simpler_invariant_tentative.

(* This section about getYES and getNO is currently unused.  Maybe
it would give us a simpler invariant, but maybe not. *)

Variable unrel_lsh_rsh : Share.unrel Share.Lsh Share.Rsh = Share.bot.

Lemma mapsto_getYES sh t v v' phi :
  writable_share sh ->
  app_pred (mapsto sh t v v') phi ->
  app_pred (mapsto Share.Rsh t v v') (getYES phi).
Proof.
  intros Hw At. pose proof writable_readable_share Hw as Hr.
  assert (Hw' : writable_share Share.Rsh). {
    apply writable_Rsh.
  }
  assert (Hr' : readable_share Share.Rsh)
    by (apply writable_readable_share; auto).
  cut
    (forall m v loc,
        (address_mapsto m v (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) loc) phi ->
        (address_mapsto m v (Share.unrel Share.Lsh Share.Rsh) (Share.unrel Share.Rsh Share.Rsh) loc) (getYES phi)).
  { intros CUT.
    unfold mapsto in *; destruct (access_mode t);
      repeat if_tac;
      repeat if_tac in At; eauto; destruct v; eauto; try tauto.
    destruct At as [[? At]|[? At]]; [left|right]; split; try assumption.
    - apply CUT; auto.
    - destruct At. eexists. apply CUT; eauto. }
  clear v v' At. intros m v loc M.
  unfold address_mapsto in *.
  destruct M as (bl & I & M); exists bl; split; auto.
  intros x; spec M x.
  simpl in *.
  if_tac.
  - destruct M as (p, M).
    unfold getYES, getYES_aux in *.
    rewrite resource_at_make_rmap.
    destruct (phi @ x); try congruence.
    injection M as -> -> -> ->.
    assert (p' : nonunit (Share.unrel Share.Rsh Share.Rsh)). {
      rewrite writable_share_right; auto.
      apply top_share_nonunit.
    }
    exists p'; f_equal.
    + rewrite unrel_lsh_rsh; reflexivity.
    + pose proof writable_share_right Hw as R.
      assert (R': Share.unrel Share.Rsh Share.Rsh = Share.top).
      { apply writable_share_right. auto. }
      revert p p' R R'.
      generalize (Share.unrel Share.Rsh sh).
      generalize (Share.unrel Share.Rsh Share.Rsh).
      intros ? ? ? ? -> ->; f_equal; apply proof_irr.
  - apply empty_NO in M.
    unfold getYES, getYES_aux in *.
    rewrite resource_at_make_rmap.
    destruct M as [-> | (k & pp & ->)].
    + apply NO_identity.
    + apply PURE_identity.
Qed.

Lemma memory_block_getYES sh z v phi :
  writable_share sh ->
  app_pred (memory_block sh z v) phi ->
  app_pred (memory_block Share.Rsh z v) (getYES phi).
Proof.
  intros Hw At. pose proof writable_readable_share Hw as Hr.
  assert (Hr' : readable_share Share.Rsh) by (apply writable_readable_share, writable_Rsh).
  Transparent memory_block.
  unfold memory_block in *. destruct v; auto.
  unfold mapsto_memory_block.memory_block' in *.
Abort.

Lemma field_at_getYES CS sh t gfs v v' phi :
  writable_share sh ->
  app_pred (@field_at CS sh t gfs v v') phi ->
  app_pred (@field_at CS Share.Rsh t gfs v v') (getYES phi).
Proof.
  intros Hw At.
  destruct At as (A, B). split. apply A.
  unfold mapsto_memory_block.at_offset in *.
  unfold data_at_rec_lemmas.data_at_rec in *.
  simpl.
  destruct (nested_field_lemmas.nested_field_type t gfs); simpl in *; repeat if_tac.
  all: try (eapply mapsto_getYES; eauto).
  all: try (eapply memory_block_getYES; eauto).
Abort.

End simpler_invariant_tentative.