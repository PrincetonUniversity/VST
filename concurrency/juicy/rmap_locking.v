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

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.veric.shares.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.res_predicates.
Require Import VST.veric.juicy_mem.
Require Import VST.floyd.field_at.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.sepcomp.Address.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.coqlib4.
Require Import VST.floyd.type_induction.
(*Require Import VST.concurrency.permjoin.*)
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.common.lksize.

Require Import Setoid.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

Lemma data_at_unfolding CS sh b ofs phi :
  readable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) 4 noattr) (Vptr b ofs)) phi ->
  forall loc,
    adr_range (b, Ptrofs.intval ofs) 4%Z loc ->
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
  destruct s0 as [([], _) | (_, (v0, (vs0 & (C0 & D0) & G0)))].
  destruct s1 as [([], _) | (_, (v1, (vs1 & (C1 & D1) & G1)))].
  destruct s2 as [([], _) | (_, (v2, (vs2 & (C2 & D2) & G2)))].
  destruct s3 as [([], _) | (_, (v3, (vs3 & (C3 & D3) & G3)))].
  rewrite reptype_lemmas.ptrofs_add_repr_0_r in *. simpl in *.
  intros (b', ofs').
  specialize (D0 (b', ofs')).
  specialize (D1 (b', ofs')).
  specialize (D2 (b', ofs')).
  specialize (D3 (b', ofs')).
  simpl in *.
  intros (<-, range).
  destruct (adr_range_dec _ _ _) as [(_, a0) | n0] in D0; swap 1 2. {
    rewrite reptype_lemmas.ptrofs_add_repr_0_r in *. simpl in *.
    destruct n0. split; auto.
  }
  Local Ltac t ofs z :=
    exfalso;
    rewrite reptype_lemmas.ptrofs_add_repr_0_r in *;
    destruct (Ptrofs.unsigned_add_either ofs (Ptrofs.repr z)) as [R|R];
    rewrite Ptrofs.unsigned_repr_eq in *;
    unfold Z.modulo in *; simpl in *;
    unfold Ptrofs.modulus, two_power_nat, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize,
      size_chunk, Mptr in *;
    destruct Archi.ptr64; simpl in *; omega.
  destruct (adr_range_dec _ _ _) as [(_, a1) | n1] in D1. t ofs (if Archi.ptr64 then 8 else 4).
  destruct (adr_range_dec _ _ _) as [(_, a2) | n2] in D2. t ofs (if Archi.ptr64 then 16 else 8).
  destruct (adr_range_dec _ _ _) as [(_, a3) | n3] in D3. t ofs (if Archi.ptr64 then 24 else 12).
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
  app_pred (mapsto sh (Tpointer Tvoid noattr) (offset_val (size_chunk Mptr * z) (Vptr b ofs)) Vundef) phi ->
  if adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (size_chunk Mptr * z)))) (size_chunk Mptr) loc then
    exists p v,
      phi @ loc =
      YES sh p (VAL v) NoneP
  else
    identity (phi @ loc).
Proof.
  unfold mapsto.
  simpl (access_mode _).
  unfold type_is_volatile in *.
  simple_if_tac. now intros _ [].
  unfold offset_val.
  if_tac. 2:tauto.
  intros _ [[[]] | [[] (v2 & bl & (wob & Sat) & _)]].
  specialize (Sat loc).
  unfold jam in *.
  app_pred_unfold.
  cbv beta in Sat.
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
    if adr_range_dec (b, Ptrofs.intval ofs) (size_chunk Mptr * Z.of_nat length)%Z loc then
      exists p v,
        phi @ loc =
        YES
          sh p (VAL v) NoneP
    else
      identity (phi @ loc).
Proof.
  intros Readable.
  intros [(_ & _ & bound & align & _) [_ H]].
  unfold size_compatible, sizeof in bound.
  rewrite <- size_chunk_Mptr in bound.
  simpl in H.
  unfold mapsto_memory_block.at_offset in *.
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
  rewrite Z.max_r in * by omega.
  assert (H' :
            app_pred
              (aggregate_pred.rangespec
                 0 (Z.to_nat (Z.of_nat length))
                 (fun (i : Z) (v : val) =>
                    SeparationLogic.mapsto
                      sh (Tpointer Tvoid noattr)
                      (offset_val (size_chunk Mptr * i)%Z v)
                      Vundef) (Vptr b (Ptrofs.add ofs (Ptrofs.repr 0)))) phi).
  {
    exact_eq H. repeat (f_equal || extensionality).
    unfold sublist.Znth. if_tac; auto.
    apply data_at_rec_lemmas.nth_list_repeat.
  }

  clear H. revert H'.
  rewrite Nat2Z.id in *.
  rewrite ptrofs_add_repr_0_r in *.
  replace (Ptrofs.intval ofs) with (Ptrofs.intval (Ptrofs.add ofs (Ptrofs.repr (size_chunk Mptr * 0))))
    by (rewrite ptrofs_add_repr_0_r; reflexivity).

  assert (bound3 : (Ptrofs.unsigned ofs + (size_chunk Mptr * 0) + size_chunk Mptr * Z.of_nat length <= Ptrofs.modulus)%Z) by omega.

  remember 0%Z as z; assert (z0 : 0 <= z) by omega; clear Heqz.
  assert (RR : forall z,
             (match z with 0 => 0 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0 end = size_chunk Mptr * z)%Z)
    by reflexivity.

  assert (AA : forall P, (b = b /\ P) <-> P) by (intros; tauto).
  revert z z0 bound3 phi.
  induction length.
  - intros z z0 bound3 phi SAT (b', ofs'). simpl.
    if_tac.
    + simpl in *. omega.
    + apply resource_at_identity, SAT.
  - rewrite Nat2Z.inj_succ in *.
    intros z z0 bound3 phi (phi1 & phi2 & j & SAT1 & SAT2) loc.
    inv align; try discriminate.
    rename H3 into align.
    pose proof (size_chunk_pos Mptr) as Hpos.
    spec IHlength.
    { rewrite size_chunk_Mptr in *; simple_if_tac; omega. }
    spec IHlength.
    { constructor; intros; apply align; omega. }
    specialize (IHlength (Z.succ z)).
    specialize (IHlength ltac:(omega)).
    spec IHlength.
    { rewrite size_chunk_Mptr in *; simple_if_tac; omega. }
    specialize (IHlength phi2 SAT2 loc).
    assert (E4 : size_chunk Mptr * z mod Ptrofs.modulus = (size_chunk Mptr * z)). {
      apply Zmod_small.
      split; [rewrite size_chunk_Mptr; simple_if_tac; omega|].
      pose proof (Ptrofs.unsigned_range ofs).
      rewrite size_chunk_Mptr in *; simple_if_tac; omega.
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
        clear -H0 H1 H AA bound.
        destruct loc as (b', ofs').
        unfold adr_range in *.
        assert (b' = b) by intuition; subst b'.
        repeat rewrite AA in *.
        repeat rewrite RR in *.
        rewrite Z.mul_succ_r in *.
        remember (size_chunk Mptr * z)%Z as a.
        change Ptrofs.intval with Ptrofs.unsigned in *.
        rewrite <-coqlib3.ptrofs_add_repr in *.
        rewrite <-Ptrofs.add_assoc in *.
        remember (Ptrofs.add ofs (Ptrofs.repr a)) as i; clear Heqi.
        destruct (Ptrofs.unsigned_add_either i (Ptrofs.repr (size_chunk Mptr))) as [E | E].
        -- rewrite E in *.
           rewrite Ptrofs.unsigned_repr_eq in *.
           change (size_chunk Mptr mod Ptrofs.modulus)%Z with (size_chunk Mptr) in *.
           omega.
        -- rewrite E in *.
           rewrite Ptrofs.unsigned_repr_eq in *.
           change (size_chunk Mptr mod Ptrofs.modulus)%Z with (size_chunk Mptr) in *.
           pose proof (Ptrofs.unsigned_range ofs); omega.
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
        replace (size_chunk Mptr * Z.of_nat (S length))%Z with (size_chunk Mptr + size_chunk Mptr * Z.of_nat length)%Z in *.
        2:simpl (Z.of_nat); zify; unfold size_chunk, Mptr; simple_if_tac; omega.
        replace (size_chunk Mptr * Z.succ z)%Z with (size_chunk Mptr + size_chunk Mptr * z)%Z in *.
        2:zify; unfold size_chunk, Mptr; simple_if_tac; omega.
        rewrite <-coqlib3.ptrofs_add_repr in *.
        rewrite <-Ptrofs.add_assoc in *.
        rewrite (Ptrofs.add_commut ofs) in H0.
        rewrite Ptrofs.add_assoc in *.
        remember (Ptrofs.add ofs (Ptrofs.repr (size_chunk Mptr * z))) as a(* ; clear Heqa *).
        change Ptrofs.intval with Ptrofs.unsigned in *.
        rewrite Ptrofs.unsigned_add_carry in *.
        unfold Ptrofs.add_carry in *.
        rewrite Ptrofs.unsigned_repr_eq in *.
        change (size_chunk Mptr mod Ptrofs.modulus)%Z with (size_chunk Mptr) in *.
        remember (Ptrofs.unsigned a) as c(* ; clear Heqc a *).
        if_tac [If|If] in H0.
        -- change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in *.
           unfold size_chunk, Mptr in *; destruct Archi.ptr64; omega.
        -- subst c a.
           (* clear -If bound3. *)
           rewrite Ptrofs.unsigned_add_carry in *.
           unfold Ptrofs.add_carry in *.
           if_tac [If2|If2] in If.
           ++ change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in *.
              rewrite Ptrofs.unsigned_repr_eq in *.
              omega.
           ++ change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in *.
              change (Ptrofs.unsigned Ptrofs.one) with 1%Z in *.
              rewrite Ptrofs.unsigned_repr_eq in *.
              omega.
    + apply mapsto_unfold with (loc := loc) in SAT1; auto.
      if_tac in SAT1.
      * exfalso.
        destruct loc as (b', ofs').
        unfold adr_range in *.
        assert (b' = b) by intuition; subst b'.
        rewrite AA in *.
        clear SAT1 IHlength SAT2 j phi2.
        rewrite Ptrofs.unsigned_add_carry in *.
        unfold Ptrofs.add_carry in *.
        rewrite Ptrofs.unsigned_repr_eq, E4 in *.
        assert (0 <= size_chunk Mptr * Z.of_nat length) by (apply Z.mul_nonneg_nonneg; omega).
        rewrite Z.mul_succ_r in *.
        if_tac in H0; omega.
      * if_tac in IHlength.
        -- exfalso. clear SAT1 SAT2 phi phi1 phi2 IHlength j.
           destruct loc as (b', ofs').
           unfold adr_range in *.
           assert (b' = b) by intuition; subst b'.
           rewrite AA in *.
           replace (size_chunk Mptr * Z.succ z)%Z with (size_chunk Mptr + size_chunk Mptr * z)%Z in *.
           2:zify; unfold size_chunk, Mptr; simple_if_tac; omega.
           rewrite <-coqlib3.ptrofs_add_repr in *.
           rewrite <-Ptrofs.add_assoc in *.
           rewrite (Ptrofs.add_commut ofs) in H1.
           rewrite Ptrofs.add_assoc in *.
           remember (Ptrofs.add ofs (Ptrofs.repr (size_chunk Mptr * z))) as a.
           change Ptrofs.intval with Ptrofs.unsigned in *.
           rewrite Ptrofs.unsigned_add_carry in *.
           unfold Ptrofs.add_carry in *.
           rewrite Ptrofs.unsigned_repr_eq in *.
           change (size_chunk Mptr mod Ptrofs.modulus)%Z with (size_chunk Mptr) in *.
           remember (Ptrofs.unsigned a) as c.
           if_tac [If|If] in H1.
           ++ change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in *.
              unfold size_chunk, Mptr in *; destruct Archi.ptr64; omega.
           ++ subst a c.
              rewrite Ptrofs.unsigned_add_carry in *.
              unfold Ptrofs.add_carry in *.
              assert (0 <= size_chunk Mptr * Z.of_nat length) by (apply Z.mul_nonneg_nonneg; omega).
              rewrite Z.mul_succ_r in *.
              if_tac [If2|If2] in If.
              ** change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in *.
                 change (Ptrofs.unsigned Ptrofs.one) with 1%Z in *.
                 rewrite Ptrofs.unsigned_repr_eq in *.
                 omega.
              ** change (Ptrofs.unsigned Ptrofs.zero) with 0%Z in *.
                 change (Ptrofs.unsigned Ptrofs.one) with 1%Z in *.
                 rewrite Ptrofs.unsigned_repr_eq in *.
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
    if adr_range_dec (b, Ptrofs.intval ofs) (size_chunk Mptr * Z.of_nat length)%Z loc then
      exists v, phi @ loc = YES sh (writable_readable_share Hw) (VAL v) NoneP
    else
      identity (phi @ loc).
Proof.
  intros Hw Hat.
  pose proof writable_readable_share Hw as Hr.
  pose proof data_at_unfold_readable _ _ _ _ _ _ Hr Hat as H.
  intros loc; specialize (H loc).
  if_tac; auto.
  destruct H as (p, H).
  exact_eq H; repeat (extensionality || f_equal).
  apply proof_irr.
Qed.

Lemma data_at_unfold_weak CS sh b ofs phi z z' loc :
  readable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) z noattr) (Vptr b ofs)) phi ->
  adr_range (b, Ptrofs.intval ofs) z' loc ->
  z' <= size_chunk Mptr * z ->
  exists p v,
    phi @ loc =
    YES
      sh p 
      (VAL v) NoneP.
Proof.
  intros R AT range L.
  pose proof data_at_unfold_readable CS sh b ofs phi (Z.to_nat z) R as H.
  assert (z0 : 0 <= z). {
    destruct loc; simpl in range.
    assert (0 <= z') by omega.
    pose proof (size_chunk_pos Mptr).
    eapply Zmult_le_0_reg_r; eauto.
    rewrite Z.mul_comm; omega.
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

Lemma data_at_noghost CS sh b ofs phi :
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) 2 noattr) (Vptr b ofs)) phi ->
  noghost phi.
Proof.
  intros Hw; simpl in *.
  destruct Hw as (_ & _ & ? & ? & ? & ? & ? & ? & J2 & ? & Hemp).
  apply join_comm, Hemp in J2; subst.
  unfold mapsto_memory_block.at_offset in *; simpl in *.
  unfold mapsto in *; simpl in *.
  destruct (readable_share_dec sh).
  - destruct H0 as [[]|[_ H0]], H1 as [[]|[_ H1]]; try contradiction.
    destruct H0 as (_ & _ & _ & ?), H1 as (_ & _ & _ & ?); simpl in *.
    apply ghost_of_join, H0 in H.
    rewrite <- H; auto.
  - destruct H0 as (_ & _ & ?), H1 as (_ & _ & ?).
    apply ghost_of_join, H0 in H.
    rewrite <- H; auto.
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
          YES sh Psh (LK length (snd x - snd loc)) (pack_res_inv (approx (level phi) R)))
    /\  (ghost_of phi = ghost_of phi').

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
  
          YES sh Psh (LK length  (snd x - snd loc)) (pack_res_inv (approx (level phi) R))) /\
  (ghost_of phi = ghost_of phi').

Definition makelock_f phi loc R length : address -> resource :=
  fun x =>
    if adr_range_dec loc length x then
      match phi @ x with
      | YES sh sh' (VAL _) _ =>
          YES sh sh' (LK length (snd x - snd loc)) (pack_res_inv (approx (level phi) R))
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
      | YES sh sh' (LK _ _) _ => YES sh sh' (VAL (contents_at m x)) NoneP
      | YES _ _ _ _
      | PURE _ _
      | NO _ _ => NO Share.bot bot_unreadable
      end
    else
      phi @ x.

(*The name is legacy. Comes from the time there was two shares. Then
 * The contradiction would look like 
 * forall (sh2 sh3:pshares) -> join pfullshare sh2 sh3 -> False. *)
Local Ltac pfulltac := try solve [exfalso; eapply join_writable_readable; eauto].

Lemma readable_part_writable:
               forall sh
                 (Hw : writable_share sh)
                 (Hr : readable_share sh),
                 readable_part (Hr) =
                 exist _ _ pure_readable_Rsh.
Proof.
intros.
apply exist_ext.
clear Hr.
unfold writable_share in Hw.
apply leq_join_sub in Hw.
apply Share.ord_antisym.
apply (Share.glb_lower1 Share.Rsh sh).
apply Share.glb_greatest; auto.
apply Share.ord_refl.
Qed.

Lemma rmap_makelock_join phi1 phi1' loc R length phi2 phi :
  0 < length ->
  rmap_makelock phi1 phi1' loc R length ->
  join phi1 phi2 phi ->
  exists phi',
    rmap_makelock phi phi' loc R length /\
    join phi1' phi2 phi'.
Proof.
  intros Hpos (Hlev & Hsame & Hchanged & Hg) j.
  assert (L1 : level phi1 = level phi) by (eapply join_level; eauto).

  pose proof make_rmap (makelock_f phi loc R length) (ghost_of phi) as Hphi'.

  specialize (Hphi' (level phi1)).

  (* the makelock_f function is stable under approximation at level phi1 *)
  assert_specialize Hphi'. {
    pose proof approx_oo_approx as AA.
    unfold "oo", makelock_f in *.
    extensionality x.
    replace (level phi1) with (level phi); auto.
    pose proof resource_at_approx phi x.
    if_tac; destruct (phi @ x) as [t | t p [] p0 | k p] eqn:E; auto.
    unfold pack_res_inv in *; simpl.
    do 2 f_equal.
    extensionality tt.
    etransitivity; swap 1 2.
    rewrite <-(AA (level phi)). reflexivity.
    reflexivity.
  }

  assert_specialize Hphi'. {
    rewrite L1; apply ghost_of_approx.
  }

  destruct Hphi' as (phi' & Hlev' & Ephi' & Hg').
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
      + specialize (Hchanged x r).
        destruct Hchanged as (val & sh & Rsh & E & Wsh & E').
        rewrite E in j. rewrite E'.
        rewrite L1 in *.
        inv j.
          -- constructor. auto.
          -- pfulltac.
      + specialize (Hsame x nr).
        congruence.
    - rewrite <- Hg, Hg'; apply ghost_of_join; auto.
  }

  split; auto.
  split. apply join_level in j. destruct j; congruence.
  split; [|split; auto].
  + intros x nr. specialize (Hsame x nr).
    eapply resource_at_join with (loc := x) in j.
    eapply resource_at_join with (loc := x) in j'.
    eapply join_eq. apply j. rewrite <-Hsame in j'. eapply j'.
  + intros x r. specialize (Hchanged x r).
    destruct Hchanged as (val & sh & Rsh & E & Wsh & E').
    exists val.
    eapply resource_at_join with (loc := x) in j.
    eapply resource_at_join with (loc := x) in j'.
    rewrite E in j.
    rewrite E' in j'.
    rewrite L1 in *.
      inv j; inv j'; try solve [pfulltac].
      eexists; eexists; split; eauto; split; eauto.
      eapply join_writable1; eauto. 
      rewrite <- H in H5. inversion H5; subst.
      assert (sh4 = sh3) by (eapply join_eq; eauto).
      subst. f_equal. apply proof_irr.
      clear RJ0; exfalso; eapply join_writable_readable; eauto.
Qed.

Lemma rmap_freelock_join phi1 phi1' m loc R length phi2 phi :
  0 < length ->
  rmap_freelock phi1 phi1' m loc R length ->
  join phi1 phi2 phi ->
  exists phi',
    rmap_freelock phi phi' m loc R length /\
    join phi1' phi2 phi'.
Proof.
  intros Hpos (Hlev & Hsame & Hchanged & Hg) j.
  assert (L1 : level phi1 = level phi) by (eapply join_level; eauto).

  pose proof make_rmap (freelock_f phi m loc length) (ghost_of phi) as Hphi'.

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

  destruct Hphi' as (phi' & Hlev' & Ephi' & Hg').
  { rewrite L1; apply ghost_of_approx. }
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
      + specialize (Hchanged x r).
        destruct Hchanged as (sh & Rsh & E' & Wsh & E).
        rewrite E in j. rewrite E'.
        rewrite L1 in *.
        inv j.
          -- constructor. auto.
          -- pfulltac.
      + specialize (Hsame x nr).
        congruence.
    - rewrite <- Hg, Hg'; apply ghost_of_join; auto.
  }

  split; auto.
  split. apply join_level in j. destruct j; congruence.
  split; [|split; auto].
  + intros x nr. specialize (Hsame x nr).
    eapply resource_at_join with (loc := x) in j.
    eapply resource_at_join with (loc := x) in j'.
    eapply join_eq. apply j. rewrite <-Hsame in j'. eapply j'.
  + intros x r. specialize (Hchanged x r).
    destruct Hchanged as (sh & Rsh & E' & Wsh & E).
    eapply resource_at_join with (loc := x) in j.
    eapply resource_at_join with (loc := x) in j'.
    rewrite E in j.
    rewrite E' in j'.
    rewrite L1 in *.
    inv j; inv j'; try solve [pfulltac].
      eexists; eexists; split; eauto; split; eauto.
      eapply join_writable1; eauto. 
      rewrite <- H in H5. inversion H5; subst.
      assert (sh4 = sh3) by (eapply join_eq; eauto).
      subst. f_equal. apply proof_irr.
      clear RJ0; exfalso; eapply join_writable_readable; eauto.
Qed.

(* TODO those definitions are also in sync_preds_defs, see if we can
include without changing the dep DAG too badly *)

(* The TT branch of the jam below might seem too weak, but we already
keep enough control over joining with other rmaps that it should be
enough *)

Definition LKspec_ext (R: pred rmap) lksize : spec :=
   fun (sh: Share.t) (l: AV.address)  =>
    allp (jam (adr_range_dec l lksize)
              (fun l' => yesat (SomeP rmaps.Mpred (fun _ => R)) (LK lksize (snd l' - snd l)) sh l')
              (fun _ => TT)).

Definition LK_at R lksize sh :=
  LKspec_ext R lksize sh.

Lemma data_at_rmap_makelock CS sh b ofs R phi length :
  0 < length ->
  writable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) length noattr) (Vptr b ofs)) phi ->
  exists phi',
    rmap_makelock phi phi' (b, Ptrofs.unsigned ofs) R (size_chunk Mptr * length) /\
    LK_at R (size_chunk Mptr * length) sh (b, Ptrofs.unsigned ofs) phi'.
Proof.
  intros Hpos Hwritable Hat.
  destruct (Z_of_nat_complete length) as (n, Hn). omega.
  rewrite Hn in Hat.
  pose proof data_at_unfold _ _ _ _ _ _ Hwritable Hat as Hbefore.
  rewrite <-Hn in *. clear n Hn.

  pose proof make_rmap (makelock_f phi (b, Ptrofs.unsigned ofs) R (size_chunk Mptr * length))  (ghost_of phi) as Hphi'.

  specialize (Hphi' (level phi)).

  assert_specialize Hphi'. {
    pose proof approx_oo_approx as AA.
    unfold "oo", makelock_f in *.
    extensionality x.
    pose proof resource_at_approx phi x.
    if_tac; destruct (phi @ x) as [t | t p [] p0 | k p] eqn:E; auto.
    unfold pack_res_inv in *; simpl.
    do 2 f_equal.
    extensionality tt.
    etransitivity; swap 1 2.
    rewrite <-(AA (level phi)). reflexivity.
    reflexivity.
  }

  destruct Hphi' as (phi' & Hlev & Ephi' & Hg').
  { apply ghost_of_approx. }
  exists phi'.
  split.
  - split3.
    + auto.
    + rewrite Ephi'.
      intros x nr; unfold makelock_f.
      if_tac; tauto.
    + rewrite Ephi'.
      split; auto.
      intros x r; unfold makelock_f.
      if_tac. 2:tauto.
      specialize (Hbefore x).
      if_tac in Hbefore. 2:tauto.
      destruct Hbefore as (val & ->).
      exists val, sh, (writable_readable_share Hwritable).
      repeat split; auto; reflexivity.
  - intros x.
    simpl.
    unfold Ptrofs.unsigned in *.
    specialize (Hbefore x).
    rewrite Ephi'. unfold makelock_f.
    if_tac. 2:easy.
    destruct Hbefore as (v, ->).
     eexists.
      f_equal.
      symmetry.
      unfold pack_res_inv.
      rewrite Hlev; reflexivity.
Qed.

Lemma nat_of_Z_nonzero z n: n <> O -> nat_of_Z z = n -> z = Z.of_nat n.
Proof.
  intros nz <-.
  symmetry; apply Coqlib.nat_of_Z_eq. unfold Z.ge.
  destruct z; simpl in *; congruence.
Qed.

Lemma lock_inv_rmap_freelock CS sh b ofs R phi m :
  (align_chunk Mptr | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + LKSIZE < Ptrofs.modulus ->
  writable_share sh ->
  app_pred (@lock_inv sh (Vptr b ofs) R) phi ->
  exists phi',
    rmap_freelock phi phi' m (b, Ptrofs.unsigned ofs) R LKSIZE /\
    app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) (LKSIZE/size_chunk Mptr) noattr) (Vptr b ofs)) phi'.
Proof.
  unfold LKSIZE at 3.
  assert (size_chunk Mptr > 0) as Hpos by (rewrite size_chunk_Mptr; destruct Archi.ptr64; omega).
  rewrite Z.div_mul by omega.
  intros Halign Hbound Hwritable Hli.
  destruct Hli as (? & ? & E & Hli & Hg). injection E as <- <- .

  pose proof make_rmap (freelock_f phi m (b, Ptrofs.unsigned ofs) LKSIZE) (ghost_of phi) as Hphi'.
  unfold LKSIZE in *.

  specialize (Hphi' (level phi)).

  assert_specialize Hphi'. {
    pose proof approx_oo_approx as AA.
    unfold "oo", freelock_f in *.
    extensionality x.
    pose proof resource_at_approx phi x.
    repeat if_tac; destruct (phi @ x) as [t | t p [] p0 | k p] eqn:E; auto.
  }

  destruct Hphi' as (phi' & Hlev & Ephi' & Hg').
  { apply ghost_of_approx. }
  exists phi'.
  split.
  - split3; [| |split; auto].
    + auto.
    + rewrite Ephi'.
      intros x nr; unfold freelock_f.
      if_tac; tauto.
    + rewrite Ephi'.
      intros x r; unfold freelock_f.
      if_tac. 2:tauto.
      specialize (Hli x). simpl in Hli.
      if_tac in Hli. 2:tauto.
      destruct Hli as (p, ->); simpl.
      exists sh, (writable_readable_share Hwritable); repeat split; auto; f_equal.
        -- apply proof_irr.
        -- f_equal; try apply proof_irr;
           try congruence.
  - rewrite data_at__memory_block.
    split.
    + repeat split.
      * unfold size_compatible, sizeof.
        rewrite size_chunk_Mptr in Hbound.
        rewrite Z.max_r; omega.
      * constructor; econstructor; simpl; eauto.
        rewrite align_chunk_Mptr.
        apply Z.divide_add_r; auto.
        apply Z.divide_factor_l.
    + split.
      { rewrite size_chunk_Mptr, Z.mul_comm in Hbound; auto. }
      rewrite mapsto_memory_block.memory_block'_eq;
        unfold mapsto_memory_block.memory_block'_alt; rewrite ?Z2Nat.id; try apply Z.ge_le, sizeof_pos.
      rewrite if_true by (apply writable_readable_share; auto).
      split; simpl; [|rewrite Hg'; auto].
      rewrite Ephi'; unfold freelock_f.
      rewrite (Z.mul_comm 2) in *.
      intro b0; specialize (Hli b0); simpl in Hli.
      rewrite <- size_chunk_Mptr; if_tac; auto.
      destruct Hli as [? ->]; eauto.
      { apply Ptrofs.unsigned_range. }
      { simpl.
        rewrite <- size_chunk_Mptr; omega. }
Qed.

Lemma rmap_makelock_unique phi phi1 phi2 loc R len :
  rmap_makelock phi phi1 loc R len ->
  rmap_makelock phi phi2 loc R len ->
  phi1 = phi2.
Proof.
  intros (L1 & out1 & in1 & g1) (L2 & out2 & in2 & g2).
  apply rmap_ext; try congruence.
  intros x.
  destruct (adr_range_dec loc len x) as [r | nr].
  - specialize (in1 x r). specialize (in2 x r). breakhyps.
    + subst.
      rewrite H in H2; inversion H2; subst.
      rewrite H4, H1. f_equal; apply proof_irr.
  - specialize (out1 x nr). specialize (out2 x nr). congruence.
Qed.

Lemma rmap_freelock_unique phi phi1 phi2 m loc R len :
  rmap_freelock phi phi1 m loc R len ->
  rmap_freelock phi phi2 m loc R len ->
  phi1 = phi2.
Proof.
  intros (L1 & out1 & in1 & g1) (L2 & out2 & in2 & g2).
  apply rmap_ext; try congruence.
  intros x.
  destruct (adr_range_dec loc len x) as [r | nr].
  - specialize (in1 x r). specialize (in2 x r). breakhyps.
    + subst.
      rewrite H1 in H4; inversion H4; subst.
      rewrite H, H2. f_equal; apply proof_irr.
  - specialize (out1 x nr). specialize (out2 x nr). congruence.
Qed.

Definition pures_same phi1 phi2 := forall loc k pp, phi1 @ loc = PURE k pp <-> phi2 @ loc = PURE k pp.

Lemma rmap_freelock_pures_same phi phi' m loc R length :
  rmap_freelock phi phi' m loc R length ->
  pures_same phi phi'.
Proof.
  intros (lev & before & after & g); intros l.
  destruct (adr_range_dec loc length l) as  [r|n].
  - specialize (after l r).
    destruct after as (sh & Psh & -> & Hw & ->). intros; split; congruence.
  - specialize (before l n). rewrite before. tauto.
Qed.

Lemma rmap_makelock_pures_same phi phi' loc R length :
  rmap_makelock phi phi' loc R length ->
  pures_same phi phi'.
Proof.
  intros (lev & before & after & g); intros l.
  destruct (adr_range_dec loc length l) as  [r|n].
  - specialize (after l r). destruct after as (val & sh & Psh & -> & ? & ->). intros; split; congruence.
  - specialize (before l n). rewrite before. tauto.
Qed.

Require Import VST.veric.juicy_mem.

Definition noyes phi := forall x sh rsh k pp, phi @ x <> YES sh rsh k pp.

Definition getYES_aux (phi : rmap) (loc : address) : resource :=
  match phi @ loc with
    YES sh Psh k pp => YES (Share.glb Share.Rsh sh) (readable_glb Psh) k pp
  | NO sh _ => NO Share.bot bot_unreadable
  | PURE k pp => PURE k pp
  end.


Lemma glb_Lsh_unreadable:
  forall sh,
    ~ readable_share  (Share.glb Share.Lsh sh).
Proof.
  intros. unfold readable_share.
  rewrite Share.glb_commute, Share.glb_assoc.
  replace (Share.glb sh Share.Rsh) with (Share.glb Share.Rsh sh) by apply Share.glb_commute.
  rewrite glb_Lsh_Rsh'.
  unfold nonempty_share, nonidentity.
  intros H; apply H; apply bot_identity.
Qed.

  
  
Definition getNO_aux (phi : rmap) (loc : address) : resource :=
  match phi @ loc with
    YES sh Psh k pp => NO (Share.glb Share.Lsh sh) (glb_Lsh_unreadable sh)
  | NO sh Psh => NO sh Psh
  | PURE k pp => PURE k pp
  end.

Lemma readable_part_glb:
      forall (sh sh0 : Share.t) (r : readable_share sh) (r0 : readable_share sh0),
  Share.glb Share.Rsh sh0 = Share.glb Share.Rsh sh ->
  readable_part (readable_glb r0) = readable_part (readable_glb r).
Proof.
intros.
unfold readable_part.
apply exist_ext.
rewrite H. auto.
Qed.

Program Definition getYES (phi : rmap) := proj1_sig (make_rmap (getYES_aux phi) (ghost_of phi) (level phi) _ _).
Next Obligation.
  pose proof resource_at_approx phi as V.
  extensionality l. specialize (V l).
  unfold getYES_aux, "oo" in *.
  destruct (phi @ _); simpl in *; auto.
  congruence.
Qed.
Next Obligation.
  apply ghost_of_approx.
Qed.

Program Definition getNO (phi : rmap) := proj1_sig (make_rmap (getNO_aux phi) (core (ghost_of phi)) (level phi) _ _).
Next Obligation.
  pose proof resource_at_approx phi as V.
  extensionality l. specialize (V l).
  unfold getNO_aux, "oo" in *.
  destruct (phi @ _); simpl in *; auto.
Qed.
Next Obligation.
  rewrite ghost_core; auto.
Qed.

Lemma getYES_getNO_join phi : join (getYES phi) (getNO phi) phi.
Proof.
  apply resource_at_join2; try apply level_make_rmap.
  unfold getYES, getNO; do 2 rewrite resource_at_make_rmap.
  unfold getYES_aux, getNO_aux; intros loc.
  destruct (phi @ loc); constructor; try apply bot_join_eq.
  pose proof (comp_parts comp_Lsh_Rsh sh).
  split.
  rewrite (Share.glb_commute Share.Rsh).
  rewrite Share.glb_assoc. rewrite <- (Share.glb_assoc Share.Rsh).
  rewrite (Share.glb_commute Share.Rsh).
  rewrite glb_Lsh_Rsh. 
  rewrite (Share.glb_commute Share.bot), !Share.glb_bot. auto.
  rewrite Share.lub_commute, <- H. auto.
  unfold getYES, getNO; do 2 rewrite ghost_of_make_rmap.
  apply join_comm, core_unit.
Qed.

Lemma noyes_getNO phi : noyes (getNO phi).
Proof.
  intros l.
  unfold getNO; rewrite resource_at_make_rmap; unfold getNO_aux.
  destruct (phi @ _); congruence.
Qed.

Lemma writable_glb_Rsh:
  forall sh, writable_share sh -> Share.glb Share.Rsh sh = Share.Rsh.
Proof.
 intros. unfold writable_share in H.
apply leq_join_sub in H.
apply Share.ord_antisym.
apply (Share.glb_lower1 Share.Rsh sh).
apply Share.glb_greatest; auto.
apply Share.ord_refl.
Qed.

Section simpler_invariant_tentative.

(* This section about getYES and getNO is currently unused.  Maybe
it would give us a simpler invariant, but maybe not. *)

(* Variable unrel_lsh_rsh : Share.unrel Share.Lsh Share.Rsh = Share.bot. *)

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
        (address_mapsto m v sh loc) phi ->
        (address_mapsto m v Share.Rsh loc) (getYES phi)).
  { intros CUT.
    unfold mapsto in *; destruct (access_mode t);
      repeat simple_if_tac; repeat if_tac;
      repeat if_tac in At; eauto; destruct v; eauto; try tauto.
    destruct At as [[? At]|[? At]]; [left|right]; split; try assumption.
    - apply CUT; auto.
    - destruct At. eexists. apply CUT; eauto. }
  clear v v' At. intros m v loc M.
  unfold address_mapsto in *.
  destruct M as (bl & (I & M) & G); exists bl; split; [split; auto|].
  intros x; specialize (M x).
  simpl in *.
  if_tac.
  - destruct M as (p, M).
    unfold getYES, getYES_aux in *.
    rewrite resource_at_make_rmap.
    destruct (phi @ x); try congruence.
    injection M as -> -> ->.
    assert (p' : readable_share Share.Rsh). {
      apply writable_readable_share.
      apply writable_Rsh.
    }
    exists p'; f_equal.
    +
      apply YES_ext. apply  writable_glb_Rsh; auto.
  - apply empty_NO in M.
    unfold getYES, getYES_aux in *.
    rewrite resource_at_make_rmap.
    destruct M as [-> | (k & pp & ->)].
    + apply NO_identity.
    + apply PURE_identity.
  - simpl; unfold getYES; rewrite ghost_of_make_rmap; auto.
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
