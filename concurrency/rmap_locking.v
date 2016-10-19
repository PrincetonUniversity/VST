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
Require Import floyd.field_at.
Require Import floyd.reptype_lemmas.
Require Import sepcomp.Address.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import veric.coqlib4.
Require Import floyd.type_induction.

Local Open Scope Z_scope.

Lemma data_at_unfolding CS sh b ofs phi :
  readable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) 4 noattr) (Vptr b ofs)) phi ->
  forall loc,
    adr_range (b, Int.intval ofs) 4%Z loc ->
    exists p v,
      phi @ loc =
      YES
        (Share.unrel Share.Lsh sh)
        (mk_lifted (Share.unrel Share.Rsh sh) p)
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
  unfold reptype_lemmas.default_val, Znth in *.
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
  unfold NoneP, "oo".
  rewrite approx_FF.
  reflexivity.
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
      YES (Share.unrel Share.Lsh sh) (mk_lifted (Share.unrel Share.Rsh sh) p) (VAL v) NoneP
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
  rewrite approx_FF; auto.
  unfold noat in *.
  apply Sat.
Qed.

Lemma data_at_unfold CS sh b ofs phi length :
  readable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) (Z.of_nat length) noattr) (Vptr b ofs)) phi ->
  forall loc,
    if adr_range_dec (b, Int.intval ofs) (4 * Z.of_nat length)%Z loc then
      exists p v,
        phi @ loc =
        YES
          (Share.unrel Share.Lsh sh)
          (mk_lifted (Share.unrel Share.Rsh sh) p)
          (VAL v) NoneP
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
    unfold Znth. if_tac; auto.
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

Lemma data_at_unfold_weak CS sh b ofs phi z z' loc :
  readable_share sh ->
  app_pred (@data_at_ CS sh (Tarray (Tpointer Tvoid noattr) z noattr) (Vptr b ofs)) phi ->
  adr_range (b, Int.intval ofs) z' loc ->
  z' <= 4 * z ->
  exists p v,
    phi @ loc =
    YES
      (Share.unrel Share.Lsh sh)
      (mk_lifted (Share.unrel Share.Rsh sh) p)
      (VAL v) NoneP.
Proof.
  intros R AT range L.
  pose proof data_at_unfold CS sh b ofs phi (Z.to_nat z) R as H.
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
