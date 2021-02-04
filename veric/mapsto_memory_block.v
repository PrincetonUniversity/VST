Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.address_conflict.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.Cop2.
Require Import VST.veric.shares.
Require Import VST.veric.slice.

Require Import VST.veric.mpred.

(*Lenb: moved to mpred
Definition assert := environ -> mpred.  (* Unfortunately
   can't export this abbreviation through SeparationLogic.v because
  it confuses the Lift system *)
*)

Lemma address_mapsto_exists:
  forall ch v sh (rsh: readable_share sh) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot bot_unreadable),
      identity (ghost_of w0) ->
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) sh loc w 
                    /\ core w = core w0.
Proof.  exact address_mapsto_exists. Qed.

Definition permission_block (sh: Share.t)  (v: val) (t: type) : mpred :=
    match access_mode t with
         | By_value ch =>
            match v with
            | Vptr b ofs =>
                 nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs)
                       (size_chunk ch)
            | _ => FF
            end
         | _ => FF
         end.

Local Open Scope pred.

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch =>
   match type_is_volatile t with
   | false =>
    match v1 with
     | Vptr b ofs =>
       if readable_share_dec sh
       then (!!tc_val t v2 &&
             address_mapsto ch v2 sh (b, Ptrofs.unsigned ofs)) ||
            (!! (v2 = Vundef) &&
             EX v2':val, address_mapsto ch v2' sh (b, Ptrofs.unsigned ofs))
       else !! (tc_val' t v2 /\ (align_chunk ch | Ptrofs.unsigned ofs)) && nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs) (size_chunk ch)
     | _ => FF
    end
    | _ => FF
    end
  | _ => FF
  end.

Definition mapsto_ sh t v1 := mapsto sh t v1 Vundef.

Lemma address_mapsto_readable:
  forall m v sh a, address_mapsto m v sh a |-- 
           !! readable_share sh.
Proof.
intros.
unfold address_mapsto.
unfold derives.
simpl.
intros ? ?.
destruct H as [bl [[[? [? ?]] ?]] ].
specialize (H2 a).
rewrite if_true in H2.
destruct H2 as [rsh ?]. auto.
destruct a; split; auto.
clear; pose proof (size_chunk_pos m); lia.
Qed.

Lemma mapsto_tc_val': forall sh t p v, mapsto sh t p v |-- !! tc_val' t v.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); auto.
  if_tac; auto;
  destruct p; auto;
  try simple_if_tac; auto.
  + apply orp_left; apply andp_left1.
    - intros ?; simpl.
      apply tc_val_tc_val'.
    - intros ? ?; simpl in *; subst.
      apply tc_val'_Vundef.
  + apply andp_left1.
    intros ?; simpl; tauto.
Qed.

Lemma mapsto_value_range:
 forall sh v sz sgn i,
   readable_share sh ->
   mapsto sh (Tint sz sgn noattr) v (Vint i) =
    !! int_range sz sgn i && mapsto sh (Tint sz sgn noattr) v (Vint i).
Proof.
intros.
rename H into Hsh.
assert (GG: forall a b, (a || !!(Vint i = Vundef) && b) = a). {
intros. apply pred_ext; intros ? ?. hnf in H.
destruct H; auto; hnf in H; destruct H; discriminate.
left; auto.
}
apply pred_ext; [ | apply andp_left2; auto].
assert (MAX: Int.max_signed = 2147483648 - 1) by reflexivity.
assert (MIN: Int.min_signed = -2147483648) by reflexivity.
assert (Byte.min_signed = -128) by reflexivity.
assert (Byte.max_signed = 128-1) by reflexivity.
assert (Byte.max_unsigned = 256-1) by reflexivity.
destruct (Int.unsigned_range i).
assert (Int.modulus = Int.max_unsigned + 1) by reflexivity.
assert (Int.modulus = 4294967296) by reflexivity.
apply andp_right; auto.
unfold mapsto; intros.
replace (type_is_volatile (Tint sz sgn noattr)) with false
  by (destruct sz,sgn; reflexivity).
simpl.
destruct (readable_share_dec sh); [| tauto].
destruct sz, sgn, v; (try rewrite FF_and; auto);
 repeat rewrite GG;
 apply prop_andp_left; intros ? ? _; hnf; try lia.
 pose proof (Int.signed_range i); lia.
 destruct H6; subst;
  try rewrite Int.unsigned_zero; try rewrite Int.unsigned_one; lia.
 destruct H6; subst;
  try rewrite Int.unsigned_zero; try rewrite Int.unsigned_one; lia.
Qed.

Definition writable_block (id: ident) (n: Z): assert :=
   fun rho => 
        EX b: block,  EX sh: Share.t,
          !! (writable_share sh /\ ge_of rho id = Some b) && VALspec_range n sh (b, 0).

Fixpoint writable_blocks (bl : list (ident*Z)) : assert :=
 match bl with
  | nil =>  fun rho => emp
  | (b,n)::bl' =>  fun rho => writable_block b n rho * writable_blocks bl' rho
 end.

Fixpoint address_mapsto_zeros (sh: share) (n: nat) (adr: address) : mpred :=
 match n with
 | O => emp
 | S n' => address_mapsto Mint8unsigned (Vint Int.zero) sh adr 
               * address_mapsto_zeros sh n' (fst adr, Z.succ (snd adr))
end.

Definition address_mapsto_zeros' (n: Z) : spec :=
     fun (sh: Share.t) (l: address) =>
          allp (jam (adr_range_dec l (Z.max n 0))
                                  (fun l' => yesat NoneP (VAL (Byte Byte.zero)) sh l')
                                  noat) && noghost.

Lemma address_mapsto_zeros_eq:
  forall sh n,
   address_mapsto_zeros sh n =
   address_mapsto_zeros' (Z_of_nat n) sh.
Proof.
  induction n;
  extensionality adr; destruct adr as [b i].
  * (* base case *)
    simpl.
    unfold address_mapsto_zeros'.
    apply pred_ext.
    intros w ?.
    split; [intros [b' i']|].
    hnf.
    rewrite if_false.
    simpl. apply resource_at_identity; auto.
    intros [? ?]. unfold Z.max in H1;  simpl in H1. lia.
    apply ghost_of_identity; auto.
    intros w [].
    simpl.
    apply all_resource_at_identity.
    intros [b' i'].
    specialize (H (b',i')).
    hnf in H.
    rewrite if_false in H. apply H.
    clear; intros [? ?]. unfold Z.max in H0; simpl in H0. lia.
    auto.
  * (* inductive case *)
    rewrite inj_S.
    simpl.
    rewrite IHn; clear IHn.
    apply pred_ext; intros w ?.
    - (* forward case *)
      destruct H as [w1 [w2 [? [? [? Hg2]]]]].
      split.
      intros [b' i'].
      hnf.
      if_tac.
      + destruct H0 as [bl [[[? [? ?]] ?] _]].
        specialize (H5 (b',i')).
        hnf in H5.
        if_tac in H5.
       ** destruct H5 as [p ?]; exists p.
          hnf in H5.
          specialize (H1 (b',i')). hnf in H1. rewrite if_false in H1.
          assert (LEV := join_level _ _ _ H).
          {
            apply (resource_at_join _ _ _ (b',i')) in H.
            apply join_comm in H; apply H1 in H.
            rewrite H in H5.
            hnf. rewrite H5. f_equal.
            f_equal.
            simpl. destruct H6. simpl in H7. replace (i'-i) with 0 by lia.
            unfold size_chunk_nat in H0. simpl in H0.
            unfold nat_of_P in H0. simpl in H0.
            destruct bl; try solve [inv H0].
            destruct bl; inv H0.
            simpl.
            clear - H3.
            (* TODO: Clean up the following proof. *)
            destruct m; try solve [inv H3].
            rewrite decode_byte_val in H3.
            f_equal.
            assert (Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.repr 0) by
              (forget (Int.zero_ext 8 (Int.repr (Byte.unsigned i))) as j; inv H3; auto).
            clear H3.
            assert (Int.unsigned (Int.zero_ext 8 (Int.repr (Byte.unsigned i))) =
                Int.unsigned Int.zero) by (f_equal; auto).
            rewrite Int.unsigned_zero in H0.
            clear H.
            rewrite Int.zero_ext_mod in H0 by (compute; split; congruence).
            rewrite Int.unsigned_repr in H0.
            rewrite Zdiv.Zmod_small in H0.
            assert (Byte.repr (Byte.unsigned i) = Byte.zero).
            apply f_equal; auto.
            rewrite Byte.repr_unsigned in H. auto.
            apply Byte.unsigned_range.
            clear.
            pose proof (Byte.unsigned_range i).
            destruct H; split; auto.
            apply Z.le_trans with Byte.modulus.
            lia.
            clear.
            compute; congruence.
          }
          destruct H2.
          intros [? ?].
          destruct H6.
          clear - H7 H9 H10. simpl in H10. lia.
       ** assert (LEV := join_level _ _ _ H).
          apply (resource_at_join _ _ _ (b',i')) in H.
          apply H5 in H.
          specialize (H1 (b',i')).
          hnf in H1.
          if_tac in H1.
         -- destruct H1 as [p ?]; exists p.
            hnf in H1|-*.
            rewrite H in H1; rewrite H1.
            f_equal.
         -- contradiction H6.
            destruct H2.
            split; auto.
            simpl.
            subst b'.
            clear - H7 H8.
            assert (~ (Z.succ i <= i' < (Z.succ i + Z.max (Z_of_nat n) 0))).
            contradict H7; split; auto.
            clear H7.
            replace (Z.max (Z.succ (Z_of_nat n)) 0) with (Z.succ (Z_of_nat n)) in H8.
            replace (Z.max (Z_of_nat n) 0) with (Z_of_nat n) in H.
            lia.
            symmetry; apply Zmax_left.
            apply Z_of_nat_ge_O.
            symmetry; apply Zmax_left.
            clear.
            pose proof (Z_of_nat_ge_O n). lia. 
      + apply (resource_at_join _ _ _ (b',i')) in H.
        destruct H0 as [bl [[[? [? ?]] ?] _]].
        specialize (H5 (b',i')); specialize (H1 (b',i')).
        hnf in H1,H5.
        rewrite if_false in H5.
        rewrite if_false in H1.
       ** apply H5 in H.
          simpl in H1|-*.
          rewrite <- H; auto.
       ** clear - H2; contradict H2.
          destruct H2; split; auto.
          destruct H0.
          lia.
       ** clear - H2; contradict H2; simpl in H2.
          destruct H2; split; auto. lia.
      + destruct H0 as (? & ? & Hg1).
        simpl; rewrite <- (Hg1 _ _ (ghost_of_join _ _ _ H)); auto.
    - (* backward direction *)
      destruct H as [H Hg].
      assert (H0 := H (b,i)).
      hnf in H0.
      rewrite if_true in H0
        by (split; auto; pose proof (Z_of_nat_ge_O n); rewrite Zmax_left; lia).
      destruct H0 as [H0 H1].
      pose proof I.
      destruct (make_rmap  (fun loc => if eq_dec loc (b,i) then 
       YES sh H0 (VAL (Byte Byte.zero)) NoneP
          else core (w @ loc)) (ghost_of w) (level w)) as [w1 [? ?]].
      extensionality loc. unfold compose.
      if_tac; [unfold resource_fmap; f_equal; apply preds_fmap_NoneP
           | apply resource_fmap_core].
      { apply ghost_of_approx. }
      pose proof I.
      destruct (make_rmap (fun loc => if adr_range_dec (b, Z.succ i) (Z.max (Z.of_nat n) 0) loc
                       then YES sh H0 (VAL (Byte Byte.zero)) NoneP
          else core (w @ loc)) (ghost_of w) (level w)) as [w2 [? ?]].
      extensionality loc. unfold compose.
      if_tac; [unfold resource_fmap; f_equal; apply preds_fmap_NoneP
           | apply resource_fmap_core].
      { apply ghost_of_approx. }
      exists w1; exists w2; split3; auto.
+apply resource_at_join2; try congruence.
  intro loc; destruct H4; rewrite H4; destruct H7; rewrite H7.
 clear - H.
 specialize (H loc).  unfold jam in H. hnf in H.
 rewrite Zmax_left by (pose proof (Z_of_nat_ge_O n); lia).
 rewrite Zmax_left in H by (pose proof (Z_of_nat_ge_O n); lia).
 if_tac. rewrite if_false.
 subst. rewrite if_true in H.
  destruct H as [H' H]; rewrite H. rewrite core_YES.
 rewrite preds_fmap_NoneP.
 apply join_unit2.
 constructor. auto.
 apply YES_ext; auto.
 split; auto; lia.
 subst. intros [? ?]; lia.
 if_tac in H.
 rewrite if_true.
 destruct H as [H' H]; rewrite H; clear H. rewrite core_YES.
 rewrite preds_fmap_NoneP.
 apply join_unit1.
 constructor; auto.
 apply YES_ext; auto.
 destruct loc;
 destruct H2; split; auto.
 assert (z<>i) by congruence.
 lia.
 rewrite if_false.
 unfold noat in H. simpl in H.
 apply join_unit1; [apply core_unit | ].
 clear - H.
 apply H. apply join_unit2. apply core_unit. auto.
 destruct loc. intros [? ?]; subst. apply H2; split; auto; lia.
 destruct H4 as [_ ->], H7 as [_ ->].
 apply identity_unit'; auto.
+ exists (Byte Byte.zero :: nil); split.
 split. split. reflexivity. split.
 unfold decode_val. simpl. f_equal.
 apply Z.divide_1_l.
 intro loc. hnf. if_tac. exists H0.
 destruct loc as [b' i']. destruct H8; subst b'.
 simpl in H9. assert (i=i') by lia; subst i'.
 rewrite Zminus_diag. hnf. rewrite preds_fmap_NoneP.
  destruct H4; rewrite H4. rewrite if_true by auto. f_equal.
 unfold noat. simpl. destruct H4; rewrite H4. rewrite if_false. apply core_identity.
  contradict H8. subst. split; auto. simpl; lia.
  simpl; destruct H4 as [_ ->]; auto.
+ split. intro loc. hnf.
 if_tac. exists H0. hnf. destruct H7; rewrite H7.
 rewrite if_true by auto. rewrite preds_fmap_NoneP. auto.
 unfold noat. simpl. destruct H7; rewrite H7.
 rewrite if_false by auto. apply core_identity.
 simpl; destruct H7 as [_ ->]; auto.
Qed.

Definition mapsto_zeros (n: Z) (sh: share) (a: val) : mpred :=
 match a with
  | Vptr b z => 
    !! (0 <= Ptrofs.unsigned z  /\ n + Ptrofs.unsigned z < Ptrofs.modulus)%Z &&
    address_mapsto_zeros sh (Z.to_nat n) (b, Ptrofs.unsigned z)
  | _ => FF
  end.

Fixpoint memory_block' (sh: share) (n: nat) (b: block) (i: Z) : mpred :=
  match n with
  | O => emp
  | S n' => mapsto_ sh (Tint I8 Unsigned noattr) (Vptr b (Ptrofs.repr i))
         * memory_block' sh n' b (i+1)
 end.

Definition memory_block'_alt (sh: share) (n: nat) (b: block) (ofs: Z) : mpred :=
 if readable_share_dec sh 
 then VALspec_range (Z_of_nat n) sh (b, ofs)
 else nonlock_permission_bytes sh (b,ofs) (Z.of_nat n).

Lemma memory_block'_eq:
 forall sh n b i,
  0 <= i ->
  Z_of_nat n + i < Ptrofs.modulus ->
  memory_block' sh n b i = memory_block'_alt sh n b i.
Proof.
  intros.
  unfold memory_block'_alt.
  revert i H H0; induction n; intros.
  + unfold memory_block'.
    simpl.
    rewrite VALspec_range_0, nonlock_permission_bytes_0.
    if_tac; auto.
  + unfold memory_block'; fold memory_block'.
    rewrite (IHn (i+1)) by (rewrite inj_S in H0; lia).
    symmetry.
    rewrite (VALspec_range_split2 1 (Z_of_nat n)) by (try rewrite inj_S; lia).
    rewrite VALspec1.
    unfold mapsto_, mapsto.
    simpl access_mode. cbv beta iota.
    change (type_is_volatile (Tint I8 Unsigned noattr)) with false. cbv beta iota.
    destruct (readable_share_dec sh).
    - f_equal.
      assert (i < Ptrofs.modulus) by (rewrite Nat2Z.inj_succ in H0; lia).
      rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia); clear H1.
      forget (Share.unrel Share.Lsh sh) as rsh.
      forget (Share.unrel Share.Rsh sh) as sh'.
      clear.

      assert (EQ: forall loc, jam (adr_range_dec loc (size_chunk Mint8unsigned)) = jam (eq_dec loc)).
      intros [b' z']; unfold jam; extensionality P Q loc;
       destruct loc as [b'' z'']; apply exist_ext; extensionality w;
       if_tac; [rewrite if_true | rewrite if_false]; auto;
        [destruct H; subst; f_equal;  simpl in H0; lia
        | contradict H; inv H; split; simpl; auto; lia].
      apply pred_ext.
      * intros w ?.
        right; split; hnf; auto.
        destruct H as [H Hg].
        assert (H':= H (b,i)).
        hnf in H'. rewrite if_true in H' by auto.
        destruct H' as [v H'].
        pose (l := v::nil).
        destruct v; [exists Vundef | exists (Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned i0)))) | exists Vundef];
        exists l; split; auto; (split; [ split3; [reflexivity |unfold l; (reflexivity || apply decode_byte_val) |  apply Z.divide_1_l ] | ]);
          rewrite EQ; intro loc; specialize (H loc);
         hnf in H|-*; if_tac; auto; subst loc; rewrite Zminus_diag;
         unfold l; simpl nth; auto.
      * apply orp_left.
        apply andp_left2.
        { intros w [l [[[? [? ?]] ?] Hg]].
          split; auto.
          intros [b' i']; specialize (H2 (b',i')); rewrite EQ in H2;
            hnf in H2|-*;  if_tac; auto. symmetry in H3; inv H3.
          destruct l; inv H. exists m.
          destruct H2 as [H2' H2]; exists H2'; hnf in H2|-*; rewrite H2.
          f_equal. f_equal. rewrite Zminus_diag. reflexivity.
        }
        { rewrite prop_true_andp by auto.
          intros w [v2' [l [[[? [? ?]] ?] Hg]]].
          split; auto.
          intros [b' i']; specialize (H2 (b',i')); rewrite EQ in H2;
            hnf in H2|-*;  if_tac; auto. symmetry in H3; inv H3.
          destruct l; inv H. exists m.
          destruct H2 as [H2' H2]; exists H2'; hnf in H2|-*; rewrite H2.
          f_equal. f_equal. rewrite Zminus_diag. reflexivity.
        }
    - rewrite Ptrofs.unsigned_repr by (rewrite Nat2Z.inj_succ in H0; unfold Ptrofs.max_unsigned; lia).
      change (size_chunk Mint8unsigned) with 1.
      rewrite prop_true_andp by (split; [apply tc_val'_Vundef | apply Z.divide_1_l]).
      apply nonlock_permission_bytes_split2.
      * rewrite Nat2Z.inj_succ; lia.
      * lia.
      * lia.
Qed.

Definition memory_block (sh: share) (n: Z) (v: val) : mpred :=
 match v with
 | Vptr b ofs => (!!(Ptrofs.unsigned ofs + n < Ptrofs.modulus)) && memory_block' sh (Z.to_nat n) b (Ptrofs.unsigned ofs)
 | _ => FF
 end.

Lemma mapsto__exp_address_mapsto: forall sh t b i_ofs ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  readable_share sh ->
  mapsto_ sh t (Vptr b i_ofs) = EX  v2' : val,
            address_mapsto ch v2' sh (b, (Ptrofs.unsigned i_ofs)).
Proof.
  pose proof (@FF_orp (pred rmap) (algNatDed _)) as HH0.
  change seplog.orp with orp in HH0.
  change seplog.FF with FF in HH0.
  pose proof (@ND_prop_ext (pred rmap) (algNatDed _)) as HH1.
  change seplog.prop with prop in HH1.

  intros. rename H1 into RS.
  unfold mapsto_, mapsto.
  rewrite H, H0.
  rewrite if_true by auto.
  assert (!!(tc_val t Vundef) = FF). {
    clear; unfold FF; f_equal; apply prop_ext; intuition.
    apply (tc_val_Vundef _ H).
  }
  rewrite H1.

  rewrite FF_and, HH0.
  assert (!!(Vundef = Vundef) = TT) by (apply HH1; tauto).
  rewrite H2.
  rewrite TT_and.
  reflexivity.
Qed.

Lemma exp_address_mapsto_VALspec_range_eq:
  forall ch sh l,
    EX v: val, address_mapsto ch v sh l = !! (align_chunk ch | snd l) && VALspec_range (size_chunk ch) sh l.
Proof.
  intros.
  apply pred_ext.
  + apply exp_left; intro.
    apply andp_right; [| apply address_mapsto_VALspec_range].
    unfold address_mapsto.
    apply exp_left; intro.
    do 2 apply andp_left1.
    apply (@prop_derives (pred rmap) (algNatDed _)); tauto.
  + apply prop_andp_left; intro.
    apply VALspec_range_exp_address_mapsto; auto.
Qed.

Lemma VALspec_range_exp_address_mapsto_eq:
  forall ch sh l,
    (align_chunk ch | snd l) ->
    VALspec_range (size_chunk ch) sh l = EX v: val, address_mapsto ch v sh l.
Proof.
  intros.
  apply pred_ext.
  + apply VALspec_range_exp_address_mapsto; auto.
  + apply exp_left; intro; apply address_mapsto_VALspec_range.
Qed.

Lemma mapsto__memory_block: forall sh b ofs t ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + size_chunk ch < Ptrofs.modulus ->
  mapsto_ sh t (Vptr b ofs) = memory_block sh (size_chunk ch) (Vptr b ofs).
Proof.
  intros.
  unfold memory_block.
  rewrite memory_block'_eq.
  2: pose proof Ptrofs.unsigned_range ofs; lia.
  2: rewrite Z2Nat.id by (pose proof size_chunk_pos ch; lia); lia.
  destruct (readable_share_dec sh).
 *
  rewrite mapsto__exp_address_mapsto with (ch := ch); auto.
  unfold memory_block'_alt. rewrite if_true by auto.
  rewrite Z2Nat.id by (pose proof size_chunk_pos ch; lia).
  rewrite VALspec_range_exp_address_mapsto_eq by (exact H1).
  rewrite <- (TT_and (EX  v2' : val,
   address_mapsto ch v2' sh (b, Ptrofs.unsigned ofs))) at 1.
  f_equal.
  pose proof (@ND_prop_ext (pred rmap) _).
  simpl in H3.
  change TT with (!! True).
  apply H3.
  tauto.
 * unfold mapsto_, mapsto, memory_block'_alt.
   rewrite prop_true_andp by auto.
   rewrite H, H0.
  rewrite !if_false by auto.
   rewrite prop_true_andp by (split; [apply tc_val'_Vundef | auto]).
   rewrite Z2Nat.id by (pose proof (size_chunk_pos ch); lia).
   auto.
Qed.

Lemma nonreadable_memory_block_mapsto: forall sh b ofs t ch v,
  ~ readable_share sh ->
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + size_chunk ch < Ptrofs.modulus ->
  tc_val' t v ->
  memory_block sh (size_chunk ch) (Vptr b ofs) = mapsto sh t (Vptr b ofs) v.
Proof.
  intros.
  unfold memory_block.
  rewrite memory_block'_eq.
  2: pose proof Ptrofs.unsigned_range ofs; lia.
  2: rewrite Z2Nat.id by (pose proof size_chunk_pos ch; lia); lia.
  destruct (readable_share_dec sh).
 * tauto.
 * unfold mapsto_, mapsto, memory_block'_alt.
   rewrite prop_true_andp by auto.
   rewrite H0, H1.
   rewrite !if_false by auto.
   rewrite prop_true_andp by auto.
   rewrite Z2Nat.id by (pose proof (size_chunk_pos ch); lia).
   auto.
Qed.

Lemma mapsto_share_join:
 forall sh1 sh2 sh t p v,
   join sh1 sh2 sh ->
   mapsto sh1 t p v * mapsto sh2 t p v = mapsto sh t p v.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t) eqn:?; try solve [rewrite FF_sepcon; auto].
  destruct (type_is_volatile t) eqn:?; try solve [rewrite FF_sepcon; auto].
  destruct p; try solve [rewrite FF_sepcon; auto].
  destruct (readable_share_dec sh1), (readable_share_dec sh2).
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eauto | auto]).
    pose proof (@guarded_sepcon_orp_distr (pred rmap) (algNatDed _) (algSepLog _)).
    simpl in H0; rewrite H0 by (intros; subst; pose proof tc_val_Vundef t; tauto); clear H0.
    f_equal; f_equal.
    - apply address_mapsto_share_join; auto.
    - rewrite exp_sepcon1.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H0; apply H0; clear H0; intro.
      rewrite exp_sepcon2.
      transitivity
       (address_mapsto m v0 sh1 (b, Ptrofs.unsigned i) *
        address_mapsto m v0 sh2 (b, Ptrofs.unsigned i)).
      * apply pred_ext; [| apply (exp_right v0); auto].
        apply exp_left; intro.
        pose proof (fun sh0 sh3 a => 
            (@add_andp (pred rmap) (algNatDed _) _ _ (address_mapsto_value_cohere m v0 x sh0 sh3 a))).
        simpl in H0; rewrite H0; clear H0.
        apply normalize.derives_extract_prop'; intro; subst; auto.
      * apply address_mapsto_share_join; auto.
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eauto | auto]).
    rewrite distrib_orp_sepcon.
    f_equal; rewrite sepcon_comm, sepcon_andp_prop;
    pose proof (@andp_prop_ext (pred rmap) _);
    (simpl in H0; apply H0; clear H0; [reflexivity | intro]).
    - rewrite (address_mapsto_align _ _ sh).
      rewrite (andp_comm (address_mapsto _ _ _ _)), sepcon_andp_prop1.
      pose proof (@andp_prop_ext (pred rmap) _); simpl in H1; apply H1; clear H1; intros.
      * apply tc_val_tc_val' in H0; tauto.
      * apply nonlock_permission_bytes_address_mapsto_join; auto.
    - rewrite exp_sepcon2.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H1; apply H1; clear H1; intro.
      rewrite (address_mapsto_align _ _ sh).
      rewrite (andp_comm (address_mapsto _ _ _ _)), sepcon_andp_prop1.
      pose proof (@andp_prop_ext (pred rmap) _); simpl in H1; apply H1; clear H1; intros.
      * subst; pose proof tc_val'_Vundef t. tauto.
      * apply nonlock_permission_bytes_address_mapsto_join; auto.
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eexists; apply join_comm in H; eauto | auto]).
    rewrite sepcon_comm, distrib_orp_sepcon.
    f_equal; rewrite sepcon_comm, sepcon_andp_prop;
    pose proof (@andp_prop_ext (pred rmap) _);
    (simpl in H0; apply H0; clear H0; [reflexivity | intro]).
    - rewrite (address_mapsto_align _ _ sh).
      rewrite (andp_comm (address_mapsto _ _ _ _)), sepcon_andp_prop1.
      pose proof (@andp_prop_ext (pred rmap) _); simpl in H1; apply H1; clear H1; intros.
      * apply tc_val_tc_val' in H0; tauto.
      * apply nonlock_permission_bytes_address_mapsto_join; auto.
    - rewrite exp_sepcon2.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H1; apply H1; clear H1; intro.
      rewrite (address_mapsto_align _ _ sh).
      rewrite (andp_comm (address_mapsto _ _ _ _)), sepcon_andp_prop1.
      pose proof (@andp_prop_ext (pred rmap) _); simpl in H1; apply H1; clear H1; intros.
      * subst; pose proof tc_val'_Vundef t. tauto.
      * apply nonlock_permission_bytes_address_mapsto_join; auto.
  + rewrite if_false by (eapply join_unreadable_shares; eauto).
    rewrite sepcon_andp_prop1, sepcon_andp_prop2, <- andp_assoc, andp_dup.
    f_equal.
    apply nonlock_permission_bytes_share_join; auto.
Qed.

Lemma mapsto_mapsto_: forall sh t v v', mapsto sh t v v' |-- mapsto_ sh t v.
Proof. unfold mapsto_; intros.
  unfold mapsto.
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); auto.
  destruct v; auto.
  if_tac.
  + apply orp_left.
    apply orp_right2.
    apply andp_left2.
    apply andp_right.
    - intros ? _; simpl; auto.
    - apply exp_right with v'; auto.
    - apply andp_left2. apply exp_left; intro v2'.
      apply orp_right2. apply andp_right; [intros ? _; simpl; auto |]. apply exp_right with v2'.
      auto.
  + apply andp_derives; [| auto].
    intros ? [? ?].
    split; auto.
    apply tc_val'_Vundef.
Qed.

Lemma mapsto_not_nonunit: forall sh t p v, ~ nonunit sh -> mapsto sh t p v |-- emp.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try solve [apply FF_derives].
  destruct (type_is_volatile t); try solve [apply FF_derives].
  destruct p; try solve [apply FF_derives].
  if_tac.
  + apply readable_nonidentity in H0.
    apply nonidentity_nonunit in H0; tauto.
  + apply andp_left2.
    apply nonlock_permission_bytes_not_nonunit; auto.
Qed.

Lemma mapsto_pure_facts: forall sh t p v,
  mapsto sh t p v |-- !! ((exists ch, access_mode t = By_value ch) /\ isptr p).
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try solve [apply FF_derives].
  destruct (type_is_volatile t); try solve [apply FF_derives].
  destruct p; try solve [apply FF_derives].

  pose proof (@seplog.prop_right (pred rmap) (algNatDed _)).
  simpl in H; apply H; clear H.
  split.
  + eauto.
  + simpl; auto.
Qed.

Lemma mapsto_overlap: forall sh {cs: compspecs} t1 t2 p1 p2 v1 v2,
  nonunit sh ->
  pointer_range_overlap p1 (sizeof t1) p2 (sizeof t2) ->
  mapsto sh t1 p1 v1 * mapsto sh t2 p2 v2 |-- FF.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t1) eqn:AM1; try (rewrite FF_sepcon; auto).
  destruct (access_mode t2) eqn:AM2; try (rewrite normalize.sepcon_FF; auto).
  destruct (type_is_volatile t1); try (rewrite FF_sepcon; auto).
  destruct (type_is_volatile t2); try (rewrite normalize.sepcon_FF; auto).
  destruct p1; try (rewrite FF_sepcon; auto).
  destruct p2; try (rewrite normalize.sepcon_FF; auto).
  if_tac.
  + apply derives_trans with ((EX  v : val,
          address_mapsto m v sh (b, Ptrofs.unsigned i)) *
      (EX  v : val,
          address_mapsto m0 v sh (b0, Ptrofs.unsigned i0))).
    - apply sepcon_derives; apply orp_left.
      * apply andp_left2, (exp_right v1).
        auto.
      * apply andp_left2; auto.
      * apply andp_left2, (exp_right v2).
        auto.
      * apply andp_left2; auto.
    - clear v1 v2.
      rewrite exp_sepcon1.
      apply exp_left; intro v1.
      rewrite exp_sepcon2.
      apply exp_left; intro v2.
      clear H H1; rename H0 into H.
      destruct H as [? [? [? [? ?]]]].
      inversion H; subst.
      inversion H0; subst.
      erewrite !size_chunk_sizeof in H1 by eauto.
      apply address_mapsto_overlap; auto.
  + rewrite sepcon_andp_prop1, sepcon_andp_prop2.
    apply andp_left2, andp_left2.
    apply nonlock_permission_bytes_overlap; auto.
    clear H H1; rename H0 into H.
    erewrite !size_chunk_sizeof in H by eauto.
    destruct H as [? [? [? [? ?]]]].
    inversion H; subst.
    inversion H0; subst.
    auto.
Qed.

Lemma Nat2Z_add_lt: forall n i, Ptrofs.unsigned i + n < Ptrofs.modulus ->
  Z.of_nat (Z.to_nat n) + Ptrofs.unsigned i < Ptrofs.modulus.
Proof.
  intros.
  destruct (zle 0 n).
  + rewrite Z2Nat.id by lia. lia.
  + rewrite Z2Nat_neg by lia.
    pose proof Ptrofs.unsigned_range i.
    simpl.
    lia.
Qed.

Lemma Nat2Z_add_le: forall n i, Ptrofs.unsigned i + n <= Ptrofs.modulus ->
  Z.of_nat (Z.to_nat n) + Ptrofs.unsigned i <= Ptrofs.modulus.
Proof.
  intros.
  destruct (zle 0 n).
  + rewrite Z2Nat.id by lia. lia.
  + rewrite Z2Nat_neg by lia.
    pose proof Ptrofs.unsigned_range i.
    simpl.
    lia.
Qed.

Lemma memory_block_overlap: forall sh p1 n1 p2 n2, nonunit sh -> pointer_range_overlap p1 n1 p2 n2 -> memory_block sh n1 p1 * memory_block sh n2 p2 |-- FF.
Proof.
  intros.
  unfold memory_block.
  destruct p1; try solve [rewrite FF_sepcon; auto].
  destruct p2; try solve [rewrite normalize.sepcon_FF; auto].
  rewrite sepcon_andp_prop1.
  rewrite sepcon_andp_prop2.
  apply normalize.derives_extract_prop; intros.
  apply normalize.derives_extract_prop; intros. 
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; lia | apply Nat2Z_add_lt; lia].
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i0; lia | apply Nat2Z_add_lt; lia].
  unfold memory_block'_alt.
  if_tac.
  + clear H2.
    apply VALspec_range_overlap.
    pose proof pointer_range_overlap_non_zero _ _ _ _ H0.
    rewrite !Z2Nat.id by lia.
    destruct H0 as [[? ?] [[? ?] [? [? ?]]]].
    inversion H0; inversion H4.
    subst.
    auto.
  + apply nonlock_permission_bytes_overlap; auto.
    pose proof pointer_range_overlap_non_zero _ _ _ _ H0.
    rewrite !Z2Nat.id by lia.
    destruct H0 as [[? ?] [[? ?] [? [? ?]]]].
    inversion H0; inversion H5.
    subst.
    auto.
Qed.

Lemma mapsto_conflict:
  forall sh t v v2 v3,
  nonunit sh ->
  mapsto sh t v v2 * mapsto sh t v v3 |-- FF.
Proof.
  intros.
  rewrite (@add_andp (pred rmap) (algNatDed _) _ _ (mapsto_pure_facts sh t v v3)).
  simpl.
  rewrite andp_comm.
  rewrite sepcon_andp_prop.
  apply prop_andp_left; intros [[? ?] ?].
  unfold mapsto.
  rewrite H0.
  destruct (type_is_volatile t); try (rewrite FF_sepcon; auto).
  destruct v; try (rewrite FF_sepcon; auto).
  pose proof (size_chunk_pos x).
  if_tac.
*
  normalize.
  rewrite distrib_orp_sepcon, !distrib_orp_sepcon2;
  repeat apply orp_left;
  rewrite ?sepcon_andp_prop1;  repeat (apply prop_andp_left; intro);
  rewrite ?sepcon_andp_prop2;  repeat (apply prop_andp_left; intro);
  rewrite ?exp_sepcon1;  repeat (apply exp_left; intro);
  rewrite ?exp_sepcon2;  repeat (apply exp_left; intro);
  apply address_mapsto_overlap;
  exists (b, Ptrofs.unsigned i); repeat split; lia.
*
  rewrite ?sepcon_andp_prop1;  repeat (apply prop_andp_left; intro);
  rewrite ?sepcon_andp_prop2;  repeat (apply prop_andp_left; intro).
  apply nonlock_permission_bytes_overlap; auto.
  exists (b, Ptrofs.unsigned i); repeat split; lia.
Qed.

Lemma memory_block_conflict: forall sh n m p,
  nonunit sh ->
  0 < n <= Ptrofs.max_unsigned -> 0 < m <= Ptrofs.max_unsigned ->
  memory_block sh n p * memory_block sh m p |-- FF.
Proof.
  intros.
  unfold memory_block.
  destruct p; try solve [rewrite FF_sepcon; auto].
  rewrite sepcon_andp_prop1.
  apply prop_andp_left; intro.
  rewrite sepcon_comm.
  rewrite sepcon_andp_prop1.
  apply prop_andp_left; intro.
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; lia | rewrite Z2Nat.id; lia].
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; lia | rewrite Z2Nat.id; lia].
  unfold memory_block'_alt.
  if_tac.
  + apply VALspec_range_overlap.
    exists (b, Ptrofs.unsigned i).
    simpl; repeat split; auto; try lia;
    rewrite Z2Nat.id; lia.
  + apply nonlock_permission_bytes_overlap; auto.
    exists (b, Ptrofs.unsigned i).
    repeat split; auto; try rewrite Z2Nat.id; lia.
Qed.

Lemma memory_block_non_pos_Vptr: forall sh n b z, n <= 0 -> memory_block sh n (Vptr b z) = emp.
Proof.
  intros. unfold memory_block.
  rewrite Z_to_nat_neg by auto.
  unfold memory_block'.
  pose proof Ptrofs.unsigned_range z.
  assert (Ptrofs.unsigned z + n < Ptrofs.modulus) by lia.
  apply pred_ext; normalize.
   apply andp_left2; auto.
  apply andp_right; auto.
  intros ? _; simpl; auto.
Qed.

Lemma memory_block_zero_Vptr: forall sh b z, memory_block sh 0 (Vptr b z) = emp.
Proof.
  intros; apply memory_block_non_pos_Vptr.
  lia.
Qed.

Lemma mapsto_zeros_memory_block: forall sh n p,
  readable_share sh ->
  mapsto_zeros n sh p |--
  memory_block sh n p.
Proof.
  intros.
  unfold mapsto_zeros.
  destruct p; try solve [intros ? ?; contradiction].
  rename i into ofs.
  intros. rename H into RS. pose proof I.
  unfold memory_block.
  destruct (zlt n 0).   {
     rewrite Z_to_nat_neg by lia. simpl.
     apply andp_derives; auto.
     intros ? ?. simpl in *. destruct H0.
     lia. 
  }
 apply prop_andp_left; intros [? ?].
 rewrite prop_true_andp by lia.
 assert (n <= Ptrofs.modulus) by lia. clear H H0. rename H1 into H'.
 assert (0 <= n <= Ptrofs.modulus) by lia. clear H2 g.
    rewrite <- (Z2Nat.id n) in H', H by lia.
    forget (Z.to_nat n) as n'.
    clear n.
    remember (Ptrofs.unsigned ofs) as ofs'.
    assert (Ptrofs.unsigned (Ptrofs.repr ofs') = ofs')
      by (subst; rewrite Ptrofs.repr_unsigned; reflexivity).
    assert (0 <= ofs' /\ ofs' + Z.of_nat n' <= Ptrofs.modulus).
    {
      pose proof Ptrofs.unsigned_range ofs.
      lia.
    }
    clear Heqofs' H'.
    assert (Ptrofs.unsigned (Ptrofs.repr ofs') = ofs' \/ n' = 0%nat) by tauto.
    clear H0; rename H2 into H0.
    revert ofs' H H1 H0; induction n'; intros.
    - simpl; auto.
    - destruct H1.
      rewrite inj_S in H2. unfold Z.succ in H2. simpl.
      apply sepcon_derives; auto.
      * unfold mapsto_, mapsto. simpl.
        rewrite if_true by auto.
        apply orp_right2.
        rewrite prop_true_andp by auto.
        apply exp_right with (Vint Int.zero).
        destruct H0; [| lia].
        rewrite H0.
        auto.
      * fold address_mapsto_zeros. fold memory_block'.
        apply IHn'. lia. lia.
        destruct (zlt (ofs' + 1) Ptrofs.modulus).
        rewrite Ptrofs.unsigned_repr; [left; reflexivity | ].
        unfold Ptrofs.max_unsigned; lia.
        right.
           destruct H0; [| inversion H0].
           lia.
Qed.

Lemma memory_block'_split:
  forall sh b ofs i j,
   0 <= i <= j ->
    j <= j+ofs < Ptrofs.modulus ->
   memory_block' sh (Z.to_nat j) b ofs =
      memory_block' sh (Z.to_nat i) b ofs * memory_block' sh (Z.to_nat (j-i)) b (ofs+i).
Proof.
  intros.
  rewrite memory_block'_eq; try rewrite Z2Nat.id; try lia.
  rewrite memory_block'_eq; try rewrite Z2Nat.id; try lia.
  rewrite memory_block'_eq; try rewrite Z2Nat.id; try lia.
  unfold memory_block'_alt.
  repeat (rewrite Z2Nat.id; try lia).
  if_tac.
  + etransitivity ; [ | eapply VALspec_range_split2; [reflexivity | lia | lia]].
    f_equal.
    lia.
  + apply nonlock_permission_bytes_split2; lia.
Qed.

Lemma memory_block_split:
  forall (sh : share) (b : block) (ofs n m : Z),
  0 <= n ->
  0 <= m ->
  n + m <= n + m + ofs < Ptrofs.modulus ->
  memory_block sh (n + m) (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh n (Vptr b (Ptrofs.repr ofs)) *
  memory_block sh m (Vptr b (Ptrofs.repr (ofs + n))).
Proof.
  intros.
  unfold memory_block.
  rewrite memory_block'_split with (i := n); [| lia |].
  2:{
    pose proof Ptrofs.unsigned_range (Ptrofs.repr ofs).
    pose proof Ptrofs.unsigned_repr_eq ofs.
    assert (ofs mod Ptrofs.modulus <= ofs) by (apply Z.mod_le; lia).
    lia.
  } 
  replace (n + m - n) with m by lia.
  replace (memory_block' sh (Z.to_nat m) b (Ptrofs.unsigned (Ptrofs.repr ofs) + n)) with
    (memory_block' sh (Z.to_nat m) b (Ptrofs.unsigned (Ptrofs.repr (ofs + n)))).
  2: {
    destruct (zeq m 0).
    + subst. reflexivity.
    + assert (ofs + n < Ptrofs.modulus) by lia.
      rewrite !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
      reflexivity.
  }
  apply pred_ext.
  + apply prop_andp_left; intros.
    apply sepcon_derives; (apply andp_right; [intros ? _; simpl | apply derives_refl]).
    - lia.
    - rewrite Ptrofs.unsigned_repr_eq.
      assert ((ofs + n) mod Ptrofs.modulus <= ofs + n) by (apply Z.mod_le; lia).
      lia.
  + apply andp_right; [intros ? _; simpl |].
    - rewrite Ptrofs.unsigned_repr_eq.
      assert (ofs mod Ptrofs.modulus <= ofs) by (apply Z.mod_le; lia).
      lia.
    - apply sepcon_derives; apply andp_left2; apply derives_refl.
Qed.

Lemma memory_block_share_join:
  forall sh1 sh2 sh n p,
   sepalg.join sh1 sh2 sh ->
   memory_block sh1 n p * memory_block sh2 n p = memory_block sh n p.
Proof.
  intros.
  destruct p; try solve [unfold memory_block; rewrite FF_sepcon; auto].
  destruct (zle 0 n).
  2:{
    rewrite !memory_block_non_pos_Vptr by lia.
    rewrite emp_sepcon; auto.
  }
  unfold memory_block.
  destruct (zlt (Ptrofs.unsigned i + n) Ptrofs.modulus).
  + rewrite !prop_true_andp by auto.
    repeat (rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; lia | rewrite Z2Nat.id; lia]).
    unfold memory_block'_alt.
    destruct (readable_share_dec sh1), (readable_share_dec sh2).
    - rewrite if_true by (eapply readable_share_join; eauto).
      apply VALspec_range_share_join; auto.
    - rewrite if_true by (eapply readable_share_join; eauto).
      rewrite sepcon_comm.
      apply nonlock_permission_bytes_VALspec_range_join; auto.
    - rewrite if_true by (eapply readable_share_join; eauto).
      apply nonlock_permission_bytes_VALspec_range_join; auto.
    - rewrite if_false.
      * apply nonlock_permission_bytes_share_join; auto.
      * eapply join_unreadable_shares; eauto.
  + rewrite !prop_false_andp by auto.
    rewrite FF_sepcon; auto.
Qed.

Lemma mapsto_pointer_void:
  forall sh t a, 
   eqb_type (Tpointer t a) int_or_ptr_type = false ->
   eqb_type (Tpointer Tvoid a) int_or_ptr_type = false ->
   mapsto sh (Tpointer t a) = mapsto sh (Tpointer Tvoid a).
Proof.
intros.
unfold mapsto.
extensionality v1 v2.
unfold tc_val', tc_val. rewrite H, H0.
reflexivity.
Qed.

Lemma is_pointer_or_null_nullval: is_pointer_or_null nullval.
Proof.
unfold is_pointer_or_null, nullval.
simple_if_tac; auto.
Qed.
#[export] Hint Resolve is_pointer_or_null_nullval : core.

Lemma tc_val_pointer_nullval':
 forall t a, tc_val (Tpointer t a) nullval.
Proof.
 intros. hnf. unfold nullval.
 simple_if_tac; hnf;
 simple_if_tac; auto.
Qed.
#[export] Hint Resolve tc_val_pointer_nullval' : core.

Arguments type_is_volatile ty / .

Definition is_int32_noattr_type t :=
 match t with
 | Tint I32 _ {| attr_volatile := false; attr_alignas := None |} => True
 | _ => False
 end.

Lemma mapsto_mapsto_int32:
  forall sh t1 t2 p v,
   is_int32_noattr_type t1 ->
   is_int32_noattr_type t2 ->
   mapsto sh t1 p v |-- mapsto sh t2 p v.
Proof.
intros.
destruct t1; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
destruct t2; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
apply derives_refl.
Qed.

Lemma mapsto_mapsto__int32:
  forall sh t1 t2 p v,
   is_int32_noattr_type t1 ->
   is_int32_noattr_type t2 ->
   mapsto sh t1 p v |-- mapsto_ sh t2 p.
Proof.
intros.
destruct t1; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
destruct t2; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
unfold mapsto_. apply mapsto_mapsto_.
Qed.

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh (Tint I32 Unsigned noattr) = mapsto sh (Tint I32 Signed noattr).
Proof.
intros.
extensionality v1 v2.
reflexivity.
Qed.

Lemma tc_val_pointer_nullval:
 forall t, tc_val (Tpointer t noattr) nullval.
Proof.
 intros. unfold nullval; simpl.
 rewrite andb_false_r.
 hnf. simple_if_tac; auto.
Qed.
#[export] Hint Resolve tc_val_pointer_nullval : core.

Lemma mapsto_tuint_tptr_nullval:
  forall sh p t, mapsto sh (Tpointer t noattr) p nullval = mapsto sh size_t p nullval.
Proof.
intros.
unfold mapsto, size_t.
destruct p; try reflexivity.
destruct Archi.ptr64 eqn:Hp.
*
simpl access_mode; cbv beta iota.
simpl type_is_volatile;  cbv beta iota.
unfold Mptr; rewrite Hp. 
if_tac.
rewrite !prop_true_andp by auto.
f_equal.
rewrite prop_true_andp; auto.
unfold nullval;rewrite Hp; apply I.
f_equal.
f_equal.
f_equal.
apply prop_ext; split; intros _ _;
unfold nullval; rewrite Hp; hnf; auto.
simple_if_tac; simpl; rewrite Hp; auto.
*
simpl access_mode; cbv beta iota.
simpl type_is_volatile;  cbv beta iota.
unfold Mptr; rewrite Hp. 
if_tac.
rewrite !prop_true_andp by auto.
f_equal.
rewrite prop_true_andp; auto.
unfold nullval;rewrite Hp; apply I.
f_equal.
f_equal.
f_equal.
apply prop_ext; split; intros _ _;
unfold nullval; rewrite Hp; hnf; auto.
simple_if_tac; simpl; rewrite Hp; auto.
Qed.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v,
   Archi.ptr64 = false -> 
             mapsto sh (Tint I32 Signed noattr) v nullval =
             mapsto sh (Tpointer t noattr) v nullval.
Proof.
  intros.
  try solve [inversion H];
 (
  unfold mapsto, nullval; rewrite H;
  simpl;
  destruct v; auto; f_equal; auto;
  if_tac;
   [f_equal; f_equal; rewrite andb_false_r;
   unfold is_pointer_or_null; rewrite H;
   apply pred_ext; unfold derives; simpl; tauto
   | f_equal; f_equal;
      unfold tc_val';
      f_equal; simpl; 
      simple_if_tac; simpl; rewrite H; auto;
      apply prop_ext; intuition]).
Qed.

Lemma repr_inj_unsigned:
  forall i j,
    0 <= i <= Int.max_unsigned ->
    0 <= j <= Int.max_unsigned ->
    Int.repr i = Int.repr j -> i=j.
Proof.
intros.
rewrite <- (Int.unsigned_repr i) by auto.
rewrite <- (Int.unsigned_repr j) by auto.
congruence.
Qed.

Lemma mapsto_zeros_mapsto_nullval:
  forall sh b z t,
      readable_share sh ->
      (align_chunk Mptr | Ptrofs.unsigned z) -> 
      mapsto_zeros (size_chunk Mptr) sh (Vptr b z) |--
      !! (0 <= Ptrofs.unsigned z /\ size_chunk Mptr + Ptrofs.unsigned z < Ptrofs.modulus) && mapsto sh (Tpointer t noattr) (Vptr b z) nullval.
Proof.
intros until t. intros H2 H.
unfold mapsto_zeros, mapsto.
simpl.
rewrite andb_false_r by auto.
rewrite (prop_true_andp (is_pointer_or_null _)) by auto.
apply prop_andp_left; intros [? ?].
rewrite prop_true_andp by  auto.
rewrite if_true by auto.
apply orp_right1.
unfold address_mapsto.
apply exp_right with  (encode_val (if Archi.ptr64 then Mint64 else Mint32) nullval).
rewrite prop_true_andp by (split3; simpl; auto).
forget (Ptrofs.unsigned z) as ofs; clear z.
replace (encode_val (if Archi.ptr64 then Mint64 else Mint32) nullval)
 with (repeat (Byte Byte.zero) (size_chunk_nat Mptr))
 by (unfold size_chunk_nat, size_chunk, Mptr, encode_val, nullval; simpl; destruct Archi.ptr64; simpl;
      change (Int64.unsigned Int64.zero) with 0;
      change (Int.unsigned Int.zero) with 0;
      unfold encode_int, inj_bytes; simpl; compute;
      destruct Archi.big_endian; simpl; reflexivity).
rewrite size_chunk_conv, Nat2Z.id.
clear - H2. simpl snd.
revert ofs; induction (size_chunk_nat Mptr); intros.
*
unfold address_mapsto_zeros.
apply andp_right.
apply allp_right; intro y.
rewrite jam_false.
intros ? ?. do 3 red. do 3 red in H.
apply resource_at_identity; auto.
simpl; destruct y; intros [? ?]; lia.
intros ? ?. do 3 red in H|-*. apply ghost_of_identity; auto.
*
rewrite inj_S.
simpl snd in *.
rewrite allp_jam_split2 with 
  (q := (fun loc : address =>
              yesat NoneP
                (VAL (nth (Z.to_nat (snd loc - ofs)) (repeat (Byte Byte.zero) (S n)) Undef)) sh loc))
  (r := (fun loc : address =>
              yesat NoneP
                (VAL (nth (Z.to_nat (snd loc - ofs)) (repeat (Byte Byte.zero) (S n)) Undef)) sh loc))
(Q_DEC := adr_range_dec (b,ofs) 1) (R_DEC := adr_range_dec ( b, Z.succ ofs) (Z.of_nat n)); auto.
5:{ split; intros. destruct a; split; intros. destruct H; subst b0. destruct (zeq z ofs); [left|right]; split; auto; lia.
     destruct H; destruct H; subst b0; split; auto; lia. destruct a; destruct H,H0; subst; lia. }
simpl.
apply sepcon_derives.
--
clear IHn.
unfold address_mapsto.
apply exp_left; intro bl.
rewrite andp_assoc.
apply prop_andp_left.
 intros [? ?].
apply andp_derives; auto.
apply allp_derives; intro y.
simpl.
destruct H0.
destruct bl; inv H. destruct bl; inv H4.
destruct (adr_range_dec (b, ofs) 1 y).
++
rewrite !jam_true by auto.
destruct y; destruct a; subst b0. assert (z=ofs) by lia. subst z.
simpl snd. rewrite Z.sub_diag. simpl.
replace m with (Byte Byte.zero); auto.
clear - H0.
destruct m; try discriminate.
rewrite decode_byte_val in H0.
apply Vint_inj in H0.
f_equal.
rewrite zero_ext_inrange in H0.
unfold Int.zero in H0.
apply repr_inj_unsigned in H0.
apply (f_equal Byte.repr) in H0.
rewrite Byte.repr_unsigned in H0. auto.
pose proof (Byte.unsigned_range i). 
change Byte.modulus with 256 in H.
split; try lia.
apply Z.le_trans with 256; try lia. compute; congruence.
split. lia. compute; congruence.
rewrite Int.unsigned_repr.
pose proof (Byte.unsigned_range i).
change Byte.modulus with 256 in H. simpl. lia.
pose proof (Byte.unsigned_range i).
assert (Byte.modulus < Int.max_unsigned) by reflexivity.
lia.
++
rewrite !jam_false by auto.
auto.
--
eapply derives_trans.
apply IHn.
clear IHn.
apply andp_derives; auto.
apply allp_derives; intros [b' ofs'].
destruct (adr_range_dec (b, Z.succ ofs) (Z.of_nat n) (b',ofs')); [rewrite !jam_true | rewrite !jam_false]; auto.
 simpl snd.
match goal with |- yesat _ (VAL ?A) _ _ |-- yesat _ (VAL ?B) _ _ => replace A with B; auto end.
change (?A = ?B) with (nth (Z.to_nat (ofs' - ofs)) (repeat (Byte Byte.zero) (S n)) Undef = B).
destruct a.
subst b'.
assert (0 <= ofs'- Z.succ ofs < Z.of_nat n) by lia.
replace (ofs'-ofs) with (Z.succ (ofs'-Z.succ ofs)) by lia.
clear - H.
forget (ofs'-Z.succ ofs) as i.
rewrite Z2Nat.inj_succ by lia.
simpl. auto.
--
eexists; apply is_resource_pred_YES_VAL'.
--
eexists; apply is_resource_pred_YES_VAL'.
--
eexists; apply is_resource_pred_YES_VAL'.
--
intros.
destruct H0.
hnf in H0. rewrite H0 in H1.
inv H1; auto.
Qed.

Lemma address_mapsto_zeros_split {sh b}: forall n n1 n2 z (N:(n=n1+n2)%nat),
      address_mapsto_zeros sh n (b,z) |--
      address_mapsto_zeros sh n1 (b,z) *
      address_mapsto_zeros sh n2 (b,Z.of_nat n1+z).
Proof.
induction n.
+ simpl; intros. destruct n1; destruct n2; simpl; try lia. rewrite emp_sepcon; trivial.
+ intros. simpl. destruct n1; simpl  in N.
  - subst. simpl. rewrite emp_sepcon; trivial.
  - inv N. rewrite Nat2Z.inj_succ. simpl. rewrite sepcon_assoc. 
     apply sepcon_derives. trivial. 
     eapply derives_trans. apply (IHn n1 n2). trivial.
     replace (Z.of_nat n1 + Z.succ z) with (Z.succ (Z.of_nat n1) + z) by lia; trivial.
Qed.

Lemma mapsto_zeros_split sh a n1 n2 (N1: 0 <= n1) (N2: 0<=n2):
      mapsto_zeros (n1+n2) sh a |-- mapsto_zeros n1 sh a * mapsto_zeros n2 sh (offset_val n1 a).
Proof. destruct a; simpl; try solve [ rewrite FF_sepcon; trivial]; intros m [H M]; simpl in H.
rewrite Z2Nat.inj_add in M by lia.
apply (address_mapsto_zeros_split (Z.to_nat n1 + Z.to_nat n2) (Z.to_nat n1) (Z.to_nat n2) _ (eq_refl _)) in M.
destruct M as [m1 [m2 [J [M1 M2]]]].
exists m1, m2; split3.
+ trivial.
+ split; [ simpl; lia | trivial].
+ replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr n1) )) with (Z.of_nat (Z.to_nat n1) + Ptrofs.unsigned i).
  - split; [ simpl; lia | trivial]. 
  - clear - H N1 N2. rewrite Z2Nat.id, Ptrofs.add_commut by trivial.
    rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr n1); [| unfold Ptrofs.max_unsigned; lia].
    rewrite Ptrofs.unsigned_repr; trivial. unfold Ptrofs.max_unsigned; lia.
Qed.

Fixpoint sepconN N (P: val -> mpred) sz (p:val):mpred :=
  match N with
    O => emp
  | S n => (P p * sepconN n P sz (offset_val sz p))
  end.

Lemma mapsto_zeros_mapsto_nullval_N {cenv sh b t}: forall N z,
       readable_share sh ->
       (align_chunk Mptr | Ptrofs.unsigned z) ->
       mapsto_zeros (Z.of_nat N * size_chunk Mptr) sh (Vptr b z)
       |-- !! (0 <= Ptrofs.unsigned z /\
               Z.of_nat N * size_chunk Mptr + Ptrofs.unsigned z < Ptrofs.modulus) &&
           sepconN N (fun p => mapsto sh (Tpointer t noattr) p nullval)
                     (@sizeof cenv (Tpointer t noattr)) (Vptr b z).
Proof.
  induction N; intros; trivial. remember (size_chunk Mptr) as sz.
  replace (Z.of_nat (S N) * sz)%Z with (sz + Z.of_nat N * sz)%Z by lia.
  specialize (size_chunk_pos Mptr); intros. specialize (Z_of_nat_ge_O N); intros.
  eapply derives_trans. apply mapsto_zeros_split; subst; try first [lia | apply Z.mul_nonneg_nonneg; lia].
  apply andp_right.
  { clear IHN. intros m [m1 [m2 [J [[M1 _] [[M2a M2b] _]]]]]; simpl in *.
    split; try lia. rewrite Ptrofs.add_unsigned in M2b, M2a.
    rewrite (Ptrofs.unsigned_repr sz), Ptrofs.unsigned_repr in M2b, M2a; try lia.
    all: subst; unfold size_chunk, Mptr in *; simple_if_tac; unfold Ptrofs.max_unsigned; try lia. }
  subst sz.
  eapply derives_trans.
  + eapply sepcon_derives.
    - apply mapsto_zeros_mapsto_nullval; trivial.
    - apply derives_refl.
  + rewrite sepcon_andp_prop1. apply prop_andp_left; intros.
    simpl sepconN. apply sepcon_derives. apply derives_refl.
    replace (offset_val (size_chunk Mptr) (Vptr b z)) with (Vptr b (Ptrofs.add z (Ptrofs.repr (if Archi.ptr64 then 8 else 4)))).
    - eapply derives_trans. apply IHN; trivial.
      { clear IHN. rewrite Ptrofs.add_unsigned.
        rewrite (Ptrofs.unsigned_repr (if Archi.ptr64 then 8 else 4)).
        + rewrite Ptrofs.unsigned_repr.
          - apply Z.divide_add_r; trivial. unfold align_chunk, Mptr. simple_if_tac; apply Z.divide_refl.
          - unfold size_chunk, Mptr in H3. simple_if_tac; unfold Ptrofs.max_unsigned; lia.
       + unfold size_chunk, Mptr in H3. simple_if_tac; unfold Ptrofs.max_unsigned; lia. }
      apply andp_left2; trivial.
    - simpl. unfold Mptr. destruct Archi.ptr64; simpl; trivial.
Qed.

Lemma address_mapsto_zeros'_split:
  forall a b sh p,
 0<=a -> 0 <= b -> 
 mapsto_memory_block.address_mapsto_zeros' (a+b) sh p =
 mapsto_memory_block.address_mapsto_zeros' a sh p 
 * mapsto_memory_block.address_mapsto_zeros' b sh (adr_add p a).
Proof.
intros.
unfold address_mapsto_zeros'.
rewrite !Z.max_l by lia.
apply allp_jam_split2; auto.
exists (fun (r : resource) (_ : address) (_ : nat) =>
        exists (b0 : memval) (rsh : readable_share sh),
          r =
          YES sh rsh (VAL (Byte Byte.zero))
            (SomeP (rmaps.ConstType unit) (fun _ : list Type => tt))).
hnf; intros.
unfold yesat.
simpl.
apply prop_ext; split; intro.
destruct H1. exists (Byte Byte.zero). exists x. auto.
destruct H1. auto.
exists (fun (r : resource) (_ : address) (_ : nat) =>
        exists (b0 : memval) (rsh : readable_share sh),
          r =
          YES sh rsh (VAL (Byte Byte.zero))
            (SomeP (rmaps.ConstType unit) (fun _ : list Type => tt))).
hnf; intros.
unfold yesat.
simpl.
apply prop_ext; split; intro.
destruct H1. exists (Byte Byte.zero). exists x. auto.
destruct H1. auto.
exists (fun (r : resource) (_ : address) (_ : nat) =>
        exists (b0 : memval) (rsh : readable_share sh),
          r =
          YES sh rsh (VAL (Byte Byte.zero))
            (SomeP (rmaps.ConstType unit) (fun _ : list Type => tt))).
hnf; intros.
unfold yesat.
simpl.
apply prop_ext; split; intro.
destruct H1. exists (Byte Byte.zero). exists x. auto.
destruct H1. auto.
split. intros q.
split; intro.
destruct (zlt (snd q) (snd p + a)); [left|right].
hnf in H1|-*. destruct p,q. simpl in *. lia.
hnf in H1|-*. destruct p,q. simpl in *. lia.
hnf in H1|-*. destruct p,q. simpl in *. lia.
intros q ?.
hnf in H1|-*. destruct p,q. simpl in *. lia.
intros.
hnf in H2.
destruct H2.
hnf in H2.
rewrite H2 in H3.
inv H3. auto.
Qed.

Lemma address_mapsto_address_mapsto_zeros:
  forall sh b z, 
  (align_chunk Mptr | z) ->
  mapsto_memory_block.address_mapsto_zeros' (size_chunk Mptr) sh (b,z)
  |-- res_predicates.address_mapsto Mptr nullval sh (b, z).
Proof.
intros.
rename H into Halign.
intros ? ?.
hnf in H|-*.
exists (list_repeat (size_chunk_nat Mptr) (Byte Byte.zero)).
destruct H; split; auto.
clear H0.
split.
split3; auto.
intros y. specialize (H y).
rewrite Z.max_l in H by (pose proof (size_chunk_pos Mptr); lia).
hnf in H|-*.
if_tac; auto.
replace (VAL _) with (VAL (Byte Byte.zero)); auto.
f_equal.
simpl.
destruct y.
destruct H0.
subst b0.
rewrite size_chunk_conv in H1.
simpl.
forget (size_chunk_nat Mptr) as n.
clear b H.
forget (Byte Byte.zero) as b.
assert (Z.to_nat (z0-z) < n)%nat by lia.
forget (Z.to_nat (z0-z)) as i.
clear - H.
revert i H; induction n; intros; auto.
lia.
destruct i.
simpl. auto.
simpl.
apply IHn. lia.
Qed.