Require Export msl.msl_standard.
Require Import veric.base.
Require Import veric.rmaps.
Require Import veric.rmaps_lemmas.

Inductive kind : Type := VAL : memval -> kind 
                                   | LK : Z -> kind 
                                   | CT: Z -> kind 
                                   | FUN: funsig -> kind.

Definition isVAL (k: kind) := match k with | VAL _ => True | _ => False end.
Definition isFUN (k: kind) := match k with | FUN _ => True | _ => False end.

Lemma isVAL_i: forall v, isVAL (VAL v).
Proof. intros; simpl; auto. Qed.
Hint Resolve isVAL_i.

Lemma isVAL_dec: forall k, {isVAL k}+{~isVAL k}.
Proof.
intros; destruct k; auto.
Qed.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition some_address : address := (xH,0).
Definition kind := kind.

Definition valid (f: address -> option (pshare*kind)) := 
  forall b ofs, 
     match f (b,ofs) with
     | Some (sh, LK n) => forall i, 0 < i < n -> f(b,ofs+i) = Some (sh, CT i)
     | Some (sh, CT i) => exists n, 0 < i < n /\ f(b,ofs-i) = Some (sh,LK n)
     | _ => True
    end.

Lemma valid_empty: valid (fun _ => None).
Proof.
unfold valid; intros.
auto.
Qed.

Lemma valid_join: forall f g h : address -> option (pshare * kind),
   @join _ (Join_fun address (option (pshare * kind))
                   (Join_lower (Join_prod pshare Join_pshare kind (Join_equiv kind))))
      f g h  ->
 valid f -> valid g -> valid h.
Proof.
 unfold valid; intros f g h J H H0 b ofs.
case_eq (h(b,ofs)); auto; intros [sh k] ?.
destruct k; auto; intros.
(**  LK -> CT **)
 generalize (H b ofs); intro H'; generalize (H0 b ofs); intro H0'.
 generalize (J (b,ofs)); rewrite H1; intro H8.
 inv H8. clear H'.  rewrite H6 in H0'. specialize (H0' _ H2).
 specialize (J (b,ofs+i)); rewrite H0' in J. 
 inv J; auto.
 specialize (H b (ofs+i)). rewrite <- H3 in H. destruct a1. inv H8. simpl in *.
 inv H9. destruct H as [n [? ?]]. replace (ofs+i-i) with ofs in H8 by omega.
 rewrite <- H4 in H8; inv H8.
 clear H0'. rewrite H6 in H'. specialize (H' _ H2).
 specialize (J (b,ofs+i)); rewrite H' in J. 
 inv J; auto.
 specialize (H0 b (ofs+i)). rewrite <- H4 in H0. destruct a2. inv H8. simpl in *.
 inv H9. destruct H0 as [n [? ?]]. replace (ofs+i-i) with ofs in H8 by omega.
 rewrite <- H5 in H8; inv H8.
 rewrite <- H3 in H'. rewrite <- H4 in H0'. destruct a1; destruct a2.
 destruct H6. simpl in *. destruct H6; subst k k0.
 specialize (H b (ofs+i)); specialize (H0 b (ofs+i)).
 rewrite (H0' _ H2) in H0.  rewrite (H' _ H2) in H.
 destruct H as [n [? ?]]; destruct H0 as [n' [? ?]].
 replace (ofs+i-i) with ofs in H6,H7 by omega.
 rewrite <- H4 in H7; inv H7. rewrite <- H3 in H6; inv H6.
 specialize (J (b,ofs+i)). rewrite (H' _ H2) in J. rewrite (H0' _ H2) in J.
 inv J; auto. inv H9; auto. simpl in *. destruct a3; simpl in *. inv H7. 
 f_equal. f_equal. eapply join_eq; eauto.
(** CT -> LK **)
 generalize (H b ofs); intros H'; generalize (H0 b ofs); intro H0'.
 generalize (J (b,ofs)); intro H8; inv H8.
 rewrite H1 in H5. rewrite H5 in H0'. destruct H0' as [n [? ?]]; exists n; split; auto.
 specialize (J (b,ofs-z)); rewrite H4 in J.
 inv J; auto. destruct a1; destruct a3. destruct H9. simpl in *. inv H9.
 specialize (H b (ofs-z)). rewrite <- H6 in H.
 specialize (H _ H2). 
 replace (ofs-z+z) with ofs in H by omega. congruence.
 rewrite H1 in H5. rewrite H5 in H'. destruct H' as [n [? ?]]; exists n; split; auto.
 specialize (J (b,ofs-z)); rewrite H3 in J.
 inv J; auto. destruct a2; destruct a3. destruct H9. simpl in *. inv H9. 
 specialize (H0 b (ofs-z)). rewrite <- H7 in H0.
 specialize (H0 _ H2). 
 replace (ofs-z+z) with ofs in H0 by omega. congruence.
 destruct a1; destruct a2; destruct a3.
 rewrite <- H3 in H0'; rewrite <- H2 in H'. destruct H5. destruct H6. simpl in *; subst. 
 rewrite H1 in H4. inv H4. 
 destruct H' as [n [? ?]]. exists n; split; auto.
 specialize (J (b,ofs-z)). rewrite H6 in J.
 assert (g (b,ofs-z) = Some (p0, LK n)).
 destruct H0' as [n' [? ?]]. rewrite H8 in J. inv J. destruct H12. inv H10; simpl in *. inv H12; auto.
 rewrite H7 in J. inv J. inv H11. simpl in *. destruct a3; simpl in *. inv H9.
 repeat f_equal. eapply join_eq; auto.
Qed.

End CompCert_AV.

Lemma getVAL: forall k, {v : memval & k = VAL v}  + {~isVAL k}.
Proof.
intros.
destruct k;
  try solve [simpl; right; tauto].
left.
eauto.
Qed.

Lemma VAL_inj: forall v v', VAL v = VAL v' -> v = v'.
Proof.
intros.
inv H; auto.
Qed.

Lemma VAL_valid:
 forall (f: address -> option (pshare*kind)),
   (forall l sh k, f l = Some (sh,k) -> isVAL k) ->
   CompCert_AV.valid f.
Proof.
intros.
intros b ofs.
case_eq (f (b,ofs)); intros; auto.
destruct p.
specialize (H _ _ _ H0).
destruct k; try solve [auto | inversion H].
Qed.

Lemma VAL_or_FUN_valid:
 forall (f: address -> option (pshare*kind)),
   (forall l sh k, f l = Some (sh,k) -> isVAL k \/ isFUN k) ->
   CompCert_AV.valid f.
Proof.
intros.
intros b ofs.
case_eq (f (b,ofs)); intros; auto.
destruct p.
specialize (H _ _ _ H0).
destruct k; try solve [auto | simpl in H; tauto].
Qed.

Lemma blockwise_valid:
  forall f,
    (forall b, exists g, CompCert_AV.valid g /\ forall ofs, f (b,ofs) = g (b,ofs)) ->
     CompCert_AV.valid f.
Proof.
intros.
intros b ofs.
destruct (H b); clear H.
destruct H0.
rewrite H0.
generalize (H b ofs); case_eq (x (b,ofs)); intros; auto.
destruct p; auto.
destruct k; auto.
intros.
rewrite H0; auto.
destruct H2 as [n [? ?]]; exists n; split; auto.
rewrite H0; auto.
Qed.

Lemma store_valid:
  forall (f f' :  address -> option (pshare*kind)),
   CompCert_AV.valid f ->
     (forall l, f l = f' l \/ 
                  match f l, f' l with
                  | Some (_, k) , Some (_, k') =>    isVAL k /\ isVAL k' 
                  | Some(_, k), None => isVAL k
                  | None, Some(_, k') => isVAL k'
                  | None, None => True
                  end) ->
   CompCert_AV.valid f'.
Proof.
intros.
intros b ofs.
generalize (H b ofs) (H0 (b,ofs)).
case_eq (f' (b,ofs)); simpl in *; intros; auto.
destruct p.
destruct k; simpl; auto.
intros.
destruct H3.
rewrite H3 in H2.
specialize (H2 _ H4).
spec H0 (b,ofs+i).
destruct H0.
congruence.
rewrite H2 in H0.
destruct (f' (b,ofs+i)).
destruct p0.
destruct H0.
destruct H0; inv H0.
destruct H0; inv H0.
destruct (f(b,ofs)).
destruct p0.
destruct H3.
inv H5.
inv H3.
destruct H3.
rewrite H3 in H2.
destruct H2 as [n [? ?]]; exists n; split; auto.
specialize (H0 (b,ofs-z)).
destruct H0; try congruence.
rewrite H4 in H0.
destruct (f' (b,ofs-z)); auto.
destruct p0.
destruct H0.
destruct H0; inv H0.
destruct H0; inv H0.
destruct (f(b,ofs)).
destruct p0.
destruct H3.
inv H4.
inv H3.
Qed.

Instance EqDec_kind: EqDec kind.
Proof.
  hnf. decide equality; try apply eq_dec; try apply zeq.
Qed.

Module R := Rmaps (CompCert_AV).
Module RML := Rmaps_Lemmas(R).

Export RML. 
Export R.

Lemma rmap_valid_e1: forall r b ofs n i, 0 < i < n -> 
     forall sh, res_option (r @ (b,ofs)) = Some (sh, LK n) -> res_option (r @ (b,ofs+i))= Some (sh, CT i).
Proof.
intros until sh.
generalize (rmap_valid r b ofs); unfold compose.
case_eq (r @ (b,ofs)); simpl; intros; try discriminate.
inv H2.
auto.
Qed.

Lemma rmap_valid_e2:  forall r b ofs i sh,
    res_option (r @ (b,ofs+i)) = Some (sh, CT i) -> 
            exists n, 0 < i < n /\ res_option (r @ (b,ofs)) = Some (sh, LK n).
Proof.
intros until sh.
generalize (rmap_valid r b (ofs+i)); unfold compose.
case_eq (r @ (b,ofs+i)); simpl; intros; try discriminate.
inv H1.
destruct H0 as [n [? ?]].
replace (ofs+i-i) with ofs in H1 by omega.
eauto.
Qed.

Definition mk_pshare : forall p: Share.t, nonunit p -> pshare := exist nonunit.

Lemma mk_share_pshare_sh: forall p (H: nonunit (pshare_sh p)),
  mk_pshare (pshare_sh p) H = p.
Proof.
  intros.
  unfold mk_pshare.
  destruct p; simpl.
  auto.
Qed.

Definition fixup_splitting
  (a:address -> Share.t) (z: address -> option (pshare * kind)) :=
  fun l => 
    match z l with
    | Some (sh, CT i) => 
       match dec_share_identity (a (fst l, snd l - i)) with
       | left _ => None
       |right p => Some (mk_pshare _ (nonidentity_nonunit p),  CT i)
       end
    | Some (sh, k) =>
       match dec_share_identity (a l) with
       | left _ => None
       |right p => Some (mk_pshare _ (nonidentity_nonunit p),  k)
       end
    | None => None
    end.

Definition share_of (x: option (pshare * kind)) : Share.t :=
  match x with Some (p,_) => pshare_sh p | None => Share.bot end.

Definition Join_pk := (Join_lower (Join_prod pshare _ kind (Join_equiv _))).

Lemma fixup_splitting_valid : forall (a: address->Share.t) (z:address -> option (pshare * kind)),
    (forall x, join_sub (a x) (share_of (z x))) ->
    AV.valid z ->
    AV.valid (fixup_splitting a z).
Proof.
  unfold AV.valid, res_option, compose; intros.
  unfold fixup_splitting.
  spec H0 b ofs.
  case_eq (z (b,ofs)); intros;
    rewrite H1 in H0; auto. destruct p.
  destruct k. simpl.
  destruct (dec_share_identity (a (b,ofs))); auto.
  destruct (dec_share_identity (a (b,ofs))); auto.
  intros.
  generalize (H0 _ H2); intros.
  rewrite  H3. simpl. replace (ofs+i-i) with ofs by omega.
  destruct (dec_share_identity (a (b,ofs))); auto; contradiction.
  simpl.
  destruct H0 as [n [? ?]].
  destruct ( dec_share_identity (a (b, ofs - z0))); auto.
  exists n. split; auto.
  rewrite H2.
  destruct ( dec_share_identity (a (b, ofs - z0))); auto; contradiction.
  simpl.
  destruct (dec_share_identity (a (b,ofs))); auto.
Qed.

Lemma share_of_Some: forall p: pshare * AV.kind, nonidentity (share_of (Some p)).
Proof.
 intros. destruct p as [[? ?] ?]; simpl.
apply nonunit_nonidentity ;auto.
Qed.

Lemma fixup_join : forall a (ac ad: address -> Share.t)  z,
  AV.valid a ->
  AV.valid z ->
  (forall x, @join_sub _ Join_pk (a x) (z x)) ->
  (forall x, join (ac x) (ad x) (share_of (a x))) ->
  (forall x,
    @join _ Join_pk 
    (fixup_splitting ac z x)
    (fixup_splitting ad z x)
    (a x)).
Proof.
  intros.
  unfold fixup_splitting.
  case_eq (z x); intros.
  destruct p;  destruct k.
  destruct (dec_share_identity (ac x)); auto.
  specialize (H2 x). apply join_unit1_e in H2; auto. 
  destruct (dec_share_identity (ad x)); auto.
  destruct (a x); try constructor.
  contradiction (share_of_Some p0). rewrite <- H2; auto.
  forget (ad x) as adx.  subst adx.
  specialize (H1 x). rewrite H3 in H1. destruct H1.
  apply join_unit1; [ apply None_unit |].
  destruct (a x); [  | simpl in n; contradiction n; auto].
  destruct p0. simpl in *.
  destruct p0; simpl in *. 
  assert (k = VAL m). inv H1; auto. inv H6; auto. destruct H2; simpl in *; subst; auto.
  subst. f_equal. f_equal. unfold mk_pshare. f_equal. 
  apply proof_irr.
  destruct (dec_share_identity (ad x)); auto.
  apply join_unit2; [ apply None_unit |].
  specialize (H1 x). rewrite H3 in H1. destruct H1.
  specialize (H2 x). apply join_unit2_e in H2; auto. 
  forget (ac x) as acx.  subst acx.
  destruct (a x); [  | simpl in n; contradiction n; auto].
  destruct p0. simpl in *.
  destruct p0; simpl in *.  
  assert (k = VAL m). inv H1; auto. inv H6; auto. destruct H2; simpl in *; subst; auto.
  subst. f_equal. f_equal. apply exist_ext. auto.
  specialize (H1 x); specialize (H2 x).
  destruct (a x).
  constructor. destruct p0. destruct p0.
  simpl in H2. 
  rewrite H3 in H1.
  assert (k = VAL m). inv H1; auto. inv H4; auto. destruct H7; simpl in *; subst; auto.
  destruct H4; subst; auto. subst k.  
 constructor; auto.
 simpl in H2. apply split_identity in H2; auto. contradiction.
 destruct (dec_share_identity (ac x)); auto.
 generalize (H2 x); intro. apply join_unit1_e in H4; auto. rewrite H4.
 destruct (dec_share_identity (share_of (a x))); auto.
 destruct (a x); try constructor.
 contradiction (share_of_Some p0).
 apply join_unit1; [ apply None_unit |].
 generalize (H1 x); intro.
 destruct H5. rewrite H3 in H5.
 destruct (a x). inv H5. simpl.
 destruct p; simpl.  
 f_equal. f_equal. apply exist_ext. auto.
 destruct p0. destruct a2. destruct H9. destruct H6. simpl in *; subst.
 repeat f_equal. destruct p0; apply exist_ext; auto.
 contradict n. simpl. apply bot_identity.
 destruct (dec_share_identity (ad x)); auto.
 apply join_unit2; [ apply None_unit |].
 generalize (H1 x); rewrite H3; intro.
 destruct H4.
 generalize (H2 x); intro. apply join_unit2_e in H5; auto.
 remember (ac x) as acx.
 subst acx.
 destruct (a x). destruct p0. destruct p0. simpl.
 f_equal. f_equal. apply exist_ext; auto.
 clear - H4; inv H4; auto. destruct a2; inv H2; auto. simpl in *. destruct H0; subst; auto.
 contradiction n. rewrite H5; simpl. auto.
 generalize (H1 x); rewrite H3; intro.
 generalize (H2 x); intro.
 destruct (a x). destruct p0. destruct p0.
 constructor. constructor. simpl.
 do 3 red; simpl. simpl in H5. auto.
 simpl. clear - H4. destruct H4. inv H; auto. destruct a2; destruct  H3 as [? [? ?]]; simpl in *; subst; auto.
 apply split_identity in H5; auto. contradiction.
 destruct x as [b ofs].
 simpl in *.
 destruct (dec_share_identity (ac (b, ofs - z0))).
 apply join_unit1; [ apply None_unit |].
 generalize (H2 (b,ofs-z0)); intro.
 apply join_unit1_e in H4; auto.
 rewrite H4.
 generalize (H0 b ofs); rewrite H3; intros [n [? ?]].
 case_eq (a (b,ofs)); intros.
 destruct p0. 
 assert (k = CT z0). generalize (H1 (b,ofs)); rewrite H7; intros [? H9]; inv H9; try congruence.
 rewrite H3 in H10. inv H10. destruct a2. destruct H12. destruct H9; simpl in *; subst; auto.
 subst k.
 specialize (H b ofs). rewrite H7 in H. destruct H as [? [? ?]].
 rewrite H8. simpl. destruct p0; simpl.
 destruct (dec_share_identity x0); auto.
 elimtype False; clear - n0 i0; apply nonunit_nonidentity in n0; contradiction n0.
 revert H4; case_eq (a (b,ofs-z0)); intros.
 elimtype False.
 destruct (H1 (b,ofs-z0)). rewrite H4 in H9; rewrite H6 in H9.
 destruct p0. 
 assert (k = LK n). inv H9; auto. destruct a2. destruct H13 as [? [? ?]]; simpl in *; subst. auto.
 subst k.
 generalize (H b (ofs-z0)); rewrite H4; intros.
 specialize (H10 _ H5). replace (ofs-z0+z0) with ofs in H10 by omega.
 congruence.
 simpl. destruct (dec_share_identity Share.bot); auto.
 contradict n0; auto.
Focus 1.
 destruct (dec_share_identity (ad (b,ofs-z0))).
 apply join_unit2; [constructor |].
 pose proof (H2 (b,ofs-z0)). apply join_comm in H4. apply i in H4.
 assert (~identity (share_of (a (b,ofs-z0)))) by (rewrite <- H4; auto).
 unfold share_of in H5.
 revert H5; case_eq (a (b,ofs-z0)); intros; [ | contradiction H6; auto].
 destruct p0.
 pose proof (H1 (b,ofs-z0)). rewrite H5 in H7.
 pose proof (H0 b ofs). rewrite H3 in H8. destruct H8 as [s [? ?]].
 rewrite H9 in H7.
 destruct H7.
 assert (k = LK s).
  inv H7; auto. destruct a2; destruct H13 as [H13 H13']; inv H13'; simpl in *; subst; auto.
 subst k.
 specialize (H b (ofs-z0)). rewrite H5 in H. specialize (H z0 H8).
 replace (ofs-z0+z0) with ofs in H by omega. rewrite H.
 repeat f_equal.
 rewrite H5 in H4. destruct p0.  apply exist_ext.  rewrite H4.
 simpl; auto.
 case_eq (a (b,ofs-z0)); intros.
Focus 2.
 specialize (H2 (b,ofs-z0)); rewrite H4 in H2.
 simpl in H2. apply split_identity in H2; auto. contradiction.
 destruct p0.
 pose proof (H0 b ofs). rewrite H3 in H5. destruct H5 as [s [? ?]].
 pose proof (H1 (b,ofs-z0)). rewrite H4 in H7; rewrite H6 in H7.
 assert (k=LK s). destruct H7; inv H7; auto. destruct a2; destruct H11; simpl in *.
    inv H8; auto. 
 subst k.
 specialize (H b (ofs-z0)). rewrite H4 in H. specialize (H _ H5).
 replace (ofs-z0+z0) with ofs in H by omega. rewrite H.
 constructor. split; auto. simpl. 
 specialize (H2 (b,ofs-z0)).
 rewrite H4 in H2. simpl in H2.
 apply H2.
 
  destruct (dec_share_identity (ac x)); auto.
  specialize (H2 x). apply join_unit1_e in H2; auto. 
  destruct (dec_share_identity (ad x)); auto.
  destruct (a x); try constructor.
  contradiction (share_of_Some p0). rewrite <- H2; auto.
  forget (ad x) as adx.  subst adx.
  specialize (H1 x). rewrite H3 in H1. destruct H1.
  apply join_unit1; [ apply None_unit |].
  destruct (a x); [  | simpl in n; contradiction n; auto].
  destruct p0. simpl in *.
  destruct p0; simpl in *. 
  assert (k = FUN f). inv H1; auto. inv H6; auto. destruct H2; simpl in *; subst; auto.
  subst. f_equal. f_equal. unfold mk_pshare. f_equal. 
  apply proof_irr.
  destruct (dec_share_identity (ad x)); auto.
  apply join_unit2; [ apply None_unit |].
  specialize (H1 x). rewrite H3 in H1. destruct H1.
  specialize (H2 x). apply join_unit2_e in H2; auto. 
  forget (ac x) as acx.  subst acx.
  destruct (a x); [  | simpl in n; contradiction n; auto].
  destruct p0. simpl in *.
  destruct p0; simpl in *.  
  assert (k = FUN f). inv H1; auto. inv H6; auto. destruct H2; simpl in *; subst; auto.
  subst. f_equal. f_equal. apply exist_ext. auto.
  specialize (H1 x); specialize (H2 x).
  destruct (a x).
  constructor. destruct p0. destruct p0.
  simpl in H2. 
  rewrite H3 in H1.
  assert (k = FUN f). inv H1; auto. inv H4; auto. destruct H7; simpl in *; subst; auto.
  destruct H4; subst; auto. subst k.  
 constructor; auto.
 simpl in H2. apply split_identity in H2; auto. contradiction.
 destruct (dec_share_identity (ac x)); auto.
 generalize (H2 x); intro. apply join_unit1_e in H4; auto.
  specialize (H1 x). rewrite H3 in H1. destruct H1. inv H1; auto; try constructor. 
  rewrite H8; constructor.
  specialize (H1 x). rewrite H3 in H1. destruct H1. inv H1; auto; try constructor. 
  rewrite H7; constructor.
Qed.
 
Lemma join_share_of: forall a b c,
     @join _ Join_pk a b c -> join (share_of a) (share_of b) (share_of c).
Proof.
  intros. inv H; simpl. apply join_unit1; auto. apply join_unit2; auto.
  destruct a1; destruct a2; destruct a3. destruct p, p0, p1; simpl.
  destruct H0. simpl in *. do 3 red in H. unfold lifted_obj in H. simpl in H. auto.
Qed.

Instance Cross_rmap_aux: Cross_alg (sig AV.valid).
Proof. 
 hnf. intros [a Ha] [b Hb] [c Hc] [d Hd] [z Hz] ? ?.
 hnf in H,H0. simpl in H,H0.
 destruct (cross_split_fun Share.t _ address share_cross_split
                   (share_of oo a) (share_of oo b) (share_of oo c) (share_of oo d) (share_of oo z))
  as [[[[ac ad] bc] bd] [? [? [? ?]]]].
 intro x. specialize (H x). unfold compose. 
 clear - H. inv H; simpl in *. apply join_unit1; auto. apply join_unit2; auto.
 destruct a1; destruct a2; destruct a3; apply H3.
 intro x. specialize (H0 x). unfold compose. 
 clear - H0. inv H0; simpl in *. apply join_unit1; auto. apply join_unit2; auto.
 destruct a1; destruct a2; destruct a3; apply H3.
 assert (Sac: forall x : address, join_sub (ac x) (share_of (z x))).
   intro x.  apply join_sub_trans with (share_of (a x)). eexists; apply (H1 x).
   exists (share_of (b x)).  apply join_share_of; auto.
 assert (Sad: forall x : address, join_sub (ad x) (share_of (z x))).
   intro x.  apply join_sub_trans with (share_of (a x)). eexists; eapply join_comm; apply (H1 x).
   exists (share_of (b x)).  apply join_share_of; auto.
 assert (Sbc: forall x : address, join_sub (bc x) (share_of (z x))).
   intro x.  apply join_sub_trans with (share_of (b x)). eexists; apply (H2 x).
   exists (share_of (a x)).  eapply join_comm; apply join_share_of; auto.
 assert (Sbd: forall x : address, join_sub (bd x) (share_of (z x))).
   intro x.  apply join_sub_trans with (share_of (b x)). eexists; eapply join_comm; apply (H2 x).
   exists (share_of (a x)).  eapply join_comm; apply join_share_of; auto.
 exists (exist AV.valid _ (fixup_splitting_valid ac z Sac Hz),
            exist AV.valid _ (fixup_splitting_valid ad z Sad Hz),
            exist AV.valid _ (fixup_splitting_valid bc z Sbc Hz),
            exist AV.valid _ (fixup_splitting_valid bd z Sbd Hz)).
 split3; [ | | split];  do 2 red; simpl; intro; apply fixup_join; auto; intro.
 exists (b x0); apply H.
 exists (a x0); apply join_comm; apply H.
 exists (d x0); apply H0.
 exists (c x0); apply join_comm; apply H0.
Qed.

Instance Trip_resource : Trip_alg resource.
Proof.
intro; intros.
destruct a as [ra | ra sa ka pa | ka pa].
destruct b as [rb | rb sb kb pb | kb pb]; try solve [elimtype False; inv H].
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
exists (NO rabc); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
exists (YES rabc sc kc pc); constructor; auto.
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
exists (YES rabc sab kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
exists (YES rabc sbc kbc pbc). inv H0; inv H; inv H1; constructor; auto.
destruct b as [rb | rb sb kb pb | kb pb]; try solve [elimtype False; inv H].
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
exists (YES rabc sab kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
exists (YES rabc sac kac pac).  inv H; inv H0; inv H1; constructor; auto.
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
exists (YES rabc sab kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
destruct (triple_join_exists_share (pshare_sh sa) (pshare_sh sb) (pshare_sh sc)
                                                     (pshare_sh sab) (pshare_sh sbc) (pshare_sh sac)) as [sabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (nonidentity sabc).
eapply join_nonidentity; try apply (join_comm j0).
 destruct sc; simpl. 
 apply (nonunit_nonidentity n).
exists (YES rabc (mk_pshare _ (nonidentity_nonunit H2)) kc pc).
 inv H. inv H1. inv H0.  
constructor; auto.
 exists ab. inv H. inv H1. inv H0. constructor.
Qed.

Instance Trip_rmap : Trip_alg rmap.
Proof.
intro; intros.
pose (f loc := @Trip_resource _ _ _ _ _ _ 
                 (resource_at_join _ _ _ loc H)
                 (resource_at_join _ _ _ loc H0)
                 (resource_at_join _ _ _ loc H1)).
assert (CompCert_AV.valid (res_option oo (fun l => projT1 (f l)))).
intros b' z'.
unfold compose. simpl.
destruct (f (b',z')); simpl.
destruct x; simpl; auto.
destruct k; simpl; auto.
intros.
destruct (f (b',z'+i)). simpl.
case_eq (ab @ (b', z')); case_eq (c @ (b', z')); intros.
rewrite H3 in j; rewrite H4 in j. inv j.
rename H3 into H6.
generalize (rmap_valid_e1 c b' z' _ _ H2 p); intro.
rewrite H4 in j; rewrite H6 in j.
assert (k = LK z) by (inv j; auto). subst.
assert (p1 = p) by (inv j; auto). subst.
spec H3; [rewrite H6; auto|].
destruct (c @ (b',z'+i)); inv H3.
case_eq (ab @ (b', z' + i)); intros.
rewrite H3 in j0. inv j0. auto.
rewrite H3 in j0. inv j0. simpl.
repeat f_equal.
inv j.
generalize (rmap_valid_e2 ab b' z' i p1); intro.
spec H5; [rewrite H3; auto|].
destruct H5 as [n [? ?]].
rewrite H4 in H7. inv H7.
intros.
rewrite H3 in j0. inv j0.
rewrite H4 in j. inv j. rewrite H3 in H7. inv H7. rewrite H4 in j. inv j.
generalize (rmap_valid_e1 ab b' z' _ _ H2 p); intro.
rewrite H4 in H5. spec H5 ; [ auto |].
destruct (ab @ (b',z'+i)); inv H5.
inv j0. reflexivity.
revert H11; case_eq (c @ (b', z' + i)); intros; inv H11.
 generalize (rmap_valid_e2 c b' z' i p1); intro. rewrite H5 in H6.
destruct H6 as [n [? ?]]; auto. rewrite H3 in H7; inv H7.
rewrite H3 in H10; inv H10.
rewrite H3 in j. rewrite H4 in j. inv j.
generalize (rmap_valid_e1 c b' z' _ _ H2 p1); intro.
spec H5; [rewrite H3; auto|].
generalize (rmap_valid_e1 ab b' z' _ _ H2 p3); intro.
spec H7; [rewrite H4; auto|].
destruct (c @ (b',z'+i)); inv H5.
destruct (ab @ (b',z'+i)); inv H7.
inv j0. simpl. repeat f_equal. eapply join_eq;  eauto.
rewrite H3 in j; inv j.
rewrite H4 in j; inv j.
rewrite H4 in j; inv j.
rewrite H3 in j; inv j.
(**)
destruct (f (b',z'-z)).
simpl.
case_eq (ab @ (b', z')); case_eq (c @ (b', z')); intros.
rewrite H2 in j; rewrite H3 in j; inv j.
rewrite H2 in j; rewrite H3 in j; inv j.
rename H2 into H5.
symmetry in H3.
generalize (rmap_valid_e2 c b' (z'-z) z p); intro.
spec H2; [replace (z'-z+z) with z' by omega; rewrite H5; auto|].
destruct H2 as [n [? ?]]; exists n; split; auto.
destruct (c @ (b',z'-z)); inv H4.
inv j0. reflexivity.
generalize (rmap_valid_e1 ab b' (z'-z) _ _ H2 sh1); intro.
spec H6; [ rewrite <- H4; auto|].
replace (z'-z+z) with z' in H6 by omega.
rewrite <- H3 in H6; inv H6.
rewrite H2 in j; inv j.
rewrite H2 in j; inv j. rewrite H3 in H5; inv H5.
generalize (rmap_valid_e2 ab b' (z'-z) z p1); intro.
rename H4 into H2'; rename H2 into H4; rename H2' into H2.
rename H3 into H5.
spec H2; [replace (z'-z+z) with z' by omega; rewrite H5; auto|].
destruct H2 as [n [? ?]]; exists n; split; auto.
destruct (ab @ (b',z'-z)); inv H3.
inv j0; try reflexivity.
generalize (rmap_valid_e1 c b' (z'-z) _ _ H2 sh2); intro.
spec H3; [ rewrite <- H10; reflexivity|].
replace (z'-z+z) with z' in H3 by omega.
rewrite H4 in H3; inv H3.
rewrite H3 in j; rewrite H2 in j; inv j.
generalize (rmap_valid_e2 c b' (z'-z) z p1); intro.
spec H4; [replace (z'-z+z) with z' by omega; rewrite H2; auto|].
destruct H4 as [n [? ?]]; exists n; split; auto.
destruct (c @ (b',z'-z)); inv H6.
generalize (rmap_valid_e2 ab b' (z'-z) z p3); intro.
spec H6; [replace (z'-z+z) with z' by omega; rewrite H3; auto|].
destruct H6 as [n' [? ?]].
destruct (ab @ (b',z'-z)); inv j0; inv H7.
simpl. do 2 f_equal.
eapply join_eq; eauto.
rewrite H2 in j; inv j.
rewrite H3 in j; inv j.
rewrite H3 in j; inv j.
rewrite H2 in j; inv j.

destruct (make_rmap _ H2 (level a)) as [abc [? ?]].
extensionality loc. unfold compose; simpl.
destruct (f loc); simpl.
destruct x; simpl; auto.
f_equal.
generalize (resource_at_join _ _ _ loc H);
generalize (resource_at_join _ _ _ loc H0);
generalize (resource_at_join _ _ _ loc H1);
inv j; intros.
inv H7.
generalize (resource_at_approx a loc); rewrite <- H9;  intro.
injection (YES_inj _ _ _ _ _ _ _ _ H7); auto.
replace (level a) with (level b).
 2:  clear - H; apply join_level in H; destruct H; congruence.
generalize (resource_at_approx b loc); rewrite <- H10;  intro.
injection (YES_inj _ _ _ _ _ _ _ _ H7); auto.
generalize (resource_at_approx a loc); rewrite <- H8;  intro.
injection (YES_inj _ _ _ _ _ _ _ _ H7); auto.
replace (level a) with (level c).
 2:  clear - H1; apply join_level in H1; destruct H1; congruence.
generalize (resource_at_approx c loc); rewrite <- H5;  intro.
injection (YES_inj _ _ _ _ _ _ _ _ H8); auto.
replace (level a) with (level c).
 2:  clear - H1; apply join_level in H1; destruct H1; congruence.
generalize (resource_at_approx c loc); rewrite <- H4;  intro.
injection (YES_inj _ _ _ _ _ _ _ _ H9); auto.
inv j.
replace (level a) with (level c).
 2:  clear - H1; apply join_level in H1; destruct H1; congruence.
generalize (resource_at_approx c loc); rewrite <- H5;  intro.
auto.
exists abc.
apply resource_at_join2.
rewrite H3. clear - H. apply join_level in H; destruct H; auto.
rewrite H3. clear - H1; apply join_level in H1; destruct H1; congruence.
intro loc.
rewrite H4.
destruct (f loc).
simpl.
auto.
Qed.

Obligation Tactic := Tactics.program_simpl.

Program Definition writable (l: address): pred rmap :=
 fun phi =>
  match phi @ l with
    | YES _ sh k lp => sh = pfullshare /\ isVAL k
    | _ => False
  end.
 Next Obligation.
  intro; intros.
  generalize (age1_res_option a a' l H); intro.
  destruct (a @ l); try contradiction.
  simpl in H1. 
  destruct (a' @ l); inv H1; auto.
  Qed.

Program Definition readable (loc: address) : pred rmap := 
   fun phi => match phi @ loc with YES _ _ k _ => isVAL k | _ => False end.
 Next Obligation.
  intro; intros.
  generalize (age1_res_option a a' loc H); intro.
  destruct (a @ loc); try contradiction.
  simpl in H1. 
  destruct (a' @ loc); inv H1; auto.
  Qed.

Lemma readable_join:
  forall phi1 phi2 phi3 loc, join phi1 phi2 phi3 -> 
            readable loc phi1 -> readable loc phi3.
Proof.
unfold readable; intros until loc.
intros.
simpl in *.
generalize (resource_at_join _ _ _ loc H); clear H; intros.
revert H0 H; destruct (phi1 @ loc); intros; try contradiction.
inv H; auto.
Qed.

Lemma readable_writable_join:
forall phi1 phi2 l, readable l phi1 -> writable l phi2 -> joins phi1 phi2 -> False.
Proof.
intros.
unfold readable, writable in *.
simpl in H, H0.
destruct H1 as [phi ?].
generalize (resource_at_join _ _ _ l H1); clear H1; revert H H0.
destruct (phi1 @ l); intros; try contradiction.
destruct (phi2 @ l); try contradiction.
destruct H0; subst.
inv H1; pfullshare_join.
Qed.

Lemma writable_join: forall loc phi1 phi2, join_sub phi1 phi2 -> 
            writable loc phi1 -> writable loc phi2.
Proof.
unfold writable; intros.
simpl in *.
destruct H; generalize (resource_at_join _ _ _ loc H); clear H.
revert H0; destruct (phi1 @ loc); intros; try contradiction.
destruct H0; subst.
inv H; split; auto; pfullshare_join.
Qed.

Lemma writable_readable: forall loc m, writable loc m -> readable loc m.
Proof.
 unfold writable, readable.
 intros ? ?. simpl.  destruct (m @ loc); auto. intros [? ?]. auto.
Qed.

Lemma writable_e: forall loc m, 
   writable loc m -> 
   exists rsh, exists v, exists p, m @ loc = YES rsh pfullshare (VAL v) p.
Proof.
unfold writable; simpl; intros; destruct (m@loc); try contradiction.
destruct H; subst.
destruct k; try solve [inversion H0].
subst.
exists t, m0, p0; auto.
Qed.
Implicit Arguments writable_e.

Lemma readable_e: forall loc m, 
   readable loc m -> 
  exists rsh, exists sh, exists v, exists p, m @ loc = YES rsh sh (VAL v) p.
Proof.
unfold readable; simpl; intros; destruct (m@loc); try contradiction.
destruct k; try solve [inversion H].
subst.
econstructor; eauto.
Qed.
Implicit Arguments readable_e.

Definition bytes_writable (loc: address) (size: Z) (phi: rmap) : Prop :=
  forall i, (0 <= i < size) -> writable (adr_add loc i) phi.

Definition bytes_readable (loc: address) (size: Z) (phi: rmap) : Prop :=
  forall i, (0 <= i < size) -> readable (adr_add loc i) phi.

Lemma readable_dec (loc: address) (phi: rmap) : {readable loc phi} + {~readable loc phi}.
Proof. intros.
unfold readable. simpl. 
case (phi @ loc); intros; auto.
apply isVAL_dec.
Qed.

Lemma writable_dec: forall loc phi, {writable loc phi}+{~writable loc phi}.
Proof.
intros.
unfold writable. simpl.
destruct (phi @ loc); auto.
destruct (isVAL_dec k).
destruct (pshare_eq_dec p pfullshare).
left; auto.
right; intros [? ?]; contradiction.
right; intros [? ?]; contradiction.
Qed.

Lemma bytes_writable_dec:
   forall loc n m, {bytes_writable loc n m}+{~bytes_writable loc n m}.
Proof.
intros.
destruct n.
left; intro; intros; omegaContradiction.
2: generalize (Zlt_neg_0 p); intro; left; intro; intros; omegaContradiction.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
remember (nat_of_P p) as n.
clear.
destruct loc as [b z].
revert z;
induction n; intros.
left; intro; intros.
simpl in H; omegaContradiction.
rewrite inj_S.
destruct (IHn (z+1)).
destruct (writable_dec (b,z) m).
left.
intro; intros.
unfold adr_add; simpl.
destruct (zeq i 0).
subst.
replace (z+0) with z by omega.
auto.
replace (z+i) with (z+1+(i-1)) by omega.
apply b0.
omega.
right.
contradict n0.
spec n0 0.
unfold adr_add in n0; simpl in n0.
replace (z+0) with z in n0.
apply n0.
omega.
omega.
right.
contradict n0.
intro; intros.
unfold adr_add; simpl.
replace (z+1+i) with (z+(1+i)) by omega.
apply n0.
omega.
Qed.

Lemma bytes_readable_dec:
   forall loc n m, {bytes_readable loc n m}+{~bytes_readable loc n m}.
Proof.
intros.
destruct n.
left; intro; intros; omegaContradiction.
2: generalize (Zlt_neg_0 p); intro; left; intro; intros; omegaContradiction.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
remember (nat_of_P p) as n.
clear.
destruct loc as [b z].
revert z;
induction n; intros.
left; intro; intros.
simpl in H; omegaContradiction.
rewrite inj_S.
destruct (IHn (z+1)).
destruct (readable_dec (b,z) m).
left.
intro; intros.
unfold adr_add; simpl.
destruct (zeq i 0).
subst.
replace (z+0) with z by omega.
auto.
replace (z+i) with (z+1+(i-1)) by omega.
apply b0.
omega.
right.
contradict n0.
spec n0 0.
unfold adr_add in n0; simpl in n0.
replace (z+0) with z in n0.
apply n0.
omega.
omega.
right.
contradict n0.
intro; intros.
unfold adr_add; simpl.
replace (z+1+i) with (z+(1+i)) by omega.
apply n0.
omega.
Qed.

Lemma bytes_writable_readable:
  forall m loc n, bytes_writable m loc n -> bytes_readable m loc n.
Proof.
unfold bytes_writable, bytes_readable; intros.
apply writable_readable; auto.
Qed.

Hint Resolve bytes_writable_readable : mem.
