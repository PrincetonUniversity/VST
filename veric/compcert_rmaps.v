Require Export VST.msl.msl_standard.
Require Import VST.veric.base.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.shares.
Require Import VST.veric.rmaps.
Require Import VST.veric.rmaps_lemmas.
Require Export VST.veric.Memory. (*for address, and eq_dec memval*)

Instance EqDec_type: EqDec type := type_eq.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)
(*moved to mpred
Definition strict_bool_val (v: val) (t: type) : option bool :=
   match v, t with
   | Vint n, Tint _ _ _ => Some (negb (Int.eq n Int.zero))
   | Vlong n, Tlong _ _ => Some (negb (Int64.eq n Int64.zero))
   | (Vint n), (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
             if Int.eq n Int.zero then Some false else None
   | Vlong n, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
            if Archi.ptr64 then if Int64.eq n Int64.zero then Some false else None else None
   | Vptr b ofs, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) => Some true
   | Vfloat f, Tfloat F64 _ => Some (negb(Float.cmp Ceq f Float.zero))
   | Vsingle f, Tfloat F32 _ => Some (negb(Float32.cmp Ceq f Float32.zero))
   | _, _ => None
   end.
*)
Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN: funsig -> calling_convention -> kind.

(*Non-Ctypes.v- using variant:
Inductive kind : Type := VAL : memval -> kind
                                   | LK : Z -> kind
                                   | CT: Z -> kind
                                   | FUN: (*funsig -> calling_convention*)signature -> kind.
 *)

Definition isVAL (k: kind) := match k with | VAL _ => True | _ => False end.
Definition isFUN (k: kind) := match k with | FUN _ _ => True | _ => False end.

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

Instance EqDec_calling_convention: EqDec calling_convention.
Proof.
  hnf. decide equality.
  destruct cc_structret, cc_structret0; intuition.
  destruct cc_unproto, cc_unproto0; intuition.
  destruct cc_vararg, cc_vararg0; intuition.
Qed.

Instance EqDec_kind: EqDec kind.
Proof.
  hnf. decide equality; try apply eq_dec; try apply zeq; try apply signature_eq.
Qed.

Module R := Rmaps (CompCert_AV).
Module RML := Rmaps_Lemmas(R).

Export RML.
Export R.

Definition mk_rshare: forall p: Share.t, pure_readable_share p -> rshare := exist pure_readable_share.
Definition rshare_sh (p: rshare) : Share.t := proj1_sig p.
(*
Definition mk_pshare : forall p: Share.t, nonunit p -> pshare := exist nonunit.
*)

Lemma mk_rshare_sh: forall (p:rshare) (H: pure_readable_share (rshare_sh p)),
  mk_rshare (rshare_sh p) H = p.
Proof.
  intros.
  unfold mk_rshare.
  destruct p; simpl.
  auto with extensionality.
Qed.

Definition fixup_splitting
  (a:address -> Share.t) (z: address -> option (rshare * kind)) : address -> option (rshare * kind) :=
  fun l => 
    match z l with
    | Some (sh, k) =>
       match dec_readable (a l) with
       | left p => Some (readable_part p,  k)
       | right _ => None
       end
    | None => None
    end.

Definition share_of (x: option (rshare * kind)) : Share.t :=
  match x with Some (p,_) => proj1_sig p | None => Share.bot end.

Definition Join_pk := (Join_lower (Join_prod rshare _ kind (Join_equiv _))).

Lemma share_of_Some: forall p: rshare * AV.kind, readable_share (share_of (Some p)).
Proof.
 intros. destruct p as [[? ?] ?]; simpl.
 auto.
 destruct p; auto.
Qed.

Lemma join_sub_same_k:
 forall {a a' : rshare} {k k': AV.kind},
      @join_sub _ Join_pk (Some (a,k)) (Some (a',k')) -> k=k'.
Proof.
  intros. destruct H. inv H; auto. inv H3. simpl in H0. inv H0; congruence.
Qed.

Lemma pure_readable_glb_Rsh:
 forall sh, pure_readable_share sh -> Share.glb Share.Rsh sh = sh.
Proof.
 intros.
 destruct H.
 rewrite (comp_parts comp_Lsh_Rsh sh) at 2. rewrite H.
 rewrite Share.lub_commute, Share.lub_bot; auto.
Qed.

Lemma join_glb_Rsh:  
  forall a b c : Share.t,
  join a b c ->
  join (Share.glb Share.Rsh a) (Share.glb Share.Rsh b) (Share.glb Share.Rsh c).
Proof.
intros.
apply (join_comp_parts comp_Lsh_Rsh). auto.
Qed.

Lemma pure_readable_share_glb:
  forall a, pure_readable_share a -> Share.glb Share.Rsh a = a.
Proof.
 intros. destruct H.
 rewrite (comp_parts comp_Lsh_Rsh a) at 2. rewrite H.
 rewrite Share.lub_commute, Share.lub_bot. auto.
Qed.

Lemma glb_Rsh_bot_unreadable:
  forall a, Share.glb Share.Rsh a = Share.bot -> ~readable_share a.
Proof.
 intros. unfold readable_share. rewrite H. intro. apply H0.
 apply bot_identity.
Qed.

Lemma fixup_join : forall a (ac ad: address -> Share.t)  z,
  (forall x, @join_sub _ Join_pk (a x) (z x)) ->
  (forall x, join (ac x) (ad x) (share_of (a x))) ->
  (forall x,
    @join _ Join_pk
    (fixup_splitting ac z x)
    (fixup_splitting ad z x)
    (a x)).
Proof.
 do 2  pose proof I.
  intros.
  unfold fixup_splitting.

Ltac glb_Rsh_tac :=
 repeat
 match goal with
 | |- Some _ = None => elimtype False
 | |- None = Some _ => elimtype False
 | |- join (Some _) _ None => elimtype False
 | |- join _ (Some _) None => elimtype False
 | |- join _ None _ => apply join_unit2; [ apply None_unit |]
 | |- join None _ _ => apply join_unit1; [ apply None_unit |]
 | |- Some (_,_) = Some(_,_) => do 2 f_equal; try apply exist_ext; auto
 | H: ~readable_share ?X, H1: join (Share.glb Share.Rsh ?X) _ _ |- _ =>
         rewrite (not_readable_Rsh_part H) in H1;
         apply join_unit1_e in H1; [ | apply bot_identity];
         rewrite ?H1 in *
 | H: ~readable_share ?X, H1: join _ (Share.glb Share.Rsh ?X) _ |- _ =>
         rewrite (not_readable_Rsh_part H) in H1;
         apply join_unit2_e in H1; [ | apply bot_identity];
         rewrite ?H1 in *
 | H: identity ?A, H1: readable_share ?A |- _ =>
    apply (readable_not_identity A _ H1 H)
 | H: pure_readable_share ?A |- Share.glb Share.Rsh ?A = ?A =>
     apply pure_readable_glb_Rsh; auto
 | H: join ?A ?B Share.bot |- _ =>
     let H1 := fresh in 
         assert (H1 := identity_share_bot _ (split_identity _ _ H bot_identity));
         rewrite ?H1 in *;
     let H2 := fresh in 
         assert (H2 := identity_share_bot _ (split_identity _ _ (join_comm H) bot_identity));
         rewrite ?H2 in *;
     clear H
 | H: readable_share Share.bot |- _ => contradiction bot_unreadable
 | H: join_sub None _ |- _ => clear H
 | H: join_sub (Some(_,?A)) (Some (_,?B)) |- _ =>
      unify A B || 
      (is_var A; pose proof (join_sub_same_k H); subst A)
 | |- _ => rewrite Share.glb_bot in *
 | H: Share.glb Share.Rsh _ = Share.bot |- _ => 
          apply glb_Rsh_bot_unreadable in H; try contradiction
 | H: pure_readable_share ?A |- _ => rewrite (pure_readable_share_glb _ H) in *
 | |- _ => assumption
 end;
 auto.

  case_eq (z x); intros; [destruct p | ].
*
  specialize (H1 x); specialize (H2 x).
  clear H H0. rewrite H3 in *. clear z H3.
  destruct (dec_readable (ac x)).
 +
  destruct (dec_readable (ad x)).
 -
  destruct (a x) as [[[? ?] ?] | ]; simpl in *.
  constructor.
  pose proof (join_sub_same_k H1); subst k.
  constructor; auto. simpl.
  red. red. simpl.
  apply join_glb_Rsh in H2.
  glb_Rsh_tac.
  glb_Rsh_tac.
  -
  apply join_glb_Rsh in H2.
  glb_Rsh_tac.
  destruct (a x) as [[[? ?] ?]|]; simpl in *.
  glb_Rsh_tac.
  glb_Rsh_tac.
+
  glb_Rsh_tac.
  apply join_glb_Rsh in H2.
  destruct (a x) as [[[? ?] ?]|]; simpl in *.
  glb_Rsh_tac.
  destruct (dec_readable (ad x)).
  glb_Rsh_tac.
  glb_Rsh_tac.
  apply n0.
  unfold readable_share. rewrite H2. destruct p. intro.
  glb_Rsh_tac.
  glb_Rsh_tac.
  destruct (dec_readable (ad x)).
  glb_Rsh_tac.
  glb_Rsh_tac.
*
 specialize (H1 x). rewrite H3 in H1.
 destruct H1.
 inv H1. constructor. rewrite H7; constructor.
Qed.

Lemma join_share_of: forall a b c,
     @join _ Join_pk a b c -> join (share_of a) (share_of b) (share_of c).
Proof.
  intros. inv H; simpl. apply join_unit1; auto. apply join_unit2; auto.
  destruct a1; destruct a2; destruct a3.
  destruct r,r0,r1; simpl.
  destruct H0. simpl in *. do 3 red in H. simpl in H. auto.
Qed.

Instance Cross_rmap_aux: Cross_alg (AV.address -> option (rshare * AV.kind)).
Proof.
 hnf. intros a b c d z ? ?.
(* hnf in H,H0. simpl in H,H0. *)
 destruct (cross_split_fun Share.t _ address share_cross_split
                   (share_of oo a) (share_of oo b) (share_of oo c) (share_of oo d) (share_of oo z))
  as [[[[ac ad] bc] bd] [? [? [? ?]]]].
 intro x. specialize (H x). unfold compose.
 clear - H. inv H; simpl in *. apply join_unit1; auto. apply join_unit2; auto.
 destruct a1; destruct a2; destruct a3; apply H3.
 intro x. specialize (H0 x). unfold compose.
 clear - H0. inv H0; simpl in *. apply join_unit1; auto. apply join_unit2; auto.
 destruct a1; destruct a2; destruct a3; apply H3.
 exists (fixup_splitting ac z, 
            fixup_splitting ad z, 
            fixup_splitting bc z, 
            fixup_splitting bd z).
 split3; [ | | split];  do 2 red; simpl; intro;
 apply fixup_join; auto; intros.
 exists (b x0); apply H.
 exists (a x0); apply join_comm; apply H.
 exists (d x0); apply H0.
 exists (c x0); apply join_comm; apply H0.
Qed.

Instance Trip_resource: Trip_alg resource.
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
assert (n5 := join_unreadable_shares j n1 n2).
exists (NO rabc n5); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable2 j sc).
exists (YES rabc sabc kc pc); constructor; auto.
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kbc pbc). inv H0; inv H; inv H1; constructor; auto.
destruct b as [rb | rb sb kb pb | kb pb]; try solve [elimtype False; inv H].
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kac pac).  inv H; inv H0; inv H1; constructor; auto.
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kc pc).
 inv H. inv H1. inv H0.
constructor; auto.
 exists ab. inv H. inv H1. inv H0. constructor.
Qed.

Lemma pure_readable_share_i:
  forall sh, readable_share sh -> (pure_readable_share (Share.glb Share.Rsh sh)).
Proof.
intros. split. rewrite <- Share.glb_assoc. rewrite glb_Lsh_Rsh.
rewrite Share.glb_commute. apply Share.glb_bot.
do 3 red in H|-*. contradict H.
rewrite glb_twice in H. auto.
Qed.

(* Do we need this?
Instance Trip_rmap : Trip_alg rmap.
Proof.
intro; intros.
pose (f loc := @Trip_resource _ _ _ _ _ _
                 (resource_at_join _ _ _ loc H)
                 (resource_at_join _ _ _ loc H0)
                 (resource_at_join _ _ _ loc H1)).
assert (CompCert_AV.valid (res_option oo (fun l => proj1_sig (f l)))).
intros b' z'.
unfold compose. simpl.
destruct (f (b',z')); simpl.
destruct x; simpl; auto.
destruct k; simpl; auto.
intros.
destruct (f (b',z'+i)). simpl.
case_eq (ab @ (b', z')); case_eq (c @ (b', z')); intros; try solve [rewrite H3 in j; inv j];
  try solve [rewrite H4 in j; inv j].
rewrite H3 in j; rewrite H4 in j. inv j.
rename H3 into H6.
pose proof (rmap_valid_e1 c b' z' _ _ H2 (readable_part r0)).
rewrite H4 in j; rewrite H6 in j.
assert (k = LK z) by (inv j; auto). subst.
assert (p0 = p) by (inv j; auto). subst.
spec H3; [rewrite H6; auto|].
inv j. rename RJ into j.
destruct (c @ (b',z'+i)); inv H3.
case_eq (ab @ (b', z' + i)); intros.
*
rewrite H3 in j0; inv j0.
simpl. f_equal; f_equal.
clear f nsh2 rsh4 rsh0 H2 H4 H6 H3 p.
clear rsh1 i p0 nsh0.
apply exist_ext.
  apply join_glb_Rsh in RJ.
  apply join_glb_Rsh in j.
  glb_Rsh_tac.
*
assert (H9 := pure_readable_share_i _ r2).
generalize (rmap_valid_e2 ab b' z' i (mk_rshare _ H9)); intro.
rewrite H3 in *. clear H3.
simpl in H5.
spec H5. inv j0. do 2 f_equal. apply exist_ext. auto.
destruct H5 as [nx [? ?]].
rewrite H4 in H5. inv H5.
*
intros.
rewrite H3 in j0. inv j0.
*
rewrite H4 in j. inv j.
assert (H99 := pure_readable_share_i _ r0).
pose proof (rmap_valid_e1 ab b' z' _ _ H2 (mk_rshare _ H99)).
rewrite H4 in H5.
spec H5. simpl. f_equal. f_equal. apply exist_ext; reflexivity.
destruct (ab @ (b',z'+i)); inv H5.
rewrite H3 in H9; inv H9.
inv j0. simpl.  repeat f_equal. apply exist_ext.
  apply join_glb_Rsh in RJ.
  apply join_glb_Rsh in RJ0.
  glb_Rsh_tac.
 simpl. do 2 f_equal. apply exist_ext.
assert (H98 := pure_readable_share_i _ rsh3).
 pose proof (rmap_valid_e2 c b' z' i  (mk_rshare _ H98)).
 rewrite <- H10 in H5.
 spec H5. simpl. do 2 f_equal. apply exist_ext. auto.
destruct H5 as [nx [? ?]]; auto. rewrite H3 in H6. inv H6.
 congruence.
*
rewrite H3 in j. rewrite H4 in j. inv j.
assert (H99 := pure_readable_share_i _ r0).
pose proof (rmap_valid_e1 c b' z' _ _ H2 (mk_rshare _ H99)).
spec H5.  rewrite H3. simpl. repeat f_equal. apply exist_ext; auto.
assert (H98 := pure_readable_share_i _ r1).
pose proof (rmap_valid_e1 ab b' z' _ _ H2 (mk_rshare _ H98)).
spec H6.  rewrite H4. simpl. repeat f_equal. apply exist_ext; auto.
destruct (c @ (b',z'+i)); inv H5.
destruct (ab @ (b',z'+i)); inv H6.
inv j0. simpl. repeat f_equal. apply exist_ext.
apply join_glb_Rsh in RJ.
apply join_glb_Rsh in RJ0.
rewrite H8 in *; rewrite H7 in *.
eapply join_eq;  eauto.
* (**)
destruct (f (b',z'-z)).
simpl.
case_eq (ab @ (b', z')); case_eq (c @ (b', z')); intros; try solve [rewrite H2, H3 in j; inv j].
+
rewrite H2 in j; rewrite H3 in j; inv j.
rename H2 into H5.
symmetry in H3.
assert (H99 := pure_readable_share_i _ r0).
pose proof (rmap_valid_e2 c b' (z'-z) z  (mk_rshare _ H99)).
rewrite Z.sub_add, H5 in H2.
spec H2.  simpl. repeat f_equal. apply exist_ext. auto.
destruct H2 as [nx [? ?]]; exists nx; split; auto.
destruct (c @ (b',z'-z)); inv H4.
inv j0. simpl. repeat f_equal. apply exist_ext.
apply join_glb_Rsh in RJ.
apply join_glb_Rsh in RJ0.
glb_Rsh_tac.
assert (H98 := pure_readable_share_i _ rsh2).
pose proof (rmap_valid_e1 ab b' (z'-z) _ _ H2 (mk_rshare _ H98)).
spec H4. rewrite <- H6. simpl. repeat f_equal. apply exist_ext. auto.
rewrite Z.sub_add in H4.
rewrite <- H3 in H4; inv H4.
+
rewrite H2 in j; inv j. rewrite H3 in H5; inv H5.
assert (H99 := pure_readable_share_i _ r0).
pose proof (rmap_valid_e2 ab b' (z'-z) z (mk_rshare _ H99)).
spec H4. rewrite Z.sub_add. rewrite H3. simpl. repeat f_equal. apply exist_ext. auto.
rename H4 into H2'; rename H2 into H4; rename H2' into H2.
rename H3 into H5.
destruct H2 as [nx [? ?]]; exists nx; split; auto.
destruct (ab @ (b',z'-z)); inv H3.
inv j0; try reflexivity.
simpl; repeat f_equal; apply exist_ext.
apply join_glb_Rsh in RJ.
apply join_glb_Rsh in RJ0.
glb_Rsh_tac.
simpl; repeat f_equal. 
assert (H98 := pure_readable_share_i _ rsh3).
pose proof (rmap_valid_e1 c b' (z'-z) _ _ H2 (mk_rshare _ H98)).
spec H3. rewrite <- H10. simpl. repeat f_equal; apply exist_ext. auto.
rewrite Z.sub_add in H3. 
rewrite H4 in H3; inv H3.
+
rewrite H3 in j; rewrite H2 in j; inv j.
assert (H99 := pure_readable_share_i _ r0).
pose proof (rmap_valid_e2 c b' (z'-z) z (mk_rshare _ H99)).
spec H4. rewrite Z.sub_add. rewrite H2. simpl. repeat f_equal; apply exist_ext; auto.
destruct H4 as [n [? ?]]; exists n; split; auto.
destruct (c @ (b',z'-z)); inv H5.
assert (H98 := pure_readable_share_i _ r1).
pose proof (rmap_valid_e2 ab b' (z'-z) z  (mk_rshare _ H98)).
spec H5. rewrite Z.sub_add. rewrite H3. simpl; repeat f_equal; apply exist_ext; auto.
destruct H5 as [n' [? ?]].
destruct (ab @ (b',z'-z)); inv j0; inv H6.
simpl. do 2 f_equal. apply exist_ext.
apply join_glb_Rsh in RJ.
apply join_glb_Rsh in RJ0.
rewrite H9 in *; rewrite H7 in *.
eapply join_eq; eauto.
*
destruct (make_rmap _ _ H2 (level a)) as [abc [? ?]].
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
generalize (resource_at_approx a loc); rewrite <- H9;  intro.
injection (YES_inj _ _ _ _ _ _ _ _ H7); auto.
replace (level a) with (level c).
 2:  clear - H1; apply join_level in H1; destruct H1; congruence.
generalize (resource_at_approx c loc); rewrite <- H5;  intro.
injection (YES_inj _ _ _ _ _ _ _ _ H8); auto.
replace (level a) with (level c).
 2:  clear - H1; apply join_level in H1; destruct H1; congruence.
generalize (resource_at_approx c loc); rewrite <- H5;  intro.
injection (YES_inj _ _ _ _ _ _ _ _ H8); auto.
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
Qed.*)

Obligation Tactic := Tactics.program_simpl.

Lemma pure_readable_Rsh: pure_readable_share Share.Rsh.
Proof.
split. apply glb_Lsh_Rsh. intro. rewrite Share.glb_idem in H.
pose proof (Share.split_nontrivial Share.Lsh Share.Rsh Share.top).
spec H0.
unfold Share.Lsh, Share.Rsh.
destruct (Share.split Share.top); auto.
apply identity_share_bot in H.
spec H0; auto.
contradiction Share.nontrivial.
Qed.

Definition rfullshare : rshare := mk_rshare _ pure_readable_Rsh.

Program Definition writable (l: address): pred rmap :=
 fun phi =>
  match phi @ l with
    | YES sh _ k lp => writable0_share sh /\ isVAL k
    | _ => False
  end.
 Next Obligation.
  intro; intros.
  generalize (age1_res_option a a' l H); intro.
  destruct (a @ l); try contradiction.
  simpl in H1.
  destruct (a' @ l); inv H1; auto.
  destruct H0; split; auto.
  unfold writable0_share in *.
  clear - H3 H0.
  apply leq_join_sub in H0.
  apply leq_join_sub.
  apply Share.ord_spec2 in H0. rewrite <- H0 in H3.
  rewrite Share.glb_absorb in H3.
  clear H0.
  rewrite H3.
  apply Share.glb_lower2.
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
inv H1.
destruct H0.
clear - RJ H0 r.
unfold readable_share, writable0_share in *.
destruct H0.
destruct (join_assoc (join_comm H) (join_comm RJ)) as [a [? ?]].
clear - r H0.
apply r; clear r.
destruct H0.
rewrite H. auto.
Qed.

Lemma writable0_join_sub:
  forall sh sh', join_sub sh sh' -> writable0_share sh -> writable0_share sh'.
Proof.
intros.
destruct H.
destruct H0 as [b ?].
destruct (join_assoc H0 H) as [c [? ?]].
exists c; auto.
Qed.

Lemma writable_join: forall loc phi1 phi2, join_sub phi1 phi2 ->
            writable loc phi1 -> writable loc phi2.
Proof.
unfold writable; intros.
simpl in *.
destruct H; generalize (resource_at_join _ _ _ loc H); clear H.
revert H0; destruct (phi1 @ loc); intros; try contradiction.
destruct H0; subst.
inv H; split; auto; eapply writable0_join_sub; eauto; eexists; eauto.
Qed.

Lemma writable_readable: forall loc m, writable loc m -> readable loc m.
Proof.
 unfold writable, readable.
 intros ? ?. simpl.  destruct (m @ loc); auto. intros [? ?]. auto.
Qed.

Lemma writable_e: forall loc m, 
   writable loc m -> 
   exists sh, exists rsh, exists v, exists p, 
     m @ loc = YES sh rsh (VAL v) p /\ writable0_share sh.
Proof.
unfold writable; simpl; intros; destruct (m@loc); try contradiction.
destruct H.
destruct k; try solve [inversion H0].
exists sh, r, m0, p; split; auto.
Qed.
Arguments writable_e [loc] [m] _.

Lemma readable_e: forall loc m, 
   readable loc m -> 
  exists sh, exists rsh, exists v, exists p, m @ loc = YES sh rsh (VAL v) p.
Proof.
unfold readable; simpl; intros; destruct (m@loc); try contradiction.
destruct k; try solve [inversion H].
subst.
econstructor; eauto.
Qed.
Arguments readable_e [loc] [m] _.

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
destruct (writable0_share_dec sh).
left; auto.
right; auto. contradict n; auto.
destruct n; auto.
right; contradict n; destruct n; auto.
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
specialize ( n0 0).
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
specialize ( n0 0).
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

Lemma rmap_age_i:
 forall w w' : rmap,
    level w = S (level w') ->
   (forall l, resource_fmap (approx (level w')) (approx (level w')) (w @ l) = w' @ l) ->
    ghost_fmap (approx (level w')) (approx (level w')) (ghost_of w) = ghost_of w' ->
    age w w'.
Proof.
intros.
hnf.
destruct (levelS_age1 _ _ H).
assert (x=w'); [ | subst; auto].
assert (level x = level w')
  by (apply age_level in H2; omega).
apply rmap_ext; auto.
intros.
specialize (H0 l).
rewrite (age1_resource_at w x H2 l (w@l)).
rewrite H3.
apply H0.
symmetry; apply resource_at_approx.
erewrite age1_ghost_of; eauto.
rewrite H3; apply H1.
Qed.
