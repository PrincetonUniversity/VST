Load loadpath.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem.
Require Import veric.seplog.
Require Import veric.res_predicates.

Definition juicy_mem_core (j: juicy_mem) : rmap := core (m_phi j).

Lemma inflate_initial_mem_empty:
  forall lev, emp (inflate_initial_mem Mem.empty lev).
intro lev.
unfold inflate_initial_mem.
destruct (make_rmap (inflate_initial_mem' Mem.empty lev)
        (inflate_initial_mem'_valid Mem.empty lev) (level lev)
        (inflate_initial_mem'_fmap Mem.empty lev)); simpl.
destruct a.
apply resource_at_empty2.
intro l; rewrite H0.
unfold inflate_initial_mem'.
destruct l.
unfold access_at; unfold empty at 1.
simpl.
rewrite ZMap.gi.
destruct (max_access_at empty (b,z)); try destruct p; try apply NO_identity.
Qed.
Local Hint Resolve inflate_initial_mem_empty.

(* fancy initial mem *)

(* TODO: move this somewhere more appropriate *)
Definition no_VALs (phi: rmap) := forall loc, 
  match phi @ loc with
    | YES _ _ (VAL _) _ => False | _ => True
  end.

Lemma components_join_joins {A} {JA: Join A}{PA: Perm_alg A}{TA: Trip_alg A}: forall a b c d,
   join a b c -> joins a d -> joins b d -> joins c d.
Proof.
intros.
destruct H0 as [x ?]. destruct H1 as [y ?].
destruct (TA a b d c y x H H1 H0).
eauto.
Qed.

(* coherence lemmas *)

Lemma contents_cohere_join_sub: forall m phi phi',
  contents_cohere m phi -> join_sub phi' phi -> contents_cohere m phi'.
Proof.
unfold contents_cohere.
intros until phi'; intros H H0.
intros.
destruct H0 as [phi1 H0].
generalize (resource_at_join phi' phi1 phi loc H0); intro H2.
rewrite H1 in H2.
inv H2;
symmetry in H9;
destruct (H _ _ _ _ _ H9); auto.
Qed.

Lemma perm_of_sh_join_sub: forall (rsh1 rsh2: Share.t) (sh1 sh2: pshare) p,
  perm_of_sh rsh1 (pshare_sh sh1) = Some p ->
  join_sub rsh1 rsh2 ->
  join_sub sh1 sh2 ->
  perm_order' (perm_of_sh rsh2 (pshare_sh sh2)) p.
Proof.
intros.
rename H0 into HR; rename H1 into H0.
destruct H0 as [sh1' ?].
unfold perm_of_sh in *.
if_tac in H.
destruct sh1; simpl in H1. subst x.
do 3 red in H0. simpl in H0.
apply pshare_join_full_false4 in H0. contradiction.
if_tac in H.
if_tac in H.
inv H.
inv H.
if_tac.
if_tac; constructor.
if_tac.
rewrite if_false. constructor.
intro; subst.
destruct HR.
apply split_identity in H5; auto. apply identity_share_bot in H5; contradiction.
constructor.
inv H.
if_tac. if_tac; constructor.
rewrite if_false.
constructor.
destruct sh2; simpl; intro.
subst x.
destruct sh1; destruct sh1'; simpl in *.
red in H0. red in H0.  red in H0.  simpl in H0.
apply nonunit_nonidentity in n. contradiction n; auto.
Qed.

Lemma perm_order'_trans: forall p1 p2 p3,
  perm_order' (Some p1) p2 -> perm_order' (Some p2) p3 -> perm_order' (Some p1) p3.
Proof.
intros.
unfold perm_order' in *.
eapply perm_order_trans; eauto.
Qed.

Lemma rmap_unage_YES: forall phi phi' rsh sh k pp loc, 
  age phi phi' 
  -> phi' @ loc = YES rsh sh k pp 
  -> exists pp', phi @ loc = YES rsh sh k pp'.
Proof.
intros.
unfold age in H.
case_eq (phi @ loc). intros.
cut (necR phi phi'). intro.
generalize (necR_NO phi phi' loc t H2). intro.
rewrite H3 in H1.
rewrite H1 in H0; inv H0.
constructor; auto.
intros.
exists p0.
apply necR_YES with (phi' := phi') in H1.
rewrite H1 in H0.
inv H0. auto.
constructor; auto.
intros.
elimtype False.
eapply necR_PURE in H1.
2: constructor 1; eassumption.
congruence.
Qed.

Lemma preds_fmap_NoneP_approx: forall pp lev1 lev2,
  preds_fmap (approx lev1) pp = NoneP -> preds_fmap (approx lev2) pp = NoneP.
Proof.
intros.
destruct pp.
unfold NoneP, approx, compose in *.
simpl in *. unfold compose in *.
inv H. simpl in *.
apply EqdepFacts.eq_sigT_eq_dep in H2.
apply Eqdep.EqdepTheory.eq_dep_eq in H2.
f_equal.
extensionality.
apply exist_ext.
extensionality.
f_equal.
intuition.
Qed.

(* Admitted:  rename this to supplant unage_juicy_mem *)
Lemma oracle_unage:
  forall (jm': juicy_mem) (w: rmap), age w (m_phi jm') -> 
       exists jm, age jm jm' /\ m_phi jm = w.
Proof.
intros.
destruct jm' as [m phi' CONTENTS ACCESS MAXA ALLOC].
simpl m_phi in H.
assert (contents_cohere m w).
hnf; intros.
destruct (necR_YES'' w phi' loc rsh sh (VAL v)).
constructor 1; auto.
destruct H1 as [p ?].
eauto.
destruct (CONTENTS _ _ _ _ _ H1); eauto.
subst p.
apply (age1_YES w phi') in H1; auto.
inversion2 H0 H1. auto.
assert (access_cohere m w).
intro loc; specialize (ACCESS loc).
case_eq (w @ loc); intros.
apply (necR_NO w phi') in H1. rewrite H1 in ACCESS; auto.
constructor 1;auto.
apply (necR_YES w phi') in H1.
rewrite H1 in ACCESS; auto.
constructor 1; auto.
apply (necR_PURE w phi') in H1.
rewrite H1 in ACCESS; auto.
constructor 1; auto.
assert (max_access_cohere m w).
intro loc; specialize (MAXA loc).
case_eq (w @ loc); intros; auto.
apply (necR_NO w phi') in H2. rewrite H2 in MAXA. auto. constructor 1; auto.
apply (necR_YES w phi') in H2.
rewrite H2 in MAXA; auto.
constructor 1; auto.
apply (necR_PURE w phi') in H2.
rewrite H2 in MAXA; auto.
constructor 1; auto.
assert (alloc_cohere m w).
intros loc ?. specialize (ALLOC _ H3).
apply (necR_NO w phi').
constructor 1; auto.
auto.
exists (mkJuicyMem m w H0 H1 H2 H3).
split; auto.
apply age1_juicy_mem_unpack''; simpl; auto.
Qed.

(* core load and coherence properties *)

Lemma writable_perm:
  forall b i jm, writable (b,i) (m_phi jm) -> Mem.perm (m_dry jm) b i Cur Writable.
Proof.
intros until jm; intros H.
assert (Hacc := juicy_mem_access jm).
unfold access_cohere in Hacc.
unfold Mem.perm, Mem.perm_order'.
spec Hacc (b, i).
simpl in H.
destruct (m_phi jm @ (b, i)).
contradiction.
destruct H as [H1 [? H2]]. subst k p.
unfold access_at in Hacc.
simpl in Hacc.
rewrite Hacc.
destruct (eq_dec t Share.top).
rewrite e.
unfold perm_of_res; simpl; rewrite perm_of_freeable; constructor.
unfold perm_of_res; simpl; rewrite perm_of_writable; auto; constructor.
contradiction.
Qed.

Lemma valid_access_None: forall m ch b b' ofs ofs' p,
  Mem.valid_access m ch b ofs p 
  -> adr_range (b, ofs) (size_chunk ch) (b', ofs') 
  -> access_at m (b', ofs') = None 
  -> False.
Proof.
unfold access_at, Mem.valid_access, Mem.perm, Mem.range_perm, Mem.perm, Mem.perm_order'.
simpl.
intros.
destruct H as [H ?].
destruct H0 as [H3 H4].
subst.
spec H ofs' H4.
rewrite H1 in H.
auto.
Qed.

Lemma core_load_getN: forall ch v b ofs bl phi m, 
  contents_cohere m phi
  -> (core_load' ch (b, ofs) v bl)%pred phi
  -> bl = Mem.getN (size_chunk_nat ch) ofs (ZMap.get b (Mem.mem_contents m)).
Proof.
intros until m; intros H0 H.
destruct H as [[H3 H4] H].
unfold allp, jam in H.
rewrite <- H3.
simpl in *.
clear H4.
revert ofs H H3.
assert (H: size_chunk_nat ch = nat_of_Z (size_chunk ch)) by auto.
rewrite H; clear H.
generalize (size_chunk ch) as z.
induction bl; intros; simpl; auto. 
rewrite IHbl with (ofs := ofs + 1) (z := z - 1); auto.
rewrite Mem.getN_length.
f_equal; auto.
spec H (b, ofs).
cut (adr_range (b, ofs) z (b, ofs)); [intro H6|].
destruct (adr_range_dec (b, ofs) z (b, ofs)).
  2: elimtype False; auto.
simpl in H.
cut (nat_of_Z (ofs - ofs) = O); [intro H7|].
rewrite H7 in H.
destruct H as [rsh [sh [p H]]].
unfold contents_cohere in H0.
symmetry.
destruct (H0 _ _ _ _ _ H) as [? _].
apply H1.
replace (ofs - ofs) with 0 by omega; auto.
unfold adr_range; split; auto.
cut (z > 0). omega.
inversion H3.
cut (z = Z_of_nat (length bl) + 1). omega.
assert (HS_nat_Z: forall n z, S n = nat_of_Z z -> Z_of_nat n + 1 = z).
  intros n z' H4.
  cut (Z_of_nat 1 = 1).
  intro H5.
  rewrite <- H5.
  rewrite <- inj_plus.
  replace (Z_of_nat (n + 1%nat)) with (Z_of_nat (S n)).
  rewrite H4.
  rewrite Coqlib.nat_of_Z_eq; auto.
  destruct z'; try solve [omega].
  inversion H4.
  rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in H6.
  rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
  rewrite <- H6.
  omega.
  simpl in H4.
  inv H4.
  idtac.
  replace (plus n (S 0)) with (S n).
  auto.
  omega.
  auto.
symmetry; apply HS_nat_Z; auto.
intros loc'.
spec H loc'.
cut ( adr_range (b, ofs + 1) (z - 1) loc' -> adr_range (b, ofs) z loc').
intro H1.
destruct (adr_range_dec (b, ofs + 1) (z - 1) loc').
destruct (adr_range_dec (b, ofs) z loc').
simpl in H.
case_eq (nat_of_Z (snd loc' - ofs)).
intro H2.
destruct loc' as (b', ofs').
simpl in *.
cut (ofs' > ofs). intro H4.
cut (exists p, ofs' - ofs = Zpos p). intros [p H5].
unfold nat_of_Z in H2.
rewrite H5 in H2.
unfold nat_of_P in H2.
generalize (le_Pmult_nat p 1) as H6; intro.
rewrite H2 in H6.
omegaContradiction.
assert (ofs' - ofs > 0).
omega.
assert (forall z, z > 0 -> exists p, z = Zpos p).
  intros.
  assert (exists n, nat_of_Z z0 = S n).
    exists (nat_of_Z (z0 - 1)).
    destruct z0; try solve [inv H6].
    destruct p; auto.
    simpl.
    change (nat_of_P p~0 = S (nat_of_P (p~0 - 1))).
    rewrite <- nat_of_P_succ_morphism.
    rewrite <- Ppred_minus.
    simpl.
    rewrite Psucc_o_double_minus_one_eq_xO.
    auto.
  destruct H7 as [n ?].
  exists (P_of_succ_nat n).
  rewrite Zpos_P_of_succ_nat.
  rewrite <- inj_S.
  rewrite <- H7.
  rewrite Coqlib.nat_of_Z_eq.
  auto.
omega.
apply H6; auto.
omega.
intros n H2.
rewrite H2 in H.
assert (nat_of_Z (snd loc' - (ofs + 1)) = n).
  destruct loc'.
  simpl in *.
  assert (Z_of_nat (nat_of_Z (z0 - ofs)) = Z_of_nat (S n)).
  auto.
  assert (z0 - ofs > 0).
    omega.
  rewrite Coqlib.nat_of_Z_eq in H4; try solve [omega].
  replace (z0 - (ofs + 1)) with (z0 - ofs - 1) by omega.
  rewrite H4.
  destruct n; try solve [simpl; omega].
  replace (Z_of_nat (S (S n)) - 1) with (Z_of_nat (S n)).
  rewrite nat_of_Z_eq.
  auto.
  replace (Z_of_nat (S n)) with (Zpos (P_of_succ_nat n)) by auto.
  replace (Z_of_nat (S (S n))) with (Zpos (P_of_succ_nat (S n))) by auto.
  do 2 rewrite Zpos_P_of_succ_nat.
  replace (Zsucc (Z_of_nat (S n)) - 1) with (Z_of_nat (S n)) by omega.
  simpl.
  rewrite Zpos_P_of_succ_nat.
  auto.
rewrite H4.
apply H.
elimtype False. auto.
auto.
unfold adr_range.
destruct loc' as (b', ofs').
intros [H1 H2].
split; auto || omega.
inversion H3.
assert (z > 0).
  assert (forall n z, S n = nat_of_Z z -> z > 0).
    intros.
    destruct z0; try solve [inv H1].
    apply Zgt_pos_0.
  eapply H1; eauto.
assert (z - 1 >= 0).
omega.
assert (Z_of_nat (S (length bl)) = Z_of_nat (nat_of_Z z)).
rewrite Coqlib.nat_of_Z_eq; try solve [omega].
rewrite H2.
rewrite Coqlib.nat_of_Z_eq; try solve [omega].
rewrite Coqlib.nat_of_Z_eq in H5; try solve [omega].
rewrite <- H5.
rewrite inj_S.
assert (forall z, Zsucc z - 1 = z) by (intros; omega).
rewrite H6.
rewrite nat_of_Z_eq.
auto.
Qed.

Lemma core_load_valid: forall ch v b ofs m phi,
  (core_load ch (b, ofs) v)%pred phi
  -> access_cohere m phi
  -> Mem.valid_access m ch b ofs Readable.
Proof.
intros until phi; intros H H0.
hnf in H.
destruct H as [bl [[H1 [H2 Halign]] H]].
hnf in H.
split.
intros ofs' H4.
spec H (b, ofs').
hnf in H.
destruct (adr_range_dec (b, ofs) (size_chunk ch) (b, ofs')) as [H5|H5].
  2: unfold adr_range in H5.
  2: elimtype False; apply H5; split; auto.
destruct H as [rsh [sh [pf H]]].
simpl in H.
unfold access_cohere in H0.
spec H0 (b, ofs').
unfold Mem.perm, Mem.perm_order'.
rewrite H in H0.
unfold access_at in H0.  simpl in H0. rewrite H0.
unfold perm_of_res. simpl.
destruct (eq_dec sh fullshare). subst.
destruct (eq_dec rsh Share.top). subst.
rewrite perm_of_freeable. constructor.
rewrite perm_of_writable; auto. constructor.
rewrite perm_of_readable; auto. constructor.
clear - pf; intro; subst. apply nonunit_nonidentity in pf. contradiction pf; auto.
auto.
Qed.

Lemma core_load_load': forall ch b ofs v m,
  core_load ch (b, ofs) v (m_phi m) -> Mem.load ch (m_dry m) b ofs = Some v.
Proof.
intros until m; intros H.
generalize H as Hcore_load; intro.
Transparent Mem.load.
unfold core_load in H; unfold Mem.load.
unfold allp, jam in H.
destruct H as [bl [[H0 [H1 Halign]] H]].
assert (H3 := juicy_mem_contents m).
pose proof I.
pose proof I.
if_tac.
f_equal.
generalize (core_load_getN ch v b ofs bl (m_phi m) (m_dry m) H3) as H7; intro.
rewrite <- H7; auto.
unfold core_load'.
repeat split; auto.
elimtype False.
apply H5.
eapply core_load_valid; eauto.
apply juicy_mem_access.
Qed.

Lemma Zminus_lem: forall z1 z2, z1 <= z2 -> nat_of_Z (z2 - z1) = O -> z1=z2.
Proof.
intros.
case_eq (z2 - z1). intro.
rewrite H1 in H0.
symmetry; apply Zminus_eq; auto.
intros.
generalize (lt_O_nat_of_P p). intro.
rewrite H1 in H0.
simpl in *.
omegaContradiction.
intros.
generalize (Zlt_neg_0 p). intro.
rewrite H1 in H0.
omegaContradiction.
Qed.

Lemma nat_of_Z_lem1: forall n z, S n = nat_of_Z z -> n = nat_of_Z (z - 1).
Proof.
intros.
destruct z; try solve [inv H].
generalize (lt_O_nat_of_P p). intro.
case_eq (Zpos p - 1). intro.
assert (Zpos p = 1) by omega.
rewrite H2 in H. auto.
intros. 
assert (Zpos p = Zpos p0 + 1) by omega.
rewrite H2 in H.
rewrite nat_of_Z_plus in H; try omega.
simpl in H.
simpl. 
assert (forall m n, S m = n + 1 -> m = n)%nat.
  intros. omega.
apply H3; auto.
generalize (lt_O_nat_of_P p0). intro. 
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
omega.
intros.
assert (Zpos p = Zneg p0 + 1) by omega.
assert (Zpos p > 0) by (rewrite Zpos_eq_Z_of_nat_o_nat_of_P; omega).
generalize (Zlt_neg_0 p0). intro.
omegaContradiction.
Qed.

Lemma nat_of_Z_lem2: forall n z1 z2, S n = nat_of_Z (z1 - z2) -> n = nat_of_Z (z1 - z2 - 1).
Proof. intros; apply nat_of_Z_lem1; auto. Qed.

Lemma nth_getN: forall m b ofs ofs' z, 
  ofs <= ofs' < ofs + z
  -> z >= 0
  -> contents_at m (b, ofs')
  = nth (nat_of_Z (ofs' - ofs)) (Mem.getN (nat_of_Z z) ofs (ZMap.get b (Mem.mem_contents m))) Undef.
Proof.
intros.
revert ofs ofs' H H0.
remember (nat_of_Z z) as n.
revert n z Heqn.
induction n; intros.
destruct z.
inv H.
omegaContradiction.
simpl in *.
generalize (lt_O_nat_of_P p). intro.
omegaContradiction.
generalize (Zlt_neg_0 p).
intro.
omegaContradiction.
simpl.
case_eq (nat_of_Z (ofs' - ofs)).
intros.
assert (ofs = ofs').
  destruct H.
  apply Zminus_lem; auto.
subst; auto.
intros.
symmetry in H1.
assert (n = nat_of_Z (z - 1)) by (apply nat_of_Z_lem1 in Heqn; auto).
rewrite (IHn (z - 1) H2 (ofs + 1)); try solve [auto|omega].
assert (nat_of_Z (ofs' - (ofs + 1)) = n0).
replace (ofs' - (ofs + 1)) with (ofs' - ofs - 1) by omega.
  apply nat_of_Z_lem1 in H1.
  auto.
rewrite H3; auto.
destruct H.
split.
case_eq (ofs' - ofs). intro. rewrite H4 in H1.
simpl in *. inv H1.
intros. rewrite H4 in H1. simpl in *.
generalize (lt_O_nat_of_P p). intro.
cut (1 <= ofs' - ofs). intro. omega.
rewrite H4.
generalize (Zpos_eq_Z_of_nat_o_nat_of_P p). intro. rewrite H6.
omega.
intros.
generalize (Zlt_neg_0 p). intro.
omegaContradiction.
omega.
Qed.

Lemma load_core_load: forall ch b ofs v m,
  Mem.load ch (m_dry m) b ofs = Some v -> core_load ch (b, ofs) v (m_phi m).
Proof.
intros until m; intros H.
hnf.
unfold Mem.load in H. 

(* unfold core_load, allp, jam. *)
if_tac in H; try solve [inv H].
inversion H.
clear H.
exists (Mem.getN (size_chunk_nat ch) ofs (ZMap.get b (Mem.mem_contents (m_dry m)))).
generalize H0 as H0'; intro.
Local Hint Resolve Mem.getN_length.
unfold Mem.valid_access in H0'.
destruct H0' as [H0'1 H0'2].
repeat split; auto.
clear H0'1 H0'2.
intros (b', ofs').
hnf.
if_tac; hnf; auto.
assert (Heqbb': b = b'). 
  unfold adr_range in H. decompose [and] H. auto.
pose proof (juicy_mem_contents m).
pose proof (juicy_mem_access m).
pose proof I.
pose proof I.
clear H4.
unfold access_cohere in H3.
spec H3 (b', ofs').
unfold perm_of_res in *.
assert (H99: valshare (m_phi m @ (b', ofs')) <> Share.bot).
intro Hx; rewrite Hx in *.
elimtype False; forget (res_retain' (m_phi m @ (b',ofs'))) as r; clear - H H0 H3.
destruct (eq_dec r Share.bot).
subst r. rewrite perm_of_empty in H3.
eapply valid_access_None; eauto.
rewrite perm_of_nonempty in H3; auto.
destruct H0 as [? _]; specialize (H0 ofs'). destruct H.
specialize (H0 H1). subst b'. 
unfold perm, access_at in H0,H3. simpl in H3. rewrite H3 in H0. inv H0.
case_eq (m_phi m @ (b', ofs')).
intros rsh H4; rewrite H4 in H99; contradiction H99; simpl; auto.
intros rsh [sh p] k pp H4.
rewrite H4 in H3, H99.
destruct k; try solve [contradiction H99; simpl; auto].
exists rsh,sh; exists p.
destruct (H1 _ _ _ _ _ H4). subst pp.
cut (m0 = nth (nat_of_Z (snd (b', ofs') - snd (b, ofs)))
           (Mem.getN (size_chunk_nat ch) ofs (ZMap.get b (Mem.mem_contents (m_dry m))))
           Undef). intro Heq0.
f_equal; auto.
f_equal; auto.
subst. 
simpl.
rewrite nth_getN with (ofs := ofs) (z := size_chunk ch); auto.
unfold adr_range in H.
replace (size_chunk ch) with (size_chunk ch) in H.
omega.
auto.
generalize (size_chunk_pos ch).
intros.
omega.
intros. rewrite H4 in H3. elimtype False.
subst b'. hnf in H0. unfold access_at in H3. simpl in H3.
destruct H0;  unfold range_perm in H0.
unfold perm in H0. destruct H. specialize (H0 _ H7).
rewrite H3 in H0. 
rewrite H4 in H99. simpl in H99. contradiction H99; auto.
Qed.

Lemma core_load_load: forall ch b ofs v m,
  core_load ch (b, ofs) v (m_phi m) <-> Mem.load ch (m_dry m) b ofs = Some v.
Proof.
intros until m.
split; [apply core_load_load'|apply load_core_load].
Qed.

Lemma address_mapsto_exists':
  forall ch v rsh (sh: pshare) loc m lev,
      (align_chunk ch | snd loc)
      -> Mem.load ch m (fst loc) (snd loc) = Some v 
      -> exists w, address_mapsto ch v rsh (pshare_sh sh) loc w /\ level w = lev.
Proof.
intros. rename H into Halign.
unfold address_mapsto.
pose (f l' := if adr_range_dec loc (size_chunk ch) l'
                     then YES rsh sh (VAL (nthbyte (snd l' - snd loc) (Mem.getN (size_chunk_nat ch) (snd loc) (ZMap.get (fst loc) (Mem.mem_contents m))))) NoneP
                     else NO Share.bot).
assert (CompCert_AV.valid (res_option oo f)).
apply VAL_valid.
unfold compose, f; intros.
if_tac in H.
simpl in H.
injection H;intros; subst k; auto.
inv H.
destruct (make_rmap f H lev) as [phi [? ?]].
extensionality l; unfold f, compose; simpl.
if_tac; hnf; auto.
simpl.
f_equal.
unfold NoneP. f_equal. unfold compose. extensionality x.
apply approx_FF.
exists phi.
split; auto.
exists (Mem.getN (size_chunk_nat ch) (snd loc) (ZMap.get (fst loc) (Mem.mem_contents m))).
split.
repeat split; auto. 
Transparent Mem.load.
unfold load in *. if_tac in H0. injection H0. auto. inv H0.
intro l'.
unfold jam.
hnf.
simpl.
rewrite H2; clear H H1 H2.
unfold f; clear f.
if_tac.
destruct sh; simpl in *.
exists n.
f_equal. 
unfold NoneP; f_equal.
extensionality xx.  unfold compose. symmetry.
apply approx_FF.
auto.
apply NO_identity.
Qed.
    
Lemma mapsto_valid_access: forall ch v rsh sh b ofs jm,
  (address_mapsto ch v rsh sh (b, ofs) * TT)%pred (m_phi jm)
  -> Mem.valid_access (m_dry jm) ch b ofs Readable.
Proof.
intros.
unfold address_mapsto in H.
unfold Mem.valid_access, Mem.range_perm.
split.
destruct H as [x [y [Hjoin ?]]].
destruct H as [[bl [[H2 [H3 H3']] H]] ?].
hnf in H.
intros ofs' H4.
spec H (b, ofs').
hnf in H.
destruct (adr_range_dec (b, ofs) (size_chunk ch) (b, ofs')) as [H5|H5].
  2: unfold adr_range in H5.
  2: elimtype False; apply H5; split; auto.
hnf in H.
destruct H as [pf H].
hnf in H.
rewrite preds_fmap_NoneP in H.
simpl in H.
generalize (resource_at_join _ _ _ (b,ofs') Hjoin); rewrite H; intro.
forget ((nth (nat_of_Z (ofs' - ofs)) bl Undef)) as v'.
assert (exists rsh', exists sh', m_phi jm @ (b,ofs') = YES rsh' sh' (VAL v') NoneP).
inv H1; eauto.
destruct H6 as [rsh' [sh' ?]].
generalize (juicy_mem_access jm (b,ofs')); rewrite H6; unfold perm_of_res; simpl; intro.
clear - H7.
unfold perm, access_at in *.
simpl in H7; rewrite H7.
clear.
unfold perm_of_sh.
if_tac. if_tac; constructor. rewrite if_false. constructor.
intro.
generalize (pshare_nonunit sh'); rewrite H0; intro.
apply nonunit_nonidentity in H1; contradiction H1; auto.
repeat match goal with [ H: context[ _ /\ _ ] |- _] => destruct H end.
auto.
Qed.


Lemma mapsto_valid_access_wr: forall ch v rsh b ofs jm,
  (address_mapsto ch v rsh Share.top (b, ofs) * TT)%pred (m_phi jm)
  -> Mem.valid_access (m_dry jm) ch b ofs Writable.
Proof.
intros.
unfold address_mapsto in H.
unfold Mem.valid_access, Mem.range_perm.
split.
destruct H as [x [y [Hjoin ?]]].
destruct H as [[bl [[H2 [H3 H3']] H]] ?].
hnf in H.
intros ofs' H4.
spec H (b, ofs').
hnf in H.
destruct (adr_range_dec (b, ofs) (size_chunk ch) (b, ofs')) as [H5|H5].
  2: unfold adr_range in H5.
  2: elimtype False; apply H5; split; auto.
hnf in H.
destruct H as [pf H].
hnf in H.
rewrite preds_fmap_NoneP in H.
simpl in H.
generalize (resource_at_join _ _ _ (b,ofs') Hjoin); rewrite H; intro.
forget ((nth (nat_of_Z (ofs' - ofs)) bl Undef)) as v'.
assert (exists rsh', m_phi jm @ (b,ofs') = YES rsh' pfullshare (VAL v') NoneP).
inv H1; try pfullshare_join.
exists rsh3.
f_equal.
apply exist_ext; auto.
destruct H6 as [rsh' ?].
generalize (juicy_mem_access jm (b,ofs')); rewrite H6; unfold perm_of_res; simpl; intro.
clear - H7.
unfold perm, access_at in *.
simpl in H7; rewrite H7.
clear.
unfold perm_of_sh.
rewrite if_true. if_tac; constructor.
auto.
repeat match goal with [ H: context[ _ /\ _ ] |- _] => destruct H end.
auto.
Qed.

Lemma mapsto_can_store: forall ch v rsh b ofs jm v',
  (address_mapsto ch v rsh Share.top (b, ofs) * TT)%pred (m_phi jm)
  -> exists m', Mem.store ch (m_dry jm) b ofs v' = Some m'.
Proof.
intros.
pose proof (mapsto_valid_access_wr _ _ _ _ _ _ H).
exists (mkmem
  (ZMap.set b (setN (encode_val ch v') ofs (ZMap.get b (mem_contents (m_dry jm))))
    (mem_contents (m_dry jm))) (mem_access (m_dry jm)) 
  (nextblock (m_dry jm)) (nextblock_pos (m_dry jm)) (access_max (m_dry jm)) (nextblock_noaccess (m_dry jm))).
Transparent Mem.store. unfold store.
rewrite if_true by auto. auto.
Qed.

Lemma store_outside':
   forall ch m b z v m',
          Mem.store ch m b z v = Some m' ->
  (forall b' ofs,
    (b=b' /\ z <= ofs < z + size_chunk ch) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ Mem.mem_access m = Mem.mem_access m'
  /\ Mem.nextblock m = Mem.nextblock m'.
Proof.
intros.
repeat split.
intros.
generalize (Mem.store_mem_contents _ _ _ _ _ _ H); intro.
destruct (eq_block b b').
subst b'.
assert (z <= ofs < z + size_chunk ch \/ (ofs < z \/ ofs >= z + size_chunk ch)) by omega.
destruct H1.
left; auto.
right.
unfold contents_at; rewrite H0; clear H0.
simpl.
rewrite ZMap.gss.
rewrite Mem.setN_other; auto.
intros.
rewrite encode_val_length in H0.
rewrite <- size_chunk_conv in H0.
destruct H0.
destruct H1.
omega.
omega.
right.
unfold contents_at; rewrite H0; clear H0.
simpl.
rewrite ZMap.gso by auto. auto.
symmetry; eapply Mem.store_access; eauto.
symmetry; eapply Mem.nextblock_store; eauto.
Qed.

Lemma adr_range_zle_zlt : forall  b lo hi ofs,
  adr_range (b,lo) (hi-lo) (b,ofs)
  -> zle lo ofs && zlt ofs hi = true.
Proof.
intros.
destruct H as [H [H1 H2]].
rewrite andb_true_iff.
split.
unfold zle.
case_eq (Z_le_gt_dec lo ofs); intros; auto.
unfold zlt.
case_eq (Z_lt_ge_dec ofs hi); intros; auto.
omegaContradiction.
Qed.

Lemma juicy_free_lemma:
  forall {j b lo hi m' m1}
    (H: Mem.free (m_dry j) b lo hi = Some m'),
    VALspec_range (hi-lo) Share.top Share.top (b,lo) m1 ->
    core m1 = core (m_phi j) ->
    (forall l rsh sh k pp, m1 @ l = YES rsh sh k pp 
      -> exists rsh', exists sh':pshare, 
            exists pp', join_sub rsh rsh' 
              /\ (join_sub (pshare_sh sh) (pshare_sh sh'))
              /\ m_phi j @ l = YES rsh' sh' k pp') -> 
    join m1 (m_phi (free_juicy_mem _ _ _ _ _ H)) (m_phi j).
Proof.
intros j b lo hi m' m1.
pose (H0 :=True).
intros H  H1 H2 Hyes.
assert (forall l, ~adr_range (b,lo) (hi-lo) l -> identity (m1 @ l)).
  unfold VALspec_range, allp, jam in H1.
  intros l. spec H1 l. intros H3.
  hnf in H1; if_tac in H1; try solve [contradiction].
  apply H1.
assert (forall l, adr_range (b,lo) (hi-lo) l 
  -> exists mv, yesat NoneP (VAL mv) Share.top Share.top l m1).
  unfold VALspec_range, allp, jam in H1.
  intros l. spec H1 l. intros H4.
  hnf in H1; if_tac in H1; try solve [contradiction].
  apply H1.
remember (free_juicy_mem _ _ _ _ _ H) as j'.
assert (m' = m_dry j') by (subst; reflexivity).
assert (Ha := juicy_mem_access j').
unfold access_cohere in Ha.
apply resource_at_join2; auto.
rewrite <- (level_core m1). rewrite <- (level_core (m_phi j)). congruence.
subst j'. simpl. unfold inflate_free. simpl. rewrite level_make_rmap. auto.
intros (b0, ofs0). 
subst j'. simpl.
unfold inflate_free; rewrite resource_at_make_rmap.
rewrite resource_at_approx.
destruct (adr_range_dec (b,lo) (hi-lo) (b0,ofs0)).
(* adr_range *)
clear H3.
spec H4 (b0,ofs0) a.
destruct H4 as [mv H4].
unfold yesat, yesat_raw in H4. destruct H4 as [pp H4].
simpl in H4.
rewrite H4.
clear H0.
assert (H0 : access_at m' (b0, ofs0) = None).
  clear - H a.
  Transparent free.
  unfold free in H.
  if_tac in H; try solve [congruence].
  unfold unchecked_free in H. inv H. simpl.
  assert (b = b0) by (destruct a; auto). subst.
  unfold access_at; simpl. rewrite ZMap.gss.
  rewrite adr_range_zle_zlt with (b:=b0); auto.
spec Ha (b0,ofs0). rewrite <- H5 in Ha.
rewrite H0 in Ha.
assert (H3 : m_phi j @ (b0, ofs0) = YES Share.top pfullshare (VAL mv) NoneP).
  clear - H H4 a Hyes.
  assert (Ha := juicy_mem_access j (b0,ofs0)).
  generalize (Hyes _ _ _ _ _ H4); intros.
  repeat rewrite preds_fmap_NoneP in *. 
  unfold pfullshare; auto.
  destruct H0 as [rsh' [? [? [RJ [? ?]]]]]. 
  rewrite H1. repeat f_equal. 
  apply join_sub_fullshare; auto. 
  destruct H0.
  apply lifted_eq. simpl.
  apply join_sub_fullshare. eauto with typeclass_instances.
  pose proof (juicy_mem_contents j).
   destruct (H2 _ _ _ _ _ H1); auto.
rewrite H3. repeat rewrite preds_fmap_NoneP. unfold pfullshare.
rewrite H0. simpl.
apply join_unit2. constructor. apply join_unit1; auto.
f_equal. apply exist_ext; auto.
unfold NoneP. f_equal. extensionality z. unfold compose. apply approx_FF.

(* ~adr_range *)
 clear H0.
generalize (H3 _ n); intro H3'.
  assert (core (m1 @ (b0,ofs0)) = core (m_phi j @ (b0,ofs0))).
  do 2 rewrite core_resource_at. unfold Join_rmap in *.  unfold Sep_rmap in  *; congruence.
  apply identity_resource in H3'.
  revert H3'; case_eq (m1 @ (b0,ofs0));intros; try contradiction; try constructor.
  apply identity_share_bot in H3'; subst t.
Focus 2.
  rewrite H6 in H0. rewrite core_PURE in H0.
  destruct (m_phi j @ (b0,ofs0)).
  rewrite core_NO in H0; inv H0. rewrite core_YES in H0; inv H0.
  rewrite core_PURE in H0. inversion H0. subst k0 p0; constructor.
  rename H6 into Hm1.
 clear H0.
destruct (free_nadr_range_eq _ _ _ _ _ _ _ n H) as [H0 H10].
rewrite <- H0 in *; clear H0.
  assert (Ha0 := juicy_mem_access j (b0,ofs0)).
 revert Ha0; 
  case_eq (m_phi j @ (b0,ofs0)); intros.
 constructor. apply join_unit1; auto.
 rewrite Ha0. unfold perm_of_res. simpl. 
 destruct k; try solve [constructor; apply join_unit1; auto].
 unfold perm_of_sh.
 if_tac. if_tac; constructor; apply join_unit1; auto.
 rewrite if_false. constructor; apply join_unit1; auto.
 intro. generalize (pshare_nonunit p); rewrite H7; intro.
apply nonunit_nonidentity in H8; contradiction H8; auto.
unfold perm_of_res in Ha0. simpl in Ha0.

  elimtype False.
  clear - H2 Hm1 H0.
  assert (core (m1 @ (b0,ofs0)) = core (m_phi j @ (b0,ofs0))).
  do 2 rewrite core_resource_at.  unfold Join_rmap in *;  unfold Sep_rmap in  *; congruence.
  rewrite H0 in H. rewrite Hm1 in H. rewrite core_PURE in H. rewrite core_NO in H; inv H.
Qed.



Lemma initial_mem_core: forall lev m j IOK,
  j = initial_mem m lev IOK -> juicy_mem_core j = core lev.
Proof.
intros.
destruct j; simpl.
unfold initial_mem in H.
inversion H; subst.
unfold juicy_mem_core. simpl.
clear - IOK.
apply rmap_ext.
repeat rewrite level_core.
erewrite inflate_initial_mem_level; eauto.
intro loc.
repeat rewrite <- core_resource_at.
unfold inflate_initial_mem.
rewrite resource_at_make_rmap.
unfold inflate_initial_mem'.
repeat rewrite <- core_resource_at.
destruct (IOK loc). clear IOK.
revert H0; case_eq (lev @ loc); intros.
rewrite core_NO.
destruct (access_at m loc); try destruct p; try rewrite core_NO; try rewrite core_YES; auto.
destruct (access_at m loc); try destruct p1; try rewrite core_NO;  repeat rewrite core_YES; auto.
destruct H1.
destruct H2. rewrite H2. auto.
Qed.

Lemma writable_writable_after_alloc' : forall m1 m2 lo hi b lev loc IOK1 IOK2,
  alloc m1 lo hi = (m2, b) ->
  writable loc (m_phi (initial_mem m1 lev IOK1)) ->
  writable loc (m_phi (initial_mem m2 lev IOK2)).
Proof.
intros.
hnf in *.
case_eq (m_phi (initial_mem m1 lev IOK1) @ loc); intros.
rewrite H1 in H0.
inv H0.
rewrite H1 in H0.
assert (~adr_range (b,lo) (hi-lo) loc).
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) loc).
  destruct loc. simpl in *.
  rewrite H1 in Ha.
  destruct H0 as [_ H0]. destruct H0. rewrite H0 in Ha. 
  intro Contra.
  destruct Contra.
  subst.
  assert (b0 = nextblock m1) by (eapply alloc_result; eauto).
  subst.
  destruct (perm_of_sh_pshare t p) as [p' H4].
  unfold perm_of_res in Ha. simpl in Ha. rewrite H4 in Ha.
  assert (access_at m1 (nextblock m1, z) = None).
    unfold access_at; apply nextblock_noaccess; simpl; omega.
  congruence.
apply alloc_dry_unchanged_on with (m1:=m1)(m2:=m2) in H2; auto.
destruct H2.
unfold initial_mem; simpl.
unfold inflate_initial_mem, inflate_initial_mem'.
rewrite resource_at_make_rmap.
destruct loc as (b',ofs').
assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) (b',ofs')).
  rewrite H1 in Ha.
  destruct H0 as [Hfree H0]. destruct H0. rewrite H0 in Ha. 
  unfold perm_of_res in Ha. simpl in Ha.
  destruct (perm_of_sh_pshare t pfullshare).
  subst.
  rewrite H4 in Ha. simpl in *.
  unfold perm_of_sh in H4.
  rewrite if_true in H4 by auto.
 if_tac in H4; inv H4. rewrite <- H2; rewrite Ha. split; eauto.
  rewrite <- H2; rewrite Ha. split; eauto.
 rewrite H1 in H0. simpl in H0. contradiction.
Qed.

Lemma readable_eq_after_alloc' : forall m1 m2 lo hi b lev loc IOK1 IOK2,
  alloc m1 lo hi = (m2, b) ->
  readable loc (m_phi (initial_mem m1 lev IOK1)) ->
  m_phi (initial_mem m1 lev IOK1) @ loc=m_phi (initial_mem m2 lev IOK2) @ loc.
Proof.
intros.
hnf in H0.
case_eq (m_phi (initial_mem m1 lev IOK1) @ loc); intros.
rewrite H1 in H0.
inv H0.
rewrite H1 in H0.
assert (~adr_range (b,lo) (hi-lo) loc).
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) loc).
  destruct loc. simpl in *.
  rewrite H1 in Ha.
  destruct H0. rewrite H0 in Ha. 
  intro Contra.
  destruct Contra.
  subst.
  assert (b0 = nextblock m1) by (eapply alloc_result; eauto).
  subst.
  destruct (perm_of_sh_pshare t p) as [p' H4].
  unfold perm_of_res in Ha; simpl in Ha; rewrite H4 in Ha.
  assert (access_at m1 (nextblock m1, z) = None).
    unfold access_at. simpl. apply nextblock_noaccess. omega.
  congruence.
apply alloc_dry_unchanged_on with (m1:=m1)(m2:=m2) in H2; auto.
destruct H2.
rewrite <- H1.
unfold initial_mem; simpl.
unfold inflate_initial_mem, inflate_initial_mem'.
do 2 rewrite resource_at_make_rmap.
destruct loc as (b',ofs').
assert (exists p, access_at m1 (b', ofs') = Some p).
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) (b',ofs')).
  rewrite H1 in Ha.
  destruct H0. rewrite H0 in Ha.   unfold perm_of_res in Ha; simpl in Ha.
  destruct (perm_of_sh_pshare t p).
  rewrite H4 in Ha. simpl in *.
  eexists; eauto.
assert (exists p, access_at m2 (b', ofs') = Some p).
  destruct H4. simpl in H2. rewrite H2 in H4 . eauto.
destruct H4 as [p1 H4].
destruct H5 as [p2 H5].
rewrite H4.
rewrite H5.
simpl in *.
rewrite H2 in H4. rewrite H5 in H4. inv H4.
rewrite H3; auto.
congruence.
rewrite H1 in *.
simpl in H0. contradiction.
Qed.


Lemma necR_m_dry:
  forall jm jm', necR jm jm' -> m_dry jm = m_dry jm'.
Proof.
intros.
induction H; auto.
unfold age in H.
apply age1_juicy_mem_unpack in H.
decompose [and] H; auto.
inv IHclos_refl_trans1.
inv IHclos_refl_trans2.
auto.
Qed.
