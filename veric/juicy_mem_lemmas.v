Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.
Require Import VST.veric.shares.

Definition juicy_mem_core (j: juicy_mem) : rmap := core (m_phi j).

(*Lemma inflate_initial_mem_empty:
  forall lev, emp (inflate_initial_mem Mem.empty lev).
intro lev.
unfold inflate_initial_mem.
destruct (make_rmap (inflate_initial_mem' Mem.empty lev) (core (ghost_of lev))
        (inflate_initial_mem'_valid Mem.empty lev) (level lev)
        (inflate_initial_mem'_fmap Mem.empty lev)); simpl.
{ rewrite core_ghost_of, <- level_core; apply ghost_of_approx. }
destruct a.
apply resource_at_empty2.
intro l; rewrite H0.
unfold inflate_initial_mem'.
destruct l.
unfold access_at; unfold empty at 1.
simpl.
rewrite PMap.gi.
destruct (max_access_at empty (b,z)); try destruct p; try apply NO_identity.
Qed.
Local Hint Resolve inflate_initial_mem_empty.*)

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
symmetry in H8;
destruct (H _ _ _ _ _ H8); auto.
Qed.

Lemma perm_of_sh_join_sub: forall (sh1 sh2: Share.t) p,
  perm_of_sh sh1 = Some p ->
  join_sub sh1 sh2 ->
  perm_order' (perm_of_sh sh2) p.
Proof.
intros.
destruct H0.
unfold perm_of_sh in *.
repeat if_tac in H; inv H.
+
inv H0. rewrite Share.glb_commute, Share.glb_top in H; subst x.
 rewrite (Share.lub_bot).
rewrite if_true by auto. rewrite if_true by auto. constructor.
+ apply join_writable1 in H0 ;auto. rewrite if_true by auto.
  if_tac; constructor.
+ apply join_readable1 in H0; auto.
  if_tac. if_tac; constructor. rewrite if_true by auto. constructor.
+ assert (sh2 <> Share.bot). contradict H3.
  apply split_identity in H0; auto. apply identity_share_bot; auto.
  subst; auto.
  repeat if_tac; try constructor. contradiction.
Qed.

Lemma perm_order'_trans: forall p1 p2 p3,
  perm_order' (Some p1) p2 -> perm_order' (Some p2) p3 -> perm_order' (Some p1) p3.
Proof.
intros.
unfold perm_order' in *.
eapply perm_order_trans; eauto.
Qed.

Lemma rmap_unage_YES: forall phi phi' sh rsh k pp loc, 
  age phi phi' 
  -> phi' @ loc = YES sh rsh k pp 
  -> exists pp', phi @ loc = YES sh rsh k pp'.
Proof.
intros.
unfold age in H.
case_eq (phi @ loc). intros.
cut (necR phi phi'). intro.
generalize (necR_NO phi phi' loc sh0 n H2). intro.
rewrite H3 in H1.
rewrite H1 in H0; inv H0.
constructor; auto.
intros.
exists p.
apply necR_YES with (phi' := phi') in H1.
rewrite H1 in H0.
inv H0. apply YES_ext; auto.
constructor; auto.
intros.
elimtype False.
eapply necR_PURE in H1.
2: constructor 1; eassumption.
congruence.
Qed.

Lemma preds_fmap_NoneP_approx: forall pp lev1 lev2,
  preds_fmap (approx lev1) (approx lev1) pp = NoneP ->
  preds_fmap (approx lev2) (approx lev2) pp = NoneP.
Proof.
intros.
destruct pp.
unfold NoneP, approx, compose in *.
simpl in *. unfold compose in *.
inv H. simpl in *.
apply EqdepFacts.eq_sigT_eq_dep in H2.
apply Eqdep.EqdepTheory.eq_dep_eq in H2.
auto.
Qed.

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
specialize ( Hacc (b, i)).
simpl in H.
destruct (m_phi jm @ (b, i)).
contradiction.
destruct H as [H1 H2]. destruct k; inv H2.
unfold access_at in Hacc.
simpl in Hacc.
rewrite Hacc.
clear - H1.
simpl.
unfold perm_of_sh. rewrite if_true by auto. if_tac; constructor.
contradiction.
Qed.

Lemma valid_access_None: forall m ch b b' ofs ofs' p,
  Mem.valid_access m ch b ofs p
  -> adr_range (b, ofs) (size_chunk ch) (b', ofs')
  -> access_at m (b', ofs') Cur = None
  -> False.
Proof.
unfold access_at, Mem.valid_access, Mem.perm, Mem.range_perm, Mem.perm, Mem.perm_order'.
simpl.
intros.
destruct H as [H ?].
destruct H0 as [H3 H4].
subst.
specialize( H ofs' H4).
rewrite H1 in H.
auto.
Qed.

Lemma core_load_getN: forall ch v b ofs bl phi m,
  contents_cohere m phi
  -> (core_load' ch (b, ofs) v bl)%pred phi
  -> bl = Mem.getN (size_chunk_nat ch) ofs (PMap.get b (Mem.mem_contents m)).
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
specialize ( H (b, ofs)).
cut (adr_range (b, ofs) z (b, ofs)); [intro H6|].
destruct (adr_range_dec (b, ofs) z (b, ofs)).
  2: elimtype False; auto.
simpl in H.
cut (nat_of_Z (ofs - ofs) = O); [intro H7|].
rewrite H7 in H.
destruct H as [sh [rsh H]].
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
specialize (H loc').
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
rewrite Pmult_nat_mult in H6.
rewrite mult_1_r in H6.
change (Pos.to_nat p) with (Z.to_nat (Z.pos p)) in H6.
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
  replace (Z.succ (Z_of_nat (S n)) - 1) with (Z_of_nat (S n)) by omega.
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
assert (forall z, Z.succ z - 1 = z) by (intros; omega).
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
specialize (H (b, ofs')).
hnf in H.
destruct (adr_range_dec (b, ofs) (size_chunk ch) (b, ofs')) as [H5|H5].
  2: unfold adr_range in H5.
  2: elimtype False; apply H5; split; auto.
destruct H as [sh [rsh H]].
simpl in H.
unfold access_cohere in H0.
specialize (H0 (b, ofs')).
unfold Mem.perm, Mem.perm_order'.
rewrite H in H0.
unfold access_at in H0.  simpl in H0.
destruct ((mem_access m) !! b ofs' Cur).
clear - H0 rsh.
unfold perm_of_sh in H0.
if_tac in H0.
if_tac in H0; inv H0; constructor.
rewrite if_true in H0. inv H0; constructor.
auto.
clear - rsh H0.
unfold perm_of_sh in H0.
repeat if_tac in H0; inv H0.
contradiction.
assumption.
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
  = nth (nat_of_Z (ofs' - ofs)) (Mem.getN (nat_of_Z z) ofs (PMap.get b (Mem.mem_contents m))) Undef.
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
  Mem.load ch (m_dry m) b ofs = Some v ->
  (forall z, ofs <= z < ofs + size_chunk ch ->
                      perm_order'' (perm_of_res (m_phi m @ (b,z))) (Some Readable)) ->
 core_load ch (b, ofs) v (m_phi m).
Proof.
intros until m; intros H PERM.
hnf.
unfold Mem.load in H.

if_tac in H; try solve [inv H].
inversion H.
clear H.
exists (Mem.getN (size_chunk_nat ch) ofs (PMap.get b (Mem.mem_contents (m_dry m)))).
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
pose proof I. (* pose proof (juicy_mem_access m).*)
pose proof I.
pose proof I.
clear H4. subst b'; clear H5.
destruct H as [_ ?].
specialize (PERM ofs' H).
(*
unfold access_cohere in H3.
specialize (H3 (b, ofs').
*)
unfold perm_of_res in *.
destruct H0 as [H0 _].
specialize (H0 ofs').
specialize (H0 H).
hnf in H0.
(*unfold access_at in H3.
simpl in H3.
*)
destruct ((mem_access (m_dry m)) !! b ofs' Cur); try contradiction.
destruct (m_phi m @ (b, ofs')) eqn:H8; try contradiction.
if_tac in PERM; inv PERM.
destruct k; try now inv PERM.
pose proof (size_chunk_pos ch).
rewrite <- nth_getN with (ofs := ofs) (z := size_chunk ch); auto; try omega.
exists sh, r.
destruct (H1 _ _ _ _ _ H8); subst.
f_equal.
inv PERM.
Qed.

Lemma core_load_load: forall ch b ofs v m,
  (forall z, ofs <= z < ofs + size_chunk ch ->
                      perm_order'' (perm_of_res (m_phi m @ (b,z))) (Some Readable)) ->
  (core_load ch (b, ofs) v (m_phi m) <-> Mem.load ch (m_dry m) b ofs = Some v).
Proof.
intros.
split; [apply core_load_load'| ].
intros; apply load_core_load; auto.
Qed.

(*Lemma address_mapsto_exists':
  forall ch v sh (rsh: readable_share sh) loc m lev,
      (align_chunk ch | snd loc)
      -> Mem.load ch m (fst loc) (snd loc) = Some v 
      -> exists w, address_mapsto ch v sh loc w /\ level w = lev.
Proof.
intros. rename H into Halign.
unfold address_mapsto.
pose (f l' := if adr_range_dec loc (size_chunk ch) l'
                     then YES sh rsh (VAL (nthbyte (snd l' - snd loc) (Mem.getN (size_chunk_nat ch) (snd loc) (PMap.get (fst loc) (Mem.mem_contents m))))) NoneP
                     else NO Share.bot bot_unreadable).
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
exists phi.
split; auto.
exists (Mem.getN (size_chunk_nat ch) (snd loc) (PMap.get (fst loc) (Mem.mem_contents m))).
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
exists rsh.
f_equal. 
apply NO_identity.
Qed.*)
    
Lemma mapsto_valid_access: forall ch v sh b ofs jm,
  (address_mapsto ch v sh (b, ofs) * TT)%pred (m_phi jm)
  -> Mem.valid_access (m_dry jm) ch b ofs Readable.
Proof.
intros.
unfold address_mapsto in H.
unfold Mem.valid_access, Mem.range_perm.
split.
destruct H as [x [y [Hjoin ?]]].
destruct H as [[bl [[[H2 [H3 H3']] H] Hg]] ?].
hnf in H.
intros ofs' H4.
specialize (H (b, ofs')).
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
clear - H7 sh'.
unfold perm, access_at in *.
simpl in H7.
forget ((mem_access (m_dry jm)) !! b ofs' Cur) as p1.
unfold perm_of_sh in H7.
if_tac in H7.
if_tac in H7; inv H7; constructor.
rewrite if_true in H7 by auto.
subst; constructor.
repeat match goal with [ H: context[ _ /\ _ ] |- _] => destruct H end.
auto.
Qed.

Lemma mapsto_valid_access_wr: forall ch v sh (wsh: writable_share sh) b ofs jm,
  (address_mapsto ch v sh (b, ofs) * TT)%pred (m_phi jm)
  -> Mem.valid_access (m_dry jm) ch b ofs Writable.
Proof.
intros.
unfold address_mapsto in H.
unfold Mem.valid_access, Mem.range_perm.
split.
destruct H as [x [y [Hjoin ?]]].
destruct H as [[bl [[[H2 [H3 H3']] H] Hg]] ?].
hnf in H.
intros ofs' H4.
specialize (H (b, ofs')).
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
assert (exists sh' (wsh': writable_share sh'), m_phi jm @ (b,ofs') = YES sh' (writable_readable_share wsh') (VAL v') NoneP).
inv H1; [ | contradiction (join_writable_readable RJ wsh rsh2)].
exists sh3, (join_writable1 RJ wsh).
apply YES_ext; auto.
destruct H6 as [sh' [wsh' ?]].
generalize (juicy_mem_access jm (b,ofs')); rewrite H6; unfold perm_of_res; simpl; intro.
clear - H7 wsh'.
unfold perm, access_at in *.
simpl in H7.
forget ((mem_access (m_dry jm)) !! b ofs' Cur) as p1.
unfold perm_of_sh in H7.
rewrite if_true in H7 by auto.
subst. if_tac; constructor.
repeat match goal with [ H: context[ _ /\ _ ] |- _] => destruct H end.
auto.
Qed.

Program Definition mapsto_can_store_definition ch v sh (wsh: writable_share sh) b ofs jm (v':val)
  (MAPSTO: (address_mapsto ch v sh (b, ofs) * TT)%pred (m_phi jm)):
  Memory.mem. 
Proof. intros.
pose proof (mapsto_valid_access_wr _ _ _ wsh _ _ _ MAPSTO).
apply (mkmem
  (PMap.set b (setN (encode_val ch v') ofs (PMap.get b (mem_contents (m_dry jm))))
    (mem_contents (m_dry jm))) (mem_access (m_dry jm))
  (nextblock (m_dry jm)) (access_max (m_dry jm)) (nextblock_noaccess (m_dry jm))).
intros. destruct jm; simpl.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Defined.

Lemma mapsto_can_store_property: forall (ch:memory_chunk) v sh (wsh: writable_share sh) b ofs jm v'
  (MAPSTO: (address_mapsto ch v sh (b, ofs) * TT)%pred (m_phi jm)),
  Mem.store ch (m_dry jm) b ofs v' = 
  Some(mapsto_can_store_definition _ _ _ wsh _ _ jm v' MAPSTO).
Proof.
intros.
pose proof (mapsto_valid_access_wr _ _ _ wsh _ _ _ MAPSTO).
unfold mapsto_can_store_definition. simpl.
Transparent Mem.store. unfold store.
destruct (valid_access_dec (m_dry jm) ch b ofs Writable).
f_equal. f_equal; auto with extensionality.
contradiction.
Opaque Mem.store.
Qed.

Lemma mapsto_can_store: forall ch v sh (wsh: writable_share sh) b ofs jm v',
  (address_mapsto ch v sh (b, ofs) * TT)%pred (m_phi jm)
  -> exists m', Mem.store ch (m_dry jm) b ofs v' = Some m'.
Proof.
intros.
exists (mapsto_can_store_definition _ _ _ wsh _ _ jm v' H).
apply mapsto_can_store_property.
Qed.

Lemma store_outside':
   forall ch m b z v m',
          Mem.store ch m b z v = Some m' ->
  (forall b' ofs,
    (b=b' /\ z <= ofs < z + size_chunk ch) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ access_at m = access_at m'
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
rewrite PMap.gss.
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
rewrite PMap.gso by auto. auto.
unfold access_at.  extensionality loc k.
f_equal.
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
case_eq (Z_lt_dec ofs hi); intros; auto.
omegaContradiction.
Qed.

Lemma join_top: forall sh2 sh, join Share.top sh2 sh -> sh = Share.top.
Proof.
intros. destruct H. rewrite Share.lub_commute, Share.lub_top in H0. auto.
Qed.

Lemma juicy_free_aux_lemma:
 forall phi b lo hi F,
 app_pred (VALspec_range (hi-lo) Share.top (b,lo) * F) phi ->
  (forall ofs : Z,
   lo <= ofs < hi -> perm_of_res (phi @ (b, ofs)) = Some Freeable).
Proof.
intros.
destruct H as [phi1 [phi2 [? [? ?]]]].
destruct H1 as [H1 _]; specialize (H1 (b,ofs)).
apply (resource_at_join _ _ _ (b,ofs)) in H.
hnf in H1. rewrite if_true in H1 by (split; auto; omega).
destruct H1 as [? [? ?]].
hnf in H1. rewrite H1 in H.
inv H. simpl.
clear - RJ.
apply join_top in RJ. subst. apply perm_of_freeable.
simpl.
apply join_top in RJ. subst. apply perm_of_freeable.
Qed.

Lemma juicy_free_lemma:
  forall {j b lo hi m' m1 F}
    (H: Mem.free (m_dry j) b lo hi = Some m')
    (VR: app_pred (VALspec_range (hi-lo) Share.top (b,lo) * F) (m_phi j)),
    VALspec_range (hi-lo) Share.top (b,lo) m1 ->
    core m1 = core (m_phi j) ->
    (forall l sh rsh k pp, m1 @ l = YES sh rsh k pp 
      -> exists sh', exists (rsh': readable_share sh'), 
            exists pp', join_sub sh sh' 
              /\ m_phi j @ l = YES sh' rsh' k pp') -> 
    join m1 (m_phi (free_juicy_mem _ _ _ _ _ H)) (m_phi j).
Proof.
intros j b lo hi m' m1.
pose (H0 :=True).
intros R H VR H1 H2 Hyes.
assert (forall l, ~adr_range (b,lo) (hi-lo) l -> identity (m1 @ l)).
  unfold VALspec_range, allp, jam in H1.
  intros l. destruct H1 as [H1 _]; specialize (H1 l). intros H3.
  hnf in H1; if_tac in H1; try solve [contradiction].
  apply H1.
assert (forall l, adr_range (b,lo) (hi-lo) l 
  -> exists mv, yesat NoneP (VAL mv) Share.top  l m1).
  unfold VALspec_range, allp, jam in H1.
  intros l. destruct H1 as [H1 _]; specialize (H1 l). intros H4.
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
destruct (adr_range_dec (b,lo) (hi-lo) (b0,ofs0)).
* (* adr_range *)
clear H3.
specialize (H4 (b0,ofs0) a).
destruct H4 as [mv H4].
unfold yesat, yesat_raw in H4. destruct H4 as [pp H4].
simpl in H4.
rewrite H4.
clear H0.
assert (H0 : access_at m' (b0, ofs0) Cur = None).
  clear - H a.
  Transparent free.
  unfold free in H.
  if_tac in H; try solve [congruence].
  unfold unchecked_free in H. inv H. simpl.
  assert (b = b0) by (destruct a; auto). subst.
  unfold access_at; simpl. rewrite PMap.gss.
  rewrite adr_range_zle_zlt with (b:=b0); auto.
specialize (Ha (b0,ofs0)). rewrite <- H5 in Ha.
rewrite H0 in Ha.
assert (H3 : m_phi j @ (b0, ofs0) = YES Share.top readable_share_top (VAL mv) NoneP). {
  clear - H H4 a Hyes.
  assert (Ha := juicy_mem_access j (b0,ofs0)).
  generalize (Hyes _ _ _ _ _ H4); intros.
  repeat rewrite preds_fmap_NoneP in *. 
  destruct H0 as [sh' [rsh' [? [RJ ?]]]]. 
  rewrite H0. repeat f_equal.
  destruct RJ as [? RJ]; apply join_top in RJ. subst sh'.
  pose proof (juicy_mem_contents j). 
  destruct (H1 _ _ _ _ _ H0); auto. subst. apply YES_ext; auto.
 }
rewrite H3. repeat rewrite preds_fmap_NoneP. unfold pfullshare.
apply join_unit2. constructor. apply join_unit1; auto.
f_equal. apply proof_irr.
* (* ~adr_range *)
  clear H0.
  generalize (H3 _ n); intro H3'.
  assert (core (m1 @ (b0,ofs0)) = core (m_phi j @ (b0,ofs0))).
  do 2 rewrite core_resource_at. unfold Join_rmap in *.  unfold Sep_rmap in  *; congruence.
  apply identity_resource in H3'.
  revert H3'; case_eq (m1 @ (b0,ofs0));intros; try contradiction; try constructor.
  + apply identity_share_bot in H3'; subst sh.
    rename H6 into Hm1.
    clear H0.
    destruct (free_nadr_range_eq _ _ _ _ _ _ _ n H) as [H0 H10].
    (* rewrite <- H0 in *; clear H0.*)
    assert (Ha0 := juicy_mem_access j (b0,ofs0)).
    revert Ha0;
      case_eq (m_phi j @ (b0,ofs0)); intros.
    constructor. apply join_unit1; auto.
    constructor. apply join_unit1; auto.

    elimtype False.
    clear - H2 Hm1 H0 H6.
    assert (core (m1 @ (b0,ofs0)) = core (m_phi j @ (b0,ofs0))).
    do 2 rewrite core_resource_at.  unfold Join_rmap in *;  unfold Sep_rmap in  *; congruence.
    rewrite Hm1 in H. rewrite H6 in H.
    rewrite core_PURE in H. rewrite core_NO in H; inv H.
  + rewrite H6 in H0. rewrite core_PURE in H0.
    destruct (m_phi j @ (b0,ofs0)).
    rewrite core_NO in H0; inv H0. rewrite core_YES in H0; inv H0.
    rewrite core_PURE in H0. inversion H0. subst k0 p0; constructor.
* destruct H1 as [_ Hg].
  rewrite (identity_core Hg), core_ghost_of, H2.
  subst j'; simpl.
  unfold inflate_free.
  rewrite ghost_of_make_rmap.
  rewrite <- core_ghost_of; apply core_unit.
Qed.

Section free.

Variables (jm :juicy_mem) (m': mem)
          (b: block) (lo hi: Z)
          (FREE: free (m_dry jm) b lo hi = Some m')
          (PERM: forall ofs, lo <= ofs < hi ->
                      perm_of_res (m_phi jm @ (b,ofs)) = Some Freeable)
          (phi1 phi2 : rmap) (Hphi1: VALspec_range (hi-lo) Share.top (b,lo) phi1)
          (Hjoin : join phi1 phi2 (m_phi jm)).

Lemma phi2_eq : m_phi (free_juicy_mem _ _ _ _ _ FREE) = phi2.
Proof.
  apply rmap_ext; simpl; unfold inflate_free; rewrite ?level_make_rmap, ?resource_at_make_rmap.
  - apply join_level in Hjoin; destruct Hjoin; auto.
  - intro.
    destruct Hphi1 as [Hphi1' _]. specialize (Hphi1' l); simpl in Hphi1'.
    apply (resource_at_join _ _ _ l) in Hjoin.
    if_tac.
    + destruct Hphi1' as (? & ? & H1); rewrite H1 in Hjoin; inv Hjoin.
      * pose proof (join_top _ _ RJ); subst; apply sepalg.join_comm, unit_identity, identity_share_bot in RJ.
        subst; apply f_equal, proof_irr.
      * pose proof (join_top _ _ RJ); subst; apply sepalg.join_comm, unit_identity, identity_share_bot in RJ.
        subst; contradiction bot_unreadable.
    + apply Hphi1' in Hjoin; auto.
  - rewrite ghost_of_make_rmap.
    destruct Hphi1 as [_ Hg].
    apply ghost_of_join in Hjoin.
    symmetry; apply Hg; auto.
Qed.

End free.

Lemma juicy_free_lemma':
  forall {j b lo hi m' m1 m2 F}
    (H: Mem.free (m_dry j) b lo hi = Some m')
    (VR: app_pred (VALspec_range (hi-lo) Share.top (b,lo) * F) (m_phi j)),
    VALspec_range (hi-lo) Share.top (b,lo) m1 ->
    join m1 m2 (m_phi j) ->
    m_phi (free_juicy_mem _ _ _ _ _ H) = m2.
Proof.
  intros.
  eapply phi2_eq; eauto.
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
destruct (access_at m loc); try destruct p0; try rewrite core_NO;  repeat rewrite core_YES; auto.
destruct H1.
destruct H2. rewrite H2. auto.
unfold inflate_initial_mem.
rewrite <- core_ghost_of, ghost_of_make_rmap, core_ghost_of; auto.
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
assert (~adr_range (b,lo) (hi-lo) loc). {
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) loc).
  destruct loc. simpl in *.
  rewrite H1 in Ha.
  destruct H0 as [_ H0]. destruct k; inv H0.
  intro Contra.
  destruct Contra.
  subst.
  assert (access_at m1 (nextblock m1, z) Cur = None).
    unfold access_at; apply nextblock_noaccess; simpl; xomega.
  assert (b0 = nextblock m1) by (eapply alloc_result; eauto).
  subst.
  rewrite Ha in H0. simpl in H0. clear - r H0.
  unfold perm_of_sh in H0. repeat if_tac in H0; try contradiction; inv H0.
}
apply alloc_dry_unchanged_on with (m1:=m1)(m2:=m2) in H2; auto.
destruct H2.
unfold initial_mem; simpl.
unfold inflate_initial_mem, inflate_initial_mem'.
rewrite resource_at_make_rmap.
destruct loc as (b',ofs').
assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) (b',ofs')). {
  rewrite H1 in Ha.
  destruct H0 as [Hfree H0]. destruct k; try solve [inversion H0].
  unfold perm_of_res in Ha. simpl in Ha.
  rewrite <- H3.
  rewrite <- H2. rewrite Ha.
  clear - Hfree r.
  unfold perm_of_sh. rewrite if_true by auto. if_tac; auto.
  rewrite Ha. unfold perm_of_sh. rewrite if_true by auto. 
  clear; if_tac; congruence.
 }
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
assert (~adr_range (b,lo) (hi-lo) loc). {
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) loc).
  destruct loc. simpl in *.
  rewrite H1 in Ha.
  destruct k; try solve [inv H0].
  intro Contra.
  destruct Contra.
  subst.
  assert (b0 = nextblock m1) by (eapply alloc_result; eauto).
  subst.
  simpl in Ha.
(*
  destruct (perm_of_sh_pshare t p) as [p' H4].
  unfold perm_of_res in Ha; simpl in Ha; rewrite H4 in Ha.
*)
  assert (access_at m1 (nextblock m1, z) Cur = None).
    unfold access_at. simpl. apply nextblock_noaccess. xomega.
  rewrite H2 in Ha.
  clear - Ha r. unfold perm_of_sh in Ha. repeat if_tac in Ha; inv Ha; try contradiction.
}
apply alloc_dry_unchanged_on with (m1:=m1)(m2:=m2) in H2; auto.
destruct H2.
rewrite <- H1.
unfold initial_mem; simpl.
unfold inflate_initial_mem, inflate_initial_mem'.
do 2 rewrite resource_at_make_rmap.
destruct loc as (b',ofs').
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) (b',ofs')). {
   rewrite H1 in Ha.   unfold perm_of_res in Ha; simpl in Ha.
   simpl in H0. destruct k; try contradiction.
  rewrite <- H2. rewrite Ha in *.
  spec H3. clear - r. unfold perm_of_sh. repeat if_tac; try congruence; contradiction.
  rewrite <- H3.
  unfold perm_of_sh. if_tac. if_tac; auto. rewrite if_true by auto. auto.

 }
 rewrite H1 in H0. contradiction.
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

Lemma perm_order''_trans p1 p2 p3 :
  perm_order'' p1 p2 ->
  perm_order'' p2 p3 ->
  perm_order'' p1 p3.
Proof.
  destruct p1, p2, p3; simpl; try tauto.
  apply perm_order_trans.
Qed.

Lemma po_join_sub_sh sh1 sh2 :
  join_sub sh2 sh1 ->
  Mem.perm_order'' (perm_of_sh sh1) (perm_of_sh sh2).
Proof.
  intros [sh J].
  unfold perm_of_sh.
  if_tac. if_tac. repeat if_tac; constructor.
  if_tac. rewrite if_false. constructor.
  contradict H0. subst. apply join_top in J; auto.
  repeat if_tac; constructor.
  assert (~writable_share sh2) by (contradict H; eapply join_writable1; eauto).
  if_tac. rewrite if_false by auto. repeat if_tac; constructor.
  rewrite (if_false (writable_share sh2)) by auto.
  assert (~readable_share sh2) by (contradict H1; eapply join_readable1; eauto).
  rewrite (if_false (readable_share sh2)) by auto.
  if_tac.
  subst. apply split_identity in J. apply identity_share_bot in J.
  rewrite if_true by auto. constructor.
  auto. if_tac; constructor.
Qed.

Lemma po_join_sub r1 r2 :
  join_sub r2 r1 ->
  Mem.perm_order'' (perm_of_res r1) (perm_of_res r2).
Proof.
  intros. destruct H as [r J]. inv J; simpl.
  if_tac. subst. apply split_identity in RJ.
  apply identity_share_bot in RJ. rewrite if_true by auto; constructor.
  auto. if_tac; constructor.
  destruct k; try constructor; apply po_join_sub_sh; eexists; eauto.
  apply perm_order''_trans with (Some Nonempty).
  destruct k; try constructor.
  unfold perm_of_sh. if_tac. if_tac; constructor. rewrite if_true by auto; constructor.
  if_tac; constructor.
  destruct k; try constructor. apply po_join_sub_sh; eexists; eauto.
  constructor.
Qed.

(*
Lemma po_join_sub' r1 r2 :
  join_sub r2 r1 ->
  Mem.perm_order'' (perm_of_res' r1) (perm_of_res' r2).
Proof.
  
*)
Lemma perm_of_res_lock_not_Freeable:
  forall r,
    Mem.perm_order'' (Some Writable) (perm_of_res_lock r).
Proof.
  intros.
  unfold perm_of_res_lock.
  destruct r; try constructor.
  destruct k; try constructor.
  unfold perm_of_sh.
  if_tac. rewrite if_false. constructor.
  apply glb_Rsh_not_top.
  repeat if_tac; constructor.
Qed.
