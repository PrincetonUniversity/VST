Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.

Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.

Require Export VST.veric.initial_world.
Import compcert.lib.Maps.

Import Clight.

Local Open Scope pred.

Obligation Tactic := idtac.

Notation initial_core' := (initial_core' function).

(* This version starts with an empty ghost. 
Program Definition initial_core (ge: Genv.t fundef type) (G: funspecs) (n: nat): rmap :=
  proj1_sig (make_rmap (initial_core' ge G n) nil n _ eq_refl).
Next Obligation.
intros.
extensionality loc; unfold compose, initial_core'.
if_tac; [ | simpl; auto].
destruct (Genv.invert_symbol ge (fst loc)); [ | simpl; auto].
destruct (find_id i G); [ | simpl; auto].
destruct f.
unfold resource_fmap.
f_equal.
simpl.
f_equal.
change R.approx with approx.
extensionality i0 ts b rho.
rewrite fmap_app.
pattern (approx n) at 7 8 9.
rewrite <- approx_oo_approx.
auto.
Qed.*)
Notation initial_core := (@initial_core function).

Notation initial_core_ext := (@initial_core_ext  function).

Notation prog_funct := (@prog_funct function).

Inductive match_fdecs: list  (ident * Clight.fundef) -> funspecs -> Prop :=
| match_fdecs_nil: match_fdecs nil nil
| match_fdecs_cons: forall i fd fspec fs G,
                  type_of_fundef fd = type_of_funspec fspec ->
                  match_fdecs fs G ->
                  match_fdecs ((i,fd)::fs) ((i,fspec)::G)
(* EXPERIMENT
| match_fdecs_skip: forall ifd fs G,
                 match_fdecs fs G ->
                 match_fdecs (ifd::fs) G*)
.

Lemma match_fdecs_exists_Gfun:
  forall prog G i f,
    find_id i G = Some f ->
    match_fdecs (prog_funct prog) G ->
    exists fd,   In (i, Gfun fd) (prog_defs prog) /\
                     type_of_fundef fd = type_of_funspec f.
Proof. unfold prog_funct. unfold prog_defs_names.
intros ? ? ? ?.
forget (prog_defs prog) as dl.
revert G; induction dl; simpl; intros.
inv H0. inv H.
destruct a as [i' [?|?]].
inv H0.
simpl in H; if_tac in H. subst i'; inv H.
eauto.
destruct (IHdl G0) as [fd [? ?]]; auto.
exists fd; split; auto.
destruct (IHdl G) as [fd [? ?]]; auto.
exists fd; split; auto.
(* EXPERIMENT
destruct (IHdl G) as [fd [? ?]]; auto.
exists fd; split; auto.
*)
Qed.

Lemma initial_core_ok: forall (prog: program) G n m,
      list_norepet (prog_defs_names prog) ->
      match_fdecs (prog_funct prog) G ->
      Genv.init_mem prog = Some m ->
     initial_rmap_ok m (initial_core (Genv.globalenv prog) G n).
Proof.
intros.
rename H1 into Hm.
intros [b z]. simpl.
unfold initial_core; simpl.
rewrite <- core_resource_at.
rewrite resource_at_make_rmap.
unfold initial_core'.
simpl in *.
change fcore with (@core _ _ (fsep_sep Sep_resource)).
if_tac; [ | rewrite core_NO; auto].
case_eq (@Genv.invert_symbol (Ctypes.fundef function) type
       (@Genv.globalenv (Ctypes.fundef function) type prog) b);
   intros;  try now (rewrite core_NO; auto).
case_eq (find_id i G); intros; [ | rewrite core_NO; auto].
apply Genv.invert_find_symbol in H2.
pose proof (Genv.find_symbol_not_fresh _ _ Hm H2).
unfold valid_block in H4.
split; intros.
contradiction.
destruct (match_fdecs_exists_Gfun _ _ _ _ H3 H0) as [fd [? _]].
destruct f.
split; auto.
subst z.
destruct (find_symbol_globalenv _ _ _ H H2) as [RANGE [d ?]].
assert (d = Gfun fd). {
  clear - H H5 H1.
  unfold prog_defs_names in H.
  change (AST.prog_defs prog) with (prog_defs prog) in H.
  forget (prog_defs prog) as dl. forget (Z.to_nat (Z.pos b-1)) as n.
  revert dl H H5 H1; induction n; simpl; intros.
  destruct dl; inv H1.
  inv H. simpl in H5.
  destruct H5. inv H; auto.
  apply (in_map (@fst ident (globdef fundef type))) in H. simpl in H;  contradiction.
  destruct dl; inv H1. inv H.
  simpl in H5. destruct H5. subst.
  clear - H2 H3. apply nth_error_in in H2.
  apply (in_map (@fst ident (globdef fundef type))) in H2. simpl in *;  contradiction.
  apply (IHn dl); auto.
} (* end assert d = Gfun fd *)
subst d.
clear H5.
clear - RANGE H2 H1 H Hm.
unfold Genv.init_mem in Hm.
forget (Genv.globalenv prog) as ge.
change (AST.prog_defs prog) with (prog_defs prog) in Hm.
forget (prog_defs prog) as dl.
rewrite <- (rev_involutive dl) in H1,Hm.
rewrite nth_error_rev in H1.
2 : { rewrite rev_length. clear - RANGE.
      destruct RANGE.
      apply inj_lt_iff. rewrite Z2Nat.id by lia. lia. }
rename H1 into H5.
replace (length (rev dl) - Z.to_nat (Z.pos b - 1) - 1)%nat
 with (length (rev dl) - Z.to_nat (Z.pos b))%nat in H5.
2 : { rewrite rev_length.
      clear - RANGE.
      replace (Z.to_nat (Z.pos b-1)) with (Z.to_nat (Z.pos b) - 1)%nat.
      assert (Z.to_nat (Z.pos b) <= length dl)%nat.
      destruct RANGE.
      apply inj_le_iff. rewrite Z2Nat.id by lia. auto.
      assert (Z.to_nat (Z.pos b) > 0)%nat. apply inj_gt_iff.
      rewrite Z2Nat.id by lia.  simpl. lia.
      lia. destruct RANGE as [? _].
      apply nat_of_Z_lem1.
      assert (Z.to_nat (Z.pos b) > 0)%nat. apply inj_gt_iff. simpl.
      pose proof (Pos2Nat.is_pos b); lia.
      lia. }
assert (0 < Z.to_nat (Z.pos b) <= length dl)%nat.
{ clear - RANGE. lia. }
clear RANGE; rename H0 into RANGE.
rewrite Z2Nat.inj_pos in *.
rewrite <- rev_length in RANGE.
forget (rev dl) as dl'; clear dl; rename dl' into dl.
destruct RANGE.
rewrite alloc_globals_rev_eq in Hm.
revert m Hm H1 H5; induction dl; intros.
inv H5.
simpl in H1,Hm.
invSome.
specialize (IHdl _ Hm).
destruct (eq_dec (Pos.to_nat b) (S (length dl))).
+ rewrite e, Nat.sub_diag in H5. simpl in H5.
  inversion H5; clear H5; subst a.
  apply alloc_globals_rev_nextblock in Hm.
  rewrite Zlength_correct in Hm.
  rewrite <- inj_S in Hm. rewrite <- e in Hm.
  rewrite positive_nat_Z in Hm.  rewrite Pos2Z.id in Hm.
  subst b.
  clear IHdl H1 H0. clear dl e.
  unfold Genv.alloc_global in H6.
  revert H6; case_eq (alloc m0 0 1); intros.
  unfold drop_perm in H6.
  destruct (range_perm_dec m1 b 0 1 Cur Freeable).
  unfold max_access_at, access_at; inv H6.
  simpl. apply alloc_result in H0. subst b.
  rewrite PMap.gss.
  simpl. auto.
  inv H6.
+ destruct IHdl.
  lia.
  replace (length (a::dl) - Pos.to_nat b)%nat with (S (length dl - Pos.to_nat b))%nat in H5.
  apply H5.
  simpl. destruct (Pos.to_nat b); lia.
  assert (b < nextblock m0)%positive.
  apply alloc_globals_rev_nextblock in Hm.
  rewrite Zlength_correct in Hm. clear - Hm n H1.
  rewrite Hm.
  apply Pos2Nat.inj_lt.
  pattern Pos.to_nat at 1; rewrite <- Z2Nat.inj_pos.
  rewrite Z2Pos.id by lia.
  rewrite Z2Nat.inj_succ by lia.
  rewrite Nat2Z.id. lia.
  destruct (alloc_global_old _ _ _ _ H6 (b,0)) as [? ?]; auto.
  unfold max_access_at.
  rewrite <- H8.
  split; auto.
Qed.

Definition initial_jm (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G) : juicy_mem :=
  initial_mem m (initial_core (Genv.globalenv prog) G n)
           (initial_core_ok _ _ _ m H1 H2 H).

Lemma initial_jm_age (prog: program) m (G: funspecs) (n : nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G) :
age
    (initial_mem m (initial_core (Genv.globalenv prog) G (S n)) (initial_core_ok _ _ _ m H1 H2 H))
    (initial_mem m (initial_core (Genv.globalenv prog) G    n ) (initial_core_ok _ _ _ m H1 H2 H)).
Proof.
apply age1_juicy_mem_unpack''; [ | reflexivity].
simpl.
unfold inflate_initial_mem in *.
match goal with |- context [ proj1_sig ?x ] => destruct x as (r & lev & bah & Hg1); simpl end.
match goal with |- context [ proj1_sig ?x ] => destruct x as (r' & lev' & bah' & Hg2); simpl end.
apply rmap_age_i.
rewrite lev,lev'.
unfold initial_core; simpl.
rewrite !level_make_rmap. auto.
intro loc.
rewrite bah, bah'.
unfold inflate_initial_mem'.
destruct (access_at m loc Cur); [ | reflexivity].
destruct p; unfold resource_fmap; f_equal; try apply preds_fmap_NoneP.
unfold initial_core.
rewrite !resource_at_make_rmap.
unfold initial_core'.
if_tac; auto.
unfold fundef.
destruct (Genv.invert_symbol (Genv.globalenv (program_of_program prog))
        (fst loc)); auto.
destruct (find_id i G); auto.
destruct f; auto.
f_equal.
simpl.
f_equal.
rewrite lev'.
unfold initial_core.
rewrite level_make_rmap.
extensionality ts x b rho.
rewrite fmap_app.
match goal with
| |- ?A (?B ?C) = _ => change (A (B C)) with ((A oo B) C)
end.
rewrite approx_oo_approx' by lia.
rewrite approx'_oo_approx by lia.
auto.
rewrite Hg1, Hg2.
unfold initial_core; rewrite !ghost_of_make_rmap; auto.
Qed.

Lemma initial_core_ext_ok: forall {Z} (ora : Z) (prog: program) G n m,
      list_norepet (prog_defs_names prog) ->
      match_fdecs (prog_funct prog) G ->
      Genv.init_mem prog = Some m ->
     initial_rmap_ok m (initial_core_ext ora (Genv.globalenv prog) G n).
Proof.
intros.
rename H1 into Hm.
intros [b z]. simpl.
unfold initial_core_ext; simpl.
rewrite <- core_resource_at.
rewrite resource_at_make_rmap.
unfold initial_core'.
simpl in *.
change fcore with (@core _ _ (fsep_sep Sep_resource)).
if_tac; [ | rewrite core_NO; auto].
case_eq (@Genv.invert_symbol (Ctypes.fundef function) type (@Genv.globalenv (Ctypes.fundef function) type prog) b);
   intros;  try now (rewrite core_NO; auto).
case_eq (find_id i G); intros; [ | rewrite core_NO; auto].
apply Genv.invert_find_symbol in H2.
pose proof (Genv.find_symbol_not_fresh _ _ Hm H2).
unfold valid_block in H4.
split; intros.
contradiction.
destruct (match_fdecs_exists_Gfun _ _ _ _ H3 H0) as [fd [? _]].
destruct f.
split; auto.
subst z.
destruct (find_symbol_globalenv _ _ _ H H2) as [RANGE [d ?]].
assert (d = Gfun fd).
clear - H H5 H1.
unfold prog_defs_names in H.
change (AST.prog_defs prog) with (prog_defs prog) in H.
forget (prog_defs prog) as dl. forget (Z.to_nat (Z.pos b-1)) as n.
revert dl H H5 H1; induction n; simpl; intros.
destruct dl; inv H1.
inv H. simpl in H5.
destruct H5. inv H; auto.
apply (in_map (@fst ident (globdef fundef type))) in H. simpl in H;  contradiction.
destruct dl; inv H1. inv H.
simpl in H5. destruct H5. subst.
clear - H2 H3. apply nth_error_in in H2.
apply (in_map (@fst ident (globdef fundef type))) in H2. simpl in *;  contradiction.
apply (IHn dl); auto.
(* end assert d = Gfun fd *)
subst d.
clear H5.
clear - RANGE H2 H1 H Hm.
unfold Genv.init_mem in Hm.
forget (Genv.globalenv prog) as ge.
change (AST.prog_defs prog) with (prog_defs prog) in Hm.
forget (prog_defs prog) as dl.
rewrite <- (rev_involutive dl) in H1,Hm.
rewrite nth_error_rev in H1.
2 : {
  rewrite rev_length. clear - RANGE.
  destruct RANGE.
  apply inj_lt_iff. rewrite Z2Nat.id by lia. lia. }
rename H1 into H5.
replace (length (rev dl) - Z.to_nat (Z.pos b - 1) - 1)%nat
  with (length (rev dl) - Z.to_nat (Z.pos b))%nat in H5.
2 : { rewrite rev_length.
  clear - RANGE.
  replace (Z.to_nat (Z.pos b-1)) with (Z.to_nat (Z.pos b) - 1)%nat.
  assert (Z.to_nat (Z.pos b) <= length dl)%nat.
  destruct RANGE.
  apply inj_le_iff. rewrite Z2Nat.id by lia. auto.
  assert (Z.to_nat (Z.pos b) > 0)%nat. apply inj_gt_iff.
  rewrite Z2Nat.id by lia.  simpl. lia.
  lia. destruct RANGE as [? _].
  apply nat_of_Z_lem1.
  assert (Z.to_nat (Z.pos b) > 0)%nat. apply inj_gt_iff. simpl.
  pose proof (Pos2Nat.is_pos b); lia.
  lia. }
assert (0 < Z.to_nat (Z.pos b) <= length dl)%nat.
{ clear - RANGE. lia. }
clear RANGE; rename H0 into RANGE.
rewrite Z2Nat.inj_pos in *.
rewrite <- rev_length in RANGE.
forget (rev dl) as dl'; clear dl; rename dl' into dl.
destruct RANGE.
rewrite alloc_globals_rev_eq in Hm.
revert m Hm H1 H5; induction dl; intros.
inv H5.
simpl in H1,Hm.
invSome.
specialize (IHdl _ Hm).
destruct (eq_dec (Pos.to_nat b) (S (length dl))).
+ rewrite e, Nat.sub_diag in H5. simpl in H5.
  inversion H5; clear H5; subst a.
  apply alloc_globals_rev_nextblock in Hm.
  rewrite Zlength_correct in Hm.
  rewrite <- inj_S in Hm. rewrite <- e in Hm.
  rewrite positive_nat_Z in Hm.  rewrite Pos2Z.id in Hm.
  subst b.
  clear IHdl H1 H0. clear dl e.
  unfold Genv.alloc_global in H6.
  revert H6; case_eq (alloc m0 0 1); intros.
  unfold drop_perm in H6.
  destruct (range_perm_dec m1 b 0 1 Cur Freeable).
  unfold max_access_at, access_at; inv H6.
  simpl. apply alloc_result in H0. subst b.
  rewrite PMap.gss.
  simpl. auto.
  inv H6.
+ destruct IHdl.
  lia.
  replace (length (a::dl) - Pos.to_nat b)%nat with (S (length dl - Pos.to_nat b))%nat in H5.
  apply H5.
  simpl. destruct (Pos.to_nat b); lia.
  assert (b < nextblock m0)%positive.
  { apply alloc_globals_rev_nextblock in Hm.
    rewrite Zlength_correct in Hm. clear - Hm n H1.
    rewrite Hm.
    apply Pos2Nat.inj_lt.
    pattern Pos.to_nat at 1; rewrite <- Z2Nat.inj_pos.
    rewrite Z2Pos.id by lia.
    rewrite Z2Nat.inj_succ by lia.
    rewrite Nat2Z.id. lia. }
  destruct (alloc_global_old _ _ _ _ H6 (b,0)) as [? ?]; auto.
  unfold max_access_at.
  rewrite <- H8.
  split; auto.
Qed.

Definition initial_jm_ext {Z} (ora : Z) (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G) : juicy_mem :=
  initial_mem m (initial_core_ext ora (Genv.globalenv prog) G n)
           (initial_core_ext_ok _ _ _ _ m H1 H2 H).

Require Import VST.veric.ghost_PCM.

Import Clight.

Lemma initial_jm_ext_eq : forall {Z} (ora : Z) (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G),
  join (m_phi (initial_jm prog m G n H H1 H2))
       (set_ghost (core (m_phi (initial_jm prog m G n H H1 H2))) (Some (ext_ghost ora, NoneP) :: nil) eq_refl)
       (m_phi (initial_jm_ext ora prog m G n H H1 H2)).
Proof.
  intros.
  apply resource_at_join2.
  - simpl.
    rewrite !inflate_initial_mem_level.
    unfold initial_core, initial_core_ext; rewrite !level_make_rmap; auto.
  - unfold set_ghost; rewrite level_make_rmap.
    rewrite level_core.
    simpl.
    rewrite !inflate_initial_mem_level.
    unfold initial_core, initial_core_ext; rewrite !level_make_rmap; auto.
  - intros.
    unfold set_ghost; rewrite resource_at_make_rmap, <- core_resource_at.
    simpl.
    unfold initial_core, initial_core_ext, inflate_initial_mem.
    rewrite !resource_at_make_rmap.
    unfold inflate_initial_mem'.
    rewrite !resource_at_make_rmap.
    change fcore with (@core _ _ (fsep_sep Sep_resource)).
    apply join_comm, core_unit.
  - unfold set_ghost; rewrite ghost_of_make_rmap.
    simpl.
    unfold initial_core, initial_core_ext, inflate_initial_mem.
    rewrite !ghost_of_make_rmap.
    constructor.
Qed.

Lemma initial_jm_wsat : forall {Z} (ora : Z) (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G),
  exists z, join (m_phi (initial_jm_ext ora prog m G n H H1 H2)) (wsat_rmap (m_phi (initial_jm_ext ora prog m G n H H1 H2))) (m_phi z) /\
    ext_order (initial_jm_ext ora prog m G n H H1 H2) z.
Proof.
  intros.
  destruct (make_rmap _ (Some (ext_ghost ora, NoneP) :: tl wsat_ghost) (level (initial_core_ext ora (Genv.globalenv prog) G n))
    (inflate_initial_mem'_fmap m _)) as (z & Hl & Hr & Hg); auto.
  destruct (juicy_mem_resource (initial_jm_ext ora prog m G n H H1 H2) z) as (jz & ? & ?); unfold initial_jm_ext; simpl; subst.
  { rewrite Hr. unfold inflate_initial_mem; rewrite resource_at_make_rmap. auto. }
  exists jz; split. apply resource_at_join2; rewrite ?inflate_initial_mem_level, ?Hl, ?Hr, ?Hg; auto.
  - unfold wsat_rmap; rewrite level_make_rmap, inflate_initial_mem_level; auto.
  - intros; unfold inflate_initial_mem, wsat_rmap; rewrite !resource_at_make_rmap.
    rewrite <- core_resource_at, resource_at_make_rmap.
    apply join_comm, core_unit.
  - unfold inflate_initial_mem, wsat_rmap; rewrite !ghost_of_make_rmap.
    unfold initial_core_ext; rewrite ghost_of_make_rmap.
    repeat constructor.
  - split; auto. apply rmap_order.
    rewrite Hl, Hr, Hg.
    unfold inflate_initial_mem; rewrite level_make_rmap, resource_at_make_rmap, ghost_of_make_rmap.
    split; auto; split; auto.
    unfold initial_core_ext; rewrite ghost_of_make_rmap.
    eexists; repeat constructor.
Qed.

Notation prog_vars := (@prog_vars function).

Lemma initial_jm_without_locks prog m G n H H1 H2:
  no_locks (m_phi (initial_jm prog m G n H H1 H2)).
Proof.
  simpl.
  unfold inflate_initial_mem; simpl.
  match goal with |- context [ proj1_sig ?a ] => destruct a as (phi & lev & E & ?) end; simpl.
  unfold inflate_initial_mem' in E.
  unfold resource_at in E.
  unfold no_locks, "@"; intros.
  rewrite E.
  destruct (access_at m addr); [ |congruence].
  destruct p; try congruence.
  destruct (fst ((snd (unsquash (initial_core (Genv.globalenv prog) G n)))) addr);
  congruence.
Qed.

Lemma initial_jm_ext_without_locks {Z} (ora : Z) prog m G n H H1 H2:
  no_locks (m_phi (initial_jm_ext ora prog m G n H H1 H2)).
Proof.
  simpl.
  unfold inflate_initial_mem; simpl.
  match goal with |- context [ proj1_sig ?a ] => destruct a as (phi & lev & E & ?) end; simpl.
  unfold inflate_initial_mem' in E.
  unfold resource_at in E.
  unfold no_locks, "@"; intros.
  rewrite E.
  destruct (access_at m addr); try congruence.
  destruct p; try congruence.
  destruct (fst ((snd (unsquash (initial_core_ext ora (Genv.globalenv prog) G n)))) addr);
   congruence.
Qed.

Definition matchfunspecs (ge : genv) (G : funspecs) : pred rmap :=
  ALL b:block, ALL fs: funspec,
  func_at fs (b,0%Z) -->
  EX id:ident, EX fs0: funspec, 
   !! (Genv.find_symbol ge id = Some b /\ find_id id G = Some fs0) &&
     funspec_sub_si fs0 fs.

Lemma approx_min: forall i j, approx i oo approx j = approx (min i j).
Proof.
intros.
extensionality a.
unfold compose.
apply pred_ext.
intros ? [? [? ?]].
split; auto.
apply Nat.min_glb_lt; auto.
intros ? [? ?].
apply Nat.min_glb_lt_iff in H.
destruct H.
split; auto.
split; auto.
Qed.

Lemma initial_jm_matchfunspecs prog m G n H H1 H2:
  matchfunspecs (globalenv prog) G (m_phi (initial_jm prog m G n H H1 H2)).
Proof.
  intros b  [fsig cc A P Q ? ?].
  simpl m_phi.
  intros phi' ? H0 Hext FAT.
  simpl in FAT.
  apply rmap_order in Hext as (Hl & Hr & _).
  rewrite <- Hr in FAT; clear Hr.
  assert (H3 := proj2 (necR_PURE' _ _ (b,0) (FUN fsig cc) H0)).
  spec H3. eauto.
  destruct H3 as [pp H3].
  unfold inflate_initial_mem at 1 in H3. rewrite resource_at_make_rmap in H3.
  unfold inflate_initial_mem' in H3. 
  destruct (access_at m (b,0) Cur) eqn:Haccess; [ | inv H3].
  destruct p; try discriminate H3.
  destruct (initial_core (Genv.globalenv prog) G n @ (b, 0)) eqn:?H; try discriminate H3.
  inv H3.
  assert (H3: inflate_initial_mem m (initial_core (Genv.globalenv prog) G n) @ (b,0) = PURE (FUN fsig cc) pp).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4. rewrite Haccess. auto.
  unfold initial_core in H4. rewrite resource_at_make_rmap in H4.
  unfold initial_world.initial_core' in H4. simpl in H4.
  destruct (Genv.invert_symbol (Genv.globalenv prog) b) eqn:?H; try discriminate.
  destruct (find_id i G) eqn:?H; try discriminate.
  destruct f; inv H4.
  assert (H8 := necR_PURE _ _ _ _ _ H0 H3). clear H0 H3.
  rewrite FAT in H8.
  injection H8; intro. subst A0.
  apply PURE_inj in H8. destruct H8 as [_ H8].
  simpl in H8.
  do 2 eexists. split. split. 
  apply Genv.invert_find_symbol; eauto. eauto.
  split. split; auto.
  clear H6 H5 i.
  rewrite later_unfash.
  do 3 red.
  clear FAT. forget (level phi') as n'. rewrite <- Hl in *. clear phi'. clear dependent a''.
  intros n1' Hn1'. apply laterR_nat in Hn1'.
  intros ts ftor garg.
  intros phi Hphi phi' phi'' Hphi' Hext'.
  apply necR_level in Hphi'. apply ext_level in Hext'.
  assert (n' > level phi'')%nat by lia.
  clear n1' Hphi phi Hphi' Hn1' phi' Hext'.
  rename phi'' into phi.
  intros [_ ?].
  assert (approx n' (P ts ftor garg) phi).
  split; auto.
  clear H3.
  apply fupd.fupd_intro.
  exists ts.
  assert (H5 := equal_f_dep (equal_f_dep H8 ts) ftor). clear H8.
  simpl in H5.
  assert (HP := equal_f (equal_f_dep H5 true) garg).
  assert (HQ := equal_f_dep H5 false).
  clear H5.
   simpl in HP, HQ.
   rewrite P_ne in H4. rewrite HP in H4. clear HP.
   change (approx _ (approx _ ?A) _) with ((approx n' oo approx n) A phi) in H4.
   rewrite fmap_app in H4.
   rewrite fmap_app in HQ.
   change (approx _ (approx _ ?A)) with ((approx n' oo approx n) A) in HQ.
   exists (fmap (dependent_type_functor_rec ts A) (approx n oo approx n')
             (approx n' oo approx n) ftor).
  rewrite (approx_min n' n) in *.
  exists emp. rewrite !emp_sepcon.
  destruct H4.
  split. auto.
  intro rho.
  pose proof (equal_f HQ rho). simpl in H5.
  intros phi' Hphi'.
  rewrite emp_sepcon.
  intros ? phi'' Hphi'' Hext''.
  intros [_ ?].
  rewrite (approx_min n n') in *.
  rewrite (Nat.min_comm n n') in *.
  assert (approx (min n' n) (Q0 ts
       (fmap (dependent_type_functor_rec ts A) (approx (Init.Nat.min n' n))
          (approx (Init.Nat.min n' n)) ftor) rho) phi'').
  split; auto.
  apply necR_level in Hphi''; apply ext_level in Hext''; lia.
  rewrite <- H5 in H7; clear H5.
  rewrite <- Q_ne in H7.
  destruct H7.
  auto.
Qed.

Lemma initial_jm_ext_matchfunspecs {Z} (ora : Z) prog m G n H H1 H2:
  matchfunspecs (globalenv prog) G (m_phi (initial_jm_ext ora prog m G n H H1 H2)).
Proof.
  intros b  [fsig cc A P Q ? ?].
  simpl m_phi.
  intros ? phi' H0 Hext FAT.
  simpl in FAT.
  apply rmap_order in Hext as (Hl & Hr & _).
  rewrite <- Hr in FAT; clear Hr.
  assert (H3 := proj2 (necR_PURE' _ _ (b,0) (FUN fsig cc) H0)).
  spec H3. eauto.
  destruct H3 as [pp H3].
  unfold inflate_initial_mem at 1 in H3. rewrite resource_at_make_rmap in H3.
  unfold inflate_initial_mem' in H3. 
  destruct (access_at m (b,0) Cur) eqn:Haccess; [ | inv H3].
  destruct p; try discriminate H3.
  destruct (initial_core_ext ora (Genv.globalenv prog) G n @ (b, 0)) eqn:?H; try discriminate H3.
  inv H3.
  assert (H3: inflate_initial_mem m (initial_core_ext ora (Genv.globalenv prog) G n) @ (b,0) = PURE (FUN fsig cc) pp).
  unfold inflate_initial_mem. rewrite resource_at_make_rmap.
  unfold inflate_initial_mem'. rewrite H4. rewrite Haccess. auto.
  unfold initial_core_ext in H4. rewrite resource_at_make_rmap in H4.
  unfold initial_world.initial_core' in H4. simpl in H4.
  destruct (Genv.invert_symbol (Genv.globalenv prog) b) eqn:?H; try discriminate.
  destruct (find_id i G) eqn:?H; try discriminate.
  destruct f; inv H4.
  assert (H8 := necR_PURE _ _ _ _ _ H0 H3). clear H0 H3.
  rewrite FAT in H8.
  injection H8; intro. subst A0.
  apply PURE_inj in H8. destruct H8 as [_ H8].
  simpl in H8.
  do 2 eexists. split. split. 
  apply Genv.invert_find_symbol; eauto. eauto.
  split. split; auto.
  clear H6 H5 i.
  rewrite later_unfash.
  do 3 red.
  clear FAT. forget (level phi') as n'. clear phi'. rewrite Hl in *. clear dependent a'.
  intros n1' Hn1'. apply laterR_nat in Hn1'.
  intros ts ftor garg.
  intros phi Hphi ? phi' Hphi' Hext'.
  apply necR_level in Hphi'. apply ext_level in Hext'.
  assert (n' > level phi')%nat by lia.
  clear n1' Hphi phi Hphi' Hn1' a' Hext'.
  rename phi' into phi.
  intros [_ ?].
  assert (approx n' (P ts ftor garg) phi).
  split; auto.
  clear H3.
  apply fupd.fupd_intro.
  exists ts.
  assert (H5 := equal_f_dep (equal_f_dep H8 ts) ftor). clear H8.
  simpl in H5.
  assert (HP := equal_f (equal_f_dep H5 true) garg).
  assert (HQ := equal_f_dep H5 false).
  clear H5.
   simpl in HP, HQ.
   rewrite P_ne in H4. rewrite HP in H4. clear HP.
   change (approx _ (approx _ ?A) _) with ((approx n' oo approx n) A phi) in H4.
   rewrite fmap_app in H4.
   rewrite fmap_app in HQ.
   change (approx _ (approx _ ?A)) with ((approx n' oo approx n) A) in HQ.
   exists (fmap (dependent_type_functor_rec ts A) (approx n oo approx n')
             (approx n' oo approx n) ftor).
  rewrite (approx_min n' n) in *.
  exists emp. rewrite !emp_sepcon.
  destruct H4.
  split. auto.
  intro rho.
  pose proof (equal_f HQ rho). simpl in H5.
  intros phi' Hphi'.
  rewrite emp_sepcon.
  intros ? phi'' Hphi'' Hext''.
  intros [_ ?].
  rewrite (approx_min n n') in *.
  rewrite (Nat.min_comm n n') in *.
  assert (approx (min n' n) (Q0 ts
       (fmap (dependent_type_functor_rec ts A) (approx (Init.Nat.min n' n))
          (approx (Init.Nat.min n' n)) ftor) rho) phi'').
  split; auto.
  apply necR_level in Hphi''; apply ext_level in Hext''; lia.
  rewrite <- H5 in H7; clear H5.
  rewrite <- Q_ne in H7.
  destruct H7.
  auto.
Qed.
