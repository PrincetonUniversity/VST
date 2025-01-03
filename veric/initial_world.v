Require Import VST.msl.age_to.
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.

Require Import VST.veric.shares.
Require Import VST.veric.mpred.
Require Import VST.veric.age_to_resource_at.
Import compcert.lib.Maps.

Local Open Scope pred.

Lemma adr_range_divide:
  forall b i p q loc,
    p >= 0 -> q >= 0 -> (adr_range (b,i) (p+q) loc <-> (adr_range (b,i) p loc \/adr_range (b,i+p) q loc)).
Proof.
split; intros.
destruct loc as [b' z']; destruct H1.
assert (i <= z' < i+p \/ i+p <= z' < i+p+q)  by lia.
destruct H3; [left|right]; split; auto; lia.
destruct loc as [b' z']; destruct H1; destruct H1; split; auto; lia.
Qed.

Lemma VALspec_range_e:
  forall n sh base m loc, VALspec_range n sh base  m ->
                                adr_range base n loc -> 
                {x | m @ loc = YES sh (snd x) (VAL (fst x)) NoneP}.
Proof.
intros.
specialize (H loc).
rewrite jam_true in H; auto.
simpl in H.
destruct (m @ loc); try destruct k;
try solve [exfalso; destruct H as [? [? ?]]; inv H].
assert (readable_share sh) by (destruct H as [? [? ?]]; auto).
exists (m0, H1).
simpl.
destruct H as [? [? ?]]. 
inv H.
apply YES_ext; auto.
Qed.

Lemma store_init_data_outside':
  forall F V (ge: Genv.t F V)  b a m p m',
  Genv.store_init_data ge m b p a = Some m' ->
  (forall b' ofs,
    (b=b' /\ p <= ofs < p + init_data_size a) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ access_at m = access_at m'
  /\ nextblock m = nextblock m'.
Proof.
intros.
  unfold max_access_at. simpl.
  destruct a; simpl in H; try apply store_outside' in H; auto.
  inv H; auto.
  invSome. apply store_outside' in H2; auto.
Qed.

Lemma store_init_data_list_outside':
  forall F V (ge: Genv.t F V)  b il m p m',
  Genv.store_init_data_list ge m b p il = Some m' ->
  (forall b' ofs,
    (b=b' /\ p <= ofs < p + init_data_list_size il) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ access_at m = access_at m'
  /\ nextblock m = nextblock m'.
Proof.
  induction il; simpl; intros.
  inv H; auto.
  invSome.
  specialize (IHil _ _ _ H2).
  destruct IHil as [? [? ?]].
  rewrite <- H3; rewrite <- H1; clear H3 H1 H2.
  remember (init_data_list_size il) as n.
  assert (n >= 0).
  subst n; clear; induction il; simpl; try lia.
  generalize (init_data_size_pos a); lia.
  clear il Heqn.
  apply store_init_data_outside' in H.
  generalize (init_data_size_pos a); intro.
  destruct H as [? [? ?]]; repeat split; auto.
  clear H3 H4.
  intros. specialize (H0 b' ofs); specialize (H b' ofs).
  destruct H0.
  destruct H0; left; split; auto; lia.
  rewrite <- H0.
  destruct H.
  destruct H; left; split; auto; lia.
  right. auto.
Qed.

Ltac destruct_cjoin phi HH :=
  match goal with
   |   |- context [@proj1_sig rmap _ ?X] => destruct X as [phi HH]; simpl
   |  H: context [@proj1_sig rmap _ ?X] |- _ => destruct X as [phi HH]; simpl in H
  end.

Lemma split_top_neq: fst (Share.split Share.top) <> Share.top.
Proof.
case_eq (Share.split Share.top); intros; simpl.
eapply nonemp_split_neq1; eauto.
Qed.

Lemma dec_pure: forall r, {exists k, exists pp, r = PURE k pp}+{core r = NO Share.bot bot_unreadable}.
Proof.
 destruct r.
 right; apply core_NO.
 right; apply core_YES.
 left; eauto.
Qed.

Lemma store_init_data_list_lem:
  forall F V (ge: Genv.t F V) m b lo d m',
        Genv.store_init_data_list ge m b lo d = Some m' ->
    forall w IOK IOK' P sh (wsh: writable_share sh),
     ((P * VALspec_range (init_data_list_size d) sh (b,lo))%pred
             (m_phi (initial_mem m w IOK))) ->
     ((P * VALspec_range (init_data_list_size d) sh (b,lo))%pred
              (m_phi (initial_mem m' w IOK'))).
Proof.
intros until 1. intros.
destruct H0 as [m0 [m1 [H4 [H1 H2]]]].
cut (exists m2,
         join m0 m2 (m_phi (initial_mem m' w IOK')) /\
         VALspec_range (init_data_list_size d) sh (b,lo) m2); 
  [intros [m2 [H0 H3]] | ].
exists m0; exists m2; split3; auto.
rename H2 into H3.
clear -  H H4 H3 wsh.
assert (MA: max_access_at m = max_access_at m'). {
 clear - H.
 revert m lo H; induction d; simpl; intros. inv H; auto.
 invSome. apply IHd in H2. rewrite <- H2.
 clear - H.
 unfold max_access_at. extensionality loc.
 destruct a; simpl in H;  try rewrite (Memory.store_access _ _ _ _ _ _ H); auto.
 inv H; auto.
 invSome.  rewrite (Memory.store_access _ _ _ _ _ _ H2); auto.
 }
apply store_init_data_list_outside' in H.
forget (init_data_list_size d) as N.
clear - H4  H3 H MA wsh.
pose (f loc :=
   if adr_range_dec (b,lo) N loc
   then YES sh (writable_readable_share wsh) (VAL (contents_at m' loc)) NoneP
   else core (w @ loc)).
pose (H0 := True).
destruct (remake_rmap f (ghost_of m1) (level w)) as [m2 [? ?]]; auto.
intros; unfold f, no_preds; simpl; intros; repeat if_tac; auto.
left. change fcore with (@core _ _ (fsep_sep Sep_resource)). exists (core w). rewrite core_resource_at. rewrite level_core.  auto.
{ apply join_level in H4 as [_ Hl].
  simpl in Hl.
  unfold inflate_initial_mem in Hl; rewrite level_make_rmap in Hl.
  rewrite <- Hl; apply ghost_of_approx. }
unfold f in *; clear f.
exists m2.
destruct H2 as [H2 Hg2].
split.
* (* case 1 of 3 ****)
apply resource_at_join2.
subst.
assert (level m0 = level (m_phi (initial_mem m w IOK))).
change R.rmap with rmap in *; change R.ag_rmap with ag_rmap in *.
apply join_level in H4; destruct H4; congruence.
change R.rmap with rmap in *; change R.ag_rmap with ag_rmap in *.
rewrite H5.
simpl; repeat rewrite inflate_initial_mem_level; auto.
rewrite H1; simpl; rewrite inflate_initial_mem_level; auto.
destruct H as [H [H5 H7]].
intros [b' z']; apply (resource_at_join _ _ _ (b',z')) in H4; specialize (H b' z').
specialize (H3 (b',z')). unfold jam in H3.
hnf in H3. if_tac in H3.
2: rename H6 into H8.
clear H. destruct H6 as [H H8].
+ (* case 1.1 *)
subst b'.
destruct H3 as [v [p H]].
rewrite H in H4.
repeat rewrite preds_fmap_NoneP in H4.

inv H4; [| contradiction (join_writable_readable (join_comm RJ) wsh rsh1)].
clear H6 m0.
rename H12 into H4.
rewrite H2.
rewrite if_true  by (split; auto; lia).
clear - H4 H5 H7 RJ wsh.
replace (m_phi (initial_mem m' w IOK') @ (b, z'))
  with (YES sh3 rsh3 (VAL (contents_at m' (b, z'))) NoneP); [ constructor; auto |].
revert H4.
simpl; unfold inflate_initial_mem.
repeat rewrite resource_at_make_rmap. unfold inflate_initial_mem'.
rewrite <- H5.
case_eq (access_at m (b,z') Cur); intros; auto.
destruct p; auto;
try solve [apply YES_inj in H4; inv H4; apply YES_ext; auto].
destruct (w @ (b,z')); inv H4.
inv H4.
+ (* case 1.2 *)
apply join_unit2_e in H4; auto.
clear m1 H3 Hg2.
destruct H. contradiction.
rewrite H2; clear H2.
rewrite if_false; auto.
rewrite H4.
clear - MA H5 H7 H.
unfold initial_mem; simpl.
unfold inflate_initial_mem; simpl.
repeat rewrite resource_at_make_rmap.
unfold inflate_initial_mem'.
rewrite <- H5.
specialize (IOK (b',z')). simpl in IOK.
destruct IOK as [IOK1 IOK2].
rewrite <- H.
revert IOK2; case_eq (w @ (b',z')); intros.
change fcore with (@core _ _ (fsep_sep Sep_resource)). rewrite core_NO.
destruct (access_at m (b', z')); try destruct p; try constructor; auto.
change fcore with (@core _ _ (fsep_sep Sep_resource)). rewrite core_YES.
destruct (access_at m (b', z')); try destruct p0; try constructor; auto.
destruct IOK2 as [? [? ?]].
rewrite H2. change fcore with (@core _ _ (fsep_sep Sep_resource)). rewrite core_PURE; constructor.
+
apply ghost_of_join in H4.
unfold initial_mem in *; simpl in *; unfold inflate_initial_mem in *; simpl in *.
rewrite ghost_of_make_rmap in *.
rewrite Hg2; auto.
* (**** case 2 of 3 ****)
intro loc.
specialize (H3 loc).
hnf in H3|-*.
if_tac.
generalize (refl_equal (m2 @ loc)).  pattern (resource_at m2) at 2; rewrite H2.
rewrite if_true; auto.
intro.
econstructor. econstructor.
hnf. repeat rewrite preds_fmap_NoneP.
apply H6.
do 3 red. rewrite H2.
rewrite if_false; auto.
apply core_identity.
Qed.

Lemma fold_right_rev_left:
  forall (A B: Type) (f: A -> B -> A) (l: list B) (i: A),
  fold_left f l i = fold_right (fun x y => f y x) i (rev l).
Proof.
intros. rewrite fold_left_rev_right.
f_equal; extensionality x y; auto.
Qed.

Definition initblocksize (V: Type)  (a: ident * globvar V)  : (ident * Z) :=
 match a with (id,l) => (id , init_data_list_size (gvar_init l)) end.

Lemma initblocksize_name: forall V a id n, initblocksize V a = (id,n) -> fst a = id.
Proof. destruct a; intros; simpl; inv H; auto.  Qed.

Fixpoint find_id {A} (id: ident) (G: list (ident * A)) : option A  :=
 match G with
 | (id', f)::G' => if eq_dec id id' then Some f else find_id id G'
 | nil => None
 end.

Lemma in_map_fst: forall {A B: Type} (i: A) (j: B) (G: list (A*B)),
  In (i,j) G -> In i (map (@fst _ _ ) G).
Proof.
 induction G; simpl; intros; auto.
 destruct H; [left|right]. subst; simpl; auto. auto.
Qed.

Lemma find_id_i {A}:
  forall id fs G,
            In (id,fs) G ->
             list_norepet (map (@fst _ _) G) ->
                  @find_id A id G = Some fs.
Proof.
induction G; simpl; intros.
contradiction.
destruct H. subst. rewrite if_true; auto.
inv H0.
destruct a as [i j].
if_tac.
subst i.
simpl in *; f_equal.
apply in_map_fst in H. contradiction.
auto.
Qed.

Lemma find_id_e {A}:
   forall id G fs, @find_id A id G = Some fs -> In (id,fs) G.
Proof.
 induction G; simpl; intros. inv H. destruct a. if_tac in H.
 inv H; subst; auto. right; apply (IHG fs); auto.
Qed.

Lemma find_id_In_map_fst {A} i t: forall V (Hi: @find_id A i V = Some t), In i (map fst V).
Proof.
induction V; simpl; intros. inv Hi.
destruct a as [j u]; simpl. unfold eq_dec, EqDec_ident, ident_eq in Hi.
destruct (peq i j); subst; [left | right]; auto.
Qed.

Lemma find_id_app {A} i fs: forall G1 G2 (G: find_id i (G1 ++ G2) = Some fs),
@find_id A i G1 = Some fs \/ find_id i G2 = Some fs.
Proof. induction G1; simpl; intros. right; trivial. 
destruct a. destruct (eq_dec i i0); [ left; trivial | eauto].
Qed.

Lemma find_id_app1 {A} i x G2: forall G1, find_id i G1 = Some x -> @find_id A i (G1++G2) = Some x.
  Proof.
    induction G1; simpl; intros. inv H.
    destruct a. destruct (eq_dec i i0); [trivial | auto].
  Qed.

Lemma find_id_app2 {A} i x G2: forall G1, list_norepet (map fst (G1++G2)) ->
                   find_id i G2 = Some x -> @find_id A i (G1++G2) = Some x.
  Proof.
    induction G1; simpl; intros. trivial. 
    destruct a. inv H. destruct (eq_dec i i0); [subst i0; elim H3; clear - H0 | auto].
    apply initial_world.find_id_e in H0. apply (in_map fst) in H0.
    rewrite map_app. apply in_or_app; right. apply H0.
  Qed.

Definition initial_core' {F} (ge: Genv.t (fundef F) type) (G: funspecs) (n: nat) (loc: address) : resource :=
   if Z.eq_dec (snd loc) 0
   then match Genv.invert_symbol ge (fst loc) with
           | Some id =>
                  match find_id id G with
                  | Some (mk_funspec fsig cc A P Q _ _) =>
                           PURE (FUN fsig cc) (SomeP (SpecArgsTT A) (fun ts => fmap _ (approx n) (approx n) (packPQ P Q ts)))
                  | None => NO Share.bot bot_unreadable
                  end
           | None => NO Share.bot bot_unreadable
          end
   else NO Share.bot bot_unreadable.

(* This version starts with an empty ghost. *)
Program Definition initial_core {F} (ge: Genv.t (fundef F) type) (G: funspecs) (n: nat): rmap :=
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
Qed.

(* We can also start with knowledge of the external state.
   Requirements for this PCM:
   1. It must not allow the holding thread to change the value.
   2. It must allow the holding thread to know the value.
   3. The holding thread must be able to synchronize with the outside world
      to change the value.
   For this purpose, we use the reference PCM. *)

Require Import VST.veric.ghost_PCM.
Import Ctypes.

Program Definition initial_core_ext {F Z} (ora : Z) (ge: Genv.t (fundef F) type) (G: funspecs) (n: nat): rmap :=
  proj1_sig (make_rmap (initial_core' ge G n) (Some (ext_ghost ora, NoneP) :: nil) n _ eq_refl).
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
Qed.

(* The initial state is compatible with the ghost-state machinery for invariants. *)

Require Import VST.veric.invariants.
Require Import VST.veric.juicy_extspec.

Definition wsat_ghost : ghost :=
  (None ::
   Some (existT _ (ghosts.snap_PCM(ORD := list_order own.gname)) (exist _ (Tsh, nil) I), NoneP) ::
   Some (existT _ set_PCM (exist _ Ensembles.Full_set I), NoneP) ::
   Some (existT _ (list_PCM token_PCM) (exist _ nil I), NoneP) ::
   nil).

Program Definition wsat_rmap (r : rmap) :=
  proj1_sig (make_rmap (resource_at (core r)) wsat_ghost (level r) _ _).
Next Obligation.
Proof.
  extensionality l; unfold compose. rewrite <- core_resource_at. apply resource_fmap_core.
Qed.

Lemma wsat_rmap_wsat : forall r, (wsat * ghost_set g_en Ensembles.Full_set)%pred (wsat_rmap r).
Proof.
  intros.
  unfold wsat.
  do 3 (rewrite exp_sepcon1; exists nil).
  rewrite prop_true_andp by auto.
  rewrite !sepcon_assoc, (sepcon_comm (iter_sepcon _ _)).
  rewrite <- (sepcon_assoc (ghost_set _ _)), ghost_set_join.
  replace (fun i : iname => nth i nil None = Some false) with (Ensembles.Empty_set(U := iname)).
  rewrite prop_true_andp, Union_Empty.
  destruct (make_rmap (resource_at (core r)) (None :: Some (existT _ (ghosts.snap_PCM(ORD := list_order own.gname)) (exist _ (Tsh, nil) I), NoneP) :: nil) (level r))
    as (r_inv & ? & Hr1 & Hg1).
  { extensionality l; unfold compose. rewrite <- core_resource_at. apply resource_fmap_core. }
  { auto. }
  destruct (make_rmap (resource_at (core r)) (None :: None :: Some (existT _ set_PCM (exist _ Ensembles.Full_set I), NoneP) ::
   Some (existT _ (list_PCM token_PCM) (exist _ nil I), NoneP) :: nil) (level r))
    as (r_rest & ? & Hr2 & Hg2).
  { extensionality l; unfold compose. rewrite <- core_resource_at. apply resource_fmap_core. }
  { auto. }
  exists r_inv, r_rest; split.
  { unfold wsat_rmap; apply resource_at_join2; rewrite ?level_make_rmap, ?resource_at_make_rmap, ?ghost_of_make_rmap; auto.
    + intros; rewrite Hr1, Hr2; apply resource_at_join, core_duplicable.
    + rewrite Hg1, Hg2; unfold wsat_ghost; repeat constructor. }
  split.
  - simpl.
    exists I.
    rewrite Hr1, Hg1; split.
    + apply resource_at_core_identity.
    + apply join_sub_refl.
  - destruct (make_rmap (resource_at (core r)) (None :: None :: Some (existT _ set_PCM (exist _ Ensembles.Full_set I), NoneP) ::
     None :: nil) (level r))
      as (r_en & ? & Hr3 & Hg3).
    { extensionality l; unfold compose. rewrite <- core_resource_at. apply resource_fmap_core. }
    { auto. }
    destruct (make_rmap (resource_at (core r)) (None :: None :: None ::
     Some (existT _ (list_PCM token_PCM) (exist _ nil I), NoneP) :: nil) (level r))
      as (r_dis & ? & Hr4 & Hg4).
    { extensionality l; unfold compose. rewrite <- core_resource_at. apply resource_fmap_core. }
    { auto. }
    exists r_dis, r_en; split.
    { apply resource_at_join2; try congruence.
      + intros; rewrite Hr2, Hr3, Hr4; apply resource_at_join, core_duplicable.
      + rewrite Hg2, Hg3, Hg4; repeat constructor. }
    simpl iter_sepcon; rewrite sepcon_emp.
    split; simpl.
    + exists I.
      rewrite Hr4, Hg4; split.
      * apply resource_at_core_identity.
      * apply join_sub_refl.
    + exists I.
      rewrite Hr3, Hg3; split.
      * apply resource_at_core_identity.
      * eexists; repeat constructor.
  - constructor; intros ? X; inv X.
    inv H.
  - extensionality; apply prop_ext; split; intro.
    + inv H.
    + destruct x; inv H.
Qed.

Lemma wsat_no : forall r, (ALL l, noat l) (wsat_rmap r).
Proof.
  simpl; intros; unfold wsat_rmap.
  rewrite resource_at_make_rmap; apply resource_at_core_identity.
Qed.

Corollary wsat_rmap_resource : forall r r', join r (wsat_rmap r) r' -> resource_at r' = resource_at r.
Proof.
  intros.
  extensionality l; apply (resource_at_join _ _ _ l) in H.
  apply join_comm, wsat_no in H; auto.
Qed.

Lemma wsat_rmap_ghost : forall r r', joins r (wsat_rmap r) -> level r' = level r -> ghost_of r' = ghost_of r ->
  joins r' (wsat_rmap r').
Proof.
  intros ?? [z ?] Hl Hg.
  destruct (make_rmap (resource_at r') (ghost_of z) (level r')) as (z' & ? & Hr' & Hg').
  { extensionality l; apply resource_at_approx. }
  { rewrite Hl; apply join_level in H as [->]; apply ghost_of_approx. }
  exists z'; apply resource_at_join2; auto.
  - unfold wsat_rmap; rewrite level_make_rmap; auto.
  - intros l; apply (resource_at_join _ _ _ l) in H.
    unfold wsat_rmap; rewrite resource_at_make_rmap, Hr'.
    apply join_comm, resource_at_join, core_unit.
  - rewrite Hg, Hg'.
    apply ghost_of_join in H.
    unfold wsat_rmap in *; rewrite ghost_of_make_rmap in *; auto.
Qed.

Lemma age_to_wsat_rmap : forall n r, (n <= level r)%nat -> age_to n (wsat_rmap r) = wsat_rmap (age_to n r).
Proof.
  intros; apply rmap_ext.
  - unfold wsat_rmap; rewrite level_make_rmap, !level_age_to; auto.
    rewrite level_make_rmap; auto.
  - intros; unfold wsat_rmap; rewrite resource_at_make_rmap, <- core_resource_at, !age_to_resource_at,
      resource_at_make_rmap.
    rewrite <- core_resource_at, resource_fmap_core'; auto.
  - unfold wsat_rmap; rewrite ghost_of_make_rmap, !age_to_ghost_of, ghost_of_make_rmap; auto.
Qed.

Lemma list_disjoint_rev2:
   forall A (l1 l2: list A), list_disjoint l1 (rev l2) = list_disjoint l1 l2.
Proof.
intros.
unfold list_disjoint.
apply prop_ext; split; intros; eapply H; eauto.
rewrite <- In_rev; auto.
rewrite In_rev; auto.
Qed.

Require Import VST.veric.mapsto_memory_block.

Open Scope pred.

Lemma writable_blocks_app:
  forall bl bl' rho, writable_blocks (bl++bl') rho = writable_blocks bl rho * writable_blocks bl' rho.
Proof.
induction bl; intros.
simpl; rewrite emp_sepcon; auto.
simpl.
destruct a as [b n]; simpl.
rewrite sepcon_assoc.
f_equal.
apply IHbl.
Qed.

Fixpoint prog_funct' {F V} (l: list (ident * globdef F V)) : list (ident * F) :=
 match l with nil => nil | (i,Gfun f)::r => (i,f):: prog_funct' r | _::r => prog_funct' r
 end.

Definition prog_funct {F} (p: program F) := prog_funct' (prog_defs p).

Lemma find_symbol_add_globals_nil:
  forall {F V} i g id p prog_pub,
     (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) ((i, g) :: nil)) id =
           Some p <-> (i = id /\ 1%positive = p)).
Proof. intros. simpl.
       unfold Genv.find_symbol, Genv.add_global in *; simpl.
      destruct (eq_dec i id); subst.
        rewrite PTree.gss. intuition. congruence.
        rewrite PTree.gso by auto. split; intro Hx.
        rewrite PTree.gempty in Hx; inv Hx.
         inv Hx. congruence.
Qed.

Lemma find_symbol_add_globals_cons:
  forall {F V} i g id dl prog_pub (HD: 0 < Zlength dl),
   ~ In i (map fst dl) -> list_norepet (map fst dl) ->
     (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) (dl ++ (i, g) :: nil)) id =
           Some (1 + (Z.to_pos (Zlength dl)))%positive <-> i = id).
Proof.
intros.
  assert (Genv.genv_next (Genv.empty_genv F V prog_pub) = 1%positive)  by reflexivity.
  assert (Genv.find_symbol (Genv.empty_genv F V prog_pub)  id = None) by (intros; apply PTree.gempty).
 forget (Genv.empty_genv F V prog_pub) as ge.
 forget (1%positive) as n.
  revert ge n H H0 H1 H2 HD; induction dl; intros.
  (*base case*)
        simpl in *. rewrite Zlength_nil in HD. lia.
  (*induction step*)
        simpl; auto.
        rewrite Zlength_cons in *.
        destruct a as [a ag]; simpl in *.
        destruct dl.
          simpl in *. clear IHdl.
          assert (a<>i /\ ~ False) by (clear - H; intuition).
          clear H; destruct H3.
          destruct (eq_dec id a).
            subst id. unfold Genv.find_symbol, Genv.add_global; simpl.
              rewrite PTree.gso; trivial. rewrite H1.
              rewrite PTree.gss.
              split; intro; try congruence. assert (n = n+1)%positive. clear - H4. congruence. lia.
          unfold Genv.find_symbol, Genv.add_global; simpl.
            rewrite H1.
            destruct (eq_dec id i).
              subst i.
              rewrite PTree.gss. rewrite Pplus_one_succ_r.
                split; intro; try congruence. trivial.
              rewrite PTree.gso; trivial.
              rewrite PTree.gso; trivial.
              unfold Genv.find_symbol in H2. rewrite H2.
              split; intros. congruence. subst. exfalso. apply n1; trivial.

        replace ((n + Z.to_pos (Z.succ (Zlength (p :: dl))))%positive) with
          ((Pos.succ n) + Z.to_pos (Zlength (p ::dl)))%positive.
        2: { clear - n dl. rewrite Z2Pos.inj_succ.
                   rewrite Pplus_one_succ_r. rewrite Pplus_one_succ_l.
                     rewrite Pos.add_assoc. trivial.
                   rewrite Zlength_correct. simpl.
                     rewrite Pos.of_nat_succ. apply Pos2Z.is_pos. }
        simpl in H0. inv H0.
        assert (a<>i /\ ~ In i (map fst (p::dl))) by (clear - H; intuition).
        clear H; destruct H0.
        destruct (eq_dec id a).
         subst id.
         split; intro; try congruence. exfalso.
         clear IHdl.
         assert (~In a (map fst (((p::dl)++(i,g)::nil)))).
             rewrite map_app. rewrite in_app_iff.
             intros [?|?]; try contradiction.
             simpl in H3. destruct H3; try congruence.
         forget ((p::dl) ++ (i, g) :: nil) as vl.
         assert (Genv.find_symbol (Genv.add_global ge (a,ag)) a = Some (Genv.genv_next ge)).
            unfold Genv.find_symbol, Genv.add_global; simpl. rewrite PTree.gss; auto.

         forget (Genv.add_global ge (a,ag)) as ge1.
         forget (Genv.genv_next ge) as N; clear ge H2.
         assert (Pos.succ N + Z.to_pos (Zlength (p :: dl)) > N)%positive by lia.
         forget (Pos.succ N + Z.to_pos (Zlength (p :: dl)))%positive as K.
         clear - H1 H3 H2 H4.
         revert ge1 K H2 H1 H3 H4; induction vl; simpl; intros.
            inversion2 H1 H4; lia.
         apply (IHvl (Genv.add_global ge1 a0) K H2); auto.
           unfold Genv.find_symbol, Genv.add_global in H4|-*; simpl in *.
           rewrite PTree.gso; auto.


         apply IHdl; auto.
        unfold Genv.find_symbol, Genv.add_global in H2|-*; simpl.
                 rewrite PTree.gso; auto.
                   rewrite Zlength_correct. simpl.
                     rewrite Pos.of_nat_succ. apply Pos2Z.is_pos.
Qed.

Lemma find_symbol_add_globals:
  forall {F V} i g id dl prog_pub,
   ~ In i (map fst dl) -> list_norepet (map fst dl) ->
  match dl with
    nil => forall p,
      (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) ((i, g) :: nil)) id =
           Some p <-> (i = id /\ 1%positive = p))
  | _ =>
     (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) (dl ++ (i, g) :: nil)) id =
           Some (1 + (Z.to_pos (Zlength dl)))%positive <-> i = id)
  end.
Proof.
intros.
destruct dl.
  intros; apply find_symbol_add_globals_nil.
  apply find_symbol_add_globals_cons; trivial.
    rewrite Zlength_correct. simpl.
    rewrite Pos.of_nat_succ. apply Pos2Z.is_pos.
Qed.


Lemma find_symbol_add_globals':
  forall {F V} i g id dl prog_pub,
  match dl with
    nil => forall p,
      (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) ((i, g) :: nil)) id =
           Some p <-> (i = id /\ 1%positive = p))
  | _ =>
     ~ In i (map fst dl) -> list_norepet (map fst dl) ->
     (Genv.find_symbol
        (Genv.add_globals (Genv.empty_genv F V prog_pub) (dl ++ (i, g) :: nil)) id =
           Some (1 + (Z.to_pos (Zlength dl)))%positive <-> i = id)
  end.
Proof.
intros.
destruct dl.
  intros; apply find_symbol_add_globals_nil.
  apply find_symbol_add_globals_cons; trivial.
    rewrite Zlength_correct. simpl.
    rewrite Pos.of_nat_succ. apply Pos2Z.is_pos.
Qed.

Lemma nth_error_app: forall {T} (al bl : list T) (j: nat),
     nth_error (al++bl) (length al + j) = nth_error bl j.
Proof.
 intros. induction al; simpl; auto.
Qed.

Lemma nth_error_app1: forall {T} (al bl : list T) (j: nat),
     (j < length al)%nat ->
     nth_error (al++bl) j = nth_error al j.
Proof.
  intros. revert al H; induction j; destruct al; simpl; intros; auto; try lia.
   apply IHj. lia.
Qed.

Lemma nth_error_rev:
  forall T (vl: list T) (n: nat),
   (n < length vl)%nat ->
  nth_error (rev vl) n = nth_error vl (length vl - n - 1).
Proof.
 induction vl; simpl; intros. apply nth_error_nil.
 destruct (eq_dec n (length vl)).
 subst.
 pattern (length vl) at 1; rewrite <- length_rev.
 rewrite <- (Nat.add_0_r (length (rev vl))).
 rewrite nth_error_app.
 case_eq (length vl); intros. simpl. auto.
 replace (S n - n - 1)%nat with O by lia.
 simpl; auto.
 rewrite nth_error_app1 by (rewrite length_rev; lia).
 rewrite IHvl by lia. clear IHvl.
 destruct n; destruct (length vl). congruence.
 simpl. replace (n-0)%nat with n by lia; auto.
 lia.
 replace (S n1 - n - 1)%nat with (S (S n1 - S n - 1))%nat by lia.
 reflexivity.
Qed.

Lemma Zlength_app: forall T (al bl: list T),
    Zlength (al++bl) = Zlength al + Zlength bl.
Proof. induction al; intros. simpl app; rewrite Zlength_nil; lia.
 simpl app; repeat rewrite Zlength_cons; rewrite IHal; lia.
Qed.
Lemma Zlength_rev: forall T (vl: list T), Zlength (rev vl) = Zlength vl.
Proof. induction vl; simpl; auto. rewrite Zlength_cons. rewrite <- IHvl.
rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil; lia.
Qed.

Lemma Zlength_map: forall A B (f: A -> B) l, Zlength (map f l) = Zlength l.
Proof. induction l; simpl; auto. repeat rewrite Zlength_cons. f_equal; auto.
Qed.

(*Partial attempt at porting add_globals_hack*)
Lemma add_globals_hack_nil {F}:
   forall gev prog_pub,
    gev = Genv.add_globals (Genv.empty_genv (fundef F) type prog_pub) (rev nil) ->
   forall id, Genv.find_symbol gev id = None.
Proof. simpl; intros; subst.
  unfold Genv.find_symbol, Genv.empty_genv. simpl. apply PTree.gempty.
Qed.

Lemma add_globals_hack_single {F}:
   forall v gev prog_pub,
    gev = Genv.add_globals (Genv.empty_genv (fundef F) type prog_pub) (cons v nil) ->
   forall id b, (Genv.find_symbol gev id = Some b <-> fst v = id /\ b = 1%positive).
Proof. simpl; intros; subst.
  unfold Genv.find_symbol, Genv.empty_genv. simpl.
  destruct (peq (fst v) id).
     subst id. rewrite PTree.gss.
       split; intros. split; trivial. congruence.
       destruct H; subst. trivial.
  rewrite PTree.gso.
    split; intros. rewrite PTree.gempty in H. inv H.
    destruct H; subst. congruence.
  auto.
Qed.

Lemma advance_next_length:
  forall F V vl n, @Genv.advance_next F V vl n = (Pos.of_nat (S (length vl)) + n - 1)%positive.
Proof.
 unfold Genv.advance_next; induction vl; simpl fold_left; intros.
  simpl Pos.of_nat. rewrite Pos.add_comm. symmetry. apply Pos.add_sub.
  simpl length. rewrite IHvl. rewrite Pplus_one_succ_l.
  f_equal.
  symmetry; rewrite Nat2Pos.inj_succ by lia.
  rewrite Pplus_one_succ_r. symmetry; apply Pos.add_assoc.
Qed.

Lemma Zpos_Posofnat: forall n, (n>0)%nat -> Z.pos (Pos.of_nat n) = Z.of_nat n.
Proof.
 intros. destruct n. lia. simpl  Z.of_nat. f_equal.
 symmetry; apply Pos.of_nat_succ.
Qed.

Lemma add_globals_hack {F}:
   forall vl gev prog_pub,
    list_norepet (map fst vl) ->
    gev = Genv.add_globals (Genv.empty_genv (fundef F) type prog_pub) (rev vl) ->

   (forall id b, 0 <= Zpos b - 1 < Zlength vl ->
                           (Genv.find_symbol gev id = Some b <->
                            nth_error (map (@fst _ _) vl) (length vl - Pos.to_nat b)  = Some id)).
Proof. intros. subst.
     apply iff_trans with (nth_error (map fst (rev vl)) (Z.to_nat (Zpos b - 1)) = Some id).
   2: {
     rewrite map_rev; rewrite nth_error_rev.
             replace (length (map fst vl) - Z.to_nat (Zpos b - 1) - 1)%nat
                        with (length vl - Pos.to_nat b)%nat ; [intuition | ].
    rewrite length_map.
    transitivity (length vl - (Z.to_nat (Z.pos b-1)+1))%nat; try lia.
    rewrite length_map.
    rewrite Zlength_correct in H1.
    forget (Z.pos b-1) as i; forget (length vl) as n; clear - H1.
    apply inj_lt_rev. rewrite Z_to_nat_max; auto.
    rewrite (Coqlib.Zmax_spec i 0). if_tac; lia.
  }
  rename H1 into Hb; revert H; induction vl; simpl rev; simpl map;
       simpl Genv.find_symbol; intros;
       try rewrite Zlength_nil in *.
      unfold Genv.find_symbol. rewrite PTree.gempty.
     intuition lia.
       destruct a. inv H. rewrite Zlength_cons in Hb.
       destruct (eq_dec (Z.pos b-1) (Zlength vl)).
        clear IHvl Hb. rewrite e. rewrite Zlength_correct.
        rewrite Nat2Z.id.
        replace b with (Z.to_pos (1+ (Zlength vl)))
          by (rewrite <- e; replace (1 + (Z.pos b - 1)) with (Z.pos b) by lia;
                  apply Pos2Z.id).
        clear e b.
        rewrite <- Zlength_rev. rewrite <- length_rev.
         replace (length (rev vl)) with (length (rev vl) + 0)%nat by lia.
         rewrite map_app. rewrite <- length_map with (f:=@fst ident (globdef (fundef F) type)).
        rewrite nth_error_app.
        apply iff_trans with (i=id); [ | simpl; split; intro; subst; auto; inv H; auto].
        rewrite In_rev in H2. rewrite <- map_rev in H2.
       rewrite <- list_norepet_rev in H3. rewrite <- map_rev in H3.
         forget (rev vl) as dl.
    assert (FSA := find_symbol_add_globals i g  id _ prog_pub H2 H3).
    { destruct dl.
      rewrite (FSA (Z.to_pos (1 + Zlength (@nil (ident * globdef (fundef F) type))))).
      simpl. intuition.
      replace (Z.to_pos (1 + Zlength (p :: dl))) with (1 + Z.to_pos (Zlength (p :: dl)))%positive ; auto.
      clear.
      rewrite Zlength_cons.      rewrite Zlength_correct.
      rewrite Z2Pos.inj_add; try solve [simpl; lia].
    }
    spec IHvl ; [ lia |].
    specialize (IHvl H3).
    rewrite Genv.add_globals_app.
    unfold Genv.add_globals at 1. simpl fold_left.
    unfold Genv.find_symbol, Genv.add_global.
    simpl Genv.genv_symb.
    destruct (eq_dec id i).
    + subst i. rewrite PTree.gss.
      rewrite Genv.genv_next_add_globals.
      rewrite advance_next_length.
      simpl Genv.genv_next.
      rewrite map_app.
      rewrite In_rev in H2. rewrite <- map_rev in H2. rewrite Pos.add_sub.
      split; intro.
      - assert (H': b = Pos.of_nat (S (length (rev vl)))) by congruence.
        clear H; rename H' into H.
          subst b. exfalso; apply n; clear.
          rewrite <- Zlength_rev. rewrite Zlength_correct. forget (length (rev vl)) as i.
          rewrite Zpos_Posofnat by lia. rewrite Nat2Z.inj_succ. unfold Z.succ.  lia.
     - exfalso.
       assert (Z.pos b-1 >= 0) by (clear - Hb; lia).
       pose proof (Z2Nat.id _ (Z.ge_le _ _ H0)).
       clear - H1 H H2 n.
       rewrite Zlength_correct in n. apply n. clear n.
       rewrite <- H1.
       f_equal. clear - H H2.
       forget (Z.to_nat (Z.pos b-1)) as j.
       replace (length vl) with (length (map fst (rev vl)))
           by (rewrite length_map; rewrite length_rev; auto).
       forget (map fst (rev vl)) as al.
       revert al H2 H; clear; induction j; destruct al; simpl; intros; auto. inv H; intuition.
       exfalso; clear - H; induction j; inv H; auto.
       f_equal. apply IHj; auto.
    + rewrite PTree.gso by auto.
      rewrite map_app.
      destruct IHvl.
      split; intro.
      - apply H in H1. rewrite nth_error_app1; auto.
        clear - n Hb. rewrite length_map. rewrite length_rev. rewrite Zlength_correct in Hb,n.
        assert (Z.pos b-1>=0) by lia.
        pose proof (Z2Nat.id _ (Z.ge_le _ _ H)).
        forget (Z.to_nat(Z.pos b-1)) as j. rewrite <- H0 in *.
        destruct Hb. clear - H2 n. lia.
      - assert (Z.to_nat (Z.pos b-1) < length (map (@fst _ _) (rev vl)))%nat.
        { clear - Hb n H1.
          rewrite Zlength_correct in n. rewrite length_map; rewrite length_rev.
          assert (Z.to_nat (Z.pos b-1) <> length vl).
          { contradict n. rewrite <- n.
            rewrite Z2Nat.id; auto. lia. }
          forget (Z.to_nat (Z.pos b-1)) as j.
          clear - H1 H.
          assert (S (length vl) = length (map fst (rev vl) ++ map fst ((i, g) :: nil))).
          { simpl. rewrite length_app; rewrite length_map; rewrite length_rev; simpl; lia. }
          assert (j < S (length vl))%nat; [ | lia].
          rewrite H0. forget (map fst (rev vl) ++ map fst ((i, g) :: nil)) as al.
          clear - H1. revert al H1; induction j; destruct al; simpl in *; intros; inv H1; auto; try lia.
          specialize (IHj _ H0); lia. }
        rewrite nth_error_app1 in H1 by auto.
        apply H0 in H1. auto.
Qed.

Lemma find_symbol_globalenv {F}:
  forall (prog: program F) i b,
   list_norepet (prog_defs_names prog) ->
  Genv.find_symbol (Genv.globalenv prog) i = Some b ->
  0 < Z.pos b <= Z_of_nat (length (prog_defs prog)) /\
  exists d, nth_error (prog_defs prog) (Z.to_nat (Z.pos b-1)) = Some (i,d).
Proof.
intros.
unfold Genv.globalenv in H0.
change (AST.prog_public prog) with (prog_public prog) in H0.
change (AST.prog_defs prog) with (prog_defs prog) in H0.
assert (RANGE: 0 <= Z.pos b - 1 < Zlength (rev (prog_defs prog))). {
 rewrite <- (rev_involutive (prog_defs prog)) in H0.
 clear - H0.
 revert H0; induction (rev (prog_defs prog));  simpl Genv.find_symbol; intros.
 unfold Genv.find_symbol in H0. simpl in H0. rewrite PTree.gempty in H0; inv H0.
 rewrite Genv.add_globals_app in H0.
 simpl in H0. destruct a.
 destruct (eq_dec i0 i). subst.
 unfold Genv.add_global, Genv.find_symbol in H0. simpl in H0.
 rewrite PTree.gss  in H0. inv H0.
 clear.
 split.
 match goal with |- _ <= Z.pos ?A - _ => pose proof (Zgt_pos_0  A); lia end.
 rewrite Zlength_cons.
 induction l. simpl. lia.
 rewrite Zlength_cons.
 Opaque Z.sub. simpl. Transparent Z.sub.
 rewrite Genv.add_globals_app.
   simpl Genv.genv_next.
 match goal with |- context [Pos.succ ?J] =>
  forget J as j
 end.
 clear - IHl.
 replace (Z.pos (Pos.succ j) - 1) with (Z.succ (Z.pos j - 1)). lia.
  unfold Z.succ.  rewrite Pos2Z.inj_succ.  lia.
 unfold Genv.add_global, Genv.find_symbol in IHl, H0. simpl in H0.
 rewrite PTree.gso in H0 by auto.
 apply IHl in H0.
 rewrite Zlength_cons. lia.
 }
 split.
 rewrite Zlength_correct in RANGE.
 rewrite length_rev in RANGE. lia.
 rewrite <- list_norepet_rev in H.
 unfold prog_defs_names in H.
 change (AST.prog_defs prog) with (prog_defs prog) in H.
 rewrite <- map_rev in H.
 rewrite add_globals_hack in H0; [ | apply H | rewrite rev_involutive; auto | auto ].
 rewrite map_rev in H0.
 rewrite nth_error_rev in H0.
 rewrite list_map_nth in H0.
 match type of H0 with option_map _ ?A = _ =>
   revert H0; case_eq A; intros
 end.
 destruct p; simpl in H1. inv H1.
 exists g.
 rewrite <- H0. f_equal.
 rewrite length_rev. rewrite length_map.
 clear - RANGE.
 rewrite Zlength_rev in RANGE. rewrite Zlength_correct in RANGE.
 rewrite <- (Z2Nat.id (Z.pos b)) in * by lia.
 rewrite Z2Nat.inj_pos in *.
 forget (Pos.to_nat b) as n. clear b.
 replace (Z.of_nat n - 1) with (Z.of_nat (n-1)) by (rewrite inj_minus1 by lia; f_equal; auto).
 rewrite Nat2Z.id.
 lia.
 inv H1.
 rewrite length_rev. rewrite length_map.
 clear - RANGE. rewrite Zlength_correct in RANGE.
 rewrite length_rev in RANGE.
 forget (length (prog_defs prog)) as N.
 assert (Z_of_nat N > 0) by lia.
 destruct N; inv H.
 assert (Pos.to_nat b > 0)%nat; [apply Pos2Nat.is_pos| lia].
Qed.

Fixpoint alloc_globals_rev {F V} (ge: Genv.t F V) (m: mem) (vl: list (ident * globdef F V))
                         {struct vl} : option mem :=
  match vl with
  | nil => Some m
  | v :: vl' =>
     match alloc_globals_rev ge m vl' with
     | Some m' => Genv.alloc_global ge m' v
     | None => None
     end
  end.

Lemma alloc_globals_app:
   forall F V (ge: Genv.t F V) m m2 vs vs',
  Genv.alloc_globals ge m (vs++vs') = Some m2 <->
    exists m', Genv.alloc_globals ge m vs = Some m' /\
                    Genv.alloc_globals ge m' vs' = Some m2.
Proof.
intros.
revert vs' m m2; induction vs; intros.
simpl.
intuition. exists m; intuition. destruct H as [? [H ?]]; inv H; auto.
simpl.
case_eq (Genv.alloc_global ge m a); intros.
specialize (IHvs vs' m0 m2).
auto.
intuition; try discriminate.
destruct H0 as [? [? ?]]; discriminate.
Qed.

Lemma alloc_globals_rev_eq:
     forall F V (ge: Genv.t F V) m vl,
     Genv.alloc_globals ge m (rev vl) = alloc_globals_rev ge m vl.
Proof.
intros.
revert m; induction vl; intros; auto.
simpl.
rewrite <- IHvl.
case_eq (Genv.alloc_globals ge m (rev vl)); intros.
case_eq (Genv.alloc_global ge m0 a); intros.
rewrite alloc_globals_app.
exists m0; split; auto.
simpl. rewrite H0; auto.
case_eq (Genv.alloc_globals ge m (rev vl ++ a :: nil)); intros; auto.
exfalso.
apply alloc_globals_app in H1.
destruct H1 as [m' [? ?]].
inversion2 H H1.
simpl in H2.
rewrite H0 in H2; inv H2.
case_eq (Genv.alloc_globals ge m (rev vl ++ a :: nil)); intros; auto.
exfalso.
apply alloc_globals_app in H0.
destruct H0 as [m' [? ?]].
inversion2 H H0.
Qed.


Lemma zlength_nonneg: forall A l, 0 <= @Zlength A l.
Proof. intros.
  induction l. rewrite Zlength_nil. lia.
  rewrite Zlength_cons. lia.
Qed.

Lemma alloc_globals_rev_nextblock:
  forall {F V} (ge: Genv.t F V) vl m, alloc_globals_rev ge empty vl = Some m ->
     nextblock m = Z.to_pos(Z.succ (Zlength vl)).
Proof.
  intros.
   revert m H; induction vl; simpl; intros. inv H; apply nextblock_empty.
  invSome. apply IHvl in H.
  apply Genv.alloc_global_nextblock in H2.  rewrite Zlength_cons. rewrite H2.
  rewrite Z2Pos.inj_succ.
  rewrite <- H. trivial. apply Z.lt_succ_r. apply zlength_nonneg.
Qed.


Lemma store_zeros_max_access:  forall m b z N m',
      store_zeros m b z N = Some m' -> max_access_at m' = max_access_at m.
Proof.
 intros. symmetry in H; apply R_store_zeros_correct in H.
 remember (Some m') as m1. revert m' Heqm1; induction H; intros; inv Heqm1.
 auto.
 rewrite (IHR_store_zeros m'0 (eq_refl _)).
 clear - e0.
 Transparent store. unfold store in e0.
 remember (valid_access_dec m Mint8unsigned b p Writable) as d.
 destruct d; inv e0. unfold max_access_at; simpl. auto.
 Opaque store.
Qed.


Lemma store_zeros_access:  forall m b z N m',
      store_zeros m b z N = Some m' -> access_at m' = access_at m.
Proof.
 intros. symmetry in H; apply R_store_zeros_correct in H.
 remember (Some m') as m1. revert m' Heqm1; induction H; intros; inv Heqm1.
 auto.
 rewrite (IHR_store_zeros m'0 (eq_refl _)).
 clear - e0.
 Transparent store. unfold store in e0.
 remember (valid_access_dec m Mint8unsigned b p Writable) as d.
 destruct d; inv e0. unfold access_at; simpl. auto.
 Opaque store.
Qed.

Lemma store_zeros_contents1: forall m b z N m' loc,
      fst loc <> b ->
      store_zeros m b z N = Some m' ->
      contents_at m loc = contents_at m' loc.
Proof.
 intros. symmetry in H0; apply R_store_zeros_correct in H0.
 remember (Some m') as m1. revert m' Heqm1; induction H0; intros; inv Heqm1.
 auto.
 transitivity (contents_at m' loc).
 Transparent store. unfold store in e0.
 remember (valid_access_dec m Mint8unsigned b p Writable) as d.
 destruct d; inv e0. unfold contents_at; simpl. rewrite PMap.gso by auto. auto.
 eapply IHR_store_zeros; eauto.
 Opaque store.
Qed.


Lemma alloc_global_old:
  forall {F V} (ge: Genv.t F V) m iv m', Genv.alloc_global ge m iv = Some m' ->
       forall loc, (fst loc < nextblock m)%positive ->
        access_at m loc = access_at m' loc
       /\ contents_at m loc = contents_at m' loc.
Proof.
 intros.
 destruct loc as [b ofs]; simpl in *; subst.
 assert (NEQ: b <> nextblock m) by (intro Hx; inv Hx; lia).
 unfold Genv.alloc_global in H. destruct iv.
 destruct g.
*
 revert H; case_eq (alloc m 0 1); intros.
 unfold drop_perm in H1.
 destruct (range_perm_dec m0 b0 0 1 Cur Freeable); inv H1.
 unfold contents_at, max_access_at, access_at in *;
 simpl in *.
 Transparent alloc. unfold alloc in H. Opaque alloc.
 inv H; simpl in *.
 rewrite PMap.gss. repeat rewrite (PMap.gso _ _ NEQ). auto.
*
 forget (init_data_list_size (gvar_init v)) as N.
 revert H; case_eq (alloc m 0 N); intros.
 invSome. invSome.
 assert (access_at m (b,ofs) = access_at m0 (b,ofs)
          /\ contents_at m (b,ofs) = contents_at m0 (b,ofs)). {
 clear - H NEQ.
 split. extensionality k. eapply alloc_access_other; try eassumption.
 left. intro. subst b0. apply alloc_result in H. contradiction.
 Transparent alloc. unfold alloc in H. Opaque alloc.
 unfold contents_at. inv H. simpl.
 rewrite PMap.gso by auto. auto.
 }
 assert (b0=nextblock m) by (inv H; auto). subst b0.
 unfold max_access_at.
 destruct H2 as [H2a H2b]; rewrite H2a,H2b; clear H H2a H2b.
 rewrite <- (store_zeros_access _ _ _ _ _ H1).
 apply store_zeros_contents1 with (loc:= (b,ofs)) in H1.
 2: simpl; congruence. rewrite H1; clear H1 m0.
 apply store_init_data_list_outside' in H4.
 destruct H4 as [? [? ?]].
 specialize (H b ofs).  destruct H.
 destruct H; subst; congruence. unfold block in *; rewrite H; rewrite H1.
 clear - H5 NEQ.
 unfold drop_perm in H5.
 destruct (range_perm_dec m2 (nextblock m) 0 N Cur Freeable); inv H5.
 unfold contents_at, access_at, max_access_at in *;
 simpl in *.
  repeat rewrite (PMap.gso _ _ NEQ). auto.
Qed.

Program Definition set_ghost (m : rmap) (g : ghost) (Hg : _) :=
  proj1_sig (make_rmap (resource_at m) g (level m) _ Hg).
Next Obligation.
Proof.
  intros.
  extensionality; apply resource_at_approx.
Qed.

Fixpoint prog_vars' {F V} (l: list (ident * globdef F V)) : list (ident * globvar V) :=
 match l with nil => nil | (i,Gvar v)::r => (i,v):: prog_vars' r | _::r => prog_vars' r
 end.

Definition prog_vars {F} (p: program F) := prog_vars' (prog_defs p).

Definition no_locks phi :=
  forall addr sh sh' z z' P,
    phi @ addr <> YES sh sh' (LK z z') P.

Lemma make_tycontext_s_find_id i G : (make_tycontext_s G) ! i = find_id i G.
Proof.
  induction G as [| (j, fs) f IHf]. destruct i; reflexivity.
  simpl.
  rewrite PTree.gsspec.
  rewrite IHf.
  reflexivity.
Qed.

(* How to relate Gamma to funspecs in memory, once we are outside the
   semax proofs?  We define 'matchfunspecs' which will be satisfied by
   the initial memory, and preserved under resource_decay / pures_eq /
   aging. *)

Definition cond_approx_eq n A P1 P2 :=
  (forall ts,
      fmap (dependent_type_functor_rec ts (AssertTT A)) (approx n) (approx n) (P1 ts) =
      fmap (dependent_type_functor_rec ts (AssertTT A)) (approx n) (approx n) (P2 ts)).

Lemma cond_approx_eq_sym n A P1 P2 :
  cond_approx_eq n A P1 P2 ->
  cond_approx_eq n A P2 P1.
Proof.
  unfold cond_approx_eq; auto.
Qed.

Lemma cond_approx_eq_trans n A P1 P2 P3 :
  cond_approx_eq n A P1 P2 ->
  cond_approx_eq n A P2 P3 ->
  cond_approx_eq n A P1 P3.
Proof.
  unfold cond_approx_eq in *.
  intros E1 E2 ts; rewrite E1, E2. reflexivity.
Qed.

Lemma cond_approx_eq_weakening n n' A P1 P2 :
  (n' <= n)%nat ->
  cond_approx_eq n A P1 P2 ->
  cond_approx_eq n' A P1 P2.
Proof.
  intros l.
  intros E ts; specialize (E ts).
  rewrite <-approx_oo_approx' with (n' := n) at 1; try lia.
  rewrite <-approx'_oo_approx with (n' := n) at 2; try lia.
  rewrite <-approx_oo_approx' with (n' := n) at 3; try lia.
  rewrite <-approx'_oo_approx with (n' := n) at 4; try lia.
  rewrite <-fmap_comp. unfold compose.
  rewrite E.
  reflexivity.
Qed.

Definition args_cond_approx_eq n A P1 P2 :=
  (forall ts,
      fmap (dependent_type_functor_rec ts (ArgsTT A)) (approx n) (approx n) (P1 ts) =
      fmap (dependent_type_functor_rec ts (ArgsTT A)) (approx n) (approx n) (P2 ts)).

Lemma args_cond_approx_eq_sym n A P1 P2 :
  args_cond_approx_eq n A P1 P2 ->
  args_cond_approx_eq n A P2 P1.
Proof.
  unfold args_cond_approx_eq; auto.
Qed.

Lemma args_cond_approx_eq_trans n A P1 P2 P3 :
  args_cond_approx_eq n A P1 P2 ->
  args_cond_approx_eq n A P2 P3 ->
  args_cond_approx_eq n A P1 P3.
Proof.
  unfold args_cond_approx_eq in *.
  intros E1 E2 ts; rewrite E1, E2. reflexivity.
Qed.

Lemma args_cond_approx_eq_weakening n n' A P1 P2 :
  (n' <= n)%nat ->
  args_cond_approx_eq n A P1 P2 ->
  args_cond_approx_eq n' A P1 P2.
Proof.
  intros l.
  intros E ts; specialize (E ts).
  rewrite <-approx_oo_approx' with (n' := n) at 1; try lia.
  rewrite <-approx'_oo_approx with (n' := n) at 2; try lia.
  rewrite <-approx_oo_approx' with (n' := n) at 3; try lia.
  rewrite <-approx'_oo_approx with (n' := n) at 4; try lia.
  rewrite <-fmap_comp. unfold compose.
  rewrite E.
  reflexivity.
Qed.

Lemma level_initial_core {F} ge G n : level (@initial_core F ge G n) = n.
Proof.
  apply level_make_rmap.
Qed.

(* func_at'': func_at without requiring a proof of non-expansiveness *)
Definition func_at'' fsig cc A P Q :=
  pureat (SomeP (SpecArgsTT A) (packPQ P Q)) (FUN fsig cc).