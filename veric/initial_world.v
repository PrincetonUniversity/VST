Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.expr veric.expr_lemmas.

Open Local Scope pred.

Obligation Tactic := idtac.
 
Lemma adr_range_divide:
  forall b i p q loc, 
    p >= 0 -> q >= 0 -> (adr_range (b,i) (p+q) loc <-> (adr_range (b,i) p loc \/adr_range (b,i+p) q loc)).
Proof.
split; intros.
destruct loc as [b' z']; destruct H1.
assert (i <= z' < i+p \/ i+p <= z' < i+p+q)  by omega.
destruct H3; [left|right]; split; auto; omega.
destruct loc as [b' z']; destruct H1; destruct H1; split; auto; omega.
Qed.

Lemma VALspec_range_e:
  forall n rsh sh base m loc, VALspec_range n rsh sh base  m ->
                                adr_range base n loc -> 
                { x| m @ loc = YES rsh (mk_lifted sh (snd x)) (VAL (fst x)) NoneP}.
Proof.
intros.
spec H loc.
rewrite jam_true in H; auto.
simpl in H.
unfold compose in H.
rewrite approx_FF in H.
destruct (m @ loc); try destruct k; 
try solve [elimtype False; destruct H as [? [? ?]]; inv H].
assert (sh = pshare_sh p).
destruct H as [? [? ?]]; inv H.
simpl. auto.
subst sh.
exists (m0, proj2_sig p).
simpl.
destruct H as [? [? ?]]. 
destruct p.
simpl in *.
inv H.
auto.
Qed.


Lemma store_init_data_outside':
  forall F V (ge: Genv.t F V)  b a m p m',
  Genv.store_init_data ge m b p a = Some m' ->
  (forall b' ofs,
    (b=b' /\ p <= ofs < p + Genv.init_data_size a) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ access_at m = access_at m'
  /\ max_access_at m = max_access_at m'
  /\ nextblock m = nextblock m'.
Proof.
intros.
  unfold access_at, max_access_at, contents_at. simpl.
  destruct a; simpl in H;
  try (apply store_outside' in H; destruct H as [? [? ?]]; repeat split; auto; intros;
        try (extensionality loc; congruence)).
 inv H; auto.
  invSome.
  apply store_outside' in H2; destruct H2 as [? [? ?]]; repeat split; auto.
  extensionality; congruence.
  extensionality; congruence.
Qed.

Lemma store_init_data_list_outside':
  forall F V (ge: Genv.t F V)  b il m p m',
  Genv.store_init_data_list ge m b p il = Some m' ->
  (forall b' ofs,
    (b=b' /\ p <= ofs < p + Genv.init_data_list_size il) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ access_at m = access_at m'
  /\ max_access_at m = max_access_at m'
  /\ nextblock m = nextblock m'.
Proof.
  induction il; simpl; intros.
  inv H; auto.
  invSome.
  specialize (IHil _ _ _ H2).
  destruct IHil as [? [? [H1' ?]]].
  rewrite <- H3; rewrite <- H1; rewrite <- H1'; clear H3 H1 H1' H2. 
  remember (Genv.init_data_list_size il) as n.
  assert (n >= 0).
  subst n; clear; induction il; simpl; try omega.
  generalize (Genv.init_data_size_pos a); omega.
  clear il Heqn.
  apply store_init_data_outside' in H.
  generalize (Genv.init_data_size_pos a); intro.
  destruct H as [? [? [Hma ?]]]; repeat split; auto.
  clear H3 H4.
  intros. specialize (H0 b' ofs); specialize (H b' ofs).
  destruct H0.
  destruct H0; left; split; auto; omega.
  rewrite <- H0.
  destruct H.
  destruct H; left; split; auto; omega.
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
apply top_share_nonidentity.
Qed.

Lemma dec_pure: forall r, {exists k, exists pp, r = PURE k pp}+{core r = NO Share.bot}.
Proof.
 destruct r.
 right; apply core_NO.
 right; apply core_YES.
 left; eauto.
Qed.

Lemma store_init_data_list_lem: 
  forall F V (ge: Genv.t F V) m b lo d m',
        Genv.store_init_data_list ge m b lo d = Some m' ->
     b > 0 ->
    forall w IOK IOK' P rsh,
     ((P * VALspec_range (Genv.init_data_list_size d) rsh Share.top (b,lo))%pred
             (m_phi (initial_mem m w IOK))) ->
     ((P * VALspec_range (Genv.init_data_list_size d) rsh Share.top (b,lo))%pred
              (m_phi (initial_mem m' w IOK'))).
Proof.
intros until 1. intro Hb; intros.
destruct H0 as [m0 [m1 [H4 [H1 H2]]]].
cut (exists m2, 
         join m0 m2 (m_phi (initial_mem m' w IOK')) /\
         VALspec_range (Genv.init_data_list_size d) rsh Share.top (b,lo) m2); 
  [intros [m2 [H0 H3]] | ].
exists m0; exists m2; split3; auto.
rename H2 into H3.
clear -  Hb  H H4 H3.
assert (MA: max_access_at m = max_access_at m').
 clear - H.
 revert m lo H; induction d; simpl; intros. inv H; auto.
 invSome. apply IHd in H2. rewrite <- H2.
 clear - H.
 destruct a; simpl in H;
 try solve [apply store_access in H;  unfold max_access_at; rewrite H; auto].
 inv H; auto. 
 invSome. apply store_access in H2;  unfold max_access_at; rewrite H2; auto.
apply store_init_data_list_outside' in H.
forget (Genv.init_data_list_size d) as N.
clear - H4  H3 Hb H MA.
pose (f loc :=
   if adr_range_dec (b,lo) N loc
   then YES rsh pfullshare (VAL (contents_at m' loc)) NoneP
   else core (w @ loc)).
pose (H0 := True).
assert (Hv: CompCert_AV.valid (res_option oo f)).
  apply VAL_valid; unfold compose,f; simpl.
  intros ? ? ? Hx; repeat if_tac in Hx; inv Hx; auto.
  elimtype False; clear - H5.
  destruct (w @ l).
  rewrite core_NO in H5; inv H5.
  rewrite core_YES in H5; inv H5.
  rewrite core_PURE in H5; inv H5.
destruct (remake_rmap f Hv (level w)) as [m2 [? ?]]; clear Hv.
intros; unfold f, no_preds; simpl; intros; repeat if_tac; auto.
left. exists (core w). rewrite core_resource_at. rewrite level_core.  auto.
unfold f in *; clear f.
exists m2.
split.
(* case 1 of 3 ****)
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
intros [b' z']; apply (resource_at_join _ _ _ (b',z')) in H4; spec H b' z'.
spec H3 (b',z'). unfold jam in H3.
hnf in H3. if_tac in H3.
2: rename H6 into H8.
clear H. destruct H6 as [H H8].
(* case 1.1 *)
subst b'.
destruct H3 as [v [p H]].
rewrite H in H4.
repeat rewrite preds_fmap_NoneP in H4.

inv H4; [ | pfullshare_join].
clear H6 m0.
rename H13 into H4.
rewrite H2.
rewrite if_true  by (split; auto; omega).
replace (mk_lifted Share.top p) with pfullshare in H4.
2: apply lifted_eq; auto.
clear - H4 H5 H7 Hb RJ.
replace (m_phi (initial_mem m' w IOK') @ (b, z'))
  with (YES rsh3 pfullshare (VAL (contents_at m' (b, z'))) NoneP); [ constructor |].
auto.
revert H4.
simpl; unfold inflate_initial_mem.
repeat rewrite resource_at_make_rmap. unfold inflate_initial_mem'.
rewrite <- H5.
case_eq (access_at m (b,z')); intros; auto.
destruct p; auto;
try solve [f_equal; apply YES_inj in H4; congruence].
destruct (w @ (b,z')); inv H4.
inv H4.
(* case 1.2 *)
apply join_unit2_e in H4; auto.
clear m1 H3.
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
rewrite core_NO.
destruct (access_at m (b', z')); try destruct p; try constructor; auto.
rewrite core_YES.
destruct (access_at m (b', z')); try destruct p1; try constructor; auto.
destruct IOK2 as [? [? ?]].
rewrite H2. rewrite core_PURE; constructor.

(**** case 2 of 3 ****)
intro loc.
spec H3 loc.
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

Lemma mem_alloc_juicy:
  forall m lo hi m' b,
     Mem.alloc m lo hi = (m',b) ->
    forall w P IOK IOK',
     (app_pred P (m_phi (initial_mem m w IOK))) ->
     (app_pred (P * VALspec_range (hi-lo) Share.top Share.top (b,lo))
               (m_phi (initial_mem m' w IOK'))).
Proof.
intros.
change m with (m_dry (initial_mem m w IOK)) in H.
assert (AV.valid  (res_option oo (fun loc => if adr_range_dec (b,lo) (hi-lo) loc
                                      then YES Share.top pfullshare (VAL Undef) NoneP
                                      else core w @ loc))).
apply VAL_valid; unfold compose; intros.
if_tac in H1. inv H1; eauto.
elimtype False; revert H1; clear; rewrite <- core_resource_at.
destruct (w @ l); simpl; [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; intro H; inv H.
destruct (make_rmap _ H1 (level w)) as [phi [? ?]].
extensionality loc; unfold compose; if_tac.
unfold resource_fmap. f_equal. apply preds_fmap_NoneP.
rewrite <- level_core.  apply resource_at_approx.
exists (m_phi (initial_mem m w IOK)); exists phi; split3; auto.
apply resource_at_join2.
simpl. unfold inflate_initial_mem. do 2 rewrite level_make_rmap. auto.
simpl. unfold inflate_initial_mem. rewrite level_make_rmap. auto.
intro.
simpl.
unfold inflate_initial_mem.
do 2 rewrite resource_at_make_rmap.
rewrite H3; clear H3 H1 H0.
unfold inflate_initial_mem'.
destruct loc as [b' z'].
destruct (eq_dec b b').
subst b'.
pose proof (alloc_result _ _ _ _ _ H).
simpl in H0. 
unfold access_at at 1.
simpl.
rewrite (nextblock_noaccess) by (subst; omega).
unfold access_at.
simpl.
change R.rmap with rmap in *.
change R.Join_rmap with Join_rmap in *.
change R.Sep_rmap with Sep_rmap in *.
replace (core w @ (b,z')) with (NO Share.bot).
Transparent alloc.
replace (match max_access_at m (b, z') with
  | Some _ => NO Share.bot
  | None => NO Share.bot
  end) with (NO Share.bot) by (destruct (max_access_at m (b, z')); auto).
replace (match max_access_at m' (b, z') with
  | Some _ => NO Share.bot
  | None => NO Share.bot
  end) with (NO Share.bot) by (destruct (max_access_at m' (b, z')); auto).
unfold contents_at.
inv H.
simpl.
rewrite ZMap.gss.
rewrite ZMap.gss.
rewrite ZMap.gi.
if_tac.
destruct H.
destruct H0.
destruct (zle lo z'); [ | omegaContradiction].
destruct (zlt z' hi); [ | omegaContradiction].
simpl.
constructor.
apply join_unit1; auto.
replace (zle lo z' && zlt z' hi)%bool with false.

simpl.
constructor.
apply join_unit1; auto.
destruct (zle lo z'); simpl; auto.
destruct (zlt z' hi); simpl; auto.
contradiction H; split; auto. omega.
clear - IOK H0.
symmetry; apply IOK.
simpl. generalize (nextblock_pos m); subst; omega.
rewrite if_false by (contradict n; destruct n; auto).
replace (access_at m' (b',z')) with (access_at m (b',z')).
replace (contents_at m' (b',z')) with (contents_at m (b',z')).
rewrite <- core_resource_at.
case_eq (w @ (b',z')); intros.
rewrite core_NO.
destruct (access_at m (b', z')).
destruct p; constructor; auto.
destruct (max_access_at m (b', z')); destruct (max_access_at m' (b', z')); constructor; auto.
rewrite core_YES.
destruct (access_at m (b', z')).
destruct p1; constructor; auto.
destruct (max_access_at m (b', z')); destruct (max_access_at m' (b', z')); constructor; auto.
rewrite core_PURE.
destruct (IOK (b',z')).
rewrite H0 in H3. destruct H3 as [? [? ?]].
rewrite H4. constructor.
unfold contents_at; inv H; simpl; auto.
rewrite ZMap.gso; auto.
unfold access_at; inv H; simpl; auto.
rewrite ZMap.gso; auto.

intros (b',z').
hnf.
unfold yesat.
simpl. rewrite H3.
if_tac.
exists Undef. exists top_share_nonunit.
f_equal.
unfold NoneP.
f_equal. extensionality z. unfold compose. rewrite approx_FF. auto.
rewrite <- core_resource_at.
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
 match a with (id,l) => (id , Genv.init_data_list_size (gvar_init l)) end.

Lemma initblocksize_name: forall V a id n, initblocksize V a = (id,n) -> fst a = id.
Proof. destruct a; intros; simpl; inv H; auto.  Qed.

Fixpoint find_id (id: ident) (G: funspecs) : option funspec  :=
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

Lemma find_id_i:
  forall id fs G, 
            In (id,fs) G ->
             list_norepet (map (@fst _ _) G) ->
                  find_id id G = Some fs.
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

Lemma find_id_e: 
   forall id G fs, find_id id G = Some fs -> In (id,fs) G.
Proof.
 induction G; simpl; intros. inv H. destruct a. if_tac in H.
 inv H; subst; auto. right; apply (IHG fs); auto.
Qed.

Definition initial_core' (ge: Genv.t fundef type) (G: funspecs) (n: nat) (loc: address) : resource :=
   if eq_dec (snd loc) 0
   then match Genv.invert_symbol ge (fst loc) with
           | Some id => 
                  match find_id id G with
                  | Some (mk_funspec fsig A P Q) => 
                           PURE (FUN fsig) (SomeP (A::boolT::environ::nil) (approx n oo packPQ P Q))
                  | None => NO Share.bot
                  end
           | None => NO Share.bot
          end
   else NO Share.bot.


Program Definition initial_core (ge: Genv.t fundef type) (G: funspecs) (n: nat) : rmap :=
  proj1_sig (make_rmap (initial_core' ge G n) _ n _).
Next Obligation.
intros.
intros ? ?.
unfold compose.
unfold initial_core'.
if_tac; simpl; auto.
destruct (Genv.invert_symbol ge b); simpl; auto.
destruct (find_id i G); simpl; auto.
destruct f; simpl; auto.
Qed.
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
change R.approx with approx.
rewrite <- compose_assoc.
 rewrite approx_oo_approx.
auto.
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

Definition prog_funct (p: program) := prog_funct' (prog_defs p).

Definition match_fdecs (fdecs: list (ident * fundef)) (G: funspecs) :=
 map (fun idf => (fst idf, Clight.type_of_fundef (snd idf))) fdecs = 
 map (fun idf => (fst idf, type_of_funspec (snd idf))) G.


Lemma match_fdecs_exists_Gfun: 
  forall prog G i f, 
    find_id i G = Some f -> 
    match_fdecs (prog_funct prog) G ->
    exists fd,   In (i, Gfun fd) (prog_defs prog).
Proof. unfold prog_funct. unfold prog_defs_names.
intros ? ? ?.
forget (prog_defs prog) as dl.
revert G; induction dl; intros.
destruct G; inv H. inv H0.
destruct a.
destruct g; simpl in *.
destruct G; inv H0.
destruct p. simpl in *.
if_tac in H. subst i0; inv H.
eexists; left; reflexivity.
destruct (IHdl _ _ H H4).
exists x; right; auto.
destruct (IHdl G f); auto.
exists x; right; auto.
Qed.

Lemma find_symbol_add_globals:
  forall {F V} i g id dl, ~ In i (map fst dl) -> list_norepet (map fst dl) ->
   (Genv.find_symbol
      (Genv.add_globals (Genv.empty_genv F V) (dl ++ (i, g) :: nil)) id =
          Some (1 + Zlength dl) <-> i = id).
Proof.
intros.
  assert (Genv.genv_next (Genv.empty_genv F V) = 1)  by reflexivity.
  assert (Genv.find_symbol (Genv.empty_genv F V)  id = None) by (intros; apply PTree.gempty).
 forget (Genv.empty_genv F V) as ge. forget 1 as n. 
  revert ge n H H0 H1 H2; induction dl; intros.
        simpl. rewrite Zlength_nil.
        unfold Genv.find_symbol, Genv.add_global in *; simpl.
        destruct (eq_dec i id); subst. rewrite PTree.gss.         intuition.
        rewrite PTree.gso by auto. rewrite H2.  split; intro Hx; inv Hx; congruence.
        simpl; auto.
        rewrite Zlength_cons. 
        replace (n + Zsucc (Zlength dl)) with (Zsucc n + Zlength dl) by omega.
        simpl. simpl in H0. inv H0.
         simpl in H.
         destruct a as [a ag]; simpl in *.
          assert (a<>i /\ ~ In i (map fst dl)) by (clear - H; intuition). clear H; destruct H0.
         destruct (eq_dec id a).
         subst id.
         split; intro; try congruence. elimtype False.
         clear IHdl.
        assert (~In a (map fst ((dl++(i,g)::nil)))).
            rewrite map_app. rewrite in_app_iff.
          intros [?|?]; try contradiction. simpl in H3. destruct H3; try congruence.
         forget   (dl ++ (i, g) :: nil) as vl.
         assert (Genv.find_symbol (Genv.add_global ge (a,ag)) a = Some (Genv.genv_next ge)).
        unfold Genv.find_symbol, Genv.add_global; simpl. rewrite PTree.gss; auto.
        forget (Genv.add_global ge (a,ag)) as ge1.
        forget (Genv.genv_next ge) as N; clear ge H2.
         assert (Zsucc N + Zlength dl > N).
         rewrite Zlength_correct; unfold block in *; omega.
         forget (Zsucc N + Zlength dl) as K.
         clear - H1 H3 H2 H4.
         revert ge1 K H2 H1 H3 H4; induction vl; simpl; intros. 
        inversion2 H1 H4; omega.
         apply (IHvl (Genv.add_global ge1 a0) K H2); auto.
        unfold Genv.find_symbol, Genv.add_global in H4|-*; simpl in *.
        rewrite PTree.gso; auto. 
         apply IHdl; auto.
        unfold Genv.find_symbol, Genv.add_global in H2|-*; simpl.
                 rewrite PTree.gso; auto.
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
  intros. revert al H; induction j; destruct al; simpl; intros; auto; try omegaContradiction.
   apply IHj. omega.
Qed.

Lemma nth_error_rev:
  forall T (vl: list T) (n: nat),
   (n < length vl)%nat -> 
  nth_error (rev vl) n = nth_error vl (length vl - n - 1).
Proof.
 induction vl; simpl; intros. apply nth_error_nil.
 destruct (eq_dec n (length vl)).
 subst.
 pattern (length vl) at 1; rewrite <- rev_length.
 rewrite <- (plus_0_r (length (rev vl))).
 rewrite nth_error_app.
 case_eq (length vl); intros. simpl. auto.
 replace (S n - n - 1)%nat with O by omega.
 simpl; auto.
 rewrite nth_error_app1 by (rewrite rev_length; omega).
 rewrite IHvl by omega. clear IHvl.
 destruct n; destruct (length vl). congruence.
 simpl. replace (n-0)%nat with n by omega; auto.
 omegaContradiction.
 replace (S n1 - n - 1)%nat with (S (S n1 - S n - 1))%nat by omega.
 reflexivity.
Qed.

Lemma Zlength_app: forall T (al bl: list T),
    Zlength (al++bl) = Zlength al + Zlength bl.
Proof. induction al; intros. simpl app; rewrite Zlength_nil; omega.
 simpl app; repeat rewrite Zlength_cons; rewrite IHal; omega.
Qed.
Lemma Zlength_rev: forall T (vl: list T), Zlength (rev vl) = Zlength vl.
Proof. induction vl; simpl; auto. rewrite Zlength_cons. rewrite <- IHvl.
rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil; omega.
Qed.

Lemma Zlength_map: forall A B (f: A -> B) l, Zlength (map f l) = Zlength l.
Proof. induction l; simpl; auto. repeat rewrite Zlength_cons. f_equal; auto.
Qed.

Lemma add_globals_hack:
   forall vl gev,
    list_norepet (map fst vl) ->
    gev = Genv.add_globals (Genv.empty_genv fundef type) (rev vl) ->

   (forall id b, 0 <= b-1 < Zlength vl ->
                           (Genv.find_symbol gev id = Some b <->
                            nth_error (map (@fst _ _) vl) (length vl - nat_of_Z b)  = Some id)).
Proof. intros. subst.
     apply iff_trans with (nth_error (map fst (rev vl)) (nat_of_Z (b - 1)) = Some id).
Focus 2. rewrite map_rev; rewrite nth_error_rev.
             replace (length (map fst vl) - nat_of_Z (b - 1) - 1)%nat 
                        with (length vl - nat_of_Z b)%nat ; [intuition | ].
  rewrite map_length.
  transitivity (length vl - (nat_of_Z (b-1)+1))%nat; try omega.
  f_equal.
  change (nat_of_Z b = (nat_of_Z (b - 1) + nat_of_Z 1)%nat).
  rewrite <- nat_of_Z_plus by omega.
  f_equal. omega.
  rewrite map_length.
  rewrite Zlength_correct in H1.
  forget (b-1) as i; forget (length vl) as n; clear - H1.
  apply inj_lt_rev. rewrite nat_of_Z_max; auto. rewrite Zmax_spec. if_tac; omega.
    rename H1 into Hb; revert H; induction vl; simpl; intros;
       try rewrite Zlength_nil in *.
      unfold Genv.find_symbol; simpl. rewrite PTree.gempty.
     intuition. 
       destruct a. inv H. rewrite Zlength_cons in Hb.
       destruct (eq_dec (b-1) (Zlength vl)).
        clear IHvl Hb. rewrite e. rewrite Zlength_correct. rewrite nat_of_Z_of_nat.
        replace b with (1+ (Zlength vl)) by omega. clear e b.
        rewrite <- Zlength_rev. rewrite <- rev_length.
         replace (length (rev vl)) with (length (rev vl) + 0)%nat by omega.
         rewrite map_app. rewrite <- map_length with (f:=@fst ident (globdef fundef type)).
        rewrite nth_error_app. 
        apply iff_trans with (i=id); [ | simpl; split; intro; subst; auto; inv H; auto].
        rewrite In_rev in H2. rewrite <- map_rev in H2.
       rewrite <- list_norepet_rev in H3. rewrite <- map_rev in H3.
         forget (rev vl) as dl. 
     apply find_symbol_add_globals; auto.   
        spec IHvl ; [ omega |].
      specialize (IHvl H3).
      rewrite Genv.add_globals_app.
      unfold Genv.add_globals at 1. simpl.
        unfold Genv.find_symbol.
       unfold Genv.add_global; simpl. 
      destruct (eq_dec id i). subst i. rewrite PTree.gss.
      rewrite Genv.genv_next_add_globals. rewrite <- Zlength_correct. simpl Genv.genv_next.
     rewrite map_app.
     rewrite In_rev in H2. rewrite <- map_rev in H2.
     split; intro.
     assert (b=1+Zlength (rev vl)) by congruence. clear H; subst b.

 elimtype False; clear - n; rewrite Zlength_rev in n; omega.
 f_equal.
 elimtype False.
  assert (b-1 >= 0) by (clear - Hb; omega).
 pose proof (Coqlib.nat_of_Z_eq _ H0).
 clear - H1 H H2 n.
 rewrite Zlength_correct in n. apply n. clear n.
 rewrite <- H1.
 f_equal. clear - H H2.
 forget (nat_of_Z (b-1)) as j.
 replace (length vl) with (length (map fst (rev vl)))
   by (rewrite map_length; rewrite rev_length; auto).
 forget (map fst (rev vl)) as al.
 revert al H2 H; clear; induction j; destruct al; simpl; intros; auto. inv H; intuition.
 elimtype False; clear - H; induction j; inv H; auto.
 f_equal. apply IHj; auto.

    rewrite PTree.gso by auto. 
  rewrite map_app.
  destruct IHvl.
  split; intro. apply H in H1. rewrite nth_error_app1; auto.
  clear - n Hb. rewrite map_length. rewrite rev_length. rewrite Zlength_correct in Hb,n.
  assert (b-1>=0) by omega.
 pose proof (Coqlib.nat_of_Z_eq _ H).
  forget (nat_of_Z(b-1)) as j. rewrite <- H0 in *.
   destruct Hb. clear - H2 n. omega. 
  assert (nat_of_Z (b-1) < length (map (@fst _ _) (rev vl)))%nat.
    clear - Hb n H1.
  rewrite Zlength_correct in n. rewrite map_length; rewrite rev_length.
  assert (nat_of_Z (b-1) <> length vl).
  contradict n. rewrite <- n.
  rewrite Coqlib.nat_of_Z_eq; auto. omega.
  forget (nat_of_Z (b-1)) as j.
  clear - H1 H.
  assert (S (length vl) = length (map fst (rev vl) ++ map fst ((i, g) :: nil))).
  simpl. rewrite app_length; rewrite map_length; rewrite rev_length; simpl; omega.
  assert (j < S (length vl))%nat; [ | omega].
  rewrite H0. forget (map fst (rev vl) ++ map fst ((i, g) :: nil)) as al.
  clear - H1. revert al H1; induction j; destruct al; simpl in *; intros; inv H1; auto; try omega.
  specialize (IHj _ H0); omega.
  rewrite nth_error_app1 in H1 by auto.
  apply H0 in H1. auto.
Qed.

Lemma find_symbol_globalenv:
  forall (prog: program) i b,
   list_norepet (prog_defs_names prog) ->
  Genv.find_symbol (Genv.globalenv prog) i = Some b ->
  0 < b <= Z_of_nat (length (prog_defs prog)) /\
  exists d, nth_error (prog_defs prog) (nat_of_Z (b-1)) = Some (i,d).
Proof.
intros.
unfold Genv.globalenv in H0.
assert (RANGE: 0 <= b - 1 < Zlength (rev (prog_defs prog))).
 rewrite <- (rev_involutive (prog_defs prog)) in H0.
 clear - H0.
 revert H0; induction (rev (prog_defs prog)); simpl; intros.
 unfold Genv.find_symbol in H0. simpl in H0. rewrite PTree.gempty in H0; inv H0.
 rewrite Genv.add_globals_app in H0.
 simpl in H0. destruct a.
 destruct (eq_dec i0 i). subst.
 unfold Genv.add_global, Genv.find_symbol in H0. simpl in H0.
 rewrite PTree.gss  in H0. inv H0.
 clear.
 split. pose proof (Genv.genv_next_pos  (Genv.add_globals (Genv.empty_genv fundef type) (rev l))).
 omega.
 rewrite Zlength_cons.
 induction l. simpl. omega.
 rewrite Zlength_cons. simpl. rewrite Genv.add_globals_app.
 simpl. omega.
 unfold Genv.add_global, Genv.find_symbol in IHl, H0. simpl in H0.
 rewrite PTree.gso in H0 by auto.
 apply IHl in H0.
 rewrite Zlength_cons. omega.
 (* end assert RANGE *)
 split.
 rewrite Zlength_correct in RANGE.
 rewrite rev_length in RANGE. omega.
 rewrite <- list_norepet_rev in H. unfold prog_defs_names in H.
rewrite <- map_rev in H.
rewrite add_globals_hack in H0; [ | apply H | rewrite rev_involutive; auto | auto ].
rewrite map_rev in H0.
 rewrite nth_error_rev in H0.
 rewrite list_map_nth in H0.
 revert H0; 
 case_eq  (nth_error (prog_defs prog)
          (length (map fst (prog_defs prog)) -
           (length (rev (prog_defs prog)) - nat_of_Z b) - 1)); intros.
 destruct p; simpl in H1. inv H1.
 exists g.
 rewrite <- H0. f_equal.
 rewrite rev_length. rewrite map_length.
 clear - RANGE.
 rewrite Zlength_rev in RANGE. rewrite Zlength_correct in RANGE.
 rewrite <- (Coqlib.nat_of_Z_eq b) in * by omega.
 forget (nat_of_Z b) as n. clear b.
 rewrite nat_of_Z_of_nat.
 replace (Z_of_nat n - 1) with (Z_of_nat (n-1)) by (rewrite inj_minus1 by omega; f_equal; auto).
 rewrite nat_of_Z_of_nat.
 omega.
 inv H1.
 rewrite rev_length. rewrite map_length.
 clear - RANGE. rewrite Zlength_correct in RANGE.
 rewrite rev_length in RANGE. 
 forget (length (prog_defs prog)) as N.
 assert (Z_of_nat N > 0) by omega.
 destruct N; inv H.
 assert (nat_of_Z b > 0)%nat; [| omega].
 assert (b>0) by omega. clear - H.
 change O with (nat_of_Z 0).
 apply inj_gt_iff.
 rewrite Coqlib.nat_of_Z_eq by omega.
 rewrite Coqlib.nat_of_Z_eq by omega.
 auto.
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
elimtype False.
apply alloc_globals_app in H1.
destruct H1 as [m' [? ?]].
inversion2 H H1.
simpl in H2.
rewrite H0 in H2; inv H2.
case_eq (Genv.alloc_globals ge m (rev vl ++ a :: nil)); intros; auto.
elimtype False.
apply alloc_globals_app in H0.
destruct H0 as [m' [? ?]].
inversion2 H H0.
Qed.

Lemma alloc_globals_rev_nextblock:
  forall {F V} (ge: Genv.t F V) vl m, alloc_globals_rev ge empty vl = Some m ->
     nextblock m = Zsucc (Zlength vl).
Proof. 
  intros.
   revert m H; induction vl; simpl; intros. inv H; apply nextblock_empty.
  invSome. apply IHvl in H.
  apply Genv.alloc_global_nextblock in H2.  rewrite Zlength_cons. rewrite H2.
  rewrite H. auto.
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
 if_tac in e0; inv e0. unfold max_access_at; simpl. auto.
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
 if_tac in e0; inv e0. unfold access_at; simpl. auto.
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
 if_tac in e0; inv e0. unfold contents_at; simpl. rewrite ZMap.gso by auto. auto.
 eapply IHR_store_zeros; eauto.
Qed.


Lemma alloc_global_old:
  forall {F V} (ge: Genv.t F V) m iv m', Genv.alloc_global ge m iv = Some m' ->
       forall loc, fst loc < nextblock m ->
        access_at m loc = access_at m' loc 
        /\ max_access_at m loc = max_access_at m' loc 
       /\ contents_at m loc = contents_at m' loc.
Proof.
 intros.
 destruct loc as [b ofs]; simpl in *; subst.
 assert (NEQ: b <> nextblock m) by (intro Hx; inv Hx; omega).
 unfold Genv.alloc_global in H. destruct iv.
 destruct g.
 revert H; case_eq (alloc m 0 1); intros.
 unfold drop_perm in H1. 
 destruct (range_perm_dec m0 b0 0 1 Cur Freeable); inv H1.
 unfold contents_at, max_access_at, access_at in *; 
 simpl in *.
 Transparent alloc. unfold alloc in H. Opaque alloc.
 inv H; simpl in *.
 rewrite ZMap.gss. repeat rewrite (ZMap.gso _ _ NEQ). auto.

 forget (Genv.init_data_list_size (gvar_init v)) as N.
 revert H; case_eq (alloc m 0 N); intros.
 invSome. invSome.
  Transparent alloc. unfold alloc in H. Opaque alloc.
  assert (access_at m (b,ofs) = access_at m0 (b,ofs) 
          /\ max_access_at m (b,ofs) = max_access_at m0 (b,ofs) 
          /\ contents_at m (b,ofs) = contents_at m0 (b,ofs)).
 clear - H NEQ.
 inv H; 
 unfold contents_at, access_at, max_access_at in *; 
 simpl in *.
 repeat rewrite (ZMap.gso _ _ NEQ). auto.
 assert (b0=nextblock m) by (inv H; auto). subst b0.
 destruct H2  as [H2a [H2b H2c]]; rewrite H2a,H2b, H2c; clear H H2a H2b H2c.
 rewrite <- (store_zeros_access _ _ _ _ _ H1).
 rewrite <- (store_zeros_max_access _ _ _ _ _ H1).
 apply store_zeros_contents1 with (loc:= (b,ofs)) in H1.
 2: simpl; congruence. rewrite H1; clear H1 m0.
 apply store_init_data_list_outside' in H4.
 destruct H4 as [? [? [Hma ?]]].
 specialize (H b ofs).  destruct H.
 destruct H; subst; congruence. unfold block in *; rewrite H; rewrite H1; rewrite Hma.
 clear - H5 NEQ.
 unfold drop_perm in H5.
 destruct (range_perm_dec m2 (nextblock m) 0 N Cur Freeable); inv H5.
 unfold contents_at, access_at, max_access_at in *; 
 simpl in *.
  repeat rewrite (ZMap.gso _ _ NEQ). auto.
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
if_tac; [ | rewrite core_NO; auto].
case_eq (Genv.invert_symbol (Genv.globalenv prog) b); intros;  [ | rewrite core_NO; auto].
case_eq (find_id i G); intros; [ | rewrite core_NO; auto].
apply Genv.invert_find_symbol in H2.
pose proof (Genv.find_symbol_not_fresh _ _ Hm H2).
unfold valid_block in H4.
split; intros.
contradiction.
destruct (match_fdecs_exists_Gfun _ _ _ _ H3 H0) as [fd ?].
destruct f.
split; auto.
subst z.
destruct (find_symbol_globalenv _ _ _ H H2) as [RANGE [d ?]].
assert (d = Gfun fd).
clear - H H5 H1.
unfold prog_defs_names in H.
forget (prog_defs prog) as dl. forget (nat_of_Z (b-1)) as n.
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
forget (prog_defs prog) as dl.
rewrite <- (rev_involutive dl) in H1,Hm.
rewrite nth_error_rev in H1.
Focus 2.
rewrite rev_length. clear - RANGE.
destruct RANGE.
apply inj_lt_iff. rewrite Coqlib.nat_of_Z_eq by omega. omega.
rename H1 into H5.
replace (length (rev dl) - nat_of_Z (b - 1) - 1)%nat
 with (length (rev dl) - nat_of_Z b)%nat in H5.
Focus 2. rewrite rev_length.
clear - RANGE.
replace (nat_of_Z (b-1)) with (nat_of_Z b - 1)%nat.
assert (nat_of_Z b <= length dl)%nat.
destruct RANGE.
apply inj_le_iff. rewrite Coqlib.nat_of_Z_eq by omega. auto.
assert (nat_of_Z b > 0)%nat. apply inj_gt_iff.
rewrite Coqlib.nat_of_Z_eq by omega.  simpl. omega.
omega. destruct RANGE as [? _].
apply nat_of_Z_lem1. 
assert (nat_of_Z b > 0)%nat. apply inj_gt_iff. simpl.
rewrite Coqlib.nat_of_Z_eq by omega. omega.
omega.
assert (0 < nat_of_Z b <= length dl)%nat.
clear - RANGE.
destruct RANGE; split.
apply inj_lt_iff. simpl; rewrite Coqlib.nat_of_Z_eq; omega.
apply inj_le_iff. simpl; rewrite Coqlib.nat_of_Z_eq; omega.
rewrite <- (Coqlib.nat_of_Z_eq b) in H2|-* by omega.
clear RANGE; rename H0 into RANGE.
forget (nat_of_Z b) as b'; clear b; rename b' into b.
rewrite <- rev_length in RANGE.
forget (rev dl) as dl'; clear dl; rename dl' into dl.
destruct RANGE.
rewrite alloc_globals_rev_eq in Hm.
revert m Hm H1 H5; induction dl; intros.
inv H5.
simpl in H1,Hm.
invSome.
specialize (IHdl _ Hm).
destruct (eq_dec b (S (length dl))).
rewrite e, minus_diag in H5. simpl in H5.
inversion H5; clear H5; subst a.
apply alloc_globals_rev_nextblock in Hm.
rewrite Zlength_correct in Hm.
rewrite <- inj_S in Hm. rewrite <- e in Hm. rewrite <- Hm in H2. 
clear IHdl H1 H0. subst b. rewrite <- Hm.
clear dl Hm.
unfold Genv.alloc_global in H6.
revert H6; case_eq (alloc m0 0 1); intros.
unfold drop_perm in H6.
destruct (range_perm_dec m1 b 0 1 Cur Freeable).
unfold access_at, max_access_at; inv H6.
simpl. apply alloc_result in H0. subst b.
rewrite ZMap.gss.
simpl. auto.
inv H6.
destruct IHdl.
omega.
replace (length (a::dl) - b)%nat with (S (length dl - b))%nat in H5.
apply H5.
simpl. destruct b; omega.
assert (Z_of_nat b < nextblock m0).
apply alloc_globals_rev_nextblock in Hm.
rewrite Zlength_correct in Hm. clear - Hm n H1.
rewrite Hm.
omega.
destruct (alloc_global_old _ _ _ _ H6 (Z_of_nat b,0)) as [? [? ?]]; auto.
rewrite <- H9. rewrite <- H8.
split; auto.
Qed.

Definition initial_jm (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G) : juicy_mem :=
  initial_mem m (initial_core (Genv.globalenv prog) G n)
           (initial_core_ok _ _ _ m H1 H2 H).



Fixpoint prog_vars' {F V} (l: list (ident * globdef F V)) : list (ident * globvar V) :=
 match l with nil => nil | (i,Gvar v)::r => (i,v):: prog_vars' r | _::r => prog_vars' r
 end.

Definition prog_vars (p: program) := prog_vars' (prog_defs p).

