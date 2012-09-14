Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.Clight_lemmas.

Open Local Scope pred.

Obligation Tactic := idtac.
 
Program Definition allneg : pred rmap := fun r => forall l, identity (r @ l) \/ fst l < 0.
 Next Obligation.
  intro; intros.  destruct (H0 l); [left|right]; auto.
  apply (age1_resource_at_identity _ _ l H); auto.
 Qed.

Program Definition allpos : pred rmap := fun r => forall l, identity (r @ l) \/ fst l >= 0.
 Next Obligation.
  intro; intros.  destruct (H0 l); [left|right]; auto.
  apply (age1_resource_at_identity _ _ l H); auto.
 Qed.

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
  /\ nextblock m = nextblock m'.
Proof.
intros.
  unfold access_at, contents_at. simpl.
  destruct a; simpl in H;
  try (apply store_outside' in H; destruct H as [? [? ?]]; repeat split; auto; intros;
        try (extensionality loc; congruence)).
 inv H; auto.
  invSome.
  apply store_outside' in H2; destruct H2 as [? [? ?]]; repeat split; auto.
  extensionality; congruence.
Qed.

Lemma store_init_data_list_outside':
  forall F V (ge: Genv.t F V)  b il m p m',
  Genv.store_init_data_list ge m b p il = Some m' ->
  (forall b' ofs,
    (b=b' /\ p <= ofs < p + Genv.init_data_list_size il) \/
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
  remember (Genv.init_data_list_size il) as n.
  assert (n >= 0).
  subst n; clear; induction il; simpl; try omega.
  generalize (Genv.init_data_size_pos a); omega.
  clear il Heqn.
  apply store_init_data_outside' in H.
  generalize (Genv.init_data_size_pos a); intro.
  destruct H as [? [? ?]]; repeat split; auto.
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
apply store_init_data_list_outside' in H.
forget (Genv.init_data_list_size d) as N.
clear - H4  H3 Hb H.
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
inv H4.
symmetry in H4; apply core_not_YES in H4. contradiction.
(* case 1.2 *)
apply join_unit2_e in H4; auto.
clear m1 H3.
destruct H. contradiction.
rewrite H2; clear H2.
rewrite if_false; auto.
rewrite H4.
clear - H5 H7 H.
unfold initial_mem; simpl.
unfold inflate_initial_mem; simpl.
repeat rewrite resource_at_make_rmap.
unfold inflate_initial_mem'.
rewrite <- H5.
specialize (IOK (b',z')). simpl in IOK.
destruct (zlt b' 0).
pose proof (nextblock_noaccess m b' z' Cur).
unfold access_at.
simpl; rewrite H0.
admit.  (* trivial *)
left; omega.
rewrite <- H.
rewrite core_resource_at.
rewrite IOK by omega.
destruct (access_at m (b',z')); try destruct p; constructor;
   apply join_unit2; auto.

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

Lemma store_zeros_lem: 
  forall m b sz m',
        Genv.store_zeros m b sz = Some m' ->
     b > 0 ->
    forall w IOK IOK' P rsh,
     ((P * VALspec_range sz rsh Share.top (b,0))%pred
             (m_phi (initial_mem m w IOK))) ->
     ((P * VALspec_range sz rsh Share.top (b,0))%pred
              (m_phi (initial_mem m' w IOK'))).
Admitted.

Lemma drop_perm_writable_lem:
  forall m b lo hi m',
      drop_perm m b lo hi Writable = Some m' ->
    b > 0 ->
    forall w IOK IOK' P,
     ((P * VALspec_range (hi-lo) Share.top Share.top (b,lo))%pred
             (m_phi (initial_mem m w IOK))) ->
     ((P * VALspec_range (hi-lo) Share.bot Share.top (b,lo))%pred
              (m_phi (initial_mem m' w IOK'))).
Admitted.

Lemma drop_perm_readable_lem:
  forall m b lo hi m',
      drop_perm m b lo hi Readable = Some m' ->
    b > 0 ->
    forall w IOK IOK' P,
     ((P * VALspec_range (hi-lo) Share.top Share.top (b,lo))%pred
             (m_phi (initial_mem m w IOK))) ->
     ((P * VALspec_range (hi-lo) Share.bot (fst (Share.split Share.top)) (b,lo))%pred
              (m_phi (initial_mem m' w IOK'))).
Admitted.


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
constructor.
apply join_unit1; auto.
destruct (zle lo z'); simpl; auto.
destruct (zlt z' hi); simpl; auto.
contradiction H; split; auto. omega.
clear - IOK H0.
symmetry; apply IOK.
simpl. generalize (nextblock_pos m); subst; omega.
rewrite if_false by (contradict n; destruct n; auto).
destruct (zlt b' 0).
unfold access_at.
simpl.
rewrite nextblock_noaccess by omega.
rewrite nextblock_noaccess by omega.
admit.  (* trivial *)
change Join_rmap with R.Join_rmap.
change Sep_rmap with R.Sep_rmap.
rewrite (IOK (b',z')) by (simpl; auto).
replace (access_at m' (b',z')) with (access_at m (b',z')).
replace (contents_at m' (b',z')) with (contents_at m (b',z')).
destruct (access_at m (b',z')); try destruct p; constructor; auto.
unfold contents_at; inv H; simpl. rewrite ZMap.gso by auto. auto.
unfold access_at; inv H; simpl. rewrite ZMap.gso; auto.
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

Definition init_juicy_mem (F V: Type) (w: rmap) (IOK: initial_rmap_ok w) (prog: AST.program F V) : option juicy_mem :=
  match
     Genv.init_mem prog as o return (Genv.init_mem prog = o -> option juicy_mem) 
  with
  | Some m =>
      fun H : Genv.init_mem prog = Some m =>
       Some (initial_mem m w IOK)
  | None => fun _ : Genv.init_mem prog = None => None
  end (refl_equal _).

Lemma fold_right_rev_left:
  forall (A B: Type) (f: A -> B -> A) (l: list B) (i: A),
  fold_left f l i = fold_right (fun x y => f y x) i (rev l).
Proof.
intros. rewrite fold_left_rev_right.
f_equal; extensionality x y; auto.
Qed.

Definition initblocksize (V: Type)  (a: ident * globvar V)  : (ident * Z) :=
 match a with (id,l) => (id , Genv.init_data_list_size (gvar_init l)) end.

Lemma initblocksize_name: forall V a id n, initblocksize V a = (id,n) -> var_name V a = id.
Proof. destruct a; intros; simpl; inv H; auto.  Qed.

Lemma list_norepet_rev:
  forall A (l: list A), list_norepet (rev l) = list_norepet l.
Proof.
induction l; simpl; auto.
apply prop_ext; split; intros.
apply list_norepet_app in H.
destruct H as [? [? ?]].
rewrite IHl in H.
constructor; auto.
eapply list_disjoint_notin with (a::nil).
apply list_disjoint_sym; auto.
intros x y ? ? ?; subst.
contradiction (H1 y y); auto.
rewrite <- In_rev; auto.
simpl; auto.
rewrite list_norepet_app.
inv H.
split3; auto.
rewrite IHl; auto.
repeat constructor.
intro Hx. inv Hx.
intros x y ? ? ?; subst.
inv H0.
rewrite <- In_rev in H; contradiction.
auto.
Qed.

Lemma alloc_variables_app:
   forall F V (ge: Genv.t F V) m m2 vs vs',
  Genv.alloc_variables ge m (vs++vs') = Some m2 <->
    exists m', Genv.alloc_variables ge m vs = Some m' /\
                    Genv.alloc_variables ge m' vs' = Some m2.
Proof.
intros.
revert vs' m m2; induction vs; intros.
simpl.
intuition. exists m; intuition. destruct H as [? [H ?]]; inv H; auto.
simpl.
case_eq (Genv.alloc_variable ge m a); intros.
specialize (IHvs vs' m0 m2).
auto.
intuition; try discriminate.
destruct H0 as [? [? ?]]; discriminate.
Qed.

Fixpoint alloc_variables_rev {F V} (ge: Genv.t F V) (m: mem) (vl: list (ident * globvar V))
                         {struct vl} : option mem :=
  match vl with
  | nil => Some m
  | v :: vl' =>
     match alloc_variables_rev ge m vl' with
     | Some m' => Genv.alloc_variable ge m' v
     | None => None
     end
  end.

Lemma alloc_variables_rev_eq: 
     forall F V (ge: Genv.t F V) m vl,
     Genv.alloc_variables ge m (rev vl) = alloc_variables_rev ge m vl.
Proof.
intros.
revert m; induction vl; intros; auto.
simpl.
rewrite <- IHvl.
case_eq (Genv.alloc_variables ge m (rev vl)); intros.
case_eq (Genv.alloc_variable ge m0 a); intros.
rewrite alloc_variables_app.
exists m0; split; auto.
simpl. rewrite H0; auto.
case_eq (Genv.alloc_variables ge m (rev vl ++ a :: nil)); intros; auto.
elimtype False.
apply alloc_variables_app in H1.
destruct H1 as [m' [? ?]].
inversion2 H H1.
simpl in H2.
rewrite H0 in H2; inv H2.
case_eq (Genv.alloc_variables ge m (rev vl ++ a :: nil)); intros; auto.
elimtype False.
apply alloc_variables_app in H0.
destruct H0 as [m' [? ?]].
inversion2 H H0.
Qed.

Definition bump_nextvar {F V} (ge: Genv.t F V)  : Genv.t F V.
intros.
apply (@Genv.mkgenv F V
    ge.(Genv.genv_symb)
    ge.(Genv.genv_funs)
    ge.(Genv.genv_vars)
    ge.(Genv.genv_nextfun)
    (ge.(Genv.genv_nextvar) + 1)); intros; destruct ge; simpl in *; auto.
unfold block in *. omega.
destruct (genv_symb_range _ _ H); split; unfold block in*; omega.
eapply genv_funs_range; eauto.
destruct (genv_vars_range _ _ H); unfold block in *;omega.
apply genv_vars_inj with b; auto.
Defined.

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


Lemma disj_no_fun:
  forall (fs: list (AST.ident * fundef)) ids, 
       list_disjoint (map (@fst _ _) fs) ids ->
       forall i, In i ids ->
      (Genv.genv_symb (Genv.add_functions (Genv.empty_genv _ unit) fs)) ! i = None.
Proof.
intros. spec H i i.
assert (~In i (map (@fst _ _) fs)). intro. contradiction H; auto.
clear - H1; rename H1 into H0. unfold Genv.add_functions.
rewrite fold_right_rev_left. rewrite <- (rev_involutive fs). rewrite In_rev in H0.
rewrite <- map_rev in H0. remember (rev fs) as fs'; rewrite rev_involutive. clear - H0.
revert H0; induction fs'; simpl; intros.
rewrite Maps.PTree.gempty; auto. destruct a; simpl in *.
rewrite Maps.PTree.gso; [ | intro; subst; intuition]. 
apply IHfs'. contradict H0; auto.
Qed.

Lemma find_var_info_add_functions:
 forall F V b fs (ge: Genv.t F V), Genv.find_var_info (Genv.add_functions ge fs) b = Genv.find_var_info ge b.
Proof. induction fs; intros. simpl. auto. simpl.
rewrite IHfs. unfold Genv.add_function, Genv.find_var_info.
simpl. auto.
Qed.

Definition upto_block' (b: block) (w: rmap) :=
  fun loc => if zlt (fst loc) b then w @ loc else NO Share.bot.

Definition upto_block (b: block) (w: rmap) : rmap.
 refine (proj1_sig (make_rmap (upto_block' b w) _ (level w) _)).
Proof.
 intros b' z'.
 unfold compose, upto_block'.
 simpl. destruct (zlt b' b).
 apply rmap_valid.
  simpl. auto.
 extensionality loc;  unfold compose.
  unfold upto_block'.
 if_tac; [ | reflexivity ].
apply resource_at_approx.
Defined.

Definition beyond_block' (b: block) (w: rmap) :=
  fun loc => if zlt (fst loc) b then NO Share.bot else w @ loc.

Definition beyond_block (b: block) (w: rmap) : rmap.
 refine (proj1_sig (make_rmap (beyond_block' b w) _ (level w) _)).
Proof.
 intros b' z'.
 unfold compose, beyond_block'.
 simpl. destruct (zlt b' b). simpl; auto.
 apply rmap_valid.
 extensionality loc;  unfold compose.
  unfold beyond_block'.
 if_tac; [ reflexivity | ].
apply resource_at_approx.
Defined.



Lemma allocate_global_blocks:
  forall (prog: AST.program fundef type)
     (H: no_dups (prog_funct prog) (prog_vars prog))
     (w: rmap)
     (IOK: initial_rmap_ok w)
     m   (Hm: Genv.init_mem prog = Some m),
     forall rho,
          app_pred (writable_blocks (map (initblocksize _) prog.(prog_vars)) rho)
            (m_phi (initial_mem m w IOK)).
Proof.
intros.
destruct prog as [fs main vs].
simpl in H.
simpl.
hnf in IOK.
unfold no_dups in H.
rewrite list_norepet_app in H.
destruct H as [? [? ?]].
unfold Genv.init_mem, Genv.globalenv in Hm; simpl in Hm.
remember (Genv.add_functions (Genv.empty_genv fundef type) fs) as g.
assert (Genv.variables_initialized (Genv.add_variables g vs) (Genv.add_variables g vs) m).
eapply Genv.alloc_variables_initialized; try eassumption.
subst g; apply Genv.add_functions_nextvar.
subst g.
clear - H H0 H1.
hnf; intros.
elimtype False; clear - H2.
rewrite find_var_info_add_functions in H2.
unfold Genv.find_var_info,Genv.empty_genv in H2; simpl in H2.
rewrite ZMap.gi in H2. inv H2.
clear Hm.
remember vs as vtot.
rewrite Heqvtot.
remember (@nil (ident*globvar type)) as vr.
assert (vr++vs=vtot) by (subst; auto).
replace (inflate_initial_mem m w)
   with (beyond_block (1+ Z_of_nat (length vr)) (inflate_initial_mem m w)).
subst g.
assert (nextblock m = 1 + Z_of_nat (length vtot)).
admit.  (* easy enough *)
clear Heqvr Heqvtot.
revert vr H3; induction vs; intros.
simpl writable_blocks.
rewrite <- app_nil_end in H3. subst vr.
apply resource_at_empty2.
intros [b z].
unfold beyond_block.
rewrite resource_at_make_rmap.
unfold beyond_block'.
simpl fst.
if_tac.
apply NO_identity.
unfold inflate_initial_mem.
rewrite resource_at_make_rmap.
unfold inflate_initial_mem'.
unfold access_at. rewrite nextblock_noaccess.
rewrite <- core_resource_at. apply core_identity.
right. simpl.
rewrite H4; auto.
simpl writable_blocks.
case_eq (initblocksize type a); intros.
specialize (IHvs (vr++ (a::nil))).
rewrite app_ass in IHvs.
specialize (IHvs H3).
Admitted.  (* the rest of this is pretty straightforward *)
