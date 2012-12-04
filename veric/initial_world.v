Load loadpath.
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
assert (MA: max_access_at m = max_access_at m').
 clear - H.
 admit. 
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

Lemma store_zeros_lem: 
  forall m b sz m',
        Genv.store_zeros m b 0 sz = Some m' ->
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
clear - H5 H Hm.
unfold Genv.init_mem in Hm.
admit.
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

