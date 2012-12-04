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
Require Import veric.Clight_new.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.Clight_lemmas.
Require Import veric.initial_world.



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


Lemma rev_prog_vars': forall {F V} vl, rev (@prog_vars' F V vl) = prog_vars' (rev vl).
Proof.
   intros.
   induction vl. simpl; auto.
   destruct a. destruct g.
   simpl. rewrite IHvl.
   clear. induction (rev vl); simpl; intros; auto. destruct a; destruct g; simpl; auto.
    rewrite IHl. auto.
   simpl.
   transitivity (prog_vars' (rev vl) ++ (@prog_vars' F V ((i,Gvar v)::nil))).
    rewrite IHvl. f_equal.
    simpl.
    clear.
    induction (rev vl); simpl; intros; auto.
    destruct a. destruct g.
    auto.
    rewrite <- IHl.
    simpl. auto.
Qed.

Lemma writable_blocks_rev:
  forall rho l, writable_blocks l rho = writable_blocks (rev l) rho.
Proof.
induction l; simpl; auto.
destruct a.
rewrite writable_blocks_app.
rewrite <- IHl.
simpl.
rewrite sepcon_emp.
apply sepcon_comm.
Qed.

Lemma add_variables_nextblock:
  forall F V vl (ge: Genv.t F V) i g ul, list_norepet (map (@fst _ _) (vl++(i,g)::ul)) ->
   Genv.find_symbol (Genv.add_globals ge (vl++(i,g)::ul)) i = 
          Some (Genv.genv_next ge + Z_of_nat (length vl)).
Proof.
Admitted.


Lemma global_initializers:
  forall prog G m n,
     list_norepet (prog_defs_names prog) ->
    match_fdecs (prog_funct prog) G ->
    Genv.init_mem prog = Some m ->
     app_pred 
      (writable_blocks (map (initblocksize type) (prog_vars prog))
          (base.empty_environ (Genv.globalenv prog)))
  (inflate_initial_mem m (initial_core (Genv.globalenv prog) G n)).
Proof.
 intros until n. intros ? SAME_IDS ?.
 assert (IOK: initial_rmap_ok m (initial_core (Genv.globalenv prog) G n))
      by (apply initial_core_ok; auto).
  unfold Genv.init_mem in H0.
  unfold Genv.globalenv in *.
  destruct prog as [fl main vl].
  simpl in *.
  remember (Genv.add_globals (Genv.empty_genv fundef type) fl) as gev.
  rewrite <- (rev_involutive fl) in *.
  rewrite alloc_globals_rev_eq in H0.
  forget (rev fl) as vl'. clear fl; rename vl' into vl.
  unfold prog_vars. simpl.
  rewrite <- rev_prog_vars'.
  rewrite map_rev. rewrite <- writable_blocks_rev.
  assert (exists ul, gev = Genv.add_globals (Genv.empty_genv fundef type) (rev vl ++ ul) /\ 
                                            list_norepet (map (@fst _ _) (rev vl ++ ul))).
  exists nil; rewrite <- app_nil_end; auto.
  clear Heqgev H.
  revert m H0 H1 IOK SAME_IDS; induction vl; simpl; intros.
 apply resource_at_empty2.
 intro l.
 unfold inflate_initial_mem.
 rewrite resource_at_make_rmap.
 unfold inflate_initial_mem'.
  inv H0.
 unfold access_at, empty. simpl. rewrite ZMap.gi. apply NO_identity.
(*
 invSome.
 destruct a; destruct g.
 apply (H3 m0).
 case_eq (initblocksize type a); intros.
 specialize (IHvl _ H0).
 unfold writable_block.
 normalize.
 unfold initblocksize in H.
 destruct a. inv H.
 unfold Genv.alloc_variable in H3.
 simpl in H3.
 revert H3; case_eq (alloc m0 0 (Genv.init_data_list_size (gvar_init g))); intros.
 invSome. invSome.
 unfold empty_environ at 1. simpl ge_of. unfold filter_genv.
 destruct H1 as [ul [? ?]].
 spec IHvl.
  exists ((i,g)::ul).
 rewrite app_ass in H1,H2; split; auto.
 assert (Genv.find_symbol gev i = Some b).
 clear - H0 H H1 H2 H9.
 apply alloc_result in H. subst.
 rewrite <- alloc_variables_rev_eq in H0. 
 apply Genv.alloc_variables_nextblock in H0.
 rewrite H0. clear - H2 H9.
 rewrite app_ass in *. simpl app in *.
 simpl nextblock. rewrite <- H9.
 apply add_variables_nextblock; auto. 
 rewrite H4.
 exists (Vptr b Int.zero, match type_of_global gev b with
      | Some t => t
      | None => Tvoid
      end).
 normalize.
 exists (b, 0).
 normalize; exists Share.bot.
 normalize.
 split.
 simpl. split.
 destruct (type_of_global gev b); auto.
 f_equal; rewrite Int.signed_zero; auto.
 rewrite sepcon_comm.
 assert (b>0). apply alloc_result in H. subst; apply nextblock_pos.
 apply (mem_alloc_juicy _ _ _ _ _ H
                    (initial_core gev G n)
                   (writable_blocks (map (initblocksize type) vl) (empty_environ gev))
                  IOK IOK) in IHvl.
 rewrite Zminus_0_r in IHvl.
 apply (store_zeros_lem _ _ _ _ H3 H7 _ IOK IOK) in IHvl.
 apply (store_init_data_list_lem _ _ _ _ _ _ _ _ H5 H7 _ IOK IOK) in IHvl.
 rewrite <- (Zminus_0_r  (Genv.init_data_list_size (gvar_init g))) in IHvl.
 assert (Genv.perm_globvar g = Writable) by admit. (* need to generalize this! *)
 rewrite H8 in *.
 apply (drop_perm_writable_lem _ _ _ _ _ H6 H7 _ IOK IOK) in IHvl.
 rewrite Zminus_0_r in IHvl.
 apply IHvl.
Qed. *)
Admitted.


Definition bump_nextvar {F V} (ge: Genv.t F V)  : Genv.t F V.
intros.
apply (@Genv.mkgenv F V
    ge.(Genv.genv_symb)
    ge.(Genv.genv_funs)
    ge.(Genv.genv_vars)
    (ge.(Genv.genv_next) + 1)); intros; destruct ge; simpl in *; auto.
unfold block in *. omega.
destruct (genv_symb_range _ _ H); split; unfold block in*; omega.
pose proof (genv_funs_range _ _ H); omega.
pose proof (genv_vars_range _ _ H); omega.
eapply genv_funs_vars; eauto.
apply genv_vars_inj with b; auto.
Defined.

Lemma disj_no_fun:
  forall (fs: list (AST.ident * globdef fundef type)) ids, 
       list_disjoint (map (@fst _ _) fs) ids ->
       forall i, In i ids ->
      (Genv.genv_symb (Genv.add_globals (Genv.empty_genv _ _) fs)) ! i = None.
Proof.
intros. spec H i i.
assert (~In i (map (@fst _ _) fs)). intro. contradiction H; auto.
clear - H1; rename H1 into H0. unfold Genv.add_globals.
rewrite fold_right_rev_left. rewrite <- (rev_involutive fs). rewrite In_rev in H0.
rewrite <- map_rev in H0. remember (rev fs) as fs'; rewrite rev_involutive. clear - H0.
revert H0; induction fs'; simpl; intros.
rewrite Maps.PTree.gempty; auto. destruct a; simpl in *.
rewrite Maps.PTree.gso; [ | intro; subst; intuition]. 
apply IHfs'. contradict H0; auto.
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
  fun loc => if zlt (fst loc) b then core (w @ loc) else w @ loc.

Definition beyond_block (b: block) (w: rmap) : rmap.
 refine (proj1_sig (make_rmap (beyond_block' b w) _ (level w) _)).
Proof.
 intros b' z'.
 unfold compose, beyond_block'.
 simpl. destruct (zlt b' b).
 pose proof (rmap_valid w b' z'). unfold compose in H.
 revert H;  case_eq (w @ (b',z')); intros;
  repeat rewrite core_NO in *; 
  repeat rewrite core_YES in *;
  repeat rewrite core_PURE in *;
   simpl; intros; auto.
 pose proof (rmap_valid w b' z'). unfold compose in H.
 revert H;  case_eq (w @ (b',z')); intros;
  repeat rewrite core_NO in *; 
  repeat rewrite core_YES in *;
  repeat rewrite core_PURE in *;
   simpl; intros; auto.
 extensionality loc;  unfold compose.
  unfold beyond_block'.
 if_tac. repeat rewrite core_resource_at. rewrite <- level_core; apply resource_at_approx.
apply resource_at_approx.
Defined.
