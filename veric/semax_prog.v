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
Require Import veric.extspec.
Require Import veric.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.
Require Import veric.initial_world.
Require Import msl.normalize.
Require Import veric.semax_call.
Require Import veric.initial_world.
Require Import veric.initialize.

Open Local Scope pred.

Definition match_globvars (gvs: list (ident * globvar type)) (V: varspecs) :=
  forall id t, In (id,t) V -> exists g: globvar type, gvar_info g = t /\ In (id,g) gvs.

Section semax_prog.
Context {Z} (Hspec: juicy_ext_spec Z).

Definition prog_contains (ge: genv) (fdecs : list (ident * fundef)) : Prop :=
     forall id f, In (id,f) fdecs -> 
         exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some f.

Definition entry_tempenv (te: temp_env) (f: function) (vl: list val) :=
   length vl = length f.(fn_params) /\
   forall id v, PTree.get id te = Some v ->  
                      In (id,v) 
                       (combine (map (@fst _ _) f.(fn_params)) vl 
                          ++ map (fun tv => (fst tv, Vundef)) f.(fn_temps)).

Definition semax_body_params_ok f : bool :=
   andb 
        (compute_list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)))
        (compute_list_norepet (map (@fst _ _) (fn_vars f))).

Definition semax_body
       (V: varspecs) (G: funspecs) (f: function) (spec: ident * funspec) : Prop :=
  match spec with (_, mk_funspec _ A P Q) =>
    forall x,
      semax Hspec (func_tycontext f V G)
          (fun rho => bind_args (fn_params f) (P x) rho *  stackframe_of f rho)
          f.(fn_body)
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x)) (stackframe_of f))
 end.

Definition semax_func
         (V: varspecs) (G: funspecs) (fdecs: list (ident * fundef)) (G1: funspecs) : Prop :=
   match_fdecs fdecs G1 /\
  forall ge, prog_contains ge fdecs -> 
          forall n, believe Hspec (nofunc_tycontext V G) ge (nofunc_tycontext V G1) n.

Definition main_pre (prog: program) : unit -> assert :=
(fun tt vl => writable_blocks (map (initblocksize type) (prog_vars prog) )
                             (empty_environ (Genv.globalenv prog))).

Definition Tint32s := Tint I32 Signed noattr.

Definition main_post (prog: program) : unit -> assert := 
  (fun tt _ => TT).

Definition semax_prog 
     (prog: program)  (V: varspecs) (G: funspecs) : Prop :=
  compute_list_norepet (prog_defs_names prog) = true  /\
  semax_func V G (prog_funct prog) G /\
   match_globvars (prog_vars prog) V /\
    In (prog.(prog_main), mk_funspec (nil,Tvoid) unit (main_pre prog ) (main_post prog)) G.

Lemma semax_func_nil: 
   forall
     V G, semax_func V G nil nil.
Proof.
intros; split; auto.
hnf; auto.
intros.
intros b fsig ty P Q w ? ?.
hnf in H1.
destruct H1 as [b' [? ?]].
simpl in H1. 
elimtype False; clear - H1.
revert H1; induction V; simpl; intros.
rewrite PTree.gempty in H1. inv H1.
destruct a.
simpl in *.
destruct (eq_dec i b'). subst. rewrite PTree.gss in H1. inv H1.
rewrite PTree.gso in H1 by auto.
apply IHV. auto.
Qed.

Program Definition HO_pred_eq {T}{agT: ageable T}
    (A: Type) (P: A -> pred T) (A': Type) (P': A' -> pred T) : pred nat :=
 fun v => exists H: A=A', 
     match H in (_ = A) return (A -> pred T) -> Prop with
     | refl_equal => fun (u3: A -> pred T) =>
                                    forall x: A, (P x <=> u3 x) v
     end P'.
 Next Obligation.
  intros; intro; intros.
  destruct H0. exists x.
  destruct x. 
   intros. specialize (H0 x). eapply pred_hereditary; eauto.
 Qed.

Lemma approx_oo_approx'':
   forall n n' : nat,
  (n' >= n)%nat ->
    approx n' oo approx n = approx n.
Proof.
intros.
extensionality P.
apply pred_ext'; extensionality w.
unfold approx, compose.
simpl. rewrite rmap_level_eq.
case_eq (unsquash w); intros; simpl in *.
apply prop_ext; intuition.
Qed.

Lemma laterR_level: forall w w' : rmap, laterR w w' -> (level w > level w')%nat.
Proof.
induction 1.
unfold age in H. rewrite <- ageN1 in H.
change rmap with R.rmap; change ag_rmap with R.ag_rmap.
rewrite (ageN_level _ _ _ H). generalize (@level _ R.ag_rmap y). intros; omega.
omega.
Qed.

Lemma necR_level:  forall w w' : rmap, necR w w' -> (level w >= level w')%nat.
Proof.
induction 1.
unfold age in H. rewrite <- ageN1 in H.
change rmap with R.rmap; change ag_rmap with R.ag_rmap.
rewrite (ageN_level _ _ _ H). generalize (@level _ R.ag_rmap y). intros; omega.
omega.
omega.
Qed.

Lemma HO_pred_eq_i1:
  forall A P P' m, 
      approx (level m) oo  P = approx (level m) oo P' ->
    (|> HO_pred_eq A P A  P') m.
Proof.
intros.
unfold HO_pred_eq.
intros ?m ?.
hnf.
exists (refl_equal A).
intros.
generalize (f_equal (fun f => f x) H); clear H; intro.
simpl in H0.
unfold compose in *.
apply clos_trans_t1n in H0.
revert H; induction H0; intros.
Focus 2. apply IHclos_trans_1n.
unfold age,age1 in H. unfold ag_nat in H. unfold natAge1 in H. destruct x0; inv H.
clear - H1.
assert (forall w, app_pred (approx (level (S y)) (P x)) w <-> app_pred (approx (level (S y)) (P' x)) w).
intros; rewrite H1; intuition.
apply pred_ext; intros w ?; destruct (H w); simpl in *; intuition.
apply H0; auto. clear - H4.  unfold natLevel in *. omega.
apply H2; auto. clear - H4.  unfold natLevel in *. omega.
(* End Focus 2 *)
unfold age,age1 in H. unfold ag_nat in H. unfold natAge1 in H. destruct x0; inv H.
intros z ?.
split; intros ? ? ?.
assert (app_pred (approx (level (S y)) (P x)) a').
simpl. split; auto. unfold natLevel.  apply necR_level in H1.
change compcert_rmaps.R.rmap with rmap in *.
change compcert_rmaps.R.ag_rmap with ag_rmap in *.
omega.
rewrite H0 in H3.
simpl in H3. destruct H3; auto.
assert (app_pred (approx (level (S y)) (P' x)) a').
simpl. split; auto. unfold natLevel.  apply necR_level in H1.
change compcert_rmaps.R.rmap with rmap in *.
change compcert_rmaps.R.ag_rmap with ag_rmap in *.
omega.
rewrite <- H0 in H3.
simpl in H3. destruct H3; auto.
Qed.

Lemma fst_match_fdecs:
 forall {fs G}, match_fdecs fs G -> map (@fst _ _) fs = map (@fst _ _) G.
Proof.
induction fs; destruct G; simpl; intros; inv H; simpl; auto.
f_equal; auto.
Qed.

Require Import JMeq.

Lemma semax_func_cons_aux:
  forall (psi: genv) id fsig1 A1 P1 Q1 fsig2 A2 P2 Q2 (V: varspecs) (G': funspecs) b fs,
  Genv.find_symbol psi id = Some b ->
  ~ In id (map (fst (A:=ident) (B:=fundef)) fs) ->
   match_fdecs fs G'  ->
   claims  psi (nofunc_tycontext V ((id, mk_funspec fsig1 A1 P1 Q1) :: G')) (Vptr b Int.zero) fsig2 A2 P2 Q2 ->
    fsig1=fsig2 /\ A1=A2 /\ JMeq P1 P2 /\ JMeq Q1 Q2.
Proof.
intros until 1; intros (*Hok*) Hin (* Had *) Hmf; intros.
destruct H0 as [id' [? ?]].
simpl in H0.
destruct (eq_dec id id').
subst id'. rewrite PTree.gss in H0. inv H0.
apply inj_pair2 in H5. apply inj_pair2 in H6.
subst.
split; auto.
rewrite PTree.gso in H0 by auto.
elimtype False.
destruct H1 as [b' [? ?]].
symmetry in H2; inv H2.
assert (In id' (map (@fst _ _) G')).
clear - H0.
revert H0; induction G'; simpl; intros; auto.
revert H0; induction  V; simpl; intros; auto.
rewrite PTree.gempty in H0; inv H0.
destruct (eq_dec id' (fst a)). subst. rewrite PTree.gss in H0 by auto. inv  H0.
rewrite PTree.gso in H0 by auto. auto.
destruct a; simpl in *.
destruct (eq_dec i id'). subst. rewrite PTree.gss in H0. auto.
rewrite PTree.gso in H0 by auto.
right; apply IHG'; auto.
destruct (eq_dec id id').
2: apply (Genv.global_addresses_distinct psi n H H1); auto.
subst id'.
clear - Hin H2 Hmf.
rewrite (fst_match_fdecs Hmf) in Hin; contradiction.
Qed.

Lemma semax_func_cons: 
   forall 
         fs id f A P Q (V: varspecs) (G G': funspecs),
      andb (id_in_list id (map (@fst _ _) G)) 
      (andb (negb (id_in_list id (map (@fst ident fundef) fs)))
        (semax_body_params_ok f)) = true ->
      semax_body V G f (id, mk_funspec (fn_funsig f) A P Q) ->
      semax_func V G fs G' ->
      semax_func V G ((id, Internal f)::fs) 
           ((id, mk_funspec (fn_funsig f) A P Q)  :: G').
Proof.
intros until G'.
intros H' H3 [Hf' Hf].
apply andb_true_iff in H'.
destruct H' as [Hin H'].
apply andb_true_iff in H'.
destruct H' as [Hni H].
split.
hnf.
simpl; f_equal; auto.
intros ge H0 n.
assert (prog_contains ge fs).
unfold prog_contains in *.
intros.
apply H0.
simpl.
auto.
spec Hf ge H1.
clear H1.
hnf in Hf|-*.
intros v fsig A' P' Q'.
apply derives_imp.
clear n.
intros n ?.
spec H0 id (Internal f).
destruct H0 as [b [? ?]].
left; auto.
rewrite <- Genv.find_funct_find_funct_ptr in H2.
apply negb_true_iff in Hni.
apply id_in_list_false in Hni.
destruct (eq_dec  (Vptr b Int.zero) v) as [?H|?H].
(* Vptr b Int.zero = v *)
subst v.
right.
exists b; exists f.
split.
apply andb_true_iff in H.
destruct H as [H H'].
apply compute_list_norepet_e in H.
apply compute_list_norepet_e in H'.
split3; auto.
rewrite Genv.find_funct_find_funct_ptr in H2; auto.
split; auto.
split; auto.
destruct H1 as [id' [? [b' [? ?]]]].
symmetry in H5; inv H5.
destruct (eq_dec id id').
subst.
simpl in H1.
rewrite PTree.gss in H1.
inv H1; auto.
contradiction (Genv.global_addresses_distinct ge n0 H0 H4); auto.
destruct H.
intro x.
simpl in H1.
pose proof (semax_func_cons_aux ge _ _ _ _ _ _ _ _ _ _ _ _ _ H0 Hni Hf' H1).
destruct H as [H4' [H4 [H4b H4c]]].
subst A' fsig.
apply JMeq_eq in H4b.
apply JMeq_eq in H4c.
subst P' Q'.
specialize (H3 x).
rename H3 into H4.
pose proof I.
specialize (H4 n).
apply now_later.
clear - H4.
rewrite semax_fold_unfold in H4|-*.
revert n H4.
apply allp_derives; intro gx.
apply imp_derives; auto.
apply allp_derives; intro k.
apply allp_derives; intro F.
apply imp_derives; auto.
unfold guard.
apply allp_derives; intro tx.
eapply allp_derives; intro vx.
eapply subp_derives; auto.
apply andp_derives; auto.
apply andp_derives; auto.
apply sepcon_derives; auto.
apply andp_left1; auto.
(***   Vptr b Int.zero <> v'  ********)
apply (Hf n v fsig A' P' Q'); auto.
destruct H1 as [id' [? ?]].
simpl in H1.
destruct (eq_dec id id').
subst. rewrite PTree.gss in H1.
destruct H5 as [? [? ?]]. congruence.
rewrite PTree.gso in H1 by auto.
exists id'; split; auto.
Qed.

Lemma semax_func_cons_ext: 
   forall 
        V (G: funspecs) fs id ef fsig A P Q (G': funspecs),
      andb (id_in_list id (map (@fst _ _) G))
              (negb (id_in_list id (map (@fst _ _) fs))) = true ->
      (forall n, semax_ext Hspec ef A P Q n) ->
      semax_func V G fs G' ->
      semax_func V G ((id, External ef (fst fsig) (snd fsig))::fs) 
           ((id, mk_funspec (arglist 1%positive (fst fsig), (snd fsig)) A P Q)  :: G').
Proof.
intros until G'.
intros H' H [Hf' Hf].
apply andb_true_iff in H'.
destruct H' as [Hin Hni].
apply id_in_list_true in Hin.
apply negb_true_iff in Hni; apply id_in_list_false in Hni.
split.
destruct fsig; hnf; simpl; f_equal; auto.
f_equal. f_equal.
clear; forget 1%positive as n.
revert n; induction t; simpl;intros; auto.
f_equal; auto.
intros ge; intros.
assert (prog_contains ge fs).
unfold prog_contains in *.
intros.
apply H0.
simpl.
auto.
specialize (Hf ge H1).
clear H1.
unfold believe.
intros v' fsig' A' P' Q'.
apply derives_imp.
clear n.
intros n ?.
unfold prog_contains in H0.
generalize (H0 id (External ef (fst fsig) (snd fsig))); clear H0; intro H0.
destruct H0 as [b [? ?]].
left; auto.
rewrite <- Genv.find_funct_find_funct_ptr in H2.
destruct (eq_dec  (Vptr b Int.zero) v') as [?H|?H].
subst v'.
left.
specialize (H n).
pose proof (semax_func_cons_aux ge _ _ _ _ _ _ _ _ _ _ _ _ _ H0 Hni Hf' H1).
destruct H3 as [H4' [H4 [H4b H4c]]].
subst A' fsig'.
apply JMeq_eq in H4b.
apply JMeq_eq in H4c.
subst P' Q'.
unfold believe_external.
rewrite H2.
split; auto.
hnf. auto.

(***   Vptr b Int.zero <> v'  ********)
apply (Hf n v' fsig' A' P' Q'); auto.
destruct H1 as [id' [? ?]].
simpl in H1.
destruct (eq_dec id id').
subst. rewrite PTree.gss in H1. inv H1.
destruct H4 as [? [? ?]]; congruence.
exists id'; split; auto.
simpl. rewrite PTree.gso in H1 by auto; auto.
Qed.

Definition main_params (ge: genv) start : Prop :=
  exists b, exists func,
    Genv.find_symbol ge start = Some b /\
        Genv.find_funct ge (Vptr b Int.zero) = Some (Internal func) /\
        func.(fn_params) = nil.

Lemma in_prog_funct'_in {F V}:
  forall i f (g: list (ident * globdef F V)), In (i,f) (prog_funct' g) -> In (i, Gfun f) g.
Proof.
induction g; intros. inv H. simpl in *. 
destruct a; destruct g0. simpl in H. destruct H; auto. left; congruence.
right; auto.
Qed.

Lemma in_prog_funct_in_prog_defs:
  forall i f prog, In (i,f) (prog_funct prog) -> In (i, Gfun f) (prog_defs prog).
Proof.
 intros; apply in_prog_funct'_in; auto.
Qed.

Lemma in_prog_vars_in_prog_defs:
  forall i v prog, In (i,v) (prog_vars prog) -> In (i, Gvar v) (prog_defs prog).
Proof.
unfold prog_vars. intros ? ? ?.
induction (prog_defs prog); intros. inv H. simpl in *. 
destruct a; destruct g. auto. simpl in H. destruct H; auto. left; congruence.
Qed.

Lemma funassert_initial_core:
  forall prog ve te V G n, 
      list_norepet (prog_defs_names prog) ->
      match_fdecs (prog_funct prog) G ->
      app_pred (funassert (nofunc_tycontext V G) (mkEnviron (filter_genv (Genv.globalenv prog)) ve te))
                      (initial_core (Genv.globalenv prog) G n).
Proof.
 intros; split.
 intros id fs.
 apply prop_imp_i; intros.
 simpl ge_of; simpl fst; simpl snd.
 unfold filter_genv.
 assert (exists f, In (id, f) (prog_funct prog)).
 simpl in H1. apply fst_match_fdecs in H0.
 forget (prog_funct prog) as g.
clear - H1 H0.
revert id G H1 H0; induction g; destruct G; intros; inv H0; simpl in *.
elimtype False.
revert H1; induction V; simpl; intros.
rewrite PTree.gempty in H1; inv H1.
destruct (eq_dec (fst a) id). subst. rewrite PTree.gss in H1. inv H1.
rewrite PTree.gso in H1 by auto; auto. 
destruct a,p; simpl in *; subst.
destruct (eq_dec i0 id). subst; eauto.
rewrite PTree.gso in H1 by auto.
destruct (IHg id G). eauto. auto.
eauto.
destruct H2 as [f ?].
 destruct (Genv.find_funct_ptr_exists prog id f) as [b [? ?]]; auto.
 apply in_prog_funct_in_prog_defs; auto.
 rewrite H3.
 exists (Vptr b Int.zero), (b,0).
 split.
 split.
 unfold type_of_global.
 case_eq (Genv.find_var_info (Genv.globalenv prog) b); intros.
 repeat f_equal.
 elimtype False; clear - H H4 H5.
 admit.
 rewrite H4.
 repeat f_equal.
 unfold no_dups in H.
 unfold prog_funct, prog_defs_names in *.
 forget (prog_defs prog) as g.
 clear - H H0 H1 H2.
 unfold match_fdecs in H0. 
 revert G H H0 H1 H2; induction g; simpl; intros. 
 contradiction.
 inv H. destruct a as [i' [a|a]]. destruct G; inv H0.
 simpl in H1. destruct p as [i p]. simpl in *.
 destruct (eq_dec i id). subst. rewrite PTree.gss in H1. inv H1.
 destruct H2. inv H. auto.
 apply in_map_fst in H.
 elimtype False; clear - H H5.
  apply in_map_iff in H. destruct H as [x [? ?]]. subst; destruct x; simpl in *.
 apply in_prog_funct'_in in H0. apply H5. apply in_map_iff.
 exists (i, Gfun f); auto.
 destruct H2. congruence.
 rewrite PTree.gso in H1 by auto.
 apply (IHg G); auto.
 apply (IHg G); auto.
 simpl. rewrite Int.signed_zero; auto.
 unfold func_at. destruct fs.
 unfold initial_core.
 hnf. rewrite resource_at_make_rmap.
 rewrite level_make_rmap.
 unfold initial_core'.
 simpl.
 rewrite (Genv.find_invert_symbol (Genv.globalenv prog) id); auto.
 assert (H9: In (id, mk_funspec f0 A a a0) G).
     unfold prog_funct, prog_defs_names in *.
    forget (prog_defs prog) as fs. clear - H H0 H1.
    revert G H0 H1; induction fs; simpl; intros; inv H0. destruct G; inv H3.
   elimtype False;    revert H1; induction V; simpl; intros.
   rewrite PTree.gempty in H1; inv H1.
   destruct (eq_dec (fst a1) id). subst. rewrite PTree.gss in H1. inv H1.
    rewrite PTree.gso in H1 by auto; auto.
    destruct a1. destruct g. inv H3. inv H. destruct G; inv H2.
    simpl in H1. destruct p. simpl in *. destruct (eq_dec i id). subst.
    rewrite PTree.gss in H1. inv H1. auto.
    rewrite PTree.gso in H1 by auto. right. apply IHfs; auto.
    inv H. apply IHfs; auto.  
 rewrite (find_id_i _ _ _ H9); auto.
 clear - H0 H. unfold prog_defs_names, prog_funct in *.
 forget (prog_defs prog) as fs.
 unfold match_fdecs in H0.
assert (list_norepet (map (@fst _ _) (prog_funct' fs))).
clear - H. admit.  (* easy *)
 revert G H1 H0; induction (prog_funct' fs); destruct G; intros. constructor. inv H0.
 constructor. inv H1. simpl in H0. destruct a.  inv H0.
 simpl; constructor; auto.
 rewrite <- (fst_match_fdecs H6); auto. 
 intros loc'  [fsig' A' P' Q'].
 unfold func_at.
 intros w ? ?.
 hnf in H2.
 assert (exists pp, initial_core (Genv.globalenv prog) G n @ loc' = PURE (FUN fsig') pp).
case_eq (initial_core (Genv.globalenv prog) G n @ loc'); intros.
destruct (necR_NO _ _ loc' t H1) as [? _].
rewrite H4 in H2 by auto.
inv H2.
eapply necR_YES in H1; try apply H3.
rewrite H1 in H2; inv H2.
eapply necR_PURE in H1; try apply H3.
rewrite H1 in H2; inv H2; eauto.
destruct H3 as [pp ?].
unfold initial_core in H3.
rewrite resource_at_make_rmap in H3.
unfold initial_core' in H3.
if_tac in H3; [ | inv H3].
simpl.
revert H3; case_eq (Genv.invert_symbol (Genv.globalenv prog) (fst loc')); intros;
  [ | congruence].
revert H5; case_eq (find_id i G); intros; [| congruence].
destruct f; inv H6.
apply Genv.invert_find_symbol in H3.
exists i.
simpl ge_of. unfold filter_genv. rewrite H3.
 destruct loc' as [b' z']; simpl in *; subst.
 exists (Vptr b' Int.zero).
 split.
  split.
 unfold type_of_global.
unfold type_of_funspec. simpl.
 assert (exists f, In (i,f) (prog_funct prog) /\ type_of_fundef f = Tfunction (type_of_params (fst fsig')) (snd fsig')).
 clear - H0 H5.
 forget (prog_funct prog) as g. unfold match_fdecs in H0.
 revert G H0 H5; induction g; destruct G; simpl; intros. inv H5. inv H0. inv H0.
 destruct a1. destruct p. simpl in *. inv H0.
 if_tac in H5. subst i1. inv H5. exists f; split; auto.
 destruct (IHg G) as [f3 [? ?]]; auto. exists f3; split; auto.
 destruct H4 as [f [H4 H4']].
 destruct (Genv.find_funct_ptr_exists prog i f) as [b [? ?]]; auto.
 apply in_prog_funct_in_prog_defs; auto.
 inversion2 H3 H6.
 case_eq (Genv.find_var_info (Genv.globalenv prog) b'); intros.
 elimtype False; clear - H7 H6. admit.
 rewrite H7.
 repeat f_equal.
 auto.
 simpl. rewrite Int.signed_zero.
 auto.
 apply find_id_e in H5. apply in_map_fst in H5.
 clear - H5.
 revert H5; induction G; simpl; intro. contradiction.
 destruct H5. subst. econstructor; rewrite PTree.gss; reflexivity.
 destruct (IHG H) as [fs ?].
 destruct (eq_dec (fst a) i). econstructor; subst; rewrite PTree.gss; eauto.
 econstructor; rewrite PTree.gso by auto; eauto.
Qed.

Lemma prog_contains_prog_funct: forall prog: program,  
      list_norepet (prog_defs_names prog) ->
          prog_contains (Genv.globalenv prog) (prog_funct prog).
Proof.
  intros; intro; intros.
  apply (Genv.find_funct_ptr_exists prog id f); auto.
  unfold prog_funct in H0.
  induction (prog_defs prog). inv H0.
   simpl in H0.  destruct a. 
  destruct g. simpl in H0. destruct H0. inv H0.  left. auto.
  right; auto.  right; auto.
Qed. 

(* there's a place this lemma should be applied, perhaps in proof of semax_call *)
Lemma funassert_rho:
  forall G rho rho', ge_of rho = ge_of rho' -> funassert G rho |-- funassert G rho'.
Proof.
unfold funassert; intros.
rewrite H; auto.
Qed.

Lemma core_inflate_initial_mem:
  forall (m: mem) (prog: program) (G: funspecs) (n: nat)
     (INIT: Genv.init_mem prog = Some m),
    match_fdecs (prog_funct prog) G ->
      list_norepet (prog_defs_names prog) ->
   core (inflate_initial_mem m (initial_core (Genv.globalenv prog) G n)) =
         initial_core (Genv.globalenv prog) G n.
Proof.
intros.
assert (IOK := initial_core_ok _ _ n _ H0 H INIT).
apply rmap_ext.
  unfold inflate_initial_mem, initial_core; simpl.
  rewrite level_core. do 2 rewrite level_make_rmap; auto.
intro l.
unfold inflate_initial_mem, initial_core; simpl.
rewrite <- core_resource_at.
repeat rewrite resource_at_make_rmap.
unfold inflate_initial_mem'.
repeat rewrite resource_at_make_rmap.
unfold initial_core'.
case_eq (Genv.invert_symbol (Genv.globalenv prog) (fst l)); intros; auto.
rename i into id.
case_eq (find_id id G); intros; auto.
rename f into fs.
assert (exists f, In (id,f) (prog_funct prog)).
apply find_id_e in H2. apply in_map_fst in H2; rewrite <- (fst_match_fdecs H) in H2.
forget (prog_funct prog) as g; clear - H2.
induction g; simpl in *. contradiction. destruct a; destruct H2; simpl in *; eauto.
destruct (IHg H); eauto.
destruct H3 as [f ?].
apply Genv.invert_find_symbol in H1.
destruct (Genv.find_funct_ptr_exists prog id f) as [b [? ?]]; auto.
apply in_prog_funct_in_prog_defs; auto.
inversion2 H1 H4.
if_tac.
 destruct (IOK l) as [_ ?].
 unfold initial_core in H6. rewrite resource_at_make_rmap in H6.
  unfold initial_core' in H6. rewrite if_true in H6 by auto.
  apply Genv.find_invert_symbol in H1. rewrite H1 in H6. rewrite H2 in H6. destruct fs.
  destruct H6 as [? [? ?]]. rewrite H7. rewrite core_PURE; auto.
  destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
 if_tac;   destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
 if_tac;   destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
Qed.

Definition Delta1 V G: tycontext := 
  make_tycontext ((1%positive,(Tfunction Tnil Tvoid))::nil) nil nil Tvoid V G.

Lemma semax_prog_rule :
  forall z V G prog m,
     semax_prog prog V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, 
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       sim.make_initial_core (juicy_core_sem cl_core_sem)
                    (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
       forall n, exists jm, 
       m_dry jm = m /\ level jm = n /\ 
       jsafeN Hspec (Genv.globalenv prog) n z q jm.
Proof.
 intros until m.
 pose proof I; intros.
 destruct H0 as [? [[? ?] [GV ?]]].
 assert (exists f, In (prog_main prog, f) (prog_funct prog) ).
 clear - H4 H2.
 forget (prog_main prog) as id.
 apply in_map_fst in H4. rewrite <- (fst_match_fdecs H2) in H4.
 forget (prog_funct prog) as g.
 clear - H4; induction g. inv H4. destruct H4.
 destruct a; simpl; eauto.
 destruct (IHg H).
 exists x; right; auto.
 destruct H5 as [f ?].
 apply compute_list_norepet_e in H0.
destruct (Genv.find_funct_ptr_exists prog (prog_main prog) f) as [b [? ?]]; auto.
apply in_prog_funct_in_prog_defs; auto.
 exists b.
 unfold sim.make_initial_core; simpl.
econstructor.
 split3; auto.
 reflexivity.
 intro n.
 exists (initial_jm _ _ _ n H1 H0 H2).
 split3.
 simpl. auto.
 simpl.
 rewrite inflate_initial_mem_level.
 unfold initial_core. rewrite level_make_rmap; auto.
 specialize (H3 (Genv.globalenv prog) (prog_contains_prog_funct _ H0)).
 unfold temp_bindings. simpl length. simpl typed_params. simpl type_of_params.
pattern n at 1; replace n with (level (m_phi (initial_jm prog m G n H1 H0 H2))).
pose (rho := mkEnviron (filter_genv (Genv.globalenv prog)) (Map.empty (block * type)) 
                      (Map.set 1 (Vptr b Int.zero) (Map.empty val))).
eapply (semax_call_aux Hspec (Delta1 V G) unit
                    _ (fun _ => main_post prog tt) _ tt (fun _ => TT) (fun _ => TT)
             None (nil,Tvoid) _ _ (normal_ret_assert (fun _ => TT)) _ _ _ _ 
                 (construct_rho (filter_genv (Genv.globalenv prog)) empty_env
  (PTree.set 1 (Vptr b Int.zero) (PTree.empty val)))
               _ _ b (prog_main prog));
  try apply H3; try eassumption; auto.
clear - GV H0.
admit.  (* typechecking proof *)
hnf; intros; intuition.
hnf; intros; intuition.
unfold normal_ret_assert; simpl.
extensionality rho'.
unfold main_post.
normalize. rewrite TT_sepcon_TT.
apply pred_ext. apply exp_right with Vundef; auto. apply exp_left; auto.
rewrite (corable_funassert _ _).
simpl m_phi.
rewrite core_inflate_initial_mem; auto.
do 3 (pose proof I).
replace (funassert (Delta1 V G)) with (funassert (nofunc_tycontext V G)).
unfold rho; apply funassert_initial_core; auto.
apply same_glob_funassert.
reflexivity.
intros ek vl tx' vx'.
unfold normal_ret_assert, frame_ret_assert.
normalize.
rewrite TT_sepcon_TT.
normalize.
apply derives_subp.
normalize.
simpl.
intros ? ? ? ? _ ?.
destruct H9 as [[? ?] ?].
hnf in H9, H11. subst ek vl.
destruct H8.
subst a.
change Clight_new.true_expr with true_expr.
change (level (m_phi jm)) with (level jm).
apply safe_loop_skip.
unfold glob_types, Delta1. simpl @snd.
forget (prog_main prog) as main.
instantiate (1:=main_post prog). 
instantiate (1:=main_pre prog).
assert (H8: list_norepet (map (@fst _ _) (prog_funct prog))).
clear - H0. admit.
forget (prog_funct prog) as fs.
clear - H4 H8 H2.
forget (mk_funspec (nil, Tvoid) unit (main_pre prog) (main_post prog)) as fd.
revert G H2 H4 H8; induction fs; destruct G; intros; inv H2.
inv H4.
destruct a; destruct p; simpl in *; subst.
inv H8.
specialize (IHfs _ H3).
destruct (eq_dec i0 main). subst.
rewrite PTree.gss; auto.
destruct H4. inv H. auto.
elimtype False; clear - H3 H2 H.
apply H2; clear H2.
revert G H3 H; induction fs; destruct G; intros; inv H3. inv H.
destruct a,p; simpl in *. subst.
destruct H. inv H. auto. right; eapply IHfs; eauto.
rewrite PTree.gso; auto. apply IHfs; auto.
destruct H4; auto. inv H. congruence.
intros.
intros ? ?.
split; apply derives_imp; auto.
unfold main_pre.
apply now_later.
rewrite TT_sepcon_TT.
rewrite sepcon_comm.
apply sepcon_TT.
simpl.
apply global_initializers; auto.
simpl.
rewrite inflate_initial_mem_level.
unfold initial_core.
apply level_make_rmap.
Qed.

End semax_prog.

