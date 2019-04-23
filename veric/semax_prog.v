Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.initial_world.
Require Import VST.msl.normalize.
Require Import VST.veric.semax_call.
Require Import VST.veric.Clight_initial_world.
Require Import VST.veric.initialize.
Require Import VST.veric.coqlib4.
Require Import Coq.Logic.JMeq.

Require Import Coq.Logic.JMeq.
Require Import VST.veric.ghost_PCM.

Local Open Scope pred.

Fixpoint match_globvars (gvs: list (ident * globvar type)) (V: varspecs) : bool :=
 match V with
 | nil => true
 | (id,t)::V' => match gvs with
                       | nil => false
                       | (j,g)::gvs' => if eqb_ident id j
                                              then andb (eqb_type t (gvar_info g)) (match_globvars gvs' V')
                                              else match_globvars gvs' V
                      end
  end.

Section semax_prog.
Context (Espec: OracleKind).

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
   (V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ident * funspec): Prop :=
match spec with (_, mk_funspec _ cc A P Q _ _) =>
forall Espec ts x, 
  semax Espec (func_tycontext f V G nil)
      (fun rho => P ts x rho * stackframe_of f rho)
       (Ssequence f.(fn_body) (Sreturn None))
      (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of f))
end.

Definition genv_contains (ge: Genv.t fundef type) (fdecs : list (ident * fundef)) : Prop :=
 forall id f, In (id,f) fdecs ->
              exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some f.

Lemma genv_prog_contains (ge:genv) fdecs: prog_contains ge fdecs = genv_contains ge fdecs.
Proof. reflexivity. Qed.
(*
Definition semax_func
     (V: varspecs) (G: funspecs) {C: compspecs} (fdecs: list (ident * fundef)) (G1: funspecs) : Prop :=
match_fdecs fdecs G1 /\
forall ge, prog_contains ge fdecs ->
      cenv_sub cenv_cs (genv_cenv ge) ->
      forall n, believe Espec (nofunc_tycontext V G) ge (nofunc_tycontext V G1) n.
*)

Definition semax_func (V: varspecs) (G: funspecs) {C: compspecs} (ge: Genv.t fundef type)
       (fdecs: list (ident * fundef)) (G1: funspecs) : Prop :=
match_fdecs fdecs G1 /\ genv_contains ge fdecs /\
forall (ge': Genv.t fundef type) (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
         (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b)) 
n, believe Espec (nofunc_tycontext V G) (Build_genv ge' (@cenv_cs C)) (nofunc_tycontext V G1) n.

Lemma semax_func_mono CS CS' (CSUB: cspecs_sub CS CS') ge ge'
  (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
  V G fdecs G1 (H: @semax_func  V G CS ge fdecs G1): @semax_func  V G CS' ge' fdecs G1.
Proof.
destruct H as [MF [GC B]]; split; [trivial | split].
+ hnf; intros. destruct (GC _ _ H) as [b [Hb1 Hb2]]. exists b; split.
specialize (Gfs id); rewrite Hb1 in Gfs; apply Gfs.
specialize (Gffp b); rewrite Hb2 in Gffp; apply Gffp.
+ intros ge2; intros. 
assert (Q1: forall i, sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge2 i)).
{ intros. eapply sub_option_trans. apply Gfs. apply Gfs0. }
assert (Q2: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge2 b)).
{ intros. eapply sub_option_trans. apply Gffp. apply Gffp0. }
apply (@believe_monoL CS Espec CS' {| genv_genv := ge2; genv_cenv := cenv_cs |} (nofunc_tycontext V G) (nofunc_tycontext V G)).
intros; apply tycontext_sub_refl. apply CSUB. apply (B _ Q1 Q2 n).
Qed. 

Definition main_pre (prog: program) : list Type -> (ident->val) -> assert :=
(fun nil gv => globvars2pred gv (prog_vars prog)).

Definition main_pre_ext {Z} (prog: program) (ora: Z) : list Type -> (ident->val) -> assert :=
(fun nil gv rho => globvars2pred gv (prog_vars prog) rho * has_ext ora).

Definition Tint32s := Tint I32 Signed noattr.

Definition main_post (prog: program) : list Type -> (ident->val) -> assert :=
(fun nil _ _ => TT).

Definition main_spec' (prog: program) 
(post: list Type -> (ident->val) -> environ ->pred rmap): funspec :=
mk_funspec (nil, tint) cc_default
 (ConstType (ident->val)) (main_pre prog) post
   (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Definition main_spec (prog: program): funspec :=
mk_funspec (nil, tint) cc_default
 (ConstType (ident->val)) (main_pre prog) (main_post prog)
   (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Definition main_spec_ext' {Z} (prog: program) (ora: Z)
(post: list Type -> (ident->val) -> environ ->pred rmap): funspec :=
mk_funspec (nil, tint) cc_default
 (ConstType (ident->val)) (main_pre_ext prog ora) post
   (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Definition main_spec_ext (prog: program) (ora: OK_ty): funspec :=
mk_funspec (nil, tint) cc_default
 (ConstType (ident->val)) (main_pre_ext prog ora) (main_post prog)
   (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Definition is_Internal (prog : program) (f : ident) :=
match Genv.find_symbol (Genv.globalenv prog) f with
None => false
| Some b =>
match Genv.find_funct_ptr (Genv.globalenv prog) b with
| None => false
| Some f =>
  match f with
  | External _ _ _ _ => false
  | Internal _ => true
  end
end
end.

Definition semax_prog {C: compspecs}
       (prog: program)  (V: varspecs) (G: funspecs) : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
cenv_cs = prog_comp_env prog /\
(*  @semax_func V G C (prog_funct prog) G /\*)
@semax_func V G C (Genv.globalenv prog) (prog_funct prog) G /\
match_globvars (prog_vars prog) V = true /\
match find_id prog.(prog_main) G with
| Some s => exists post, s = main_spec' prog post
| None => False
end.

Definition semax_prog_ext {C: compspecs}
       (prog: program) (ora: OK_ty) (V: varspecs) (G: funspecs) : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
cenv_cs = prog_comp_env prog /\
(*  @semax_func V G C (prog_funct prog) G /\*)
@semax_func V G C (Genv.globalenv prog) (prog_funct prog) G /\
match_globvars (prog_vars prog) V = true /\
match find_id prog.(prog_main) G with
| Some s => exists post, s = main_spec_ext' prog ora post
| None => False
end.

Lemma semax_func_nil:
forall
 V G {C: compspecs} ge, @semax_func V G C ge nil nil.
Proof.
intros; split. constructor. split; [ hnf; intros; inv H | intros].
(*rename H0 into HGG.*)
intros b fsig cc ty P Q w ? ?.
hnf in H0.
destruct H0 as [b' [NEP [NEQ [? ?]]]].
simpl in H0.
rewrite PTree.gempty in H0. inv H0.
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
2 : { apply IHclos_trans_1n.
  unfold age,age1 in H. unfold ag_nat in H. unfold natAge1 in H. destruct x0; inv H.
  clear - H1.
  assert (forall w, app_pred (approx (level (S y)) (P x)) w <-> app_pred (approx (level (S y)) (P' x)) w).
  { intros; rewrite H1; intuition. }
  apply pred_ext; intros w ?; destruct (H w); simpl in *; intuition.
  apply H0; auto. clear - H4.  unfold natLevel in *. omega.
  apply H2; auto. clear - H4.  unfold natLevel in *. omega. }
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

Lemma semax_func_cons_aux:
forall (psi: genv) id fsig1 cc1 A1 P1 Q1 NEP1 NEQ1 fsig2 cc2 A2 P2 Q2 (V: varspecs) (G': funspecs) {C: compspecs} b fs,
Genv.find_symbol psi id = Some b ->
~ In id (map (fst (A:=ident) (B:=fundef)) fs) ->
match_fdecs fs G'  ->
claims  psi (nofunc_tycontext V ((id, mk_funspec fsig1 cc1 A1 P1 Q1 NEP1 NEQ1) :: G')) (Vptr b Ptrofs.zero) fsig2 cc2 A2 P2 Q2 ->
fsig1=fsig2 /\ cc1 = cc2 /\ A1=A2 /\ JMeq P1 P2 /\ JMeq Q1 Q2.
Proof.
intros until fs. intros H Hin Hmf; intros.
destruct H0 as [id' [NEP2 [NEQ2 [? ?]]]].
simpl in H0.
destruct (eq_dec id id').
subst id'. rewrite PTree.gss in H0. inv H0.
apply inj_pair2 in H6. apply inj_pair2 in H7.
subst.
split; auto.
rewrite PTree.gso in H0 by auto.
elimtype False.
destruct H1 as [b' [? ?]].
symmetry in H2; inv H2.
assert (In id' (map (@fst _ _) G')).
clear - H0.
revert H0; induction G'; simpl; intros; auto.
rewrite PTree.gempty in H0; inv H0.
destruct (eq_dec id' (fst a)). subst.
change (@ptree_set) with (@PTree.set) in H0.
destruct a; simpl in *.
rewrite PTree.gss in H0 by auto. inv  H0.
auto.
destruct a; simpl in *.
destruct (eq_dec i id'). subst. rewrite PTree.gss in H0. auto.
rewrite PTree.gso in H0 by auto.
right; apply IHG'; auto.
destruct (eq_dec id id').
2: apply (Genv.global_addresses_distinct psi n H H1); auto.
subst id'.
clear - Hin H2 Hmf.
eapply match_fdecs_in in Hmf; eauto.
Qed.

Lemma var_block'_cenv_sub {CS CS'} (CSUB: cenv_sub CS CS') sh a
(CT: complete_type CS (@snd ident type a) = true):
var_block' sh CS a = var_block' sh CS' a.
Proof.
extensionality rho.
unfold var_block'. rewrite (cenv_sub_sizeof CSUB); trivial.
Qed. 

Lemma stackframe_of'_cenv_sub {CS CS'} (CSUB: cenv_sub CS CS') f
  (COMPLETE : Forall (fun it : ident * type => complete_type CS (snd it) = true) (fn_vars f)):
stackframe_of' CS f = stackframe_of' CS' f .
Proof.
extensionality rho. 
unfold stackframe_of'. forget (fn_vars f) as vars.
induction vars; simpl; trivial.
inv COMPLETE. rewrite (var_block'_cenv_sub CSUB _ _ H1), IHvars; clear IHvars; trivial.
Qed.

Lemma var_block_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') sh a
(CT: complete_type (@cenv_cs CS) (@snd ident type a) = true):
@var_block sh CS a = @var_block sh CS' a.
Proof.
extensionality rho.
unfold var_block. rewrite (cenv_sub_sizeof CSUB); trivial.
Qed. 

Lemma stackframe_of_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') f
  (COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)):
@stackframe_of CS f = @stackframe_of CS' f .
Proof.
extensionality rho. 
unfold stackframe_of. forget (fn_vars f) as vars.
induction vars; simpl; trivial.
inv COMPLETE. rewrite (var_block_cenv_sub CSUB _ _ H1), IHvars; clear IHvars; trivial.
Qed.

Lemma semax_body_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') V G f spec
(COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)):
@semax_body V G CS f spec -> @semax_body V G CS' f spec.
Proof.
destruct spec. simpl. destruct f0; intros.  specialize (H Espec0 ts x).
rewrite <- (stackframe_of_cenv_sub CSUB); [apply (semax_cssub CSUB); apply H | trivial].
Qed. 

Lemma semax_func_cons: forall 
     fs id f cc (A: TypeTree) P Q NEP NEQ (V: varspecs) (G G': funspecs) {C: compspecs} ge b,
  andb (id_in_list id (map (@fst _ _) G))
  (andb (negb (id_in_list id (map (@fst ident fundef) fs)))
    (semax_body_params_ok f)) = true ->
  Forall
     (fun it : ident * type =>
      complete_type cenv_cs (snd it) =
      true) (fn_vars f) ->
   var_sizes_ok cenv_cs (f.(fn_vars)) ->
   f.(fn_callconv) = cc ->
 (*NEW*)  Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (Internal f) -> 
   precondition_closed f P ->
  semax_body V G f (id, mk_funspec (fn_funsig f) cc A P Q NEP NEQ) ->
  semax_func V G ge fs G' ->
  semax_func V G ge ((id, Internal f)::fs)
       ((id, mk_funspec (fn_funsig f) cc A P Q NEP NEQ)  :: G').
Proof.
intros until C.
intros ge b H' COMPLETE Hvars Hcc Hb1 Hb2 Hpclos H3 [HfsG' [Hfs HG]].
apply andb_true_iff in H'.
destruct H' as [Hin H'].
apply andb_true_iff in H'.
destruct H' as [Hni H]. 
split.
{ simpl. econstructor 2; auto.
simpl.
unfold type_of_function. f_equal. auto. }
apply id_in_list_true in Hin. rewrite negb_true_iff in Hni.
split.
{ hnf; intros. destruct H0; [ symmetry in H0; inv H0 | apply (Hfs _ _ H0)].
exists b; split; trivial. } 
intros ge' H0 HGG n.
specialize (HG _ H0 HGG).
hnf in HG |- *. 
intros v fsig cc' A' P' Q'.
apply derives_imp.
clear n.
intros n ?.
subst cc. 
rewrite <- Genv.find_funct_find_funct_ptr in Hb2.
apply id_in_list_false in Hni.
destruct (eq_dec  (Vptr b Ptrofs.zero) v) as [?H|?H].
* (* Vptr b Ptrofs.zero = v *)
subst v.
right.
exists b; exists f.
split(*; auto*).
+
apply andb_true_iff in H.
destruct H as [H H'].
apply compute_list_norepet_e in H.
apply compute_list_norepet_e in H'.
(*split3; auto.*)
rewrite Genv.find_funct_find_funct_ptr in Hb2; auto.
split; auto.
split. { specialize (HGG b). unfold fundef in HGG;  rewrite Hb2 in HGG; simpl in HGG.
      unfold fundef; simpl. rewrite HGG; trivial. } 
split; auto.
split; auto.
split; auto.
destruct H1 as [id' [NEP' [NEQ' [? [b' [? ?]]]]]].
symmetry in H4; inv H4.
destruct (eq_dec id id').
subst.
simpl in H1.
rewrite PTree.gss in H1.
inv H1; auto.
specialize (H0 id); unfold fundef in H0. simpl in H0.  rewrite Hb1 in H0; simpl in H0.
simpl in H2. 
contradiction (Genv.global_addresses_distinct ge' n0 H0 H2); auto.
+
(*destruct H. *) 
intros Delta' CS' k NK HDelta' w KW CSUB.
intros ts x.
simpl in H1. specialize (H0 id); unfold fundef in H0; simpl in H0. rewrite Hb1 in H0; simpl in H0.
pose proof (semax_func_cons_aux (Build_genv ge' cenv_cs) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 Hni HfsG' H1).
destruct H2 as [H4' [H4 [H4a [H4b H4c]]]].
subst A' fsig cc'.
apply JMeq_eq in H4b.
apply JMeq_eq in H4c.
subst P' Q'. 
specialize (H3 Espec ts x). 
rename H3 into H4. (* destruct H3 as [Ann H4].*)
pose proof I.
(*specialize (H4 n).*)specialize (H4 k).
apply now_later. 
rewrite <- (stackframe_of'_cenv_sub CSUB); trivial.
apply (semax'_cssub CSUB).
(*rewrite HGG.*)
clear - Hpclos H4 NK KW HDelta'.
rewrite semax_fold_unfold in H4|-*. intros gx DD CS' u WU [SUB GX] v UV BEL.
assert (HDD: tycontext_sub (func_tycontext f V G nil) DD).
{ unfold func_tycontext, func_tycontext'. simpl.
eapply tycontext_sub_trans; eauto. }
assert (WV: @necR nat ag_nat w v). { eapply necR_trans.  apply WU. apply UV. }
specialize (H4 gx DD CS' _ KW (conj HDD GX) v WV BEL). 
revert H4.
apply allp_derives; intro kk.
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
apply sepcon_derives; auto.
unfold bind_args.
apply andp_left2; auto.
destruct (Hpclos ts x).
apply close_precondition_e; auto.
* (***   Vptr b Ptrofs.zero <> v'  ********)
apply (HG n v fsig cc' A' P' Q'); auto.
destruct H1 as [id' [NEP' [NEQ' [? ?]]]].
simpl in H1.
destruct (eq_dec id id').
subst. rewrite PTree.gss in H1.
destruct H4 as [? [? ?]]. specialize (H0 id'); unfold fundef in H0; simpl in H0. rewrite Hb1 in H0; simpl in H0. unfold fundef in H4; simpl in H4; congruence.
rewrite PTree.gso in H1 by auto.
exists id', NEP', NEQ'; split; auto.
Qed.

(* EXPERIMENT
Lemma semax_func_skip:
forall
    V (G: funspecs) {C: compspecs} fs idf (G': funspecs),
  semax_func V G fs G' ->
  semax_func V G (idf::fs) G'.
Proof.
intros.
hnf in H|-*.
destruct H; split.
constructor 3. auto.
intros.
eapply H0; eauto.
hnf in H1|-*.
intros; eapply H1; eauto.
right; auto.
Qed.
*)

Lemma semax_external_FF:
forall Espec ids ef A n,
@semax_external Espec ids ef A (fun _ _ _ => FF) (fun _ _ _ => FF) n.
intros.
hnf; intros.
simpl.
intros.
destruct H2 as [? [? [? [? [? ?]]]]].
contradiction.
Qed.

Lemma semax_func_cons_ext:
forall (V: varspecs) (G: funspecs) {C: compspecs} ge fs id ef argsig retsig A P Q NEP NEQ
      argsig'
      (G': funspecs) cc (ids: list ident) b,
  ids = map fst argsig' -> (* redundant but useful for the client,
           to calculate ids by reflexivity *)
  argsig' = zip_with_tl ids argsig ->
  ef_sig ef =
  mksignature
    (typlist_of_typelist (type_of_params argsig'))
    (opttyp_of_type retsig) cc ->
  id_in_list id (map (@fst _ _) fs) = false ->
  length ids = length (typelist2list argsig) ->
  (forall gx ts x (ret : option val),
     (Q ts x (make_ext_rval gx ret)
        && !!has_opttyp ret (opttyp_of_type retsig)
        |-- !!tc_option_val retsig ret)) ->
(*new*) Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
  (forall n, semax_external Espec ids ef A P Q n) ->
  semax_func V G ge fs G' ->
  semax_func V G ge ((id, External ef argsig retsig cc)::fs)
       ((id, mk_funspec (argsig', retsig) cc A P Q NEP NEQ)  :: G').
Proof.
intros until ids.
intros b Hids Hargsig Hef Hni Hlen Hretty B1 B2 H [Hf' [GC Hf]].
rewrite Hargsig in *.  clear Hids Hargsig argsig'.
apply id_in_list_false in Hni.
split.
hnf; simpl; f_equal; auto.
constructor 2. simpl.
f_equal.
clear -Hlen.
revert ids Hlen; induction argsig; simpl; intros; auto.
destruct ids; auto.
destruct ids; auto. inv Hlen. simpl. f_equal; auto.
auto.
split; [ clear - B1 B2 GC; red; intros; destruct H; [ symmetry in H; inv H; exists b; auto | apply GC; trivial] |].
intros ge' GE1 GE2 ?.
specialize (Hf ge' GE1 GE2). 
unfold believe.
intros v' fsig' cc' A' P' Q'.
apply derives_imp. clear n. intros n ?. 
specialize (GE1 id); simpl in GE1. unfold fundef in GE1; rewrite B1 in GE1; simpl in GE1. 
specialize (GE2 b); simpl in GE2. unfold fundef in GE2; rewrite B2 in GE2; simpl in GE2.
destruct (eq_dec  (Vptr b Ptrofs.zero) v') as [?H|?H].
+ subst v'.
left.
specialize (H n).
destruct (semax_func_cons_aux {| genv_genv := ge'; genv_cenv := cenv_cs |} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GE1 Hni Hf' H0)
as [H4' [H4'' [H4 [H4b H4c]]]].
subst A' fsig' cc'.
apply JMeq_eq in H4b.
apply JMeq_eq in H4c.
subst P' Q'.
unfold believe_external; simpl; rewrite if_true; trivial. 
unfold fundef in GE2; unfold fundef; simpl; rewrite GE2.
assert (Hty: map fst (zip_with_tl ids argsig) = ids).
{ clear -Hlen. revert argsig Hlen. induction ids; auto.
simpl; intros. destruct argsig; auto. inv Hlen.
simpl. f_equal. auto. }
rewrite fst_split. simpl map. rewrite Hty.
split; auto.
split; auto. split; auto.
intros ts x ret phi Hlev Hx Hnec. apply Hretty.
+
(* **   Vptr b Ptrofs.zero <> v'  ********)
apply (Hf n v' fsig' cc' A' P' Q'); auto.
destruct H0 as [id' [NEP' [NEQ' [? ?]]]].
simpl in H0.
destruct (eq_dec id id').
- subst id'. rewrite PTree.gss in H0. inv H0.
destruct H2 as [? [? ?]]; subst. unfold fundef in H0; simpl in H0. congruence.
- exists id', NEP', NEQ'; split; auto.
simpl. rewrite PTree.gso in H0 by auto; auto.
Qed.

Definition main_params (ge: genv) start : Prop :=
exists b, exists func,
Genv.find_symbol ge start = Some b /\
    Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal func) /\
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

Lemma find_funct_ptr_exists:
forall (p: program) id f,
list_norepet (prog_defs_names p) ->
In (id, Gfun f) (prog_defs p) ->
exists b,
 Genv.find_symbol (Genv.globalenv p) id = Some b
/\ Genv.find_funct_ptr (Genv.globalenv p) b = Some f.
Proof.
intros.
pose proof (prog_defmap_norepet _ _ _ H H0).
destruct (proj1 (Genv.find_def_symbol _ _ _) H1)
as [b [? ?]].
exists b; split; auto.
unfold Genv.find_funct_ptr.
rewrite H3.
auto.
Qed.

Lemma funassert_initial_core:
forall (prog: program) ve te V G n,
  list_norepet (prog_defs_names prog) ->
  match_fdecs (prog_funct prog) G ->
  app_pred (funassert (nofunc_tycontext V G) (mkEnviron (filter_genv (globalenv prog)) ve te))
                  (initial_core (Genv.globalenv prog) G n).
Proof.
intros; split.
* intros id fs.
apply prop_imp_i; intros.
simpl ge_of; simpl fst; simpl snd.
unfold filter_genv, Map.get.
assert (exists f, In (id, f) (prog_funct prog)). {
  simpl in H1.
  forget (prog_funct prog) as g.
  clear - H1 H0.
  revert G H1 H0; induction g; destruct G; intros; simpl in *.
  elimtype False.
  rewrite PTree.gempty in H1; inv H1.
  inv H0.
  destruct a; simpl in *; subst.
  destruct (eq_dec i id). subst; eauto.
  specialize (IHg nil H1). inv H0.
  destruct a. destruct p.
  inv H0.
  simpl in H1.
  destruct (ident_eq i0 id). subst. eauto.
  destruct (IHg G); auto. rewrite PTree.gso in H1; auto.
  eauto.
}
destruct H2 as [f ?].
destruct (find_funct_ptr_exists prog id f) as [b [? ?]]; auto.
apply in_prog_funct_in_prog_defs; auto.
exists b. unfold fundef.
unfold globalenv. simpl. rewrite H3.
split; auto.
unfold func_at. destruct fs as [f0 cc0 A a a0].
unfold initial_core.
hnf. rewrite resource_at_make_rmap.
rewrite level_make_rmap.
unfold initial_core'.
simpl.
rewrite (Genv.find_invert_symbol (Genv.globalenv prog) id); auto.
assert (H9: In (id, mk_funspec f0 cc0 A a a0 P_ne Q_ne) G). {
  clear - H1.
  simpl in H1. unfold make_tycontext_g in H1; simpl in H1.
  induction G; simpl in *.
  rewrite PTree.gempty in H1; inv H1.
  destruct (ident_eq (fst a1) id); subst.
  change (@ptree_set) with (@PTree.set) in *. destruct a1; simpl in *.
  rewrite PTree.gss in H1; inv H1. left; auto.
  change (@ptree_set) with (@PTree.set) in *. destruct a1; simpl in *. 
  rewrite PTree.gso in H1; auto.
}
rewrite (find_id_i _ _ _ H9); auto.
clear - H0 H. unfold prog_defs_names, prog_funct in *.
eapply match_fdecs_norepet; eauto.
apply list_norepet_prog_funct'; auto.
*
intros loc' fsig' cc'.
intros w ? ?.
destruct H2 as [pp ?].
hnf in H2.
assert (exists pp, initial_core (Genv.globalenv prog) G n @ (loc',0) = PURE (FUN fsig' cc') pp).
case_eq (initial_core (@Genv.globalenv (Ctypes.fundef function) type prog) G n @ (loc', 0)); intros.
destruct (necR_NO _ _ (loc',0) sh n0 H1) as [? _].
rewrite H4 in H2 by auto.
inv H2.
eapply necR_YES in H1; try apply H3.
rewrite H1 in H2; inv H2.
eapply necR_PURE in H1; try apply H3.
rewrite H1 in H2; inv H2; eauto.
destruct H3 as [pp' ?].
unfold initial_core in H3.
rewrite resource_at_make_rmap in H3.
unfold initial_core' in H3.
if_tac in H3; [ | inv H3].
simpl.
simpl @fst in *. 
revert H3; case_eq (@Genv.invert_symbol (Ctypes.fundef function) 
                                        type (@Genv.globalenv (Ctypes.fundef function) type prog) loc' ); intros;
  [ | congruence].
revert H5; case_eq (find_id i G); intros; [| congruence].
destruct f as [?f ?A ?a ?a]; inv H6.
apply Genv.invert_find_symbol in H3.
exists i.
simpl ge_of. unfold filter_genv, Map.get.
unfold globalenv; simpl.
unfold fundef; rewrite H3.
split; auto.
assert (exists f, In (i,f) (prog_funct prog)
                  /\ type_of_fundef f = Tfunction (type_of_params (fst fsig')) (snd fsig') cc'). {
  clear - H0 H5.
  forget (prog_funct prog) as g.
  revert G H0 H5; induction g; intros.
  inv H0. inv H5.
  inv H0.
  simpl in H5.
  if_tac in H5. subst i0. inv H5. exists fd; split; auto. left; auto.
  destruct (IHg G0) as [f3 [? ?]]; auto. exists f3; split; auto.
  right; auto.
}
clear H4.
destruct H6 as [f [H4 H4']].
destruct (find_funct_ptr_exists prog i f) as [b [? ?]]; auto.
apply in_prog_funct_in_prog_defs; auto.
unfold fundef in *.
inversion2 H3 H6.
case_eq (Genv.find_var_info (Genv.globalenv prog) loc'); intros.
elimtype False; clear - H7 H6.
unfold Genv.find_funct_ptr in H7.
unfold Genv.find_var_info in H6.
destruct (Genv.find_def (Genv.globalenv prog) loc'); try destruct g0; congruence.
apply find_id_e in H5. apply in_map_fst in H5.
clear - H5.
revert H5; induction G; simpl; intro. contradiction.
destruct H5. subst.
change (@ptree_set) with (@PTree.set) in *. destruct a; simpl in *.
econstructor; rewrite PTree.gss; reflexivity.
destruct (IHG H) as [fs ?].
change (@ptree_set) with (@PTree.set) in *. destruct a; simpl in *.
destruct (eq_dec i0 i). econstructor; subst; rewrite PTree.gss; eauto.
econstructor; rewrite PTree.gso by auto; eauto.
Qed.

Lemma prog_contains_prog_funct: forall prog: program,
  list_norepet (prog_defs_names prog) ->
      prog_contains (globalenv prog) (prog_funct prog).
Proof.
intros; intro; intros.
apply (find_funct_ptr_exists prog id f); auto.
unfold prog_funct in H0.
change (AST.prog_defs prog) with (prog_defs prog).
induction (prog_defs prog). inv H0.
simpl in H0.  destruct a.
destruct g. simpl in H0. destruct H0. inv H0.  left. auto.
right; auto.  right; auto.
Qed.

Lemma funassert_initial_core_ext:
forall (ora : OK_ty) (prog: program) ve te V G n,
  list_norepet (prog_defs_names prog) ->
  match_fdecs (prog_funct prog) G ->
  app_pred (funassert (nofunc_tycontext V G) (mkEnviron (filter_genv (globalenv prog)) ve te))
                  (initial_core_ext ora (Genv.globalenv prog) G n).
Proof.
intros; split.
*
intros id fs.
apply prop_imp_i; intros.
simpl ge_of; simpl fst; simpl snd.
unfold filter_genv, Map.get.
assert (exists f, In (id, f) (prog_funct prog)). {
simpl in H1.
forget (prog_funct prog) as g.
clear - H1 H0.
revert G H1 H0; induction g; destruct G; intros; simpl in *.
elimtype False.
rewrite PTree.gempty in H1; inv H1.
inv H0.
destruct a; simpl in *; subst.
destruct (eq_dec i id). subst; eauto.
specialize (IHg nil H1). inv H0.
(*destruct (IHg). destruct g; simpl; auto.
constructor. apply match_fdecs_nil.
eauto. *)
destruct a. destruct p.
inv H0.
simpl in H1.
destruct (ident_eq i0 id). subst. eauto.
destruct (IHg G); auto. rewrite PTree.gso in H1; auto.
eauto.
(* simpl in H1.
destruct (IHg ((i0,f0)::G)); auto. eauto.
*)
}
destruct H2 as [f ?].
destruct (find_funct_ptr_exists prog id f) as [b [? ?]]; auto.
apply in_prog_funct_in_prog_defs; auto.
exists b. unfold fundef.
unfold globalenv. simpl. rewrite H3.
split; auto.
unfold func_at. destruct fs as [f0 cc0 A a a0].
unfold initial_core_ext.
hnf. rewrite resource_at_make_rmap.
rewrite level_make_rmap.
unfold initial_core'.
simpl.
rewrite (Genv.find_invert_symbol (Genv.globalenv prog) id); auto.
assert (H9: In (id, mk_funspec f0 cc0 A a a0 P_ne Q_ne) G). {
clear - H1.
simpl in H1. unfold make_tycontext_g in H1; simpl in H1.
induction G; simpl in *.
rewrite PTree.gempty in H1; inv H1.
destruct (ident_eq (fst a1) id); subst.
change (@ptree_set) with (@PTree.set) in *. destruct a1; simpl in *.
rewrite PTree.gss in H1; inv H1. left; auto.
change (@ptree_set) with (@PTree.set) in *. destruct a1; simpl in *. 
rewrite PTree.gso in H1; auto.
}
rewrite (find_id_i _ _ _ H9); auto.
clear - H0 H. unfold prog_defs_names, prog_funct in *.
eapply match_fdecs_norepet; eauto.
apply list_norepet_prog_funct'; auto.
*
(*intros loc'  [fsig' cc' A' P' Q' NEP' NEQ']; unfold func_at.*)
intros loc'  fsig' cc'.
intros w ? ?.
destruct H2 as [pp ?].
hnf in H2.
assert (exists pp, initial_core_ext ora (Genv.globalenv prog) G n @ (loc',0) = PURE (FUN fsig' cc') pp).
case_eq (initial_core_ext ora (Genv.globalenv prog) G n @ (loc',0)); intros.
destruct (necR_NO _ _ (loc',0) sh n0 H1) as [? _].
rewrite H4 in H2 by auto.
inv H2.
eapply necR_YES in H1; try apply H3.
rewrite H1 in H2; inv H2.
eapply necR_PURE in H1; try apply H3.
rewrite H1 in H2; inv H2; eauto.
destruct H3 as [pp' ?].
unfold initial_core_ext in H3.
rewrite resource_at_make_rmap in H3.
unfold initial_core' in H3.
if_tac in H3; [ | inv H3].
simpl.
simpl @fst in *.
revert H3; case_eq (@Genv.invert_symbol (Ctypes.fundef function) type
          (@Genv.globalenv (Ctypes.fundef function) type prog) loc'); intros;
[ | congruence].
revert H5; case_eq (find_id i G); intros; [| congruence].
destruct f as [?f ?A ?a ?a]; inv H6.
apply Genv.invert_find_symbol in H3.
exists i.
simpl ge_of. unfold filter_genv, Map.get.
unfold globalenv; simpl.
unfold fundef; rewrite H3.
split; auto.
assert (exists f, In (i,f) (prog_funct prog)
          /\ type_of_fundef f = Tfunction (type_of_params (fst fsig')) (snd fsig') cc'). {
clear - H0 H5.
forget (prog_funct prog) as g.
revert G H0 H5; induction g; intros.
inv H0. inv H5.
inv H0.
simpl in H5.
if_tac in H5. subst i0. inv H5. exists fd; split; auto. left; auto.
destruct (IHg G0) as [f3 [? ?]]; auto. exists f3; split; auto.
right; auto.
(*
destruct (IHg _ H3 H5) as [f [H4 H4']].
exists f; split; auto. right; auto.
*)
}
clear H4.
destruct H6 as [f [H4 H4']].
destruct (find_funct_ptr_exists prog i f) as [b [? ?]]; auto.
apply in_prog_funct_in_prog_defs; auto.
unfold fundef in *.
inversion2 H3 H6.
case_eq (Genv.find_var_info (Genv.globalenv prog) loc'); intros.
elimtype False; clear - H7 H6.
unfold Genv.find_funct_ptr in H7.
unfold Genv.find_var_info in H6.
destruct (Genv.find_def (Genv.globalenv prog) loc'); try destruct g0; congruence.
apply find_id_e in H5. apply in_map_fst in H5.
clear - H5.
revert H5; induction G; simpl; intro. contradiction.
destruct H5. subst.
change (@ptree_set) with (@PTree.set) in *. destruct a; simpl in *.
econstructor; rewrite PTree.gss; reflexivity.
destruct (IHG H) as [fs ?].
change (@ptree_set) with (@PTree.set) in *. destruct a; simpl in *.
destruct (eq_dec i0 i). econstructor; subst; rewrite PTree.gss; eauto.
econstructor; rewrite PTree.gso by auto; eauto.
Qed.

(* there's a place this lemma should be applied, perhaps in proof of semax_call *)
Lemma funassert_rho:
forall G rho rho', ge_of rho = ge_of rho' -> funassert G rho |-- funassert G rho'.
Proof. intros. apply funspecs_assert_rho; trivial. Qed.
(*Lenb: maybe move to seplog?*)

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
case_eq (@Genv.invert_symbol (Ctypes.fundef function) type (@Genv.globalenv (Ctypes.fundef function) type prog) (@fst block Z l) ); intros; auto.
rename i into id.
case_eq (find_id id G); intros; auto.
rename f into fs.
assert (exists f, In (id,f) (prog_funct prog)).
apply find_id_e in H2.
apply in_map_fst in H2.
eapply match_fdecs_in in H2; eauto.
apply in_map_iff in H2.
destruct H2 as [[i' f] [? ?]]. subst id; exists f; auto.
destruct H3 as [f ?].
apply Genv.invert_find_symbol in H1.
destruct (find_funct_ptr_exists prog id f) as [b [? ?]]; auto.
apply in_prog_funct_in_prog_defs; auto.
inversion2 H1 H4.
+ if_tac.
- destruct (IOK l) as [_ ?].
unfold initial_core in H6. rewrite resource_at_make_rmap in H6.
unfold initial_core' in H6. rewrite if_true in H6 by auto.
apply Genv.find_invert_symbol in H1.
unfold fundef in *; rewrite H1 in *.
rewrite H2 in *. destruct fs.
destruct H6 as [? [? ?]]. rewrite H7.
rewrite core_PURE; auto.
- destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
+ (*unfold fundef in *. rewrite H1,H2 in *.*)
if_tac;  destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
+ (*unfold fundef in *; rewrite H1 in *.*)
if_tac;   destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
+ rewrite ghost_of_core.
unfold inflate_initial_mem, initial_core; rewrite !ghost_of_make_rmap, ghost_core; auto.
Qed.

Lemma core_inflate_initial_mem':
forall (ora : OK_ty) (m: mem) (prog: program) (G: funspecs) (n: nat)
 (INIT: Genv.init_mem prog = Some m),
match_fdecs (prog_funct prog) G ->
  list_norepet (prog_defs_names prog) ->
core (inflate_initial_mem m (initial_core_ext ora (Genv.globalenv prog) G n)) =
     initial_core (Genv.globalenv prog) G n.
Proof.
intros.
assert (IOK := initial_core_ext_ok ora _ _ n _ H0 H INIT).
apply rmap_ext.
unfold inflate_initial_mem, initial_core, initial_core_ext; simpl.
rewrite level_core. rewrite !level_make_rmap; auto.
intro l.
unfold inflate_initial_mem, initial_core, initial_core_ext; simpl.
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
apply find_id_e in H2.
apply in_map_fst in H2.
eapply match_fdecs_in in H2; eauto.
apply in_map_iff in H2.
destruct H2 as [[i' f] [? ?]]. subst id; exists f; auto.
destruct H3 as [f ?].
apply Genv.invert_find_symbol in H1.
destruct (find_funct_ptr_exists prog id f) as [b [? ?]]; auto.
apply in_prog_funct_in_prog_defs; auto.
inversion2 H1 H4.
+ if_tac.
- destruct (IOK l) as [_ ?].
unfold initial_core_ext in H6. rewrite resource_at_make_rmap in H6.
unfold initial_core' in H6. rewrite if_true in H6 by auto.
apply Genv.find_invert_symbol in H1.
unfold fundef in *; rewrite H1 in *.
rewrite H2 in *. destruct fs.
destruct H6 as [? [? ?]]. rewrite H7.
rewrite core_PURE; auto.
- destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
+ (*unfold fundef in *; rewrite H1,H2 in *.*)
if_tac;  destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
+ (*unfold fundef in *; rewrite H1 in *.*)
if_tac;   destruct (access_at m l); try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
+ rewrite ghost_of_core.
unfold inflate_initial_mem, initial_core; rewrite !ghost_of_make_rmap, ghost_core; auto.
Qed.

Definition Delta1 V G {C: compspecs}: tycontext :=
make_tycontext ((1%positive,(Tfunction Tnil Tvoid cc_default))::nil) nil nil Tvoid V G nil.

Lemma match_globvars_in':
forall i t vl vs,
match_globvars vl vs = true ->
In (i,t) vs ->
exists g, In (i,g) vl /\ gvar_info g = t.
Proof.
induction vl; destruct vs; intros. inv H0.
destruct p; inv H.
inv H0. destruct p, H0. inv H0.  simpl in *.
destruct a.
pose proof (eqb_ident_spec i i0); destruct (eqb_ident i i0).
assert (i=i0) by (rewrite <- H0; auto). subst i0; clear H0.
apply andb_true_iff in H; destruct H.
apply eqb_type_true in H. subst t.
exists g; split3; auto.
destruct (IHvl _ H) as [g' [? ?]]. left; auto. exists g'; split; auto.
simpl in H. destruct a.
pose proof (eqb_ident_spec i0 i1); destruct (eqb_ident i0 i1).
apply andb_true_iff in H; destruct H.
destruct (IHvl _ H2) as [g' [? ?]]; auto. exists g'; split; auto.
right; auto.
apply IHvl in H. destruct H as [g' [? ?]]. exists g'; split; auto.
right; auto.
right; auto.
Qed.

Lemma match_globvars_in:
forall i vl vs, match_globvars vl vs = true -> In i  (map (@fst _ _) vs) -> In i (map (@fst _ _) vl).
Proof.
intros.
apply list_in_map_inv in H0. destruct H0 as [t [? ?]]. subst i.
destruct t as [i t].
destruct  (match_globvars_in' _ _ _ _ H H1) as [g [? ?]].
simpl. apply in_map_fst with g; auto.
Qed.

Lemma match_globvars_norepet:
forall vl vs,
list_norepet (map (@fst _ _) vl) ->
match_globvars vl vs = true ->
list_norepet (map (@fst _ _) vs).
Proof.
induction vl; destruct vs; simpl; intros.
constructor. destruct p. inv H0.
constructor.
destruct p; destruct a.
simpl in *.
inv H.
pose proof (eqb_ident_spec i i0); destruct (eqb_ident i i0).
assert (i=i0) by (apply H; auto); subst i0; clear H.
apply andb_true_iff in H0; destruct H0.
constructor; auto.
contradict H3.
eapply match_globvars_in; eauto.
assert (i<>i0). intro; subst; destruct H. specialize (H1 (eq_refl _)); inv H1.
clear H.
specialize (IHvl ((i,t)::vs) H4 H0).
inv IHvl.
constructor; auto.
Qed.

Lemma make_tycontext_g_denote:
forall id t l vs G,
list_norepet (map fst l) ->
match_globvars (prog_vars' l) vs = true ->
match_fdecs (prog_funct' l) G ->
((make_tycontext_g vs G) ! id = Some t <->
((exists f, In (id,f) G /\ t = type_of_funspec f) \/ In (id,t) vs)).
Proof.
intros.
assert (list_norepet (map (@fst _ _) (prog_funct' l) ++  (map (@fst _ _) (prog_vars' l)))). {
clear - H.
induction l; simpl. constructor.
destruct a; destruct g; simpl in *; inv H.
constructor; auto.
clear - H2; contradict H2.
induction l. inv H2. destruct a; destruct g; simpl in *. destruct H2; auto.
apply in_app in H2. destruct H2. right; apply IHl. apply in_app; auto.
destruct H; auto. right; apply IHl; apply in_app; auto.
specialize (IHl H3).
apply list_norepet_app in IHl. destruct IHl as [? [? ?]].
apply list_norepet_app; split3; auto.
constructor; auto.
clear - H2; contradict H2.
induction l. inv H2. destruct a; destruct g. simpl in H2. constructor 2; auto.
simpl in H2. destruct H2. subst; left; auto. right. auto.
apply list_disjoint_cons_r; auto.
clear - H2; contradict H2.
induction l. inv H2. destruct a; destruct g. simpl in H2.
destruct H2. subst; left; auto. right; auto.
simpl in *. right; auto.
}
forget (prog_vars' l) as vl.
forget (prog_funct' l) as fl.
clear l H.
revert G H2 H1; induction fl; intros.
* (* fl = nil *)
destruct G; inv H1.
simpl in H2.
apply iff_trans with (In (id, t) vs );
[ | clear; intuition; destruct H0 as [? [? ?]]; contradiction].
revert vs H0; induction vl; destruct vs; simpl in *; intros.
+(* fl = nil /\ vl = nil /\ vs = nil*)
rewrite PTree.gempty.
split; intros. discriminate. contradiction.
+ (* fl = nil /\ vl = nil /\ vs<>nil *)
clear H2.
destruct p. inv H0.
+ (* fl = nil /\ vl inductive case /\ vs = nil  *)
clear H0. rewrite PTree.gempty.
clear. intuition congruence.
+ (* fl = nil /\ vl inductive case /\ vs <> nil *)
destruct p. destruct a. simpl in *. inv H2.
specialize (IHvl H4).
destruct (ident_eq id i).
- subst id.
rewrite PTree.gss. split; intro. inv H.
auto.
destruct H. inv H. auto.
pose proof (eqb_ident_spec i i0); destruct (eqb_ident i i0).
assert (i=i0) by (rewrite <- H1; auto). subst i0; clear H1.
apply andb_true_iff in H0; destruct H0.
contradiction H3.
eapply match_globvars_in; eauto. apply in_map_fst with t. auto.
assert (i<>i0). intro; subst. clear - H1. destruct H1. specialize (H0 (eq_refl _)); inv H0.
clear H1.
pose proof (match_globvars_norepet _ _ H4 H0).
inv H1. contradiction H7. apply in_map_fst with t; auto.
- (* id <> i *)
rewrite PTree.gso by auto.
pose proof (eqb_ident_spec i i0).
destruct (ident_eq i i0).
subst. destruct H. rewrite H1 in H0 by auto.
rewrite andb_true_iff in H0; destruct H0.
apply eqb_type_true in H0. subst t0.
clear H H1.
rewrite IHvl; auto.
clear - n; intuition. inv H0; congruence.
destruct (eqb_ident i i0). contradict n0; apply H; auto.
eapply iff_trans; [ | apply (IHvl ((i,t0)::vs))]; clear IHvl.
simpl;  rewrite PTree.gso by auto. apply iff_refl.
auto.
*
inv H1.
+
inv H2.
specialize (IHfl _ H5 H6).
destruct (ident_eq id i). subst.
simpl; rewrite PTree.gss.
split; intro.
left; exists fspec.  inv H; auto.
f_equal.
destruct H as [[f [? ?]]| ?].
destruct H. inv H. auto.
elimtype False; clear - H3 H H6.
apply H3; apply in_app_iff. left; eapply match_fdecs_in; eauto.
apply in_map_fst in H; auto.
contradiction H3. apply in_app_iff; right.
subst.
eapply match_globvars_in; eauto.
apply in_map_fst in H; auto.
simpl; rewrite PTree.gso; auto.
rewrite IHfl. clear IHfl.
split; intros [[f [? ?]]| ?]; subst.
left; eauto. right; eauto.
left; eauto. destruct H. congruence.
exists f; eauto.
right; eauto.
(*+
simpl in H2; inv H2.
apply (IHfl G); auto.
*)
Qed.

Lemma tc_ge_denote_initial:
forall vs G (prog: program),
list_norepet (prog_defs_names prog) ->
match_globvars (prog_vars prog) vs = true->
match_fdecs (prog_funct prog) G ->
typecheck_glob_environ (filter_genv (globalenv prog)) (make_tycontext_g vs G).
Proof.
intros.
hnf; intros.
rewrite make_tycontext_g_denote in H2; eauto.
destruct H2 as [[f [? ?]]|?].
*
subst t.
unfold filter_genv.
destruct (match_fdecs_exists_Gfun prog G id f) as [fd [? H20]]; auto.
apply find_id_i; auto.
eapply match_fdecs_norepet; eauto.
unfold prog_defs_names in H.
clear - H.
unfold prog_funct.
change (AST.prog_defs prog) with (prog_defs prog) in H.
induction (prog_defs prog). constructor.
inv H. destruct a; simpl.  destruct g.
simpl map. constructor; auto. simpl in H2.
contradict H2.
clear - H2. induction l; simpl; auto.
destruct a. destruct g; simpl in *. destruct H2; auto. right; auto.
apply IHl; auto.
destruct (find_funct_ptr_exists prog id fd) as [b [? ?]]; auto.
exists b; auto.
*
unfold filter_genv.
destruct (match_globvars_in' _ _ _ _ H0 H2) as [g [? ?]].
apply in_prog_vars_in_prog_defs in H3.
pose proof (prog_defmap_norepet _ _ _ H H3).
destruct (proj1 (Genv.find_def_symbol _ _ _) H5)
as [b [? ?]].
exists b; auto.
Qed.

Lemma semax_prog_typecheck_aux:
forall vs G {C: compspecs} (prog: program) b,
list_norepet (prog_defs_names prog) ->
match_globvars (prog_vars prog) vs = true ->
match_fdecs (prog_funct prog) G ->
typecheck_environ
  (Delta1 vs G) (construct_rho (filter_genv (globalenv prog)) empty_env
    (PTree.set 1 (Vptr b Ptrofs.zero) (PTree.empty val))) .
Proof.
unfold Delta1; intros.
unfold construct_rho.
unfold make_tycontext.
unfold typecheck_environ.
unfold ve_of, ge_of, te_of.
split3.
*
unfold temp_types. unfold fst.
unfold make_tycontext_t.
unfold fold_right. unfold snd, fst.
unfold typecheck_temp_environ.
unfold make_tenv.
unfold Map.get.
intros.
rewrite PTree.gsspec in *. if_tac. inv H2.
+ exists (Vptr b Ptrofs.zero); split; auto. apply tc_val_tc_val'. simpl; auto.
+ rewrite PTree.gempty in H2. congruence.
*
unfold var_types.
unfold typecheck_var_environ. intros.
unfold make_tycontext_v. simpl.
rewrite PTree.gempty.
unfold Map.get, make_venv, empty_env.
rewrite PTree.gempty.
intuition. inv H2. destruct H2; inv H2.
*
unfold glob_types. unfold make_tycontext_t, snd.
eapply tc_ge_denote_initial; eauto.
Qed.

Lemma in_map_sig {A B} (E:forall b b' : B, {b=b'}+{b<>b'}) y (f : A -> B) l : In y (map f l) -> {x : A | f x = y /\ In x l }.
Proof.
induction l; intros HI.
- inversion HI.
- simpl in HI.
destruct (E (f a) y).
+ exists a; intuition.
+ destruct IHl. tauto. exists x; intuition.
Qed.

Lemma find_symbol_funct_ptr_ex_sig V ge id f :
(exists b : block,
  Genv.find_symbol ge id = Some b /\
  Genv.find_funct_ptr ge b = Some f) ->
{b : block |
Genv.find_symbol ge id = Some b /\
@Genv.find_funct_ptr (Ctypes.fundef function) V ge b = Some f}.
Proof.
intros Ex.
apply (decidable_countable_ex_sig Pos.of_nat); auto.
now intro; eexists; symmetry; apply Pos2Nat.id.
intros p.
assert (group : forall {A} {B} (a a':A) (b b':B), (a = a' /\ b = b') <-> ((a, b) = (a', b')))
by (intros;split; [ intros [<- <-]; reflexivity | intros E; injection E; auto]).
assert (sumbool_iff_left : forall (A A' B : Prop), (A -> A') -> {A}+{B} -> {A'}+{B}) by tauto.
assert (sumbool_iff_right : forall (A B B' : Prop), (B -> B') -> {A}+{B} -> {A}+{B'}) by tauto.
eapply sumbool_iff_left. apply group.
eapply sumbool_iff_right. rewrite group. apply (fun x => x).
pose proof type_eq.
pose proof eq_dec_statement.
repeat (hnf; decide equality; auto).
Qed.

Lemma initial_jm_funassert V (prog : Clight.program) m G n H H1 H2 :
(funassert (nofunc_tycontext V G) (empty_environ (globalenv prog)))
(m_phi (initial_jm prog m G n H H1 H2)).
Proof.
unfold initial_jm.
assert (FA: app_pred (funassert (nofunc_tycontext V G) (empty_environ (globalenv prog)))
(initial_world.initial_core (Genv.globalenv prog) G n)
     ).
apply funassert_initial_core; auto.
revert FA.
pose proof corable_funassert (nofunc_tycontext V G) (empty_environ (globalenv prog)) as CO.
rewrite corable_spec in CO. apply CO.
pose proof initial_mem_core as E.
unfold juicy_mem_core in *. erewrite E; try reflexivity.
Qed.

Lemma initial_jm_ext_funassert (ora : OK_ty) V (prog : Clight.program) m G n H H1 H2 :
(funassert (nofunc_tycontext V G) (empty_environ (globalenv prog)))
(m_phi (initial_jm_ext ora prog m G n H H1 H2)).
Proof.
unfold initial_jm_ext.
assert (FA: app_pred (funassert (nofunc_tycontext V G) (empty_environ (globalenv prog)))
(initial_world.initial_core_ext ora (Genv.globalenv prog) G n)
     ).
apply funassert_initial_core_ext; auto.
revert FA. 
pose proof corable_funassert (nofunc_tycontext V G) (empty_environ (globalenv prog)) as CO.
rewrite corable_spec in CO. apply CO.
pose proof initial_mem_core as E.
unfold juicy_mem_core in *. erewrite E; try reflexivity.
Qed.

Lemma semax_prog_rule_ext {CS: compspecs} :
  forall V G prog m h z,
     @semax_prog_ext CS prog z V G ->
     Genv.init_mem prog = Some m ->
     { b : block & { q : corestate &
       (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
       (forall jm, m_dry jm = m -> exists jm', semantics.initial_core (juicy_core_sem (cl_core_sem (globalenv prog))) h
                    jm q jm' (Vptr b Ptrofs.zero) nil) *
       forall n,
         { jm |
           m_dry jm = m /\ level jm = n /\
           nth_error (ghost_of (m_phi jm)) 0 = Some (Some (ext_ghost z, NoneP)) /\
           jsafeN (@OK_spec Espec) (globalenv prog) n z q jm /\
           no_locks (m_phi jm) /\
           matchfunspecs (globalenv prog) G (m_phi jm) /\
           (funassert (nofunc_tycontext V G) (empty_environ (globalenv prog))) (m_phi jm)
     } } }%type.
Proof.
  intros until m.
  pose proof I; intros.
  destruct H0 as [? [AL [HGG [[? [GC ?]] [GV ?]]]]].
  destruct (find_id (prog_main prog) G) as [fspec|] eqn:Hfind; try contradiction.
  assert (H4': exists post, In (prog_main prog, main_spec_ext' prog z post) G /\ fspec = main_spec_ext' prog z post). {
    destruct (find_id (prog_main prog) G) eqn:?.
    apply find_id_e in Heqo. destruct H4 as [post ?]. exists post.
    subst. split; auto. inv Hfind. auto. inv Hfind.
  } clear H4. rename H4' into H4.
  assert ({ f | In (prog_main prog, f) (prog_funct prog)}).
  forget (prog_main prog) as id.
  assert (H4': In id (map fst G)). {
  destruct H4 as [? [H4 _]].
  apply in_map_fst in H4. auto.
  }
  pose proof (match_fdecs_in _ _ _ H4' H2).
  apply in_map_sig in H5. 2:decide equality.
  destruct H5 as [[? ?] [? ?]]; subst.
  eauto.
  destruct H5 as [f ?].
  apply compute_list_norepet_e in H0.
  assert (indefs: In (prog_main prog, Gfun f) (AST.prog_defs prog))
    by (apply in_prog_funct_in_prog_defs; auto).
  pose proof (find_funct_ptr_exists prog (prog_main prog) f) as EXx.
  (* Genv.find_funct_ptr_exists is a Prop existential, we use constructive epsilon and
     decidability on a countable set to transform it to a Type existential *)
  apply find_symbol_funct_ptr_ex_sig in EXx; auto.

  pose proof I.
  destruct EXx as [b [? ?]]; auto.
  assert (E: type_of_fundef f = Tfunction Tnil tint cc_default). {
     destruct H4 as [post [? ?]].
      destruct (match_fdecs_exists_Gfun
                  prog G (prog_main prog)
                  (main_spec_ext' prog z post))
        as (fd, (Ifd, sametypes)); auto.
      {
        apply find_id_i; auto.
        eapply match_fdecs_norepet; eauto.
        clear -H0; revert H0.
        apply sublist_norepet.
        unfold prog_funct, prog_funct', prog_defs_names.
        replace (AST.prog_defs prog) with (prog_defs prog) by reflexivity.
        generalize (prog_defs prog); intros l; induction l as [|(i,[g|]) l];
          constructor; auto.
      }
      assert (fd = f).
      cut (Gfun fd = @Gfun _ type f); [ intros E; injection E; auto | ].
      apply (list_norepet_In_In (prog_main prog) _ _ (prog_defs prog)); auto.
      subst fd.
      auto.
    }
  exists b.
  unfold semantics.initial_core, juicy_core_sem.
  unfold j_initial_core, semantics.initial_core, cl_core_sem, cl_initial_core.
  eexists.
  unfold fundef in *.
  change (Genv.globalenv prog) with (genv_genv (globalenv prog)) in *.
  rewrite H6, H7.
  rewrite if_true by auto.
  repeat split; eauto.
  {
    intros. eexists; split. reflexivity.
    rewrite E.  
    repeat split; eauto; try solve [constructor].
  }
  intros n.
  exists (initial_jm_ext z _ _ _ n H1 H0 H2).
  repeat split.
  - simpl.
    rewrite inflate_initial_mem_level.
    unfold initial_core_ext. rewrite level_make_rmap; auto.

  - unfold initial_jm_ext; simpl.
    unfold inflate_initial_mem; rewrite ghost_of_make_rmap.
    unfold initial_core_ext; rewrite ghost_of_make_rmap.
    reflexivity.

  - specialize (H3 (genv_genv (globalenv prog))).
    spec H3. intros; apply sub_option_refl.
    spec H3. intros; apply sub_option_refl.
(*    specialize (H3 (globalenv prog) (prog_contains_prog_funct _ H0)).*)
    destruct H4 as [post [? ?]].
    unfold temp_bindings. simpl length. simpl typed_params. simpl type_of_params.
    pattern n at 1; replace n with (level (m_phi (initial_jm_ext z prog m G n H1 H0 H2))).
    pose (rho1 := mkEnviron (filter_genv (globalenv prog)) (Map.empty (block * type))
                           (Map.set 1 (Vptr b Ptrofs.zero) (Map.empty val))).
    pose (post' := fun rho => TT * EX rv:val, post nil (globals_of_env rho1) (env_set (globals_only rho) ret_temp rv)).
    eapply (semax_call_aux (Delta1 V G) (ConstType (ident->val))
              _ post _ (const_super_non_expansive _ _) (const_super_non_expansive _ _)
              nil (globals_of_env rho1) (fun _ => TT) (fun _ => TT)
              None (nil, tint) cc_default _ _ (normal_ret_assert post') _ _ _ _
              (construct_rho (filter_genv (globalenv prog)) empty_env
                 (PTree.set 1 (Vptr b Ptrofs.zero) (PTree.empty val)))
              _ _ b (prog_main prog));
      try apply H3; try eassumption; auto.
    + simpl.
        unfold inflate_initial_mem; rewrite ghost_of_make_rmap.
        unfold initial_core_ext; rewrite ghost_of_make_rmap.
        exists (Some (ext_both z, NoneP) :: nil); repeat constructor.
    + simpl.
      exists (Vptr b Ptrofs.zero).
      split; auto.
    + simpl snd.
      replace (params_of_fundef f) with (@nil type). simpl; auto. clear -E.
      destruct f as [[? ? [ | [] ]] | e [|] ? c] ; compute in *; congruence.
    + clear - GV H2 H0.
      split.
      eapply semax_prog_typecheck_aux; eauto.
      simpl.
      auto.
    + hnf; intros; intuition.
    +       intros rho' u U y UY k YK K.
      unfold normal_ret_assert; simpl.
      destruct K as [v [a1 [a2 [J [A1 [w A2]]]]]]. exists a1, a2; intuition. exists w; trivial.
    + rewrite HGG. apply cenv_sub_refl.
    + rewrite (corable_funassert _ _).
      simpl m_phi.
      rewrite core_inflate_initial_mem'; auto.
      do 3 (pose proof I).
      replace (funassert (Delta1 V G)) with
      (funassert (@nofunc_tycontext V G)).
      unfold rho1; apply funassert_initial_core; auto.
      apply same_glob_funassert.
      reflexivity.
    + apply now_later. intros ek vl tx' vx'.
      cbv zeta. rewrite proj_frame_ret_assert. simpl seplog.sepcon.
      subst post'. cbv beta.
      destruct ek; simpl proj_ret_assert; normalize.
      apply derives_subp.
      normalize. intro rv.
      simpl.
      eapply derives_trans, own.bupd_intro.
      intros ? ? ? ? Hora _ ?.
      destruct H9 as [[? [H10' [H11 ?]]] ?].
      hnf in H10', H11.
      destruct H9.
      subst a.
      change Clight_new.true_expr with true_expr.
      change (level (m_phi jm)) with (level jm).
      apply safe_loop_skip.
(*    +rewrite HGG. apply cenv_sub_refl.*)
    + unfold glob_types, Delta1. simpl @snd.
      forget (prog_main prog) as main.
      instantiate (1:= post).
      instantiate (1:= main_pre_ext prog z).
      assert (H8': list_norepet (map (@fst _ _) (prog_funct prog))). {
      clear - H0.
      unfold prog_defs_names in H0. unfold prog_funct.
      change (AST.prog_defs prog) with (prog_defs prog) in H0.
      induction (prog_defs prog); auto. inv H0.
      destruct a; destruct g; simpl; auto. constructor; auto.
      clear - H2; simpl in H2; contradict H2; induction l; simpl in *; auto.
      destruct a; destruct g; simpl in *; auto. destruct H2; auto.
      }
      forget (prog_funct prog) as fs.
      clear - H4 H8' H2. rename H8' into H8.
      fold (main_spec prog).
      forget (main_spec prog) as fd.
      revert G H2 H4 H8; induction fs; intros; inv H2.
      contradiction H4.
      simpl in *.
      destruct (ident_eq i main). subst. rewrite PTree.gss.
      destruct H4. inv H; auto.
      inv H8.
      contradiction H3.
      eapply match_fdecs_in; eauto.
      apply in_map_fst in H; auto.
      rewrite PTree.gso by auto.
      destruct H4; try congruence.
      inv H8.
      eapply IHfs; eauto.
    + intros.
      intros ? ?.
      split; apply derives_imp; auto.
    + unfold main_pre_ext.
      apply now_later.
      rewrite TT_sepcon_TT.
      eexists _, _; split; [apply core_unit|]; split; auto.
      eexists; eexists; split; [apply initial_jm_ext_eq|].
      split.
      * match goal with |- app_pred (globvars2pred (globals_of_env ?A) _ ?B) _ => 
           change (globals_of_env A) with (globals_of_env B)
          end.
          apply global_initializers; auto.
      * simpl.
        unshelve eexists; [split; auto; apply Share.nontrivial|].
        unfold set_ghost; rewrite ghost_of_make_rmap, resource_at_make_rmap.
        split; [apply resource_at_core_identity|].
        unfold ext_ghost; repeat f_equal.
        apply proof_irr.
    + simpl.
      rewrite inflate_initial_mem_level.
      unfold initial_core.
      apply level_make_rmap.
  - apply initial_jm_ext_without_locks.
  - apply initial_jm_ext_matchfunspecs. 
  -  destruct (initial_jm_ext_funassert z V prog m G n H1 H0 H2). auto.
  -  destruct (initial_jm_ext_funassert z V prog m G n H1 H0 H2). auto.
Qed.

Lemma semax_prog_rule' {CS: compspecs} :
forall V G prog m h,
 @semax_prog CS prog V G ->
 Genv.init_mem prog = Some m ->
 { b : block & { q : corestate &
   (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
   (forall jm, m_dry jm = m -> exists jm', semantics.initial_core (juicy_core_sem (cl_core_sem (globalenv prog))) h
                jm q jm' (Vptr b Ptrofs.zero) nil) *
   forall n z,
     { jm |
       m_dry jm = m /\ level jm = n /\
       nth_error (ghost_of (m_phi jm)) 0 = Some (Some (ext_ghost z, NoneP)) /\
       jsafeN (@OK_spec Espec) (globalenv prog) n z q jm /\
       no_locks (m_phi jm) /\
       matchfunspecs (globalenv prog) G (m_phi jm) /\
       (funassert (nofunc_tycontext V G) (empty_environ (globalenv prog))) (m_phi jm)
 } } }%type.
Proof.
intros until m.
pose proof I; intros.
destruct H0 as [? [AL [HGG [[? [Gcontains ?]] [GV ?]]]]].
assert (CSUBmain: cenv_sub  (@cenv_cs CS) (@prog_comp_env function prog)).
{ rewrite HGG; apply cenv_sub_refl. }
destruct (find_id (prog_main prog) G) as [fspec|] eqn:Hfind; try contradiction.
assert (H4': exists post, In (prog_main prog, main_spec' prog post) G /\ fspec = main_spec' prog post). {
destruct (find_id (prog_main prog) G) eqn:?.
apply find_id_e in Heqo. destruct H4 as [post ?]. exists post.
subst. split; auto. inv Hfind. auto. inv Hfind.
} clear H4. rename H4' into H4.
assert ({ f | In (prog_main prog, f) (prog_funct prog)}).
forget (prog_main prog) as id.
assert (H4': In id (map fst G)). {
destruct H4 as [? [H4 _]].
apply in_map_fst in H4. auto.
}
pose proof (match_fdecs_in _ _ _ H4' H2).
apply in_map_sig in H5. 2:decide equality.
destruct H5 as [[? ?] [? ?]]; subst.
eauto.
destruct H5 as [f ?].
apply compute_list_norepet_e in H0.
assert (indefs: In (prog_main prog, Gfun f) (AST.prog_defs prog))
by (apply in_prog_funct_in_prog_defs; auto).
pose proof (find_funct_ptr_exists prog (prog_main prog) f) as EXx.
(* Genv.find_funct_ptr_exists is a Prop existential, we use constructive epsilon and
 decidability on a countable set to transform it to a Type existential *)
apply find_symbol_funct_ptr_ex_sig in EXx; auto.

pose proof I.
destruct EXx as [b [? ?]]; auto.
assert (E: type_of_fundef f = Tfunction Tnil tint cc_default). {
 destruct H4 as [post [? ?]].
  destruct (match_fdecs_exists_Gfun
              prog G (prog_main prog)
              (main_spec' prog post))
    as (fd, (Ifd, sametypes)); auto.
  {
    apply find_id_i; auto.
    eapply match_fdecs_norepet; eauto.
    clear -H0; revert H0.
    apply sublist_norepet.
    unfold prog_funct, prog_funct', prog_defs_names.
    replace (AST.prog_defs prog) with (prog_defs prog) by reflexivity.
    generalize (prog_defs prog); intros l; induction l as [|(i,[g|]) l];
      constructor; auto.
  }
  assert (fd = f).
  cut (Gfun fd = @Gfun _ type f); [ intros E; injection E; auto | ].
  apply (list_norepet_In_In (prog_main prog) _ _ (prog_defs prog)); auto.
  subst fd.
  auto.
}
exists b.
unfold semantics.initial_core, juicy_core_sem.
unfold j_initial_core, semantics.initial_core, cl_core_sem, cl_initial_core.
eexists.
unfold fundef in *.
change (Genv.globalenv prog) with (genv_genv (globalenv prog)) in *.
rewrite H6, H7.
rewrite if_true by auto.
repeat split; eauto.
{
intros. eexists; split. reflexivity.
rewrite E.  
repeat split; eauto; try solve [constructor].
}
intros n z.
exists (initial_jm_ext z _ _ _ n H1 H0 H2).
repeat split.
- simpl.
rewrite inflate_initial_mem_level.
unfold initial_core_ext. rewrite level_make_rmap; auto.

- unfold initial_jm_ext; simpl.
unfold inflate_initial_mem; rewrite ghost_of_make_rmap.
unfold initial_core_ext; rewrite ghost_of_make_rmap.
reflexivity.

- specialize (H3 (globalenv prog)).
spec H3; [ intros; apply sub_option_refl |].
spec H3; [ intros; apply sub_option_refl |]. 
destruct H4 as [post [? ?]].
unfold temp_bindings. simpl length. simpl typed_params. simpl type_of_params.
pattern n at 1; replace n with (level (m_phi (initial_jm_ext z prog m G n H1 H0 H2))).
pose (rho1 := mkEnviron (filter_genv (globalenv prog)) (Map.empty (block * type))
                       (Map.set 1 (Vptr b Ptrofs.zero) (Map.empty val))).
pose (post' := fun rho => TT * EX rv:val, post nil (globals_of_env rho1) (env_set (globals_only rho) ret_temp rv)).
eapply (semax_call_aux (Delta1 V G) (ConstType (ident->val))
          _ post _ (const_super_non_expansive _ _) (const_super_non_expansive _ _)
          nil (globals_of_env rho1) (fun _ => TT) (fun _ => TT)
          None (nil, tint) cc_default _ _ (normal_ret_assert post') _ _ _ _
          (construct_rho (filter_genv (globalenv prog)) empty_env
             (PTree.set 1 (Vptr b Ptrofs.zero) (PTree.empty val)))
          _ _ b (prog_main prog));
  try apply H3; try eassumption; auto.
+ simpl.
    unfold inflate_initial_mem; rewrite ghost_of_make_rmap.
    unfold initial_core_ext; rewrite ghost_of_make_rmap.
    exists (Some (ext_both z, NoneP) :: nil); repeat constructor.
+ simpl.
  exists (Vptr b Ptrofs.zero).
  split; auto.
+ simpl snd.
  replace (params_of_fundef f) with (@nil type). simpl; auto. clear -E.
  destruct f as [[? ? [ | [] ]] | e [|] ? c] ; compute in *; congruence.
+ clear - GV H2 H0.
  split.
  eapply semax_prog_typecheck_aux; eauto.
  simpl.
  auto.
+ hnf; intros; intuition.
+ (*hnf; intros; intuition.
  unfold normal_ret_assert; simpl.
  extensionality rho'.
  normalize.
  unfold post'.
  apply pred_ext.
       normalize. intro rv. do 2 apply exp_right with rv; auto.
       normalize. intro rv. apply exp_right with rv; auto. *)
  intros rho' u U y UY k YK K.
  unfold normal_ret_assert; simpl.
  destruct K as [v [a1 [a2 [J [A1 [w A2]]]]]]. exists a1, a2; intuition. exists w; trivial.
+ rewrite (corable_funassert _ _).
  simpl m_phi.
  rewrite core_inflate_initial_mem'; auto.
  do 3 (pose proof I).
  replace (funassert (Delta1 V G)) with
  (funassert (@nofunc_tycontext V G)).
  unfold rho1; apply funassert_initial_core; auto.
  apply same_glob_funassert.
  reflexivity.
+ apply now_later.
  intros ek vl tx' vx'.
  cbv zeta. rewrite proj_frame_ret_assert. simpl seplog.sepcon.
  subst post'. cbv beta.
  destruct ek; simpl proj_ret_assert; normalize.
  apply derives_subp.
  normalize. intro rv.
  simpl.
  eapply derives_trans, own.bupd_intro.
  intros ? ? ? ? Hora _ ?.
  destruct H9 as [[? [H10' [H11 ?]]] ?].
  hnf in H10', H11.
  destruct H9.
  subst a.
  change Clight_new.true_expr with true_expr.
  change (level (m_phi jm)) with (level jm).
  apply safe_loop_skip.
+ unfold glob_types, Delta1. simpl @snd.
  forget (prog_main prog) as main.
  instantiate (1:= post).
  instantiate (1:= main_pre prog).
  assert (H8': list_norepet (map (@fst _ _) (prog_funct prog))). {
  clear - H0.
  unfold prog_defs_names in H0. unfold prog_funct.
  change (AST.prog_defs prog) with (prog_defs prog) in H0.
  induction (prog_defs prog); auto. inv H0.
  destruct a; destruct g; simpl; auto. constructor; auto.
  clear - H2; simpl in H2; contradict H2; induction l; simpl in *; auto.
  destruct a; destruct g; simpl in *; auto. destruct H2; auto.
  }
  forget (prog_funct prog) as fs.
  clear - H4 H8' H2. rename H8' into H8.
  fold (main_spec prog).
  forget (main_spec prog) as fd.
  revert G H2 H4 H8; induction fs; intros; inv H2.
  contradiction H4.
  simpl in *.
  destruct (ident_eq i main). subst. rewrite PTree.gss.
  destruct H4. inv H; auto.
  inv H8.
  contradiction H3.
  eapply match_fdecs_in; eauto.
  apply in_map_fst in H; auto.
  rewrite PTree.gso by auto.
  destruct H4; try congruence.
  inv H8.
  eapply IHfs; eauto.
+ intros.
  intros ? ?.
  split; apply derives_imp; auto.
+ unfold main_pre.
  apply now_later.
  rewrite TT_sepcon_TT.
  rewrite sepcon_comm.
  eexists; eexists; split; [apply initial_jm_ext_eq|].
  split; auto.
 match goal with |- app_pred (globvars2pred (globals_of_env ?A) _ ?B) _ => 
   change (globals_of_env A) with (globals_of_env B)
  end.
  apply global_initializers; auto.
+ simpl.
  rewrite inflate_initial_mem_level.
  unfold initial_core.
  apply level_make_rmap.
- apply initial_jm_ext_without_locks.
- apply initial_jm_ext_matchfunspecs. 
-  destruct (initial_jm_ext_funassert z V prog m G n H1 H0 H2). auto.
-  destruct (initial_jm_ext_funassert z V prog m G n H1 H0 H2). auto.
Qed.

(* This version works if we don't need to know anything about the external state. *)
Lemma semax_prog_rule {CS: compspecs} :
OK_ty = unit -> 
forall V G prog m h,
 @semax_prog CS prog V G ->
 Genv.init_mem prog = Some m ->
 { b : block & { q : corestate &
   (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
   (forall jm, m_dry jm = m -> exists jm', semantics.initial_core (juicy_core_sem (cl_core_sem (globalenv prog))) h
                jm q jm' (Vptr b Ptrofs.zero) nil) *
   forall n,
     { jm |
       m_dry jm = m /\ level jm = n /\
       (forall z, jsafeN (@OK_spec Espec) (globalenv prog) n z q jm) /\
       no_locks (m_phi jm) /\
       matchfunspecs (globalenv prog) G (m_phi jm) /\
       (funassert (nofunc_tycontext V G) (empty_environ (globalenv prog))) (m_phi jm)
 } } }%type.
Proof.
intro OKunit; intros.
destruct (semax_prog_rule' V G prog m h H H0) as [b [q [[?H ?H] ?H]]].
clear H H0.
destruct Espec. simpl in *.
exists b, q; split; auto.
clear H1 H2.
intros n. specialize (H3 n).
subst OK_ty. specialize (H3 tt).
destruct H3 as [jm [? [? ?]]]; exists jm; split3; auto.
destruct H1 as [? [? [? [? ?]]]]. split3; auto.
intro. destruct z. auto.
Qed.

Definition Delta_types V G {C: compspecs} (tys : list type) : tycontext :=
make_tycontext
(params_of_types
   1 ((Tfunction (type_of_params (params_of_types 2 tys)) Tvoid cc_default) :: tys))
nil nil Tvoid V G nil.

Lemma semax_prog_typecheck_aux_types:
forall vs G {C: compspecs} (prog: program) b (typed_args : list (val * type)),
list_norepet (prog_defs_names prog) ->
match_globvars (prog_vars prog) vs = true ->
match_fdecs (prog_funct prog) G ->
Forall (fun x => tc_val (snd x) (fst x)) typed_args ->
typecheck_environ
 (Delta_types vs G (map snd typed_args))
 (construct_rho
    (filter_genv (globalenv prog)) empty_env
    (PTree.set 1 (Vptr b Ptrofs.zero)
               (temp_bindings 2 (map fst typed_args)))).
Proof.
intros vs G C prog b typed_args NR MG MF TYP.
repeat split.
- unfold te_of, construct_rho.
intros i ty.
unfold make_tycontext, temp_types.
intros Found.
assert (make_tycontext_t_cons1 : forall i i' t l1 l2, (make_tycontext_t ((i, t) :: l1) l2) ! i' =
  if peq i' i then Some t else (make_tycontext_t l1 l2) ! i')
by (clear; intros i i' t l1 l2; simpl; rewrite PTree.gsspec; reflexivity).
unfold Delta_types, make_tycontext in Found.
simpl params_of_types in Found.
rewrite make_tycontext_t_cons1 in Found.
rewrite <-map_ptree_rel, Map.gsspec.
if_tac; if_tac in Found; subst; try tauto.
+ injection Found as <-.
  exists (Vptr b Ptrofs.zero); split; auto.
  apply tc_val_tc_val'; simpl; auto.
+ revert Found; generalize (2%positive).
  induction typed_args; intros p Found.
  * rewrite PTree.gempty in Found.
    discriminate.
  * simpl (params_of_types _ _ ) in Found.
    rewrite make_tycontext_t_cons1 in Found.
    simpl (map _ _).
    change (exists v : val, Map.get (make_tenv (PTree.set p (fst a) (temp_bindings (p+1)
      (map fst typed_args)))) i = Some v /\ tc_val' ty v).
    rewrite <-map_ptree_rel, Map.gsspec.
    inversion TYP.
    { if_tac; if_tac in Found; subst; try tauto.
      - injection Found as <-. apply tc_val_tc_val' in H3; eauto.
      - apply IHtyped_args; auto. }
- simpl.
rewrite PTree.gempty.
intro; discriminate.
- simpl.
unfold make_venv, Map.get, empty_env.
rewrite PTree.gempty.
intros [? ?]; discriminate.
- eapply tc_ge_denote_initial; eauto.
Qed.

Lemma find_id_maketycontext_s G id : (make_tycontext_s G) ! id = find_id id G.
Proof.
induction G as [|(i,t) G]; simpl.
- destruct id; reflexivity.
- rewrite PTree.gsspec.
do 2 if_tac; congruence.
Qed.

Lemma semax_prog_entry_point {CS: compspecs} V G prog b id_fun id_arg arg A 
(P Q: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A)) mpred)
NEP NEQ h:
@semax_prog CS prog V G ->
Genv.find_symbol (globalenv prog) id_fun = Some b ->
find_id id_fun G =
Some (mk_funspec ((id_arg, Tpointer Tvoid noattr) :: nil, tptr Tvoid)
                 cc_default A P Q NEP NEQ) ->
is_pointer_or_null arg ->
(* initial environment *)
let rho0 : environ :=
  construct_rho
    (filter_genv (globalenv prog)) empty_env
    (PTree.set 1 (Vptr b Ptrofs.zero)
               (PTree.set id_arg arg (PTree.empty val))) in

(* initial environment without the function => to check jm |= P a *)
let rho1 : environ :=
  construct_rho
    (filter_genv (globalenv prog)) empty_env
    ((* PTree.set 1 (Vptr b Ptrofs.zero) *)
      (PTree.set id_arg arg (PTree.empty val))) in

{ q : corestate |
(forall jm, Val.inject (Mem.flat_inj (nextblock (m_dry jm))) arg arg ->
  exists jm', semantics.initial_core
  (juicy_core_sem (cl_core_sem (globalenv prog))) h
  jm q jm' (Vptr b Ptrofs.zero) (arg :: nil)) /\

forall (jm : juicy_mem) ts a,
  app_pred (P ts a rho1) (m_phi jm) ->
(*      (forall rho, app_pred (! (Q ts a rho >=> !!False)) (m_phi jm)) ->*)
  app_pred (funassert (Delta_types V G (Tpointer Tvoid noattr::nil)) rho0) (m_phi jm) ->
  forall z, app_pred (ext_compat z) (m_phi jm) -> jsafeN (@OK_spec Espec) (globalenv prog) (level jm) z q jm }.
Proof.
intros SP Findb id_in_G arg_p.
assert (CSUBmain: cenv_sub (@cenv_cs CS) (globalenv prog)).
{ destruct SP as [_ [_ [CSEQ _]]]. rewrite CSEQ; apply cenv_sub_refl. }
destruct ((fun x => x) SP) as (_ & _ & _ & (MatchFdecs & (Gcontains & Believe)) & _).
specialize (Believe (globalenv prog)).
spec Believe; [ intros; apply sub_option_refl |].
spec Believe; [ intros; apply sub_option_refl |]. (*
spec Believe. now apply prog_contains_prog_funct, compute_list_norepet_e, SP.
spec Believe. (*now symmetry; apply SP.*) apply CSUBmain. *)
pose proof Believe as Believe_.
specialize (Believe 5%nat).
unfold claims in *.
unfold nofunc_tycontext in *.
simpl glob_specs in Believe.
rewrite <-find_id_maketycontext_s in id_in_G.

specialize (Believe (Vptr b Ptrofs.zero)
                  ((id_arg, Tpointer Tvoid noattr) :: nil, tptr Tvoid)
                  cc_default A P Q _ (necR_refl _)).
spec Believe.
{ exists id_fun, NEP, NEQ. split; auto. exists b; split; auto. }
simpl (semantics.initial_core _). unfold j_initial_core.
simpl (semantics.initial_core _). unfold cl_initial_core.
if_tac [_|?]. 2:solve[tauto].

destruct (Genv.find_funct_ptr (globalenv prog) b) as [f|] eqn:Eb; swap 1 2.
{ exfalso.
destruct Believe as [H | (b' & fu & (? & WOB & ASD) & WOBk)].
+ unfold believe_external in *.
  unfold Genv.find_funct in *. rewrite if_true in H by trivial.
  simpl in Eb, H. rewrite Eb in H. auto. 
+ assert (b' = b) by congruence. simpl in WOB, Eb. subst b'. congruence.
}
assert (Ef : type_of_fundef f = Tfunction (Tcons (Tpointer Tvoid noattr) Tnil) (tptr Tvoid) cc_default). {
(* I think this can be proved using believe_internal / believe_external ? *)
destruct Believe as [BE|BI].
- unfold believe_external in *.
  simpl in BE. if_tac [_|?] in BE. 2:tauto.
  replace (Genv.find_funct_ptr (globalenv prog)) with
  (Genv.find_funct_ptr (Genv.globalenv prog)) in *
    by reflexivity.
  unfold fundef in BE.
  rewrite Eb in BE.
  destruct f as [ | ef sigargs sigret c'']. tauto.
  simpl.
  destruct BE as [((Es & -> & ASD & LEN) & ?) _]. injection Es as Es <-. f_equal.
  destruct sigargs as [ | ? [ | ]]; simpl in Es.
  + congruence.
  + congruence.
  + (* in believe_external, zip_with_tl throws away arguments if they are not named *)
    simpl in LEN. disc.

- destruct BI as (b' & fu & (? & WOB & ? & ? & ? & ? & wob & ?) & WOBk).
  unfold fn_funsig in *. injection wob as Hpar Hret.
  assert (b' = b) by congruence. subst b'.
  simpl in Eb, WOB. assert (f = Internal fu) by congruence. subst f.
  simpl.
  unfold type_of_function.
  destruct fu as [? ? [ | [] [ | [] ]] ? ?]; simpl in *; congruence.
}
rewrite Ef.
eexists. split.
intros. eexists; repeat split; eauto.
repeat constructor.
{clear - arg_p.
destruct arg; try contradiction.
first [apply val_casted_long_ptr |  apply val_casted_int_ptr]; reflexivity.
apply val_casted_ptr_ptr. }
{ clear - arg_p. destruct arg; try contradiction; simpl in *.
  unfold Tptr. destruct Archi.ptr64; try contradiction; auto.
  unfold Tptr. destruct Archi.ptr64; auto.
}
{ unfold arg_well_formed. constructor; auto. } 

intros jm ts a m_sat_Pa m_funassert.

assert (Pf : params_of_fundef f = Tpointer Tvoid noattr :: nil).
{ clear -Ef.
destruct f as [f|f]. simpl in *.
unfold type_of_function in *.
destruct f as [? ? [ | [] [ | [] ]] ? ?]; simpl in *; congruence.
simpl in *. injection Ef; intros; subst. reflexivity. }

pose (rho3 :=
      construct_rho
        (filter_genv (globalenv prog)) empty_env
        (PTree.set 1 (Vptr b Ptrofs.zero)
                   (temp_bindings 2 (map fst ((arg, Tpointer Tvoid noattr) :: nil))))).
pose proof I.
intros z HZ.
set (R:= fun rho' => EX _ : val,
       (EX x : val, emp * Q ts a (env_set (globals_only rho') ret_temp x))).
eapply
(semax_call_aux
   (Delta_types V G (Tpointer Tvoid noattr::nil)) A P
   (fun _ _ => Q ts a) Q NEP NEQ
   ts a (fun _ => emp) (fun _ => emp)
   None ((id_arg, Tpointer Tvoid noattr)::nil, tptr Tvoid) cc_default _ _
   (normal_ret_assert R)
   _ _ _ _ rho3
   _ _ b id_fun);
try apply H3; try eassumption; auto.

(* tc_expr *)

simpl. exists (Vptr b Ptrofs.zero); auto.

(* tc_exprlist *)
rewrite Pf. simpl. exists arg; simpl; auto.

(* guard_environ *)
split; try apply I.
eapply semax_prog_typecheck_aux_types; eauto.
apply compute_list_norepet_e. apply SP. apply SP.

(* closed_wrt_modvars *)
intro.
reflexivity.

(* equality of normal_ret_assert 
unfold R.
unfold normal_ret_assert; simpl.
extensionality rho'.
normalize.
reflexivity.*)

(*entailment of  normal_ret_assert *)
rewrite <- box_all. apply now_later. unfold R.
unfold normal_ret_assert. simpl. intros. destruct H2 as [v [a1 [a2 [J [HY [w HQ]]]]]].
exists v, w, a1, a2; auto.

(* globalenv prog = cenv_cs *)
(*destruct SP as [? [AL [HGG [[H2 H3] [GV _]]]]].
rewrite HGG. reflexivity.*)

(* safety: we conclude as we add an infinite loop at the end *)
apply now_later.
intros ek ret te env phi lev phi' necr [[Guard FrameRA] FunAssert].
apply own.bupd_intro; intros ora jm0 Hora Heq <-.
rewrite proj_frame_ret_assert in FrameRA. simpl seplog.sepcon in FrameRA.
destruct ek; simpl proj_ret_assert in FrameRA;
try solve [elimtype False; clear - FrameRA; destruct FrameRA as [? [? [? [[? ?] ?]]]]; contradiction];
try solve [elimtype False; clear - FrameRA; destruct FrameRA as [? [? [? [? ?]]]]; contradiction].
apply safe_loop_skip.
(* equivalence between Q and Q' *)
intros vl; split; apply derives_imp; apply derives_refl'; reflexivity.

(* precondition *)
refine (derives_e _ _ _ _ m_sat_Pa).
normalize.
eapply derives_trans; [|apply now_later].
apply derives_refl'; f_equal.
rewrite Pf.
simpl.
unfold globals_only, env_set, construct_rho.
simpl.
f_equal.
extensionality i; destruct i; reflexivity.
unfold make_tenv, force_val, sem_cast_pointer, eval_id.
extensionality i.
rewrite PTree.gsspec.
unfold Map.set.
if_tac; if_tac; try congruence; subst.
unfold liftx, lift; simpl.
now destruct arg; inversion arg_p; auto.
now destruct i; reflexivity.
Qed.

Lemma match_fdecs_length funs K:
  match_fdecs funs K -> length funs = length K.
Proof. induction 1; trivial. 
simpl; rewrite IHmatch_fdecs; trivial.
Qed.

Lemma match_fdecs_nil_iff funs K (M: match_fdecs funs K):
(funs = nil) <-> (K=nil).
Proof. apply match_fdecs_length in M. 
split; intros; subst; simpl in M.
destruct K; trivial; inv M.
destruct funs; trivial; inv M.
Qed.

Lemma match_fdecs_cons_D f funs k K (M: match_fdecs (cons f funs) (cons k K)):
exists i fd fspec, f=(i,fd) /\ k=(i,fspec) /\ 
     type_of_fundef fd = type_of_funspec fspec /\
     match_fdecs funs K.
Proof. inv M. exists i, fd, fspec; intuition. Qed.

Lemma match_fdecs_cons_D1 f funs K (M: match_fdecs (cons f funs) K):
exists i fd fspec G, f=(i,fd) /\ K=cons (i,fspec) G /\ 
     type_of_fundef fd = type_of_funspec fspec /\
     match_fdecs funs G.
Proof. inv M. exists i, fd, fspec, G; intuition. Qed.

Lemma match_fdecs_cons_D2 funs k K (M: match_fdecs funs (cons k K)):
exists i fd fspec fs, funs=cons (i,fd) fs /\ k=(i,fspec) /\ 
     type_of_fundef fd = type_of_funspec fspec /\
     match_fdecs fs K.
Proof. inv M. exists i, fd, fspec, fs; intuition. Qed.

(*Lemma semax_func_length V G {C: compspecs} funs K (M: semax_func V G funs K):
 length funs = length K.
Proof. destruct M as [M _]. apply match_fdecs_length in M; trivial. Qed.*)
Lemma semax_func_length ge V G {C: compspecs} funs K (M: semax_func V G ge funs K):
 length funs = length K.
Proof. destruct M as [M _]. apply match_fdecs_length in M; trivial. Qed.

Lemma match_fdecs_app: forall vl G vl' G',
match_fdecs vl G -> match_fdecs vl' G' -> match_fdecs (vl ++ vl') (G ++ G').
Proof. induction vl; simpl; intros; inv H; simpl in *; trivial; econstructor; eauto. Qed.

Lemma prog_contains_nil ge: prog_contains ge nil.
Proof. red; intros. inv H. Qed.
Lemma prog_contains_app_inv ge: forall funs1 funs2, prog_contains ge (funs1 ++ funs2) ->
  prog_contains ge funs1 /\ prog_contains ge funs2.
Proof. induction funs1; simpl; intros; split; trivial.
+ apply prog_contains_nil.
+ red; intros. apply (H id f).
destruct H0; [ left; trivial | right; apply in_or_app; left; trivial].
+ red; intros. apply (H id f).
right; apply in_or_app; right; trivial.
Qed.

Lemma genv_contains_nil ge: genv_contains ge nil.
Proof. red; intros. inv H. Qed.
Lemma genv_contains_app_inv ge: forall funs1 funs2, genv_contains ge (funs1 ++ funs2) ->
  genv_contains ge funs1 /\ genv_contains ge funs2.
Proof. induction funs1; simpl; intros; split; trivial.
+ apply genv_contains_nil.
+ red; intros. apply (H id f).
destruct H0; [ left; trivial | right; apply in_or_app; left; trivial].
+ red; intros. apply (H id f).
right; apply in_or_app; right; trivial.
Qed.
Lemma genv_contains_app ge funs1 funs2 (G1:genv_contains ge funs1) (G2: genv_contains ge funs2):
genv_contains ge (funs1 ++ funs2).
Proof. red; intros. apply in_app_or in H; destruct H; [apply G1 | apply G2]; trivial. Qed. 

Lemma find_id_app i fs: forall (G1 G2: funspecs) (G: find_id i (G1 ++ G2) = Some fs),
find_id i G1 = Some fs \/ find_id i G2 = Some fs.
Proof. induction G1; simpl; intros. right; trivial. 
destruct a. destruct (eq_dec i i0); [ left; trivial | eauto].
Qed.

Lemma make_tycontext_s_app_inv i fs G1 G2 (G: (make_tycontext_s (G1 ++ G2)) ! i = Some fs):
  (make_tycontext_s G1) ! i = Some fs \/ (make_tycontext_s G2) ! i = Some fs.
Proof. rewrite ! find_id_maketycontext_s  in *. apply find_id_app; trivial. Qed.

Lemma believe_app {cs} ge V H G1 G2 n 
(B1: @believe cs Espec (nofunc_tycontext V H) ge (nofunc_tycontext V G1) n)
(B2: @believe cs Espec (nofunc_tycontext V H) ge (nofunc_tycontext V G2) n):
@believe cs Espec (nofunc_tycontext V H) ge (nofunc_tycontext V (G1 ++ G2)) n.
Proof. 
intros v fsig cc A P Q k NEC CL.
destruct CL as [i [HP [HQ [G B]]]].
simpl in G. apply make_tycontext_s_app_inv in G; destruct G.
+ apply B1; trivial. exists i, HP, HQ; simpl; split; trivial.
+ apply B2; trivial. exists i, HP, HQ; simpl; split; trivial.
Qed.

Lemma semax_func_app ge cs V H: forall funs1 funs2 G1 G2
(SF1: @semax_func V H cs ge funs1 G1) (SF2: @semax_func V H cs ge funs2 G2)
(L:length funs1 = length G1),
@semax_func V H cs ge (funs1 ++ funs2) (G1++G2).
Proof.
intros. destruct SF1 as [MF1 [GC1 B1]]. destruct SF2 as [MF2 [GC2 B2]]. 
split; [ apply match_fdecs_app; trivial | intros; subst].
split; [ apply genv_contains_app; trivial | intros].
apply believe_app; [ apply B1 | apply B2]; trivial.
Qed.

Lemma semax_func_subsumption ge cs V V' F F'
  (SUB: tycontext_sub (nofunc_tycontext V F) (nofunc_tycontext V F'))
  (HV: forall id, sub_option (make_tycontext_g V F) ! id (make_tycontext_g V' F') ! id):
forall funs G (SF: @semax_func V F cs ge funs G),  @semax_func V' F' cs ge funs G.
Proof.
intros. destruct SF as [MF [GC B]]. split; [trivial | split; [ trivial | intros]]. specialize (B _ Gfs Gffp n). 
assert (TS: forall f, tycontext_sub (func_tycontext' f (nofunc_tycontext V F)) (func_tycontext' f (nofunc_tycontext V' F'))).
{ clear - SUB HV.
destruct SUB as [SUBa [SUBb [SUBc [SUBd [SUBe SUBf]]]]]; simpl in *.
unfold func_tycontext'; split; simpl; intuition.
destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! id); trivial. }
eapply believe_monoL; [eassumption | apply cspecs_sub_refl | eassumption]. 
Qed.

Lemma semax_func_join {cs ge V1 H1 V2 H2 V funs1 funs2 G1 G2 H}
  (SF1: @semax_func V1 H1 cs ge funs1 G1) (SF2: @semax_func V2 H2 cs ge funs2 G2)

  (K1: forall i, sub_option ((make_tycontext_g V1 H1) ! i) ((make_tycontext_g V1 H) ! i))
  (K2: forall i, subsumespec ((make_tycontext_s H1) ! i) ((make_tycontext_s H) ! i))
  (K3: forall i, sub_option ((make_tycontext_g V1 H) ! i) ((make_tycontext_g V H) ! i))

  (N1: forall i, sub_option ((make_tycontext_g V2 H2) ! i) ((make_tycontext_g V2 H) ! i))
  (N2: forall i, subsumespec ((make_tycontext_s H2) ! i) ((make_tycontext_s H) ! i))
  (N3: forall i, sub_option ((make_tycontext_g V2 H) ! i) ((make_tycontext_g V H) ! i)):
@semax_func V H cs ge (funs1 ++ funs2) (G1++G2).
Proof.
apply semax_func_app.
+ eapply semax_func_subsumption; [ | | apply SF1].
- hnf; simpl. intuition.
* rewrite PTree.gempty; trivial.
* rewrite PTree.gempty. simpl; trivial.
- intros. specialize (K1 id). eapply sub_option_trans. apply K1. trivial.
+ eapply semax_func_subsumption; [ | | apply SF2].
- hnf; simpl. intuition.
* rewrite PTree.gempty; trivial.
* rewrite PTree.gempty. simpl; trivial.
- intros. specialize (N1 id). eapply sub_option_trans. apply N1. trivial.
+ clear - SF1. eapply semax_func_length. apply SF1.
Qed.

Lemma semax_func_join_sameV {cs ge H1 H2 V funs1 funs2 G1 G2 H}
  (SF1: @semax_func V H1 cs ge funs1 G1) (SF2: @semax_func V H2 cs ge funs2 G2)

  (K1: forall i, sub_option ((make_tycontext_g V H1) ! i) ((make_tycontext_g V H) ! i))
  (K2: forall i, subsumespec ((make_tycontext_s H1) ! i) ((make_tycontext_s H) ! i))

  (N1: forall i, sub_option ((make_tycontext_g V H2) ! i) ((make_tycontext_g V H) ! i))
  (N2: forall i, subsumespec ((make_tycontext_s H2) ! i) ((make_tycontext_s H) ! i)):
@semax_func V H cs ge (funs1 ++ funs2) (G1++G2).
Proof. apply (semax_func_join SF1 SF2); try eassumption; intros; apply sub_option_refl. Qed.

Lemma sub_option_subsumespec x1 x2 (H:sub_option x1 x2): subsumespec x1 x2.
Proof.
destruct x1 as [fs1 |]; destruct x2 as [fs2 |]; trivial; inv H.
apply subsumespec_refl.
Qed.

Lemma make_tycontext_g_nilV_elim G i t: (make_tycontext_g nil G) ! i = Some t ->
  exists fs, find (fun x => ident_eq i (fst x)) G = Some (i,fs) /\ t=type_of_funspec fs.
Proof.
induction G; simpl; intros. rewrite PTree.gempty in H. congruence.
destruct a as [j fs]; unfold ident_eq; simpl in *.
rewrite PTree.gsspec in H. destruct (peq i j); subst; simpl; eauto.
inv H. exists fs; split; trivial.
Qed.

Fixpoint find_idV (id : ident) (G : varspecs) {struct G} : option type:=
match G with
| nil => None
| (id', f) :: G' => if peq id id' then Some f else find_idV id G'
end.

Lemma make_tycontext_s_g V H i fs (HH: (make_tycontext_s H) ! i = Some fs):
  (make_tycontext_g V H) ! i = Some (type_of_funspec fs).
Proof.
induction H; simpl in *.  rewrite PTree.gempty in HH; congruence.
destruct a as [j gs]; simpl in *.  rewrite PTree.gsspec.
destruct (peq i j); subst.
+ rewrite PTree.gss in HH; inv HH; trivial.
+ rewrite PTree.gso in HH; auto.
Qed.

Lemma make_tycontext_g_consV_elim:
forall i t v vs G (HV: list_norepet ((map fst (v::vs)) ++ (map fst G))),
(make_tycontext_g (v::vs) G) ! i = Some t ->
if peq i (fst v) then t=snd v else (make_tycontext_g vs G) ! i = Some t.
Proof.
intros. destruct v as [j u]. induction G; simpl in *.
+ rewrite PTree.gsspec in H. destruct (peq i j); subst; trivial. inv H; trivial.
+ destruct a as [k s]; simpl in *.  rewrite PTree.gsspec in *.
destruct (peq i k); subst.
- inv H. destruct (peq k j); trivial; subst. clear - HV. inv HV.
elim H1; clear. apply in_or_app.  right; left; trivial.
- apply IHG; trivial.  clear - HV. inv HV. apply list_norepet_append_inv in H2.
destruct H2 as [? [? ?]]. constructor.
* intros N. apply H1; clear - N.  apply in_app_or in N. apply in_or_app.
  destruct N; [left; trivial | right; right; trivial].
* inv H0. apply list_norepet_append; trivial.
  clear - H2. hnf; intros. apply H2; trivial.  right; trivial.
Qed.
Lemma make_tycontext_g_consV_mk:
forall i t v vs G (HV: list_norepet ((map fst (v::vs)) ++ (map fst G))),
(if peq i (fst v) then t=snd v else (make_tycontext_g vs G) ! i = Some t) ->
(make_tycontext_g (v::vs) G) ! i = Some t.
Proof.
intros. destruct v as [j u]. simpl in *. induction G; simpl in *. rewrite app_nil_r in HV.
+ rewrite PTree.gsspec. destruct (peq i j); subst; trivial.
+ destruct a as [k s]; simpl in *. rewrite PTree.gsspec in *.
destruct (peq i k); subst.
- destruct (peq k j); trivial; subst. clear - HV. inv HV.
elim H1; clear. apply in_or_app.  right; left; trivial.
- apply IHG; trivial.  clear - HV. inv HV. apply list_norepet_append_inv in H2.
destruct H2 as [? [? ?]]. constructor.
* intros N. apply H1; clear - N.  apply in_app_or in N. apply in_or_app.
  destruct N; [left; trivial | right; right; trivial].
* inv H0. apply list_norepet_append; trivial.
  clear - H2. hnf; intros. apply H2; trivial.  right; trivial.
Qed.

Lemma make_tycontext_g_nilG_findV V i: (make_tycontext_g V nil) ! i = find_idV i V.
Proof.
induction V; simpl. apply PTree.gempty.
destruct a as [j t]; simpl.
rewrite PTree.gsspec. destruct (peq i j); subst; simpl; eauto.
Qed.

Lemma make_tycontext_g_consG_elim i t V g G (HG: (make_tycontext_g V (g::G)) ! i = Some t):
if peq i (fst g) then t=type_of_funspec (snd g) else (make_tycontext_g V G) ! i = Some t.
Proof.
destruct g as [j fs]; simpl in *.
rewrite PTree.gsspec in HG. destruct (peq i j); subst; auto. inv HG; trivial.
Qed.
Lemma make_tycontext_g_consG_mk i t V g G
  (HG: if peq i (fst g) then t=type_of_funspec (snd g) else (make_tycontext_g V G) ! i = Some t):
(make_tycontext_g V (g::G)) ! i = Some t.
Proof.
destruct g as [j fs]; simpl in *.
rewrite PTree.gsspec. destruct (peq i j); subst; auto.
Qed.

Lemma find_idV_In_map_fst i t: forall V (Hi: find_idV i V = Some t), In i (map fst V).
Proof.
induction V; simpl; intros. inv Hi.
destruct a as [j u]; simpl. destruct (peq i j); subst; [left | right]; auto.
Qed.

Lemma list_norepet_cut_middle {A:Set} l1 l2 (a:A) (Ha: list_norepet (l1 ++ (a :: l2))): list_norepet (l1 ++ l2).
Proof.
apply list_norepet_append_inv in Ha. destruct Ha as [VH1 [VH2 D]]. inv VH2.
apply list_norepet_append; trivial.
intros x y X Y. apply D; [ trivial | right; trivial].
Qed.

Lemma make_context_g_mk_findV_mk: forall H V (VH:list_norepet (map fst V ++ map fst H)) i t
(Heqd : find_idV i V = Some t), (make_tycontext_g V H) ! i = Some t.
Proof.
induction H; intros.
+ rewrite make_tycontext_g_nilG_findV; trivial.
+ apply make_tycontext_g_consG_mk. destruct a as [j fs]; simpl in *.
destruct (peq i j); subst; simpl.
- apply list_norepet_append_inv in VH. destruct VH as [_ [_ VH]].
elim (VH j j); trivial.
apply (find_idV_In_map_fst _ _ _ Heqd). left; trivial.
- apply list_norepet_cut_middle in VH. apply IHlist; trivial.
Qed.

Lemma make_context_g_char:
forall H V (VH:list_norepet (map fst V ++ map fst H)) i,
(make_tycontext_g V H) ! i = match (make_tycontext_s H)!i with
                               None => find_idV i V
                             | Some fs => Some (type_of_funspec fs)
                             end.
Proof.
induction H; intros.
+ rewrite make_tycontext_g_nilG_findV.
simpl; rewrite PTree.gleaf; trivial.
+ apply list_norepet_cut_middle in VH.
remember ((make_tycontext_g V (a :: H)) ! i) as d; symmetry in Heqd; destruct d. 
- apply make_tycontext_g_consG_elim in Heqd. destruct a as [j fs]; simpl in *. rewrite PTree.gsspec.
destruct (peq i j); subst; simpl in *; trivial. rewrite <- IHlist, Heqd; trivial.
- destruct a as [j fs]; simpl in *; rewrite PTree.gsspec in *.
destruct (peq i j); subst; simpl in *. congruence.
rewrite <- IHlist, Heqd; trivial.
Qed.

Lemma suboption_make_tycontext_s_g V G H 
  (GH: forall i : positive, sub_option (make_tycontext_s G) ! i (make_tycontext_s H) ! i)
  (VH: list_norepet (map fst V ++ map fst H))
  (LNR : list_norepet (map fst G)) i:
sub_option (make_tycontext_g V G) ! i (make_tycontext_g V H) ! i.
Proof.
remember ((make_tycontext_g V G) ! i) as d; destruct d; simpl; trivial; symmetry in Heqd.
rewrite make_context_g_char in *; trivial.
- remember ((make_tycontext_s G) ! i) as q; destruct q.
* specialize (GH i). rewrite <- Heqq in GH; simpl in GH. rewrite GH; trivial.
* rewrite Heqd, find_id_maketycontext_s. apply find_idV_In_map_fst in Heqd.
  remember (find_id i H) as w; destruct w; trivial. symmetry in Heqw; apply find_id_e in Heqw.
  apply list_norepet_append_inv in VH. destruct VH as [_ [_ D]].
  elim (D i i); trivial. eapply in_map_fst in Heqw; apply Heqw.
- clear Heqd i t. apply list_norepet_append_inv in VH. destruct VH as [LNRV [LNRH D]].
apply list_norepet_append; trivial.
intros x y ? ?. apply D; trivial.  specialize (GH y). clear - GH H1 LNR.
hnf in GH. rewrite 2 find_id_maketycontext_s in GH. apply list_in_map_inv in H1.
destruct H1 as [[i fs] [? ?]]; subst.
erewrite find_id_i in GH; [| apply H1 | trivial]. apply find_id_e in GH. apply in_map_fst in GH. apply GH.
Qed.

Lemma semax_func_join_sameV' {cs ge H1 H2 V funs1 funs2 G1 G2 H}
  (SF1: @semax_func V H1 cs ge funs1 G1) (SF2: @semax_func V H2 cs ge funs2 G2)

  (K1: forall i, sub_option ((make_tycontext_s H1) ! i) ((make_tycontext_s H) ! i))
  (K2: forall i, sub_option ((make_tycontext_s H2) ! i) ((make_tycontext_s H) ! i))

  (LNR: list_norepet ((map fst V)++(map fst H)))
  (LNR1: list_norepet (map fst H1)) (LNR2: list_norepet (map fst H2)):
@semax_func V H cs ge (funs1 ++ funs2) (G1++G2).
Proof.
apply (semax_func_join_sameV SF1 SF2); try eassumption.
+ apply suboption_make_tycontext_s_g; eauto.
+ intros; apply sub_option_subsumespec; auto.
+ apply suboption_make_tycontext_s_g; eauto.
+ intros; apply sub_option_subsumespec; auto.
Qed.

Lemma find_id_firstn i fs: forall n G (N: find_id i (firstn n G) = Some fs), find_id i G = Some fs.
Proof.
induction n; simpl; intros. inv N.
destruct G; simpl in *. inv N.
destruct p as [j gs]; simpl in *.
destruct (eq_dec i j); subst; trivial. auto.
Qed.

Lemma find_id_skipn i fs: forall n G (HG: list_norepet (map fst G))
                             (N: find_id i (skipn n G) = Some fs), find_id i G = Some fs.
Proof.
induction n; simpl; intros; trivial.
destruct G; simpl in *; trivial.
destruct p as [j gs]; simpl in *. inv HG.
destruct (eq_dec i j); [ subst | auto].
apply IHn in N; [clear IHn; exfalso| trivial].
apply find_id_e in N. apply in_map_fst in N; auto.
Qed.

Lemma In_firstn {A} (a:A): forall n l, In a (firstn n l) -> In a l.
Proof.
induction n; simpl; intros. contradiction.
destruct l; inv H. left; trivial. right; auto.
Qed.
Lemma In_skipn {A} (a:A): forall n l, In a (skipn n l) -> In a l.
Proof.
induction n; simpl; intros. trivial. 
destruct l. inv H. right; auto.
Qed.

Lemma semax_func_firstn {cs ge H V n funs G}:
  forall (SF: @semax_func V H cs ge funs G),
    @semax_func V H cs ge (firstn n funs) (firstn n G).
Proof.
intros. destruct SF as [SF1 [SF2 SF3]]; split; [|split].
+ clear SF2 SF3. specialize (match_fdecs_length _ _ SF1); intros. (*clear PC.*)
generalize dependent G. generalize dependent funs. induction n; simpl; intros. constructor.
destruct funs; simpl in *. destruct G; simpl in *. constructor. congruence.
destruct G; simpl in *. congruence. inv SF1. inv H0. constructor; auto.
+ clear SF1 SF3. red; intros. apply SF2. eapply In_firstn; eauto.
+ clear SF2. intros ? ? ? k v fsig cc A P Q p KP HP.
apply (SF3 ge' Gfs Gffp k v fsig cc A P Q p KP); clear SF3.
hnf; hnf in HP. destruct HP as [i [HP [HQ [GS B]]]].
exists i, HP, HQ; split; trivial.
clear -GS. simpl in*. rewrite find_id_maketycontext_s.
rewrite find_id_maketycontext_s in GS. apply find_id_firstn in GS; trivial.
Qed.

Lemma semax_func_skipn {cs ge H V funs G} (HV:list_norepet (map fst funs)) (SF: @semax_func V H cs ge funs G):
forall n ,
@semax_func V H cs ge (skipn n funs) (skipn n G).
Proof.
intros. destruct SF as [SF1 [SF2 SF3]]; split; [|split].
+ clear SF2 SF3. specialize (match_fdecs_length _ _ SF1); intros.
generalize dependent G. generalize dependent funs. induction n; simpl; intros; trivial.
destruct funs; simpl in *. inv SF1; constructor. destruct G; simpl in *; inv SF1. inv H0. inv HV. auto.
+ clear SF1 SF3. red; intros. apply SF2. eapply In_skipn; eauto.
+ clear SF2. intros ? ? ? k v fsig cc A P Q p KP HP.
apply (SF3 ge' Gfs Gffp k v fsig cc A P Q p KP); clear SF3. 
eapply match_fdecs_norepet in HV; [|eassumption ].
hnf; hnf in HP. destruct HP as [i [HP [HQ [GS B]]]].
exists i, HP, HQ; split; trivial.
clear - GS HV. simpl in *. rewrite find_id_maketycontext_s.
rewrite find_id_maketycontext_s in GS. apply find_id_skipn in GS; trivial.
Qed.
Lemma semax_func_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) V H ge funs G:
@semax_func V H CS ge funs G -> @semax_func V H CS' ge funs G.
Proof. apply semax_func_mono; [ apply CSUB | | ]; intros ?; apply sub_option_refl. Qed. 

Lemma semax_body_subsumption cs V V' F F' f spec
      (SF: @semax_body V F cs f spec)
      (TS: tycontext_sub (func_tycontext f V F nil) (func_tycontext f V' F' nil)):
  @semax_body V' F' cs f spec.
Proof.
  intros.
  destruct spec. destruct f0; hnf; intros. intros n. 
  eapply semax_mono.  apply TS. apply (SF Espec0 ts x n).
Qed. 
  
(*
Lemma semax_func_loeb V G C (prog:program):
@semax_func V G C (Genv.globalenv prog) (prog_funct prog) G ->
@semax_func V nil C (Genv.globalenv prog) (prog_funct prog) G.
Proof.
intros [MFD [GC GE]].
split. trivial. split. trivial. intros. specialize (GE _ Gfs Gffp n).
eapply believe_monoL. 3: apply GE. 2: apply cspecs_sub_refl.
intros. red; simpl. intuition; intros.
+ remember ((make_tycontext_t (fn_params f) (fn_temps f)) ! id) as x; destruct x; trivial.
+ red; intros. Search make_tycontext_g.
    *)

End semax_prog.

      (*

(*We may always add unused assumptions to G - intuitively, this context weakening rule 
  is sound since one could have done the proof of f wrt the larger gprog in the first place. *)
Lemma semax_func_weakening_L {cs} V H G funs K:
   @semax_func V H cs funs K -> funspecs_sub V H G ->
   @semax_func V G cs funs K.
Proof.
intros [MF B] SUB.
split; [ trivial | intros]. specialize (B _ H0 H1 n). clear - B SUB.
eapply believe_monoL; [ clear B; intros | eassumption].
apply funspecs_sub_nofunctycontext_sub; trivial.
Qed.

(*Similarly for semax_body*)
Lemma semax_body_weakening {cs} V G1 f spec G2 :
  @semax_body V G1 cs f spec -> funspecs_sub V G1 G2 -> 
  @semax_body V G2 cs f spec.
Proof. intros. red. destruct spec. destruct f0; intros.
intros n. eapply semax.semax_mono. 
apply funspecs_sub_functycontext_sub; eauto.
apply H.
Qed.

Definition match_fdecs_sub funs G funs' G' :=
  sublist funs funs' /\
  sublist G G' /\ 
  match_fdecs funs G.

Definition hide_auxiliary_functions {cs} V K funs G := 
   exists funs' G', match_fdecs_sub funs G funs' G' /\
                    @semax_func V K cs funs' G'.
*)
