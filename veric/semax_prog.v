Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
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
Require Import VST.veric.semax_conseq. (*for use of semax_pre*)
Require Import VST.veric.Clight_initial_world.
Require Import VST.veric.initialize.
Require Import VST.veric.coqlib4.
Require Import Coq.Logic.JMeq.

Require Import Coq.Logic.JMeq.
Require Import VST.veric.ghost_PCM.

Import Ctypes Clight.

Local Open Scope pred.

Lemma funspec_eq {sig cc A P Q P' Q' Pne Qne Pne' Qne'}:
      P = P' -> Q=Q' -> 
      mk_funspec sig cc A P Q Pne Qne = mk_funspec sig cc A P' Q' Pne' Qne'.
Proof. intros. subst. f_equal; apply proof_irr. Qed.

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

Lemma typecheck_temp_environ_i:
 forall (V : varspecs) (G : funspecs)
   (args : list val) (retty: type)
   (params temps vars : list (ident * type))
   (te' : temp_env),
 tc_vals (map snd params) args ->
 list_norepet (map fst params ++ map fst temps) ->
 bind_parameter_temps params args (create_undef_temps temps) = Some te' ->
 typecheck_temp_environ (make_tenv te')
   (temp_types (make_tycontext params temps vars retty V G nil)).
Proof.
intros.
apply list_norepet_app in H0.
destruct H0 as [? [? ?]].
intros id t ?.
unfold make_tycontext, temp_types in H4.
unfold make_tycontext_t in H4.
set (f1 := fun param : ident * type => PTree.set (fst param) (snd param)) in *.
set (f2 := fun (temp : ident * type) (tenv : PTree.t type) =>
            let (id, ty) := temp in PTree.set id ty tenv) in *.
unfold Map.get, make_tenv.
(***)
set (t0 := PTree.empty type) in *.
set (v0 := PTree.empty val) in *.
assert (t0 ! id = Some t ->
   exists v : val, v0 ! id = Some v /\ tc_val' t v). {
  subst t0 v0. 
  intros. rewrite PTree.gempty in H5; inv H5.
}
set (t1 := fold_right f2 t0 temps) in *.
set (v1 := create_undef_temps temps) in *.
unfold create_undef_temps in v1.
fold v0 in v1.
clearbody t0. clearbody v0.
assert (t1 ! id = Some t ->
   exists v : val, v1 ! id = Some v /\ tc_val' t v). {
  subst t1 v1.
  clear - H5.
  revert t0 v0 H5.
  induction temps as [|[??]]; simpl; intros.
  destruct (H5 H) as [v [? ?]].
  eauto.
  destruct (ident_eq i id). subst.
  rewrite PTree.gss. eexists; split; eauto.
  intro Hx; contradiction Hx; auto.
  rewrite PTree.gso by auto.
  eapply IHtemps; eauto.
  rewrite PTree.gso in H; auto.
}
clearbody v1. clearbody t1.
clear H5 t0 v0.
clear f2.
clear temps H3 H2.
revert t1 v1 H4 H6 H1.
revert args H; induction params as [|[??]]; destruct args; simpl; intros; try contradiction.
inv H1.
auto.
unfold f1 in H4. simpl in H4.
destruct (ident_eq i id).
subst i. rewrite PTree.gss in H4.
inv H4.
exists v.
destruct H.
split; [| intro; auto].
inv H0.
assert ((PTree.set id v v1) ! id = Some v).
apply PTree.gss.
forget (PTree.set id v v1) as e1.
clear - H H5 H2 H0 H1.
revert e1 H args H0 H1 H2; induction params as [|[??]]; destruct args; simpl; intros; try contradiction.
inv H1. auto.
destruct H2.
simpl in H5.
apply Decidable.not_or in H5.
destruct H5.
eapply IHparams; try apply H1; auto.
rewrite PTree.gso by auto; auto.
destruct H.
rewrite PTree.gso in H4 by auto.
inv H0.
eapply IHparams; try apply H1; auto.
eassumption.
rewrite PTree.gso; auto.
Qed.

Lemma typecheck_var_environ_i:
 forall ge (vars : list (ident * type))
    (ve' : env)
    (m1 m2 : Memory.mem),
  list_norepet (map fst vars) ->
 alloc_variables ge empty_env m1 vars ve' m2 ->
 typecheck_var_environ (make_venv ve') (make_tycontext_v vars).
Proof.
intros.
hnf; intros.
unfold make_tycontext_v, make_venv, Map.get.
set (f := fun (var : ident * type) (venv : PTree.t type) =>
    let (id0, ty0) := var in PTree.set id0 ty0 venv).
transitivity (option_map snd (ve' ! id) = Some ty).
2:{ destruct (ve' ! id) as [[??]|]; simpl; split; intro.
     inv H1; exists b; eauto. destruct H1; inv H1; auto.
     inv H1. destruct H1; inv H1.
}
assert ((fold_right f (PTree.empty type) vars) ! id =
           option_map snd (ve' ! id)).
2: rewrite H1; split; auto.
set (s := PTree.empty type).
set (r := empty_env) in *.
assert (s ! id = option_map snd (r ! id)).
subst s r.
unfold empty_env.
rewrite !PTree.gempty.
reflexivity.
assert (In id (map fst vars) -> s ! id = None) 
   by (intros; apply PTree.gempty).
clearbody r.
clearbody s.
induction H0.
simpl. auto.
inv H.
destruct (ident_eq id0 id); simpl in *.
subst.
spec H2; auto.
rewrite H2 in *.
rewrite PTree.gss in *.
clear - H3 H6.
set (e1 := PTree.set id (b1, ty0) e) in *.
transitivity (option_map snd e1 ! id).
subst e1. rewrite PTree.gss; reflexivity.
induction H3. auto.
simpl in H6.
apply Decidable.not_or in H6.
destruct H6.
rewrite PTree.gso in * by auto.
auto.
rewrite PTree.gso in * by auto.
apply IHalloc_variables; auto.
Qed.

Section semax_prog.
Context (Espec: OracleKind).

Definition prog_contains (ge: genv) (fdecs : list (ident * Clight.fundef)) : Prop :=
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
match spec with (_, mk_funspec fsig cc A P Q _ _) =>
  fst fsig = map snd (fst (fn_funsig f)) /\ 
  snd fsig = snd (fn_funsig f) /\
forall Espec ts (x:dependent_type_functor_rec ts A mpred),
  semax Espec (func_tycontext f V G nil)
      (fun rho => close_precondition (map fst f.(fn_params)) (P ts x) rho * stackframe_of f rho)
       f.(fn_body)
      (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of f))
end.

Definition genv_contains (ge: Genv.t Clight.fundef type) (fdecs : list (ident * Clight.fundef)) : Prop :=
 forall id f, In (id,f) fdecs ->
              exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some f.

Lemma genv_prog_contains (ge:genv) fdecs: prog_contains ge fdecs = genv_contains ge fdecs.
Proof. reflexivity. Qed.

Definition semax_func (V: varspecs) (G: funspecs) {C: compspecs} (ge: Genv.t Clight.fundef type)
       (fdecs: list (ident * Clight.fundef)) (G1: funspecs) : Prop :=
match_fdecs fdecs G1 /\ genv_contains ge fdecs /\
forall (ge': Genv.t Clight.fundef type) (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
         (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b)) 
n, believe Espec (nofunc_tycontext V G) (Build_genv ge' (@cenv_cs C)) (nofunc_tycontext V G1) n.

Lemma semax_func_cenv_sub CS CS' (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) ge ge'
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
apply (@believe_cenv_sub_L CS Espec CS' {| genv_genv := ge2; genv_cenv := cenv_cs |} (nofunc_tycontext V G) (nofunc_tycontext V G)).
intros; apply tycontext_sub_refl. apply CSUB. apply (B _ Q1 Q2 n).
Qed. 
Lemma semax_func_mono CS CS' (CSUB: cspecs_sub CS CS') ge ge'
  (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
  V G fdecs G1 (H: @semax_func  V G CS ge fdecs G1): @semax_func  V G CS' ge' fdecs G1.
Proof.
  destruct CSUB as [CSUB _].
  eapply (@semax_func_cenv_sub _ _ CSUB); eassumption.
  (*explicit proof:
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
    intros; apply tycontext_sub_refl. apply CSUB. apply (B _ Q1 Q2 n).*)
Qed.

Definition main_pre {Z} (prog: program) (ora: Z) : (ident->val) -> argsassert :=
(fun gv gvals => !!(gv = genviron2globals (fst gvals) /\snd gvals=nil) 
       && globvars2pred gv (prog_vars prog) * has_ext ora).

Lemma main_pre_vals_nil {Z prog ora gv g vals}:
      @main_pre Z prog ora gv (g, vals) |-- !!(vals=nil).
Proof. unfold main_pre; simpl. intros ? [? [? [? [[X ?] _]]]]. apply X.
Qed.

Definition Tint32s := Tint I32 Signed noattr.

Definition main_post (prog: program) : (ident->val) -> assert :=
(fun _ _ => TT).

Definition main_spec_ext' {Z} (prog: program) (ora: Z)
(post: (ident->val) -> environ ->pred rmap): funspec :=
NDmk_funspec (nil, tint) cc_default (ident->val) (main_pre prog ora) post.

Definition main_spec_ext (prog: program) (ora: OK_ty): funspec :=
NDmk_funspec (nil, tint) cc_default (ident->val) (main_pre prog ora) (main_post prog).

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

Definition postcondition_allows_exit retty :=
   forall 
      v  ora (jm : juicy_mem),
      tc_option_val retty v ->
      app_pred (ext_compat ora) (m_phi jm) ->
      ext_spec_exit OK_spec v ora jm.

Definition semax_prog {C: compspecs}
       (prog: program) (ora: OK_ty) (V: varspecs) (G: funspecs) : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
PTree.elements cenv_cs = PTree.elements (prog_comp_env prog) /\
(*  @semax_func V G C (prog_funct prog) G /\*)
@semax_func V G C (Genv.globalenv prog) (prog_funct prog) G /\
match_globvars (prog_vars prog) V = true /\
match find_id prog.(prog_main) G with
| Some s => exists post, 
      s = main_spec_ext' prog ora post
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
try (intros; intro; intros).
destruct H0. exists x.
destruct x.
intros. specialize (H0 x). eapply pred_hereditary; eauto.
Qed.

Lemma laterR_level: forall w w' : rmap, laterR w w' -> (level w > level w')%nat.
Proof.
induction 1.
unfold age in H. rewrite <- ageN1 in H.
change rmap with R.rmap; change ag_rmap with R.ag_rmap.
rewrite (ageN_level _ _ _ H). generalize (@level _ R.ag_rmap y). intros; lia.
lia.
Qed.

Lemma necR_level:  forall w w' : rmap, necR w w' -> (level w >= level w')%nat.
Proof.
induction 1.
unfold age in H. rewrite <- ageN1 in H.
change rmap with R.rmap; change ag_rmap with R.ag_rmap.
rewrite (ageN_level _ _ _ H). generalize (@level _ R.ag_rmap y). intros; lia.
lia.
lia.
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
  { intros; rewrite H1; tauto. }
  apply pred_ext; intros w ?; destruct (H w); simpl in *; intuition.
  apply H0; auto. clear - H4.  unfold natLevel in *. lia.
  apply H2; auto. clear - H4.  unfold natLevel in *. lia. }
unfold age,age1 in H. unfold ag_nat in H. unfold natAge1 in H. destruct x0; inv H.
intros z ?.
split; intros ? ? ?.
assert (app_pred (approx (level (S y)) (P x)) a').
simpl. split; auto. unfold natLevel.  apply necR_level in H1.
change compcert_rmaps.R.rmap with rmap in *.
change compcert_rmaps.R.ag_rmap with ag_rmap in *.
lia.
rewrite H0 in H3.
simpl in H3. destruct H3; auto.
assert (app_pred (approx (level (S y)) (P' x)) a').
simpl. split; auto. unfold natLevel.  apply necR_level in H1.
change compcert_rmaps.R.rmap with rmap in *.
change compcert_rmaps.R.ag_rmap with ag_rmap in *.
lia.
rewrite <- H0 in H3.
simpl in H3. destruct H3; auto.
Qed.

Lemma semax_func_cons_aux:
forall (psi: genv) id fsig1 cc1 A1 P1 Q1 NEP1 NEQ1 fsig2 cc2 A2 P2 Q2 (V: varspecs) (G': funspecs) {C: compspecs} b fs,
Genv.find_symbol psi id = Some b ->
~ In id (map (fst (A:=ident) (B:=Clight.fundef)) fs) ->
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

Lemma var_block_cspecs_sub {CS CS'} (CSUB: cspecs_sub CS CS') sh a
(CT: complete_type (@cenv_cs CS) (@snd ident type a) = true):
@var_block sh CS a = @var_block sh CS' a.
Proof.
extensionality rho. destruct CSUB as [CSUB _].
unfold var_block. unfold expr.sizeof. rewrite (cenv_sub_sizeof CSUB); trivial.
Qed. 

Lemma stackframe_of_cspecs_sub {CS CS'} (CSUB: cspecs_sub CS CS') f
  (COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)):
@stackframe_of CS f = @stackframe_of CS' f .
Proof.
extensionality rho. 
unfold stackframe_of. forget (fn_vars f) as vars.
induction vars; simpl; trivial.
inv COMPLETE. rewrite (var_block_cspecs_sub CSUB _ _ H1), IHvars; clear IHvars; trivial.
Qed.

Lemma semax_body_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') V G f spec
(COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)):
@semax_body V G CS f spec -> @semax_body V G CS' f spec.
Proof.
destruct spec.
destruct f0.
intros [H' [H'' H]]; split3; auto. clear H' H''.
intros.
  specialize (H Espec0 ts x).
rewrite <- (stackframe_of_cspecs_sub CSUB); [apply (semax_cssub CSUB); apply H | trivial].
Qed. 

Lemma semax_body_type_of_function {V G cs f i phi} (SB : @semax_body V G cs f (i, phi))
      (CC: fn_callconv f = callingconvention_of_funspec phi):
type_of_function f = type_of_funspec phi.
Proof.
  destruct phi as [[? ?] ? ? ? ? ? ?]. destruct SB as [? [? _]].
  unfold type_of_function; simpl in *. subst.
  rewrite <- TTL1; trivial.
Qed.

Lemma semax_func_cons: forall 
     fs id f fsig cc (A: TypeTree) P Q NEP NEQ (V: varspecs) (G G': funspecs) {C: compspecs} ge b,
  andb (id_in_list id (map (@fst _ _) G))
  (andb (negb (id_in_list id (map (@fst ident Clight.fundef) fs)))
    (semax_body_params_ok f)) = true ->
  Forall
     (fun it : ident * type =>
      complete_type cenv_cs (snd it) =
      true) (fn_vars f) ->
   var_sizes_ok cenv_cs (f.(fn_vars)) ->
   f.(fn_callconv) = cc ->
   Genv.find_symbol ge id = Some b -> 
   Genv.find_funct_ptr ge b = Some (Internal f) -> 
  semax_body V G f (id, mk_funspec fsig cc A P Q NEP NEQ) ->
  semax_func V G ge fs G' ->
  semax_func V G ge ((id, Internal f)::fs)
       ((id, mk_funspec fsig cc A P Q NEP NEQ)  :: G').
Proof.
intros until C.
intros ge b H' COMPLETE Hvars Hcc Hb1 Hb2 SB [HfsG' [Hfs HG]].
apply andb_true_iff in H'.
destruct H' as [Hin H'].
apply andb_true_iff in H'.
destruct H' as [Hni H]. 
split3.
{ econstructor 2; auto. 
  eapply semax_body_type_of_function. apply SB. apply Hcc. }
{ apply id_in_list_true in Hin. rewrite negb_true_iff in Hni.
  hnf; intros. destruct H0; [ symmetry in H0; inv H0 | apply (Hfs _ _ H0)].
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
apply negb_true_iff in Hni.
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
destruct H1 as [id' [NEP' [NEQ' [? [b' [FS' Hbb']]]]]].
symmetry in Hbb'; inv Hbb'.
destruct (eq_dec id id').
 - subst. simpl in H1. rewrite PTree.gss in H1.
   symmetry in H1; inv H1. apply inj_pair2 in H6. apply inj_pair2 in H7. subst Q' P'. simpl in *.
   destruct SB. apply list_norepet_app in H. tauto.
 - specialize (H0 id); unfold fundef in H0. simpl in H0.  rewrite Hb1 in H0; simpl in H0.
   simpl in FS'.
   elim (Genv.global_addresses_distinct ge' n0 H0 FS'); trivial.
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
destruct SB as [X [Y SB]]. specialize (SB Espec ts x). simpl fst in X. simpl snd in Y.
specialize (SB k).
apply now_later. 
rewrite <- (stackframe_of'_cenv_sub CSUB); trivial.
apply (semax'_cenv_sub CSUB). 
clear - SB NK KW HDelta' X.
rewrite semax_fold_unfold in SB|-*. intros gx DD CS' u WU [SUB GX] v UV BEL.
assert (HDD: tycontext_sub (func_tycontext f V G nil) DD).
{ unfold func_tycontext, func_tycontext'. simpl.
eapply tycontext_sub_trans; eauto. }
assert (WV: @necR nat ag_nat w v). { eapply necR_trans.  apply WU. apply UV. }
specialize (SB gx DD CS' _ KW (conj HDD GX) v WV BEL). 
revert SB.
apply allp_derives; intro kk.
apply allp_derives; intro F.
apply allp_derives; intro curf.
apply imp_derives; auto.
unfold guard.
apply allp_derives; intro tx.
eapply allp_derives; intro vx.
eapply subp_derives; auto.
apply andp_derives; auto.
apply andp_derives; auto.
apply sepcon_derives; auto.
apply andp_left1.
apply sepcon_derives; auto.
apply andp_left2; trivial.
* (***   Vptr b Ptrofs.zero <> v'  ********)
apply (HG n v fsig cc' A' P' Q'); auto.
destruct H1 as [id' [NEP' [NEQ' [? B]]]].
simpl in H1. rewrite PTree.gsspec in H1.
destruct (peq id' id); subst.
- specialize (H0 id); unfold fundef in H0; simpl in H0.
  destruct B as [? [? ?]]. rewrite Hb1 in H0; simpl in H0. unfold fundef in H3; simpl in H3; congruence.
- exists id', NEP', NEQ'; split; auto.
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
forall Espec ef A n,
@semax_external Espec ef A (fun _ _ _ => FF) (fun _ _ _ => FF) n.
intros.
hnf; intros.
simpl.
intros.
destruct H2 as [? [? [? [? [? ?]]]]].
contradiction.
Qed.

Lemma TTL6 {l}: typelist_of_type_list (typelist2list l) = l.
Proof. induction l; simpl; intros; trivial. rewrite IHl; trivial. Qed.

Lemma semax_func_cons_ext:
forall (V: varspecs) (G: funspecs) {C: compspecs} ge fs id ef argsig retsig A P Q NEP NEQ
      argsig'
      (G': funspecs) cc (*(ids: list ident)*) b,
  (*ids = map fst argsig' ->*) (* redundant but useful for the client,
           to calculate ids by reflexivity *)
  argsig' = typelist2list argsig ->
  ef_sig ef = mksignature (typlist_of_typelist argsig) (rettype_of_type retsig) cc ->
  id_in_list id (map (@fst _ _) fs) = false ->
  (ef_inline ef = false \/ withtype_empty A) ->
  (forall gx ts x (ret : option val),
     (Q ts x (make_ext_rval gx (rettype_of_type retsig) ret)
        && !!Builtins0.val_opt_has_rettype ret (rettype_of_type retsig)
        |-- !!tc_option_val retsig ret)) ->
  Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
  (forall n, semax_external Espec ef A P Q n) ->
  semax_func V G ge fs G' ->
  semax_func V G ge ((id, External ef argsig retsig cc)::fs)
       ((id, mk_funspec (argsig', retsig) cc A P Q NEP NEQ)  :: G').
Proof.
intros until b.
intros (*Hids NORM*) Hargsig' Hef Hni (*Hlen*) Hinline Hretty B1 B2 H [Hf' [GC Hf]].
subst argsig'.
apply id_in_list_false in Hni.
split.
{ hnf; simpl; f_equal; auto.
  constructor 2; trivial.
  simpl; rewrite TTL6; trivial. }
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
simpl map. rewrite TTL6 in *.
split. { split; trivial. split3; eauto. } 
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
  destruct a1; simpl in *.
  rewrite PTree.gss in H1; inv H1. left; auto.
  destruct a1; simpl in *. 
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
destruct f as [?f ?A ?a ?a]. symmetry in H6; inv H6.
apply Genv.invert_find_symbol in H3.
exists i.
simpl ge_of. unfold filter_genv, Map.get.
unfold globalenv; simpl.
rewrite make_tycontext_s_find_id.
split; [ | eexists]; eassumption.
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
destruct a1; simpl in *.
rewrite PTree.gss in H1; inv H1. left; auto.
destruct a1; simpl in *. 
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
unfold filter_genv, Map.get.
rewrite make_tycontext_s_find_id.
split; [ | eexists]; eassumption.
Qed.

(* there's a place this lemma should be applied, perhaps in proof of semax_call;
  or maybe this lemma is dead; or maybe it should be moved to seplog.v *)
Lemma funassert_rho:
forall G rho rho', ge_of rho = ge_of rho' -> funassert G rho |-- funassert G rho'.
Proof. intros. apply funspecs_assert_rho; trivial. Qed.

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
(*
Definition Delta_types V G {C: compspecs} (tys : list type) : tycontext :=
make_tycontext
(params_of_types
   1 ((Tfunction (type_of_params (params_of_types 2 tys)) Tvoid cc_default) :: tys))
nil nil Tvoid V G nil.
*)

Lemma find_id_maketycontext_s G id : (make_tycontext_s G) ! id = find_id id G.
Proof.
induction G as [|(i,t) G]; simpl.
- destruct id; reflexivity.
- rewrite PTree.gsspec.
do 2 if_tac; congruence.
Qed.

Lemma ext_ref_join : forall {Z} (z : Z), join (ext_ghost z) (ext_ref z) (ext_both z).
Proof.
  intros; repeat constructor.
Qed.

(**************Adaptation of seplog.funspecs_assert, plus lemmas ********)
(*Maybe this definition can replace seplog.funassert globally?. In fact it
  really needs a genvinron as parameter, not a genviron * list val*)
Definition funspecs_gassert (FunSpecs: PTree.t funspec): argsassert :=
 fun gargs => let g := fst gargs in
   (ALL  id: ident, ALL fs:_,  !! (FunSpecs!id = Some fs) -->
              EX b:block,
                   !! (Map.get g id = Some b) && func_at fs (b,0))
 &&  (ALL  b: block, ALL fsig:typesig, ALL cc: calling_convention, sigcc_at fsig cc (b,0) -->
             EX id:ident, !! (Map.get g id = Some b)
                             && !! exists fs, FunSpecs!id = Some fs).

(*Maybe this definition can replace Clight_seplog.funassert globally?*)
Definition fungassert (Delta: tycontext): argsassert := funspecs_gassert (glob_specs Delta).

(*EXCTLY THE SAME PROOFSCRIPT AS semax_call.resource_decay_funassert*)
Lemma resource_decay_fungassert:
  forall G gargs b w w',
         necR (core w) (core w') ->
         resource_decay b w w' ->
         app_pred (fungassert G gargs) w ->
         app_pred (fungassert G gargs) w'.
Proof.
unfold resource_decay, funassert; intros until w'; intro CORE; intros.
destruct H. 
destruct H0.
split; [clear H2 | clear H0].
+ intros id fs w2 Hw2 H3.
  specialize (H0 id fs). cbv beta in H0.
  specialize (H0 _ (necR_refl _) H3).
  destruct H0 as [loc [? ?]].
  exists loc; split; auto.
  destruct fs as [f cc A a a0].
  simpl in H2|-*.
  pose proof (necR_resource_at (core w) (core w') (loc,0)
         (PURE (FUN f cc) (SomeP (SpecArgsTT A) (packPQ a a0))) CORE).
  pose proof (necR_resource_at _ _ (loc,0)
         (PURE (FUN f cc) (SomeP (SpecArgsTT A) (packPQ a a0))) Hw2).
  apply H5.
  clear - H4 H2.
  repeat rewrite <- core_resource_at in *.
  spec H4. rewrite H2.  rewrite core_PURE.  simpl.  rewrite level_core; reflexivity.
  destruct (w' @ (loc,0)).
  rewrite core_NO in H4; inv H4.
  rewrite core_YES in H4; inv H4.
  rewrite core_PURE in H4; inv H4. rewrite level_core; reflexivity.
+
intros loc sig cc w2 Hw2 H6.
specialize (H2 loc sig cc _ (necR_refl _)).
spec H2.
{ clear - Hw2 CORE H6. simpl in *.
  destruct H6 as [pp H6].
  rewrite <- resource_at_approx.
  case_eq (w @ (loc,0)); intros.
  + assert (core w @ (loc,0) = resource_fmap (approx (level (core w))) (approx (level (core w))) (NO _ bot_unreadable)).
     - rewrite <- core_resource_at.
       simpl; erewrite <- core_NO; f_equal; eassumption.
     - pose proof (necR_resource_at _ _ _ _ CORE H0).
       pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
       rewrite <- core_resource_at in H2; rewrite H6 in H2;
       rewrite core_PURE in H2; inv H2.
  + assert (core w @ (loc,0) = resource_fmap (approx (level (core w))) (approx (level (core w))) (NO _ bot_unreadable)).
    - rewrite <- core_resource_at.
      simpl; erewrite <- core_YES; f_equal; eassumption.
    - pose proof (necR_resource_at _ _ _ _ CORE H0).
      pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
      rewrite <- core_resource_at in H2; rewrite H6 in H2;
      rewrite core_PURE in H2; inv H2.
  + pose proof (resource_at_approx w (loc,0)).
    pattern (w @ (loc,0)) at 1 in H0; rewrite H in H0.
    symmetry in H0.
    assert (core (w @ (loc,0)) = core (resource_fmap (approx (level w)) (approx (level w))
       (PURE k p))) by (f_equal; auto).
    rewrite core_resource_at in H1.
    assert (core w @ (loc,0) =
        resource_fmap (approx (level (core w))) (approx (level (core w)))
         (PURE k p)).
    - rewrite H1.  simpl. rewrite level_core; rewrite core_PURE; auto.
    - pose proof (necR_resource_at _ _ _ _ CORE H2).
      assert (w' @ (loc,0) = resource_fmap
         (approx (level w')) (approx (level w')) (PURE k p)).
      * rewrite <- core_resource_at in H3. rewrite level_core in H3.
        destruct (w' @ (loc,0)).
        ++ rewrite core_NO in H3; inv H3.
        ++ rewrite core_YES in H3; inv H3.
        ++ rewrite core_PURE in H3; inv H3.
           reflexivity.
      * pose proof (necR_resource_at _ _ _ _ Hw2 H4).
        inversion2 H6 H5. 
        exists p. trivial. }
destruct H2 as [id [? ?]].
exists id. split; auto.
Qed.
 


Lemma believe_cs_ext:
 forall CS Espec Delta ge1 ge2 Delta' n,
  @genv_genv ge1 = @genv_genv ge2 ->
  PTree.elements (@genv_cenv ge1) = PTree.elements (@genv_cenv ge2) ->
  @believe CS Espec Delta ge1 Delta' n ->
  @believe CS Espec Delta ge2 Delta' n.
Proof.
intros. 
intros b fsig0 cc A P Q; specialize (H1 b fsig0 cc A P Q).
intros n1 H2 H3. specialize (H1 n1 H2).
destruct ge1 as [ge ce1]; destruct ge2 as [ge2 ce2]; simpl in H; subst ge2.
simpl in H0.
specialize (H1 H3).
clear H3 H2.
apply H1.
Qed.

Lemma semax_prog_entry_point {CS: compspecs} V G prog b id_fun params args A 
   (P: forall ts : list Type, (dependent_type_functor_rec ts (ArgsTT A)) mpred)
   (Q: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A)) mpred)
  NEP NEQ h z:
  let retty := tint in
  postcondition_allows_exit retty ->
  @semax_prog CS prog z V G ->
  Genv.find_symbol (globalenv prog) id_fun = Some b ->
  find_id id_fun G =
     Some (mk_funspec (params, retty) cc_default A P Q NEP NEQ) ->
  tc_vals params args ->
  let gargs := (filter_genv (globalenv prog), args) in
  { q : CC_core |
   (forall jm, 
     Forall (fun v => Val.inject (Mem.flat_inj (nextblock (m_dry jm))) v v)  args->
     inject_neutral (nextblock (m_dry jm)) (m_dry jm) /\
     Coqlib.Ple (Genv.genv_next (Genv.globalenv prog)) (nextblock (m_dry jm)) ->
    exists jm', semantics.initial_core
    (juicy_core_sem (cl_core_sem (globalenv prog))) h
    jm q jm' (Vptr b Ptrofs.zero) args) /\

  forall (jm : juicy_mem) ts (a: (dependent_type_functor_rec ts A) mpred),
    app_pred (P ts a gargs) (m_phi jm) ->
    app_pred (fungassert (nofunc_tycontext V G) gargs ) (m_phi jm) ->
    nth_error (ghost_of (m_phi jm)) 0 = Some (Some (ext_ghost z, NoneP)) ->
    jsafeN (@OK_spec Espec) (globalenv prog) (level jm) z q jm }.
Proof.
intro retty.
intros EXIT SP Findb id_in_G arg_p.
rewrite <-find_id_maketycontext_s in id_in_G.
generalize SP; intros [_ [_ [CSEQ _]]].
destruct ((fun x => x) SP) as (_ & _ & _ & (MatchFdecs & (Gcontains & Believe)) & _).
specialize (Believe (globalenv prog)).
spec Believe; [ intros; apply sub_option_refl |].
spec Believe; [ intros; apply sub_option_refl |]. 
specialize (Believe 0%nat).
apply believe_cs_ext with (ge2 := 
  {| genv_genv := genv_genv (globalenv prog);
     genv_cenv := prog_comp_env prog |}) in Believe; auto.
replace  {|
               genv_genv := genv_genv (globalenv prog);
               genv_cenv := prog_comp_env prog |}
 with (globalenv prog) in Believe
  by (unfold globalenv; f_equal; auto).
(*
replace {| genv_genv := globalenv prog; genv_cenv := cenv_cs |}
  with (globalenv prog) in *
 by (unfold globalenv; simpl; symmetry; f_equal; assumption). 
*)
unfold nofunc_tycontext in *.
destruct (believe_exists_fundef Findb Believe id_in_G) as [f [Eb Ef]].
clear Believe.
exists (Clight_core.Callstate f args Kstop).
simpl semantics.initial_core.
unfold j_initial_core.
simpl semantics.initial_core.
fold fundef in *.
split.
intros; exists jm; split; auto.
rewrite if_true by auto.
change (Genv.globalenv (program_of_program prog))
  with (genv_genv (globalenv prog)).
rewrite Eb; auto.
intros jm ts a m_sat_Pa m_funassert.
intros HZ.
set (psi := globalenv prog) in *.
destruct SP as [H0 [AL [_ [[H2 [GC H3]] [GV _]]]]].
set (fspec := mk_funspec (params, retty) cc_default A P Q NEP NEQ) in *.
specialize (H3 (genv_genv psi)).
spec H3. intros; apply sub_option_refl.
spec H3. intros; apply sub_option_refl.
(*set (rho := make_args (map fst params) args
                   (empty_environ psi)) in *.*)
specialize (H3 (S (level jm))).
apply believe_cs_ext with (ge2 := 
  {| genv_genv := genv_genv (globalenv prog);
     genv_cenv := prog_comp_env prog |}) in H3; auto.
 fold psi in H3.
replace  {|
               genv_genv := genv_genv psi;
               genv_cenv := prog_comp_env prog |}
 with psi in *
  by (subst psi; unfold globalenv; f_equal; auto).
rename H3 into Prog_OK. assert (H3 := I).

rename z into ora.
assert (Hora: app_pred (ext_compat ora) (m_phi jm)). {
 red. red. red.
 pose proof (ext_ref_join ora).
 exists ((Some (ext_both ora, NoneP)) :: tl (ghost_of (m_phi jm))).
 destruct (ghost_of (m_phi jm)). inv HZ.
 simpl in HZ. inv HZ.
 constructor; auto.
 constructor.
 constructor; auto. simpl. constructor; auto.
 simpl.
 apply ghost_join_nil_r.
}
clear HZ. clear AL.
set (Delta := nofunc_tycontext V G) in *.
change (make_tycontext_s G) 
   with (glob_specs Delta) in id_in_G.
change (make_tycontext nil nil nil Tvoid V G nil)
  with Delta in m_funassert.
assert  (TC5: typecheck_glob_environ (filter_genv psi) (glob_types Delta)). {
     eapply tc_ge_denote_initial; try eassumption.
     apply compute_list_norepet_e; auto.
}

clearbody Delta.
forget cc_default as cc.
change (prog_comp_env prog) with (genv_cenv psi) in *.


assert (HGG: cenv_sub (@cenv_cs CS) (globalenv prog)).
 { clear - CSEQ. forget (@cenv_cs CS) as cs1.
   subst psi. forget (genv_cenv (globalenv prog)) as cs2. 
   hnf; intros; hnf.
   destruct (cs1 ! i) eqn:?H; auto.
   apply PTree.elements_correct in H.
   apply PTree.elements_complete. congruence.
 }

(***  cut here ****)

assert (H5 := Prog_OK).
specialize (H5 (Vptr b Ptrofs.zero)).
specialize (H5 (typesig_of_funspec fspec) 
   (callingconvention_of_funspec fspec)).
specialize (H5 A P Q _ (necR_refl _)).
spec H5. { clear H5. 
 exists id_fun. exists NEP. exists NEQ.
 split.
  rewrite id_in_G. reflexivity.
  exists b; split; auto.
}
destruct H5 as [H5|H5].
-
 simpl in H5.
 unfold believe_external in H5.
 change (Genv.find_funct (genv_genv psi)
           (Vptr b Ptrofs.zero)) 
   with (Genv.find_funct_ptr (genv_genv psi) b) in H5.
  rewrite Eb in H5.
  destruct f; try contradiction.
 destruct H5 as [[[? [? [? Hinline]]] ?] ?].
 destruct Hinline as [Hinline|Hempty].
 2:{ elimtype False; clear - a Hempty. eapply Hempty; eauto. }
 subst c.
 simpl in H4.
 injection H; clear H; intros.
 subst t0.
 change (level (m_phi jm)) with (level jm) in H6.
 specialize (H5 psi ts a (level jm)).
 spec H5. constructor. reflexivity.
 specialize (H5 TT (typlist_of_typelist (typelist_of_type_list params)) args).
 specialize (H5 jm (le_refl _) _ (necR_refl _)).
 rewrite TTL2 in *.
 spec H5. { clear H5.
 split. simpl.
 rewrite H4; simpl.
 clear - arg_p.
 revert args arg_p; induction params; destruct args; simpl; intros; try discriminate; try contradiction;  auto.
 destruct arg_p;  split; auto.
 apply tc_val_has_type; auto.
 simpl fst.
 clear H3 H6.
 eapply sepcon_derives.
 apply derives_refl.
 instantiate (1:=emp); auto.
 rewrite sepcon_emp.
 auto.
}
 destruct (level jm) eqn:?H.
 constructor.
 destruct H5 as [x' [? H9]].
 specialize (H5 ora _ (necR_refl _)).
 clear H1 H3 m_funassert m_sat_Pa Ef Eb.
 eapply jsafeN_external.
 simpl. rewrite Hinline.
 reflexivity.
 rewrite H4. simpl.
 apply H5.
 apply Hora.
 simpl.
 intros.
 rewrite H4 in *. simpl sig_res in *. simpl sig_args in *.
 assert (tc_option_val retty ret). {
  specialize (H9 (sig_res (ef_sig e)) ret z' m').
  spec H9. destruct H3 as [? [? ?]];  lia.
  change (genv_symb_injective (Genv.globalenv prog)) 
   with (genv_symb_injective psi) in H7.
  rewrite H4 in H9.
  specialize (H9 _ (necR_refl _) H7).
  specialize (H6 ts a ret).
  destruct H9 as [? [? [? [? _]]]].
  specialize (H6 x).
  spec H6.  simpl. unfold natLevel. destruct H3 as [? [? ?]].
  change (level (m_phi ?a)) with (level a).
  apply join_level in H8. destruct H8.
  change (level (m_phi ?a)) with (level a) in H8.
  lia.
  specialize (H6 _ (necR_refl _)).
  spec H6. split; auto.
  auto.
 }
 clear H6.
 eexists. split. reflexivity.
 repeat intro.
 exists m'. split3; auto.
 split3; auto.
 hnf in H9.
 unfold retty in H8. destruct ret; try contradiction H8.
 destruct v; try contradiction H8.
 eapply jsafeN_halted with i.
 simpl. congruence.
 apply (EXIT (Some (Vint i)) z' m').
 reflexivity.
 clear - H10 H6.
 eapply joins_comm, join_sub_joins_trans, joins_comm, H10.
 destruct H6.
 change (Some (ghost_PCM.ext_ref z', NoneP) :: nil) with
      (own.ghost_approx (m_phi m') (Some (ghost_PCM.ext_ref z', NoneP) :: nil)).
  eexists; apply ghost_fmap_join; eauto.
-
(* internal case *)
(*
assert (Pf : params_of_fundef f = map snd params).
{ clear -Ef.
destruct f. subst fspec.
destruct f; inv Ef; simpl; auto.
revert fn_params params H0; induction fn_params as [|[??]]; destruct params as [|[??]]; simpl; intros; try discriminate; auto.
inv H0; f_equal; auto.
simpl in *. inv Ef.
induction params as [|[??]]; simpl; f_equal; auto.
}*)
hnf in H5.
destruct H5 as [b' [f' [[H5 [H9 H10]] H11]]].
symmetry in H5; inv H5.
inversion2 Eb H9. rename f' into f.
rename Eb into H7.

specialize (H11 Delta CS _ (necR_refl _)).

spec H11. { intro; apply tycontext_sub_refl. }
specialize (H11 _ (necR_refl _) cenv_sub_refl ts a). 
red in H11.
specialize (H11 (level jm)).
spec H11. apply later_nat; clear; lia.
  rewrite semax_fold_unfold in H11.

specialize (H11 psi (func_tycontext' f Delta) CS _ (necR_refl _)
     (conj (tycontext_sub_refl _) (conj cenv_sub_refl HGG))
      _ (necR_refl _)).
  spec H11.
  eapply pred_nec_hereditary; try apply Prog_OK.
  apply nec_nat; lia.
  clear Prog_OK H3.
  specialize (H11 Kstop (fun _ => TT) f _ (necR_refl _)).
  simpl in Ef.
  assert (Hret: fn_return f = retty) by (destruct f; inv Ef; auto).
  spec H11. { clear H11.
   split. hnf; intros; reflexivity.
red. red. red. intros ek vl te ve.
set (rhox := construct_rho (filter_genv psi) ve te).
cbv zeta.
cut ((!! guard_environ (func_tycontext' f Delta) f rhox &&
 (stackframe_of' cenv_cs f rhox *
  bind_ret vl (fn_return f) (Q ts a) rhox * 
  TT) && funassert (func_tycontext' f Delta) rhox >=>
 assert_safe Espec psi f ve te (exit_cont EK_return vl Kstop) rhox)
  (level jm)). {
  clearbody rhox; clear.
  evar (j: mpred).
  replace (proj_ret_assert
   (frame_ret_assert
      (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts a))
         (stackframe_of' cenv_cs f)) (fun _ : environ => TT)) ek vl rhox)
    with j.
  subst j.
  apply guard_fallthrough_return; auto.
  subst j.
  destruct ek; simpl; normalize.
  destruct (fn_return f); simpl; normalize;
  f_equal; pull_left (stackframe_of' cenv_cs f rhox); auto.
  pull_left (stackframe_of' cenv_cs f rhox); auto.
}
  subst rhox.
   intros y H3 a' H5 [[H8 H9] H11].
   clear ek.
   simpl exit_cont.
   unfold proj_ret_assert, frame_ret_assert,
   function_body_ret_assert, RA_return in H9.
     rewrite sepcon_assoc in H9.
    rewrite sepcon_comm in H9. 
   rewrite Hret in *.
   intros ? ?. exists (ghost_of a'); split; auto.
   exists a'; split; auto. split; auto. split; auto.
   simpl.
   hnf; intros.
   destruct (can_free_list Delta TT f jm0
                       psi ve te)
     as [m2 ?].
  - destruct H10 as [_ [_ [? _]]]; auto.
  - destruct H10; auto.
  - auto.
  - apply H8.
  -
    subst a'.
     eapply sepcon_derives; try apply H9; auto.
  - 
     clear H4.
     set (rho' := construct_rho (filter_genv psi)
            ve te) in *.
     destruct H10 as [COMPLETE [_ [H17' _]]].
  assert (H10:=I).
 assert (SFFB := stackframe_of_freeable_blocks Delta f rho' (globalenv prog) ve
     HGG COMPLETE H17'  (eq_refl _) H8).
  subst a'.
  exploit sepcon_derives; [ | | apply H9 |].
   2:  apply SFFB.  apply derives_refl.  clear H9.
  pull_left (freeable_blocks (blocks_of_env (globalenv prog) ve)).
 intro H13.
  rewrite sepcon_assoc in H13.
  destruct (free_list_juicy_mem_i _ _ _ _ H12 H13) as [jm2 [? [? ?]]].
  change (level (m_phi jm0)) with (level jm0).
  destruct (age1 jm0) as [jm0' | ] eqn:?.
  2: apply age1_level0 in Heqo; destruct vl; intros; rewrite Heqo; constructor.
   rewrite (age_level _ _ Heqo).
   destruct (age_twin' _ _ _ H9 Heqo) 
       as [jm2' [? ?]].
   subst m2. 
 assert (resource_decay (nextblock (m_dry jm0)) (m_phi jm0) (m_phi jm2') /\
            level jm0 = S (level jm2') /\
            ghost_of (m_phi jm2') =
            ghost_fmap (approx (level jm2')) (approx (level jm2'))
                  (ghost_of (m_phi jm0))). {
   split3.
  eapply resource_decay_trans.
  2: eapply free_list_resource_decay; eassumption.
  2: eapply age1_resource_decay; eassumption.
  rewrite (mem_lemmas.nextblock_freelist _ _ _ H12).
  apply Pos.le_refl.
  rewrite <- H14.
  apply age_level; auto.
  erewrite age1_ghost_of by (eapply age_jm_phi; eauto).
  change (level (m_phi jm2')) with (level jm2').
  f_equal.
  eapply free_list_juicy_mem_ghost; eauto.
 }
 assert ((ext_compat ora0) (m_phi jm2)). {
   pose proof (free_list_juicy_mem_ghost _ _ _ H4).
   clear - H16 H1.
   hnf in H1|-*. rewrite H16; auto.
 }
 eapply free_list_juicy_mem_lem in H4;[ | eassumption].
 apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H15)))) in H4.
 apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H15)))) in H16.
 move EXIT after H4.
 specialize (EXIT vl ora0 jm2').
 assert (tc_option_val retty vl). {
  clear - H13.
  rewrite sepcon_comm in H13.
  rewrite !sepcon_assoc in H13.
  destruct H13 as [? [? [? [? _]]]].
  subst retty.  destruct vl; simpl in H0; try contradiction.
  destruct H0 as [? _]. destruct v; try contradiction. eauto.
 }
 specialize (EXIT H17 H16).
 destruct vl; try contradiction.
 destruct v; try contradiction.
 clear H17.
 intros; econstructor; try instantiate (1:=jm2').
 split; auto; rewrite <- (age_jm_dry H15); econstructor; eauto.
 apply jm_bupd_intro; eapply jsafeN_halted.
 instantiate (1:=i).
 simpl. clear; congruence.
 apply EXIT.
}

remember (alloc_juicy_variables psi empty_env jm (fn_vars f)) eqn:AJV.
destruct p as [ve' jm']; symmetry in AJV.
destruct (alloc_juicy_variables_e _ _ _ _ _ _ AJV) as [H15 [H20' CORE]].
assert (MATCH := alloc_juicy_variables_match_venv _ _ _ _ _ AJV).
assert (H20 := alloc_juicy_variables_resource_decay _ _ _ _ _ _ AJV).
destruct (build_call_temp_env f args)
as [te' H21]; auto. 
  { clear - H10 (*Pf*) arg_p. subst fspec; simpl in H10. 
    destruct f; simpl in *.
    assert (Datatypes.length (map snd fn_params) =
                Datatypes.length params). assert (params = map snd fn_params) by apply H10. subst; trivial. 
   rewrite !map_length in H. rewrite H.
   clear - arg_p. apply tc_vals_length; trivial.
}

(*** split here ****)
destruct (level jm) eqn:H2'; [constructor |].

destruct (levelS_age1 _ _ H2') as [jm2 H13]. change (age jm jm2) in H13.
rewrite <- H2' in *. clear H2'.
pose proof (age_twin' _ _ _ H20' H13) as [jm'' [_ H20x]].
rewrite (age_level _ _ H13).
destruct H10 as [COMPLETE [H17 [H17' [Hvars H18]]]].

eapply jsafeN_step
  with (c' := Clight_core.State f (f.(fn_body)) Kstop ve' te')
       (m' := jm''); auto.
split; auto.
apply Clight_core.step_internal_function.
apply list_norepet_append_inv in H17; destruct H17 as [H17 [H22 H23]]; constructor; auto.
rewrite <- (age_jm_dry H20x); auto.
split.
 destruct H20;  apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm'); auto.
 apply age1_resource_decay; auto.
 split.
 rewrite H20'; apply age_level; auto.
 erewrite <- (alloc_juicy_variables_ghost _ _ _ jm), AJV; simpl.
 apply age1_ghost_of, age_jm_phi; auto.
assert (H22: (level jm2 >= level jm'')%nat)
  by (apply age_level in H13; apply age_level in H20x; lia).
(*pose (rho3 := mkEnviron (*(ge_of rho)*)(filter_genv psi) (make_venv ve') (make_tenv te')).
assert (H23: app_pred (funassert Delta rho3) (m_phi jm'')). {
  apply (resource_decay_funassert _ _ (nextblock (m_dry jm)) _ (m_phi jm'')) in m_funassert.
  2: apply laterR_necR; apply age_laterR; auto.
  unfold rho3; clear rho3.
  apply m_funassert.
  rewrite CORE. apply age_core. apply age_jm_phi; auto.
  destruct H20;  apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm'); auto.
   apply age1_resource_decay; auto.
}*)
assert (H23: app_pred (fungassert Delta (filter_genv psi, args)) (m_phi jm'')).
{ apply (resource_decay_fungassert _ _ (nextblock (m_dry jm)) _ (m_phi jm'')) in m_funassert.
  2: apply laterR_necR; apply age_laterR; auto.
  apply m_funassert.
  rewrite CORE. apply age_core. apply age_jm_phi; auto.
  destruct H20;  apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm'); auto.
  apply age1_resource_decay; auto.
}
  apply (pred_nec_hereditary  _ _ _ (necR_level' (laterR_necR (age_laterR H13))))
    in H11.
  specialize (H11 te' ve' _ H22 _ (necR_refl _)).
  spec H11; [clear H11|]. {
  split; [split |]; auto.
  (*3:{ unfold rho3 in H23. unfold construct_rho.
     unfold rho in H23.
     simpl ge_of in H23. rewrite ge_of_make_args in H23.
    auto.
  }*)
  split; [ | simpl; split; [ | reflexivity]; apply MATCH ].
 -
  rewrite (age_jm_dry H20x) in H15.
  clear m_sat_Pa m_funassert.
  eapply semax_call_typecheck_environ
   with (jm := jm2); try eassumption.
 +
  erewrite <- age_jm_dry by apply H13;  eassumption.
 + destruct H23 as [H _]. 
    intros. specialize (H b0 b1 a' H1 H3).
    destruct H as [b2 [? ?]]; exists b2; split; auto.
 + rewrite snd_split. subst fspec; simpl in H18. destruct H18; subst. trivial.
- 
 normalize.
 split; auto. (*unfold rho3 in H23.*) unfold construct_rho.
(* subst rho.
 rewrite ge_of_make_args in H23. auto.
 clear H23.*)
 rewrite <- sepcon_assoc.
 apply (pred_nec_hereditary  _ _ _ (laterR_necR (age_laterR (age_jm_phi H20x)))).
 unfold bind_args.
 unfold tc_formals.
 normalize.
 simpl fst in H18; simpl snd in H18.
 split.
 +
 hnf.
 destruct H18 as [H18 [H18b H18']].
 clear m_funassert.
 destruct fspec; simpl in *.
 destruct f; inv Ef; simpl in *.
 clear - (*Pf*) arg_p H21 H17.
 (*rewrite <- Pf in arg_p. clear Pf.*)
 simpl in *.
 match goal with H: tc_vals _ ?A |- tc_vals _ ?B => replace B with A; auto end.
 rewrite list_norepet_app in H17. destruct H17 as [H17 [_ _]].
 clear - H17 H21.
 forget (create_undef_temps fn_temps) as te.
 revert  args te te' H21 H17.
 induction fn_params as [|[??]]; destruct args; intros; auto; try discriminate.
 inv H17.
 simpl. f_equal. unfold eval_id, construct_rho; simpl.
  inv H21.
 erewrite pass_params_ni; try eassumption.
  rewrite PTree.gss. reflexivity. 
 eapply IHfn_params; try eassumption.
+
 rewrite sepcon_assoc.
 eapply sepcon_derives.
 instantiate (1:=emp); auto. apply derives_refl.
 rewrite emp_sepcon.
(* apply (alloc_juicy_variables_age H13 H20x) in AJV.*)
 destruct H18 as [H18a [_ H18c]]. subst params.
 assert (list_norepet (map fst (fn_params f))).
 { apply list_norepet_app in H17. apply H17. }
 eapply sepcon_derives.
 assert (VUNDEF:= tc_vals_Vundef arg_p).
 eapply make_args_close_precondition; eauto.
 apply derives_refl.
 eapply alloc_juicy_variables_lem2; eauto.
 unfold var_sizes_ok in Hvars;
 rewrite Forall_forall in Hvars, COMPLETE |- *.
 intros.
 specialize (COMPLETE x H1).
 specialize (Hvars x H1).
 rewrite (cenv_sub_sizeof HGG); auto.
}
replace (level jm2) with (level jm'').
apply assert_safe_jsafe.
apply H11.
clear - H13 H20x H20'.
apply age_level in H13.
apply age_level in H20x.
congruence.
Qed.

Lemma semax_prog_rule {CS: compspecs} :
  forall V G prog m h z,
     postcondition_allows_exit tint ->
     @semax_prog CS prog z V G ->
     Genv.init_mem prog = Some m ->
     { b : block & { q : CC_core &
       (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
       (forall jm, m_dry jm = m -> exists jm',
                    semantics.initial_core (juicy_core_sem (cl_core_sem (globalenv prog))) h
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
  intros until z. intro EXIT. intros. rename H0 into H1. 
  generalize H; intros [? [AL [HGG [[? [GC ?]] [GV ?]]]]].
  destruct (find_id (prog_main prog) G) as [fspec|] eqn:Hfind; try contradiction.
  assert (H4': exists post, In (prog_main prog, main_spec_ext' prog z post) G 
                    /\ fspec = main_spec_ext' prog z post). {
    destruct (find_id (prog_main prog) G) eqn:?.
    apply find_id_e in Heqo. destruct H4 as [post ?]. exists post.
    subst. split; auto. inv Hfind. auto. inv Hfind.
  } clear H4. rename H4' into H4.
  assert (H5:{ f | In (prog_main prog, f) (prog_funct prog)}).
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
  destruct EXx as [b [? ?]]; auto.
  destruct fspec as [[ params retty] cc A P Q NEP NEQ].
  assert (cc = cc_default /\ params = nil). {
    clear - H4. destruct H4 as [? [? ?]]. inv H0. auto.
  }
  destruct H7; subst cc.
  assert (Hretty: retty = tint). {
    destruct H4 as [post [? ?]].
    inv H7. auto. 
  }
  subst retty.
  assert (SPEP := semax_prog_entry_point V G prog b (prog_main prog)
       params nil A P Q NEP NEQ h z EXIT H H5 Hfind).
  spec SPEP. subst params; constructor.
  set (gargs:= (filter_genv (globalenv prog), @nil val)) in *.
  cbv beta iota zeta in SPEP.
  destruct SPEP as [q [? ?]].
  exists b, q.
  split; [split |]; auto.
 - 
  intros. apply H7; clear H7; auto.
  clear - H1 H10.
  rewrite H10.
  split.  red.  apply neutral_inject. eapply Genv.initmem_inject; eauto.
  erewrite Genv.init_mem_genv_next; eauto. apply Coqlib.Ple_refl.
 - clear H7.
  intro n.
  pose (jm := initial_jm_ext z prog m G n H1 H0 H2).
  exists jm.
  assert (level jm = n)
    by (subst jm; simpl; rewrite inflate_initial_mem_level;
          apply level_make_rmap).
  assert (nth_error (ghost_of (m_phi jm)) 0 = Some (Some (ext_ghost z, NoneP)))
    by (simpl; unfold inflate_initial_mem; rewrite ghost_of_make_rmap;
          unfold initial_core_ext; rewrite ghost_of_make_rmap;  auto).
  split3; [ | | split3; [ | | split3]]; auto.
  + rewrite <- H7.
    destruct H4 as [post [H4 H4']].
    unfold main_spec_ext' in H4'.
    injection H4'; intros.  subst params A.
    apply inj_pair2 in H11.
    apply inj_pair2 in H12. subst P Q. clear H14.
    apply (H9 jm nil (globals_of_genv (filter_genv (globalenv prog)))); eauto.
    * eexists; eexists; split; [apply initial_jm_ext_eq|].
     split.
        split; [ simpl; trivial |].
        split; auto. 
        apply global_initializers; auto.
     -- simpl.
        unshelve eexists; [split; auto; apply Share.nontrivial|].
        unfold set_ghost; rewrite ghost_of_make_rmap, resource_at_make_rmap.
        split; [apply resource_at_core_identity|].
        unfold ext_ghost. repeat f_equal.
    * apply (initial_jm_ext_funassert z V prog m G n H1 H0 H2).
+
  apply initial_jm_ext_without_locks.
+
  apply initial_jm_ext_matchfunspecs.
+
  apply (initial_jm_ext_funassert z V prog m G n H1 H0 H2).
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
Proof. inv M. exists i, fd, fspec; tauto. Qed.

Lemma match_fdecs_cons_D1 f funs K (M: match_fdecs (cons f funs) K):
exists i fd fspec G, f=(i,fd) /\ K=cons (i,fspec) G /\ 
     type_of_fundef fd = type_of_funspec fspec /\
     match_fdecs funs G.
Proof. inv M. exists i, fd, fspec, G; tauto. Qed.

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

Lemma make_tycontext_g_nilG_find_id V i: (make_tycontext_g V nil) ! i = find_id i V.
Proof.
induction V; simpl. apply PTree.gempty.
destruct a as [j t]; simpl.
rewrite PTree.gsspec. unfold eq_dec, EqDec_ident, ident_eq. destruct (peq i j); subst; simpl; eauto.
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

Lemma make_tycontext_g_G_None V i: forall G, find_id i G = None ->
   (make_tycontext_g V G) ! i = find_id i V.
Proof. induction G; intros.
+ apply semax_prog.make_tycontext_g_nilG_find_id. 
+ simpl in H. destruct a as [j a]; simpl. rewrite PTree.gsspec.
  if_tac in H; subst. inv H. rewrite if_false; auto.
Qed.

Lemma list_norepet_cut_middle {A:Set} l1 l2 (a:A) (Ha: list_norepet (l1 ++ (a :: l2))): list_norepet (l1 ++ l2).
Proof.
apply list_norepet_append_inv in Ha. destruct Ha as [VH1 [VH2 D]]. inv VH2.
apply list_norepet_append; trivial.
intros x y X Y. apply D; [ trivial | right; trivial].
Qed.

Lemma make_context_g_mk_findV_mk: forall H V (VH:list_norepet (map fst V ++ map fst H)) i t
(Heqd : find_id i V = Some t), (make_tycontext_g V H) ! i = Some t.
Proof.
induction H; intros.
+ rewrite make_tycontext_g_nilG_find_id; trivial.
+ apply make_tycontext_g_consG_mk. destruct a as [j fs]; simpl in *.
destruct (peq i j); subst; simpl.
- apply list_norepet_append_inv in VH. destruct VH as [_ [_ VH]].
elim (VH j j); trivial.
apply (find_id_In_map_fst _ _ _ Heqd). left; trivial.
- apply list_norepet_cut_middle in VH. apply IHlist; trivial.
Qed.

Lemma make_context_g_char:
forall H V (VH:list_norepet (map fst V ++ map fst H)) i,
(make_tycontext_g V H) ! i = match (make_tycontext_s H)!i with
                               None => find_id i V
                             | Some fs => Some (type_of_funspec fs)
                             end.
Proof.
induction H; intros.
+ rewrite make_tycontext_g_nilG_find_id.
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
* rewrite Heqd, find_id_maketycontext_s. apply find_id_In_map_fst in Heqd.
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

Lemma semax_func_cenv_sub' {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) V H ge funs G:
@semax_func V H CS ge funs G -> @semax_func V H CS' ge funs G.
Proof. eapply (@semax_func_cenv_sub _ _ CSUB); intros ?; apply sub_option_refl. Qed. 

Lemma semax_body_subsumption cs V V' F F' f spec
      (SF: @semax_body V F cs f spec)
      (TS: tycontext_sub (func_tycontext f V F nil) (func_tycontext f V' F' nil)):
  @semax_body V' F' cs f spec.
Proof.
  destruct spec. destruct f0.
  destruct SF as [? [HH SF]]; split3; auto. clear H.
  intros. 
  intros n. 
  eapply semax_mono. apply TS. apply (SF Espec0 ts x n).
Qed. 

Lemma semax_external_binaryintersection {ef A1 P1 Q1 P1ne Q1ne A2 P2 Q2 P2ne Q2ne 
      A P Q P_ne Q_ne sig cc n}
  (EXT1: semax_external Espec ef A1 P1 Q1 n)
  (EXT2: semax_external Espec ef A2 P2 Q2 n)
  (BI: binary_intersection (mk_funspec sig cc A1 P1 Q1 P1ne Q1ne) 
                      (mk_funspec sig cc A2 P2 Q2 P2ne Q2ne) =
       Some (mk_funspec sig cc A P Q P_ne Q_ne))
  (LENef: length (fst sig) = length (sig_args (ef_sig ef))):
  semax_external Espec ef A P Q n.
Proof.
  intros ge ts x.
  simpl in BI.
  rewrite ! if_true in BI by trivial. 
  inv BI. apply inj_pair2 in H1; subst P. apply inj_pair2 in H2; subst Q.
  destruct x as [bb BB]; destruct bb.
  * apply (EXT1 ge ts BB). 
  * intros m NM FRM typs vals r MR rr R [TYS H].
    apply (EXT2 ge ts BB m NM FRM typs vals r MR rr R). split; trivial.
Qed.

Lemma semax_body_binaryintersection {V G cs} f sp1 sp2 phi
  (SB1: @semax_body V G cs f sp1) (SB2: @semax_body V G cs f sp2)
  (BI: binary_intersection (snd sp1) (snd sp2) = Some phi):
  @semax_body V G cs f (fst sp1, phi).
Proof.
  destruct sp1 as [i phi1]. destruct phi1 as [[tys1 rt1] cc1 A1 P1 Q1 P1_ne Q1_ne]. 
  destruct sp2 as [i2 phi2]. destruct phi2 as [[tys2 rt2] cc2 A2 P2 Q2 P2_ne Q2_ne]. 
  destruct phi as [[tys rt] cc A P Q P_ne Q_ne]. simpl in BI.
  if_tac in BI; [ inv H | discriminate]. if_tac in BI; [inv BI | discriminate].
  apply Classical_Prop.EqdepTheory.inj_pair2 in H6.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H5. subst. simpl fst; clear - SB1 SB2.
  destruct SB1 as [X [X1 SB1]]; destruct SB2 as [_ [X2 SB2]].
  split3; [ apply X | trivial | simpl in X; intros ].
  destruct x as [b Hb]; destruct b; [ apply SB1 | apply SB2].
Qed.

Lemma typecheck_temp_environ_eval_id {f lia} 
          (LNR: list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
          (TC : typecheck_temp_environ (te_of lia) (make_tycontext_t (fn_params f) (fn_temps f))):
      map (Map.get (te_of lia)) (map fst (fn_params f)) =
      map Some (map (fun i : ident => eval_id i lia) (map fst (fn_params f))).
Proof.
  specialize (tc_temp_environ_elim LNR TC).
  forget (fn_params f) as l. clear.
  induction l; unfold eval_id; simpl; intros; trivial.
  rewrite IHl; clear IHl; [ f_equal | intros; apply H; right; trivial].
  unfold force_val; destruct a; simpl in *.
  destruct (H i t) as [v [Hv Tv]]. left; trivial.
  rewrite Hv; trivial.
Qed.

Lemma typecheck_environ_eval_id {f V G lia} (LNR: list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
                                (TC : typecheck_environ (func_tycontext f V G nil) lia):
      map (Map.get (te_of lia)) (map fst (fn_params f)) =
      map Some (map (fun i : ident => eval_id i lia) (map fst (fn_params f))).
Proof. apply typecheck_temp_environ_eval_id; trivial. apply TC. Qed.

Lemma map_Some_inv {A}: forall {l l':list A}, map Some l = map Some l' -> l=l'.
Proof. induction l; simpl; intros; destruct l'; inv H; trivial. f_equal; auto. Qed. 

Lemma semax_body_funspec_sub {V G cs f i phi phi'} (SB: @semax_body V G cs f (i, phi))
  (Sub: funspec_sub phi phi')
  (LNR: list_norepet (map fst (fn_params f) ++ map fst (fn_temps f))):
  @semax_body V G cs f (i, phi').
Proof.
 destruct phi as [sig cc A P Q Pne Qne].
 destruct phi' as [sig' cc' A' P' Q' Pne' Qne'].
 destruct Sub as [[Tsigs CC] Sub]. subst cc'. simpl in Sub.
 destruct SB as [SB1 [SB2 SB3]].
 subst sig'.
 split3; trivial. intros.
 specialize (Sub ts x).
 eapply semax_adapt
 with
  (Q'0:= frame_ret_assert (function_body_ret_assert (fn_return f) (Q' ts x))
           (stackframe_of f))
  (P'0 := fun tau =>
    EX vals:list val,
    EX ts1:list Type, EX x1 : dependent_type_functor_rec ts1 A mpred,
    EX FR: mpred,
    !!(forall rho' : environ,
              !! tc_environ (rettype_tycontext (snd sig)) rho' && (FR * Q ts1 x1 rho') |-- Q' ts x rho') &&
      (stackframe_of f tau * FR * P ts1 x1 (ge_of tau, vals) &&
            !! (map (Map.get (te_of tau)) (map fst (fn_params f)) = map Some vals /\ tc_vals (map snd (fn_params f)) vals))).
 + intros lia m [TC [OM [m1 [m2 [JM [[vals [[MAP VUNDEF] HP']] M2]]]]]].
   destruct (Sub (ge_of lia, vals) m1) as [ts1 [x1 [FR1 [M1 RetQ]]]]; clear Sub.
   { split; trivial.
     simpl.
       rewrite SB1. simpl in TC. destruct TC as [TC1 [TC2 TC3]].
       unfold fn_funsig. simpl. clear - TC1 MAP LNR VUNDEF.
       specialize (@tc_temp_environ_elim (fn_params f) (fn_temps f) _ LNR TC1). simpl in TC1.  red in TC1. clear - MAP (*VUNDEF*); intros TE.
       forget (fn_params f) as params. generalize dependent vals.
       induction params; simpl; intros.
       - destruct vals; inv MAP. constructor.
       - destruct vals; inv MAP. constructor.
         * clear IHparams. intros. destruct (TE (fst a) (snd a)) as [w [W Tw]].
           left; destruct a; trivial.
           rewrite W in H0. inv H0. 
           apply tc_val_has_type; apply Tw; trivial.
         * apply IHparams; simpl; trivial.
           intros. apply TE. right; trivial. }
    split; [ | simpl; trivial].
    split; [ | simpl; trivial].
    split; [ | simpl; trivial].
    split; [| simpl; trivial].
    exists vals, ts1, x1, FR1. simpl in MAP.
    split3.
    - simpl; intros. eapply derives_trans. 2: apply RetQ.
      (*similar proof as in seplog*)
      intros ? [? ?]. split; trivial. simpl.
      simpl in H. clear - H. destruct H as [_ [Hve _]].
      simpl in *. red in Hve. destruct rho'; simpl in *.
      apply Map.ext; intros x. specialize (Hve x).
      destruct (Map.get ve x); simpl.
      * destruct p; simpl in *. destruct (Hve t) as [_ H]; clear Hve. 
        exploit H. exists b; trivial. rewrite PTree.gempty. congruence.
      * reflexivity.
    - apply join_comm in JM. rewrite sepcon_assoc.
      exists m2, m1; split3; trivial.
    - split; trivial. destruct TC as [TC1 _]. simpl in TC1. red in TC1.
      clear - MAP VUNDEF TC1 LNR. forget (fn_params f) as params. forget (fn_temps f) as temps. forget (te_of lia) as tau.
      clear f lia. generalize dependent vals. induction params; simpl; intros; destruct vals; inv MAP; trivial.
      inv VUNDEF. inv LNR. destruct a; simpl in *.
      assert (X: forall id ty, (make_tycontext_t params temps) ! id = Some ty ->
                 exists v : val, Map.get tau id = Some v /\ tc_val' ty v).
      { intros. apply TC1. simpl.  rewrite PTree.gso; trivial.
        apply make_context_t_get in H. intros ?; subst id. contradiction. } 
      split; [ clear IHparams | apply (IHparams H6 X _ H1 H4)].
      destruct (TC1 i t) as [u [U TU]]; clear TC1. rewrite PTree.gss; trivial.
      rewrite U in H0; inv H0. apply TU; trivial.
  + clear Sub.
    apply extract_exists_pre; intros vals.
    apply extract_exists_pre; intros ts1.
    apply extract_exists_pre; intros x1.
    apply extract_exists_pre; intros FRM.
    apply semax_extract_prop; intros QPOST.
    unfold fn_funsig in *. simpl in SB2; rewrite SB2 in *. 
    apply (semax_frame (func_tycontext f V G nil)
      (fun rho : environ =>
            close_precondition (map fst (fn_params f)) (P ts1 x1) rho * 
            stackframe_of f rho)
      (fn_body f)
      (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts1 x1)) (stackframe_of f))
      (fun rho => FRM)) in SB3.
    - eapply semax_pre_post.
      6: apply SB3.
      all: clear SB3; intros; simpl; try solve [normalize]. 
      * intros m [TC [[n1 [n2 [JN [N1 N2]]]] [VALS TCVals]]].
        unfold close_precondition. apply join_comm in JN. rewrite sepcon_assoc. 
        exists n2, n1; split3; trivial.
        exists vals. simpl in *. split; trivial. split; trivial.
        apply (tc_vals_Vundef TCVals).
      * intros m [TC M].
        destruct (fn_return f); 
        try solve [rewrite sepcon_assoc in M; 
                   rewrite predicates_sl.FF_sepcon in *; apply M].
        rewrite sepcon_comm, <- sepcon_assoc in M.
           eapply sepcon_derives; [ clear M | apply derives_refl | apply M].
           eapply derives_trans; [ | apply QPOST]; apply andp_right; trivial.
           intros k K; clear; apply tc_environ_rettype.
      * apply andp_left2. intros u U.
        rewrite sepcon_comm, <- sepcon_assoc in U.
        eapply sepcon_derives; [ clear U | apply derives_refl | apply U].
        destruct vl; simpl; normalize.
        ++ eapply derives_trans; [ | apply QPOST]; apply andp_right; trivial.
           intros k K; clear. apply tc_environ_rettype_env_set.
        ++ destruct (fn_return f). 
           { eapply derives_trans; [ | apply QPOST]; apply andp_right; trivial.
           intros k K; clear; apply tc_environ_rettype. }
           all: rewrite semax_lemmas.sepcon_FF; trivial. 
    - do 2 red; intros; trivial.
Qed.

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
