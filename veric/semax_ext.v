Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.juicy_mem_ops.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_call.
Require Import VST.veric.res_predicates.

Require Import VST.veric.res_predicates.
Require Import compcert.cfrontend.Clight.
Require Import compcert.export.Clightdefs.
Import compcert.lib.Maps.

Definition funsig2signature (s : funsig) cc : signature :=
  mksignature (map argtype_of_type (map snd (fst s))) (rettype_of_type (snd s)) cc.

Definition typesig2signature (s : typesig) cc : signature :=
  mksignature (map argtype_of_type (fst s)) (rettype_of_type (snd s)) cc.

(* NOTE.   ext_link: Strings.String.string -> ident
   represents the mapping from the _name_ of an external function
  (an ASCII string) to the [ident] that's used to represent it in this program module.
  That mapping can be computed from the prog_defs component of the Clight.program
  produced by clightgen.
*)

Definition ef_id_sig (ext_link: Strings.String.string -> ident) ef :=
  match ef with EF_external id sig => Some (ext_link id, sig) | _ => None end.

Section funspecs2jspec.

Variable Z : Type.

Variable Espec : juicy_ext_spec Z.

Definition symb2genv_upper_bound (s: PTree.t block) : block :=
  Pos.succ (fold_right Pos.max  1%positive (map snd (PTree.elements s))).

Definition symb2genv (ge_s: injective_PTree block) : genv.
    refine (Build_genv (@Genv.mkgenv _ _ nil (proj1_sig ge_s) (PTree.empty _) (symb2genv_upper_bound (proj1_sig ge_s)) _ _ _) (PTree.empty _)).
*
intros.
unfold Coqlib.Plt.
apply Pos.lt_le_trans with (Pos.succ b).
apply Pos.lt_succ_r.
apply Pos.le_refl.
unfold symb2genv_upper_bound.
apply -> Pos.succ_le_mono.
apply PTree.elements_correct in H.
revert H.
induction (PTree.elements (proj1_sig ge_s)); intros. inv H.
destruct H. subst. simpl.
apply Pos.le_max_l.
simpl.
eapply Pos.le_trans; [  | apply Pos.le_max_r].
auto.
*
intros.
rewrite PTree.gempty in H. inv H.
*
intros.
destruct ge_s; simpl in *.
revert id1 id2 b H H0.
simpl.
auto.
Defined.

Lemma symb2genv_ax' : forall (ge_s : injective_PTree block), genv_symb_injective (symb2genv ge_s) = ge_s.
Proof.
intros.
destruct ge_s.
unfold genv_symb_injective.
f_equal.
Qed.

Lemma symb2genv_ax : forall (ge: genv), Genv.genv_symb (symb2genv (genv_symb_injective ge)) = Genv.genv_symb ge.
Proof.
intros.
reflexivity.
Qed.

(* Making this particular instance of EqDec opaque *)
Lemma oi_eq_dec : forall a a' : option (ident * signature), { a = a' } + { a <> a' }.
Proof.
  intros; repeat (apply eq_dec || decide equality).
Qed.

Definition funspec2pre (ext_link: Strings.String.string -> ident) (A : TypeTree)
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (id: ident) (sig : signature) (ef: external_function) x (ge_s: injective_PTree block)
           (tys : list typ) args (z : Z) m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then (rmap*(sigT (fun ts => dependent_type_functor_rec ts A mpred)))%type else ext_spec_type Espec ef) -> Prop)
  with
    | left _ => fun x' => Val.has_type_list args (map proj_xtype (sig_args (ef_sig ef))) /\
        exists phi0 phi1, join phi0 phi1 (m_phi m)
                       /\ P (projT1 (snd x')) (projT2 (snd x')) (filter_genv (symb2genv ge_s), args) phi0
                       /\ necR (fst x') phi1 /\ ext_compat z (m_phi m)
    | right n => fun x' => ext_spec_pre Espec ef x' ge_s tys args z m
  end x.

Definition funspec2post (ext_link: Strings.String.string -> ident) (A : TypeTree)
  (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  id sig ef x ge_s (tret : xtype) ret (z : Z) m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then (rmap*(sigT (fun ts => dependent_type_functor_rec ts A mpred)))%type else ext_spec_type Espec ef) -> Prop)
  with
    | left _ => fun x' => exists phi0 phi1, join phi0 phi1 (m_phi m)
                       /\ Q (projT1 (snd x')) (projT2 (snd x')) (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret) phi0
                       /\ necR (fst x') phi1
    | right n => fun x' => ext_spec_post Espec ef x' ge_s tret ret z m
  end x.

Definition funspec2post' (ext_link: Strings.String.string -> ident) (A : TypeTree)
  (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  id sig ef x ge_s (tret : xtype) ret (z : Z) m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then (rmap*(sigT (fun ts => dependent_type_functor_rec ts A mpred)))%type else ext_spec_type Espec ef) -> Prop)
  with
    | left _ => fun x' => exists phi0 phi1, join phi0 phi1 (m_phi m)
                       /\ Q (projT1 (snd x')) (projT2 (snd x')) (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret) phi0
                       /\ necR (fst x') phi1
    | right n => fun x' => ext_spec_post Espec ef x' ge_s tret ret z m
  end x.

Definition funspec2extspec (ext_link: Strings.String.string -> ident) (f : (ident*funspec))
  : external_specification juicy_mem external_function Z :=
  match f with
    | (id, mk_funspec ((params, sigret) as fsig) cc A P Q NEP NEQ) =>
      let sig := typesig2signature fsig cc in
      Build_external_specification juicy_mem external_function Z
        (fun ef => if oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) then (rmap* (sigT (fun ts => dependent_type_functor_rec ts A mpred)))%type else ext_spec_type Espec ef)
        (funspec2pre ext_link A P id sig)
        (funspec2post ext_link A Q id sig)
        (fun rv z m => True)
  end.

Local Open Scope pred.

Definition wf_funspec (f : funspec) :=
  match f with
    | mk_funspec sig cc A P Q _ _ =>
        forall ts a (ge ge': genv)  args,
          Genv.genv_symb ge = Genv.genv_symb ge' ->
          P ts a (filter_genv ge, args) 
         |-- P ts a (filter_genv ge', args)
  end.

Lemma make_ext_args_filtergenv (ge ge' : genv)
      (H: Genv.genv_symb ge = Genv.genv_symb ge'):
  filter_genv ge = filter_genv ge'.
Proof.
intros.
unfold filter_genv, Genv.find_symbol.
rewrite H; auto.
Qed.

Lemma all_funspecs_wf f : wf_funspec f.
Proof.
destruct f; simpl; intros ts a ge ge' n args H.
erewrite make_ext_args_filtergenv; eauto.
Qed.

#[local] Obligation Tactic := idtac.

Program Definition funspec2jspec (ext_link: Strings.String.string -> ident) f : juicy_ext_spec Z :=
  Build_juicy_ext_spec _ (funspec2extspec ext_link f) _ _ _ _ _ _.
Next Obligation.
destruct f; simpl; unfold funspec2pre, pureat; simpl; destruct f; simpl;
  destruct t; simpl; intros.
if_tac [e0|e0].
* destruct e; try discriminate; injection e0 as E; subst i sg; intros a a' Hage.
intros [Hargs H].
split; auto.
apply age_jm_phi in Hage.
destruct H as [phi0 [phi1 [Hjoin [Hx [Hy Hg]]]]].
destruct (age1_join2 phi0 Hjoin Hage) as [x' [y' [Hjoin' [Hage' H]]]].
exists x', y'; split; auto.
destruct P as (? & h & ?). split. eapply h; eauto.
split. apply (necR_trans (fst t0) phi1 y'); auto.
unfold necR. constructor; auto.
unfold ext_compat in *; rewrite (age1_ghost_of _ _ Hage).
apply ext_join_approx; auto.
* intros ? ?; auto.
destruct Espec; simpl; apply JE_pre_hered.
Qed.
Next Obligation.
destruct f; simpl; unfold funspec2pre, pureat; simpl; destruct f; simpl;
  destruct t; simpl; intros.
if_tac [e0|e0].
* destruct e; try discriminate; injection e0 as E; subst i sg.
destruct H as [_ Hext]; apply rmap_order in Hext as (Hl & Hr & J).
destruct H1 as [? H].
split; auto.
destruct H as [phi0 [phi1 [Hjoin [Hx [Hy Hg]]]]].
destruct J as [? J]; destruct (join_assoc (join_comm (ghost_of_join _ _ _ Hjoin)) J) as (g' & ? & ?).
destruct (make_rmap (resource_at phi0) (own.ghost_approx (level phi0) g') (level phi0))
  as (phi0' & Hl' & Hr' & Hg').
{ extensionality; apply resource_at_approx. }
{ rewrite ghost_fmap_fmap, !approx_oo_approx; auto. }
destruct (join_level _ _ _ Hjoin).
exists phi0', phi1; repeat split; auto.
+ apply resource_at_join2; try congruence.
  - intros; rewrite Hr', <- Hr.
    apply resource_at_join; auto.
  - rewrite Hg'.
    rewrite <- (ghost_of_approx phi1), <- (ghost_of_approx (m_phi a')), <- Hl, H3, H4.
    apply ghost_fmap_join; auto.
+ eapply pred_upclosed, Hx.
  rewrite rmap_order; repeat split; auto.
  rewrite Hg'.
  rewrite <- ghost_of_approx; eexists; apply ghost_fmap_join; eauto.
* eapply JE_pre_ext, H1; auto.
Qed.
Next Obligation.
destruct f; simpl; unfold funspec2post, pureat; simpl; destruct f; simpl;
  destruct t; simpl; intros.
if_tac [e0|e0].
* destruct e; try discriminate; injection e0 as E; subst i sg. intros a a' Hage. destruct Q as (? & h & ?); simpl.
intros [phi0 [phi1 [Hjoin [Hx Hy]]]].
apply age_jm_phi in Hage.
destruct (age1_join2 phi0 Hjoin Hage) as [x' [y' [Hjoin' [Hage' H]]]].
exists x', y'; split; auto.
split; [solve[eapply h; eauto]|].
apply (necR_trans (fst t0) phi1 y'); auto.
unfold necR. constructor; auto.
* intros ? ?; auto.
destruct Espec; simpl; apply JE_post_hered.
Qed.
Next Obligation.
destruct f; simpl; unfold funspec2post, pureat; simpl; destruct f; simpl;
  destruct t; simpl; intros.
if_tac [e0|e0].
* destruct e; try discriminate; injection e0 as E; subst i sg. intros a a' Hext. destruct Q as (? & h & e); simpl.
intros [phi0 [phi1 [Hjoin [Hx Hy]]]].
destruct Hext as [_ Hext]; apply rmap_order in Hext as (Hl & Hr & ? & J).
destruct (join_assoc (join_comm (ghost_of_join _ _ _ Hjoin)) J) as (g' & ? & ?).
destruct (make_rmap (resource_at phi0) (own.ghost_approx (level phi0) g') (level phi0))
  as (phi0' & Hl' & Hr' & Hg').
{ extensionality; apply resource_at_approx. }
{ rewrite ghost_fmap_fmap, !approx_oo_approx; auto. }
destruct (join_level _ _ _ Hjoin).
exists phi0', phi1; repeat split; auto.
+ apply resource_at_join2; try congruence.
  - intros; rewrite Hr', <- Hr.
    apply resource_at_join; auto.
  - rewrite Hg'.
    rewrite <- (ghost_of_approx phi1), <- (ghost_of_approx (m_phi a')), <- Hl, H1, H2.
    apply ghost_fmap_join; auto.
+ eapply e, Hx.
  rewrite rmap_order; repeat split; auto.
  rewrite Hg'.
  rewrite <- ghost_of_approx; eexists; apply ghost_fmap_join; eauto.
* intros ? ?; auto.
destruct Espec; simpl; apply JE_post_ext.
Qed.
Next Obligation.
intros ? ? ? ?; destruct f; destruct f; destruct t; simpl.
intros a' Hage; auto.
Qed.
Next Obligation.
intros ? ? ? ?; destruct f; destruct f; destruct t; simpl.
intros a' Hext; auto.
Qed.

End funspecs2jspec.

Definition funspecs_norepeat (fs : funspecs) := list_norepet (map fst fs).

Fixpoint add_funspecs_rec (ext_link: Strings.String.string -> ident) (Z : Type) (Espec : juicy_ext_spec Z) (fs : funspecs) :=
  match fs with
    | nil => Espec
    | cons (i,f) fs' => funspec2jspec Z (add_funspecs_rec ext_link Z Espec fs') ext_link (i,f)
  end.

Require Import Stdlib.Logic.JMeq.

Lemma add_funspecs_pre  (ext_link: Strings.String.string -> ident)
              {Z fs id sig cc A P Q NEP NEQ}
              {x: sigT (fun ts => dependent_type_functor_rec ts A mpred)} {args m} Espec tys ge_s phi0 phi1 :
  let ef := EF_external id (typesig2signature sig cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec sig cc A P Q NEP NEQ)) fs ->
  join phi0 phi1 (m_phi m) ->
  Val.has_type_list args (map proj_xtype (sig_args (ef_sig ef))) ->
  P (projT1 x) (projT2 x) (filter_genv (symb2genv ge_s), args) phi0 ->
  exists x' : ext_spec_type (JE_spec _ (add_funspecs_rec ext_link Z Espec fs)) ef,
    JMeq (phi1, x) x'
    /\ forall z, ext_compat z (m_phi m) ->
          ext_spec_pre (add_funspecs_rec ext_link Z Espec fs) ef x' ge_s tys args z m.
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1 H2 Hargsty Hpre.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; revert x H2 Hpre; unfold funspec2pre; simpl.
destruct sig; simpl.
if_tac [e0|e0].
intros x Hjoin Hp. exists (phi1, x). split; eauto.
split; eauto 6.
exfalso; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ eapply (in_map fst) in H1; apply H1. }
inversion H as [|? ? Ha Hb]; subst.
destruct (IHfs Hb H1 H2 Hargsty Hpre) as [x' H3].
clear -Ha Hin H1 H3; revert x' Ha Hin H1 H3.
destruct a; simpl; destruct f; simpl; destruct t; simpl; unfold funspec2pre; simpl.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; exfalso; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  exfalso; auto.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_pre_void  (ext_link: Strings.String.string -> ident)
              {Z fs id sig cc A P Q NEP NEQ}
              {x: sigT (fun ts => dependent_type_functor_rec ts A mpred)}
              {args m} Espec tys ge_s phi0 phi1 :
  let ef := EF_external id (mksignature (map argtype_of_type sig) Xvoid cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec (sig, tvoid) cc A P Q NEP NEQ)) fs ->
  join phi0 phi1 (m_phi m) ->
  Val.has_type_list args (map proj_xtype (sig_args (ef_sig ef))) ->
  P (projT1 x) (projT2 x) (filter_genv (symb2genv ge_s), args) phi0 ->
  exists x' : ext_spec_type (JE_spec _ (add_funspecs_rec ext_link Z Espec fs)) ef,
    JMeq (phi1, x) x'
    /\ forall z, ext_compat z (m_phi m) ->
          ext_spec_pre (add_funspecs_rec ext_link Z Espec fs) ef x' ge_s tys args z m.
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1 H2 Hargsty Hpre.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; revert x H2 Hpre; unfold funspec2pre; simpl.
if_tac [e|e].
intros x Hjoin Hp. exists (phi1,x). split; eauto.
unfold funsig2signature in e.
simpl in e.
split; eauto 6.

exfalso; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ eapply (in_map fst) in H1; apply H1. }
inversion H as [|? ? Ha Hb]; subst.
destruct (IHfs Hb H1 H2 Hargsty Hpre) as [x' H3].
clear -Ha Hin H1 H3; revert x' Ha Hin H1 H3.
destruct a; simpl; destruct f; simpl; destruct t; simpl; unfold funspec2pre; simpl.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; exfalso; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  exfalso; auto.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_post_void (ext_link: Strings.String.string -> ident)
  {Z Espec tret fs id sig cc A P Q NEP NEQ x ret m z ge_s} :
  let ef := EF_external id (mksignature (map argtype_of_type sig) Xvoid cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec (sig, tvoid) cc A P Q NEP NEQ)) fs ->
  ext_spec_post (add_funspecs_rec ext_link Z Espec fs) ef x ge_s tret ret z m ->
  exists (phi0 phi1 phi1' : rmap) (x': sigT (fun ts => dependent_type_functor_rec ts A mpred)),
       join phi0 phi1 (m_phi m)
    /\ necR phi1' phi1
    /\ JMeq x (phi1', x')
    /\ Q (projT1 x') (projT2 x') (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret) phi0.
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1 Hpost.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; revert x Hpost; unfold funspec2post; simpl.
if_tac [e|e].
intros x [phi0 [phi1 [Hjoin [Hq Hnec]]]].
exists phi0, phi1, (fst x), (snd x).
split; auto. split; auto. destruct x; simpl in *. split; destruct s; auto.
exfalso; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ apply (in_map fst) in H1; auto. }
inversion H as [|? ? Ha Hb]; subst.
clear -Ha Hin H1 Hb Hpost IHfs; revert x Ha Hin H1 Hb Hpost IHfs.
destruct a; simpl; destruct f; simpl; unfold funspec2post; simpl.
destruct t; simpl.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; exfalso; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  exfalso; auto.
* intros. apply IHfs; auto.
}
Qed.

Lemma add_funspecs_post (ext_link: Strings.String.string -> ident){Z Espec tret fs id sig cc A P Q NEP NEQ x ret m z ge_s} :
  let ef := EF_external id (typesig2signature sig cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec sig cc A P Q NEP NEQ)) fs ->
  ext_spec_post (add_funspecs_rec ext_link Z Espec fs) ef x ge_s tret ret z m ->
  exists (phi0 phi1 phi1' : rmap) (x': sigT (fun ts => dependent_type_functor_rec ts A mpred)),
       join phi0 phi1 (m_phi m)
    /\ necR phi1' phi1
    /\ JMeq x (phi1',x')
    /\ Q (projT1 x') (projT2 x') (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret) phi0.
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1 Hpost.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; revert x Hpost; unfold funspec2post; simpl.
destruct sig; simpl.
if_tac [e|e].
intros x [phi0 [phi1 [Hjoin [Hq Hnec]]]].
exists phi0, phi1, (fst x), (snd x).
split; auto. split; auto. destruct x; simpl in *. split; auto.
exfalso; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ apply (in_map fst) in H1; auto. }
inversion H as [|? ? Ha Hb]; subst.
clear -Ha Hin H1 Hb Hpost IHfs; revert x Ha Hin H1 Hb Hpost IHfs.
destruct a; simpl; destruct f; simpl; unfold funspec2post; simpl.
destruct t; simpl.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; exfalso; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  exfalso; auto.
* intros. apply IHfs; auto.
}
Qed.

Definition add_funspecs (Espec : OracleKind) (ext_link: Strings.String.string -> ident) (fs : funspecs) : OracleKind :=
  match Espec with
    | Build_OracleKind ty spec =>
      Build_OracleKind ty (add_funspecs_rec ext_link ty spec fs)
  end.

Lemma necR_jm_phi : forall jm jm', necR jm jm' -> necR (m_phi jm) (m_phi jm').
Proof.
  induction 1; auto.
  - apply age_jm_phi in H; constructor; auto.
  - eapply necR_trans; eauto.
Qed.

Section semax_ext.

Variable Espec : OracleKind.

Lemma semax_ext' (ext_link: Strings.String.string -> ident) id sig cc A P Q NEP NEQ (fs : funspecs) :
  let f := mk_funspec sig cc A P Q NEP NEQ in
  In (ext_link  id,f) fs ->
  funspecs_norepeat fs ->
  (forall n, semax_external (add_funspecs Espec ext_link fs)
               (EF_external id (typesig2signature sig cc)) _ P Q n).
Proof.
intros f Hin Hnorepeat.
unfold semax_external.
intros n ge Ts x n0 Hlater F ts args jm H ? jm' H2 Hext [Hargsty H3].
destruct H3 as [s [t [Hjoin [Hp Hf]]]].
destruct Espec.

assert (Hp'': P Ts x (filter_genv (symb2genv (genv_symb_injective ge)), args)
                    s).
{ generalize (all_funspecs_wf f) as Hwf2; intro.
  specialize (Hwf2 Ts x ge (symb2genv (genv_symb_injective ge)) args).
  spec Hwf2.
  rewrite symb2genv_ax; auto.
  apply Hwf2; auto. }

destruct (@add_funspecs_pre ext_link _ _ _ _ _ _ _ _ _ _ (existT _ Ts x) _ _ OK_spec ts (genv_symb_injective ge) s t Hnorepeat Hin Hjoin Hargsty Hp'')
  as [x' [Heq Hpre]].
simpl.
exists x'.
split.
intros z ?.
eapply nec_hereditary, Hpre; auto.
apply JE_pre_hered.

intros tret ret z' jm2 Hlev ? jm3 Hnec Hext' Hpost.
eapply add_funspecs_post in Hpost; eauto.
destruct Hpost as [phi0 [phi1 [phi1' [x'' [Hjoin' [Hnec' [Hjmeq' Hq']]]]]]].
exists phi0, phi1; split; auto.
assert (E : (t, existT _ Ts x) = (phi1',x'')) by (eapply JMeq_eq, JMeq_trans; eauto).
inv E.
split; auto.
unfold filter_genv, Genv.find_symbol in Hq'|-*.
rewrite symb2genv_ax in Hq'; auto.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma semax_ext (ext_link: Strings.String.string -> ident) id sig sig' cc A P Q NEP NEQ (fs : funspecs) :
  let f := mk_funspec sig cc A P Q NEP NEQ in
  In (ext_link id,f) fs ->
  funspecs_norepeat fs ->
  sig' = typesig2signature sig cc ->
  (forall n, semax_external (add_funspecs Espec ext_link fs) (EF_external id sig') _ P Q n).
Proof.
intros; subst.
eapply semax_ext'; eauto.
Qed.

End semax_ext.
