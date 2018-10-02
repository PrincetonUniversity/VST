(* this file is a version of veric/semax_ext.v that let external
specifications reason about the oracle. *)

Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.juicy_mem_ops.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import compcert.cfrontend.Clight.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_call.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.

(* NOTE.   ext_link: Strings.String.string -> ident
   represents the mapping from the _name_ of an external function
  (an ASCII string) to the [ident] that's used to represent it in this program module.
  That mapping can be computed from the prog_defs component of the Clight.program
  produced by clightgen.
*)

Section funspecsOracle2jspec.

Variable Z : Type.
Variable Espec : juicy_ext_spec Z.

Definition funspecOracle2pre (ext_link: Strings.String.string -> ident) (A : Type) (P : A -> Z -> environ -> mpred) (ids: list ident) (id: ident) sig (ef: external_function) x ge_s
           (tys : list typ) args z m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then (rmap * A)%type else ext_spec_type Espec ef) -> Prop)
  with
  | left _ =>
    fun x => exists phi0 phi1, join phi0 phi1 (m_phi m)
                       /\ P (snd x) z (make_ext_args (filter_genv (symb2genv ge_s)) ids args) phi0
                       /\ necR (fst x) phi1
  | right n => fun x' => ext_spec_pre Espec ef x' ge_s tys args z m
  end x.

Definition funspecOracle2post (ext_link: Strings.String.string -> ident) (A : Type) (Q : A -> Z -> environ -> mpred)
                        id sig ef x ge_s (tret : option typ) ret z m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then (rmap * A)%type else ext_spec_type Espec ef) -> Prop)
  with
  | left _ =>
    fun x => exists phi0 phi1, join phi0 phi1 (m_phi m)
                       /\ Q (snd x) z (make_ext_rval (filter_genv (symb2genv ge_s)) ret) phi0
                       /\ necR (fst x) phi1
  | right n => fun x' => ext_spec_post Espec ef x' ge_s tret ret z m
  end x.

Inductive funspecOracle : Type :=
  mk_funspecOracle : funsig -> calling_convention -> forall A : Type,
      (A -> Z -> environ -> mpred) ->
      (A -> Z -> environ -> mpred) -> funspecOracle.

Definition funspecOracle2extspec (ext_link: Strings.String.string -> ident) (f : ident * funspecOracle)
  : external_specification juicy_mem external_function Z :=
  match f with
    | (id, mk_funspecOracle ((params, sigret) as fsig) cc A P Q) =>
      let sig := funsig2signature fsig cc in
      Build_external_specification juicy_mem external_function Z
        (fun ef => if oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) then (rmap * A)%type else ext_spec_type Espec ef)
        (funspecOracle2pre ext_link A P (fst (split params)) id sig)
        (funspecOracle2post ext_link A Q id sig)
        (fun rv z m => False)
  end.

Local Open Scope pred.

Definition wf_funspecOracle (f : funspecOracle) :=
  match f with
    | mk_funspecOracle sig cc A P Q =>
        forall a (ge ge': genv) n args z,
          Genv.genv_symb ge = Genv.genv_symb ge' ->
          P a z (make_ext_args (filter_genv ge) n args) |-- P a z (make_ext_args (filter_genv ge') n args)
  end.

Lemma make_ext_args_symb (ge ge' : genv)
      (H: Genv.genv_symb ge = Genv.genv_symb ge') n args :
  make_ext_args (filter_genv ge) n args = make_ext_args (filter_genv ge') n args.
Proof.
revert ge ge' n H; induction args.
* simpl; unfold filter_genv, Genv.find_symbol. intros ? ? ? ->; auto.
* intros ge ge' n H. simpl. destruct n; auto.
  erewrite IHargs; eauto.
  erewrite IHargs; eauto.
Qed.

Lemma all_funspecsOracle_wf f : wf_funspecOracle f.
Proof.
destruct f; simpl; intros a ge ge' n args z H.
erewrite make_ext_args_symb; eauto.
Qed.

Program Definition funspecOracle2jspec (ext_link: Strings.String.string -> ident) f : juicy_ext_spec Z :=
  Build_juicy_ext_spec _ (funspecOracle2extspec ext_link f) _ _ _.
Next Obligation.
destruct f; simpl; unfold funspecOracle2pre, pureat; simpl; destruct f; simpl;
  destruct f; simpl; intros e t0 ge_s typs args z.
if_tac [e0|e0].
* destruct e; try discriminate; injection e0 as E; subst i sg; intros a a' Hage.
intros [phi0 [phi1 [Hjoin [Hx Hy]]]].
apply age1_juicy_mem_unpack in Hage.
destruct Hage as [Hage Hdry].
destruct (age1_join2 phi0 Hjoin Hage) as [x' [y' [Hjoin' [Hage' H]]]].
exists x', y'; split; auto.
destruct m. split. eapply h; eauto.
apply (necR_trans (fst t0) phi1 y'); auto.
unfold necR. constructor; auto.
* intros ? ?; auto.
destruct Espec; simpl; apply JE_pre_hered.
Qed.
Next Obligation.
destruct f; simpl; unfold funspecOracle2post, pureat; simpl; destruct f; simpl;
  destruct f; simpl. intros e t0 ge_s tret rv z.
if_tac [e0|e0].
* destruct e; try discriminate; injection e0 as E; subst i sg; intros a a' Hage; destruct m0; simpl.
intros [phi0 [phi1 [Hjoin [Hx Hy]]]].
apply age1_juicy_mem_unpack in Hage.
destruct Hage as [Hage Hdry].
destruct (age1_join2 phi0 Hjoin Hage) as [x' [y' [Hjoin' [Hage' H]]]].
exists x', y'; split; auto.
split; [solve[eapply h; eauto]|].
apply (necR_trans (fst t0) phi1 y'); auto.
unfold necR. constructor; auto.
* intros ? ?; auto.
destruct Espec; simpl; apply JE_post_hered.
Qed.
Next Obligation.
intros ? ? ? ?; destruct f; destruct f; destruct f; simpl.
intros a' Hage; auto.
Qed.

End funspecsOracle2jspec.
Import String.

Fixpoint add_funspecsOracle_rec (ext_link: string -> ident) Z (Espec : juicy_ext_spec Z) (fs : list (ident * funspecOracle Z)) :=
  match fs with
    | nil => Espec
    | cons (i,f) fs' => funspecOracle2jspec Z (add_funspecsOracle_rec ext_link Z Espec fs') ext_link (i,f)
  end.

Require Import Coq.Logic.JMeq.

Lemma add_funspecs_pre  (ext_link: Strings.String.string -> ident)
              {Z fs id sig cc A P Q x args m} Espec tys ge_s phi0 phi1 z :
  let ef := EF_external id (funsig2signature sig cc) in
  list_norepet (map fst fs) ->
  In (ext_link id, (mk_funspecOracle Z sig cc A P Q)) fs ->
  join phi0 phi1 (m_phi m) ->
  P x z (make_ext_args (filter_genv (symb2genv ge_s)) (fst (split (fst sig))) args) phi0 ->
  exists x' : ext_spec_type (JE_spec _ (add_funspecsOracle_rec ext_link Z Espec fs)) ef,
    JMeq (phi1, x) x'
    /\ ext_spec_pre (add_funspecsOracle_rec ext_link Z Espec fs) ef x' ge_s tys args z m.
Proof.
induction fs; [intros; elimtype False; auto|]; intros ef H H1 H2 Hpre.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; revert x H2 Hpre; unfold funspecOracle2pre; simpl.
destruct sig; simpl.
if_tac [e0|e0].
rewrite fst_split.
intros x Hjoin Hp. exists (phi1,x). split; eauto.
elimtype False; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ eapply (in_map fst) in H1; apply H1. }
inversion H as [|? ? Ha Hb]; subst.
destruct (IHfs Hb H1 H2 Hpre) as [x' H3].
clear -Ha Hin H1 H3; revert x' Ha Hin H1 H3.
destruct a; simpl; destruct f; simpl; destruct f; simpl; unfold funspecOracle2pre; simpl.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; elimtype False; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  elimtype False; auto.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_post (ext_link: Strings.String.string -> ident)
      {Z Espec tret fs id sig cc A}
      {P Q : A -> Z -> environ -> mpred} {x ret z m ge_s} :
  let ef := EF_external id (funsig2signature sig cc) in
  list_norepet (map fst fs) ->
  In (ext_link id, (mk_funspecOracle Z sig cc A P Q)) fs ->
  In (ext_link id) (map fst fs) ->
  ext_spec_post (add_funspecsOracle_rec ext_link Z Espec fs) ef x ge_s tret ret z m ->
  exists (phi0 phi1 phi1' : rmap) (x' : A),
       join phi0 phi1 (m_phi m)
    /\ necR phi1' phi1
    /\ JMeq x (phi1', x')
    /\ Q x' z (make_ext_rval (filter_genv (symb2genv ge_s)) ret) phi0.
Proof.
induction fs; [intros; elimtype False; auto|]; intros ef H H1 Hid Hpost.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; revert x Hpost; unfold funspecOracle2post; simpl.
destruct sig; simpl.
if_tac [e0|e0].
intros x [phi0 [phi1 [Hjoin [Hq Hnec]]]].
exists phi0, phi1, (fst x), (snd x).
split; auto. split; auto. destruct x; simpl in *. split; auto.
elimtype False; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ apply (in_map fst) in H1; auto. }
inversion H as [|? ? Ha Hb]; subst.
clear -Ha Hin H1 Hb Hpost IHfs; revert x Ha Hin H1 Hb Hpost IHfs.
destruct a; simpl; destruct f; simpl; unfold funspecOracle2post; simpl.
destruct f; simpl.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; elimtype False; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  elimtype False; auto.
* intros. apply IHfs; auto.
}
Qed.

(* for now, giving up on the previously convenient add_funspecs because it is too much dependent now
Definition add_funspecs (Espec : OracleKind) (ext_link: string -> ident) (fs : list (ident * funspecOracle Espec.(@OK_ty))) : OracleKind :=
  match Espec
        as e
        return
        match e with
          Build_OracleKind ty _ => list (ident * funspecOracle ty) -> OracleKind
        end
  with
  | Build_OracleKind ty spec =>
    fun fs => Build_OracleKind ty (add_funspecsOracle_rec ext_link ty spec fs)
  end fs.
*)

(*! Adapting semax_external to a judgment mentioning oracles *)

Definition semax_external_oracle (Espec: OracleKind) (ids: list ident) ef (A: Type) (P Q: A -> Espec.(@OK_ty) -> environ -> pred rmap):
        pred nat :=
 ALL gx: genv, ALL x: A,
 |>  ALL F: pred rmap, ALL ts: list typ, ALL args: list val, ALL z : Espec.(@OK_ty),
   juicy_mem_op (P x z (make_ext_args (filter_genv gx) ids args) * F) >=>
   EX x': ext_spec_type OK_spec ef,
    ext_spec_pre' Espec ef x' (genv_symb_injective gx) ts args z &&
     ! ALL tret: option typ, ALL ret: option val, ALL z': OK_ty,
      ext_spec_post' Espec ef x' (genv_symb_injective gx) tret ret z' >=>
          juicy_mem_op (Q x z' (make_ext_rval (filter_genv gx) ret) * F).

Section semax_ext_oracle.

Variable Espec : OracleKind.
Local Notation ty := Espec.(@OK_ty).
Local Notation spec := Espec.(@OK_spec).

Lemma semax_ext'_oracle (ext_link: Strings.String.string -> ident) id sig cc A P Q (fs : list (ident * funspecOracle ty)) :
  let f := mk_funspecOracle ty sig cc A P Q in
  In (ext_link id, f) fs ->
  list_norepet (map fst fs) ->
  (forall n, semax_external_oracle
          (Build_OracleKind _ (add_funspecsOracle_rec ext_link ty spec fs))
          (fst (split (fst sig)))
          (EF_external id (funsig2signature sig cc))
          _ P Q n).
Proof.
intros f Hin Hnorepeat.
unfold semax_external.
intros n ge x n0 Hlater F ts args z jm H jm' H2 H3.
destruct H3 as [s [t [Hjoin [Hp Hf]]]].

assert (Hp'': P x z (make_ext_args (filter_genv (symb2genv (genv_symb_injective ge)))
                                 (fst (split (fst sig))) args) s).
{ generalize (all_funspecsOracle_wf ty f) as Hwf2; intro.
  unfold wf_funspecOracle in Hwf2.
  specialize (Hwf2 x ge (symb2genv (genv_symb_injective ge)) (fst (split (fst sig))) args z).
  spec Hwf2.
  rewrite symb2genv_ax; auto.
  apply Hwf2; auto. }
destruct (@add_funspecs_pre
            ext_link ty _ _ _ cc _ _ _ _ _ _ OK_spec ts (genv_symb_injective ge) s t z Hnorepeat Hin Hjoin Hp'')
  as [x' [Heq Hpre]].
simpl.
exists x'.
split; [solve[apply Hpre]|].
intros tret ret z' jm2 Hlev jm3 Hnec Hpost.

eapply add_funspecs_post in Hpost; eauto. 2:eapply (in_map fst _ _ Hin).
destruct Hpost as [phi0 [phi1 [phi1' [x'' [Hjoin' [Hnec' [Hjmeq' Hq']]]]]]].
exists phi0, phi1; split; auto.
assert (E : (t, x) = (phi1', x'')) by (eapply JMeq_eq, JMeq_trans; eauto).
inv E.
split; auto.
unfold filter_genv, Genv.find_symbol in Hq'|-*.
rewrite symb2genv_ax in Hq'; auto.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma semax_ext_oracle (ext_link: Strings.String.string -> ident) id ids sig sig' cc A P Q (fs : list (ident * funspecOracle ty)) :
  let f := mk_funspecOracle ty sig cc A P Q in
  In (ext_link id,f) fs ->
  list_norepet (map fst fs) ->
  ids = fst (split (fst sig)) ->
  sig' = funsig2signature sig cc ->
  (forall n, semax_external_oracle
          (Build_OracleKind _ (add_funspecsOracle_rec ext_link ty spec fs))
          ids
          (EF_external id sig')
          _ P Q n).
Proof.
intros; subst.
apply semax_ext'_oracle; auto.
Qed.

End semax_ext_oracle.
