Require Import Coq.Logic.JMeq.
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
(*Require Import VST.veric.juicy_mem_ops.*)
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_call.
Require Import VST.veric.external_state.
Require Import VST.veric.res_predicates.
Require Import compcert.cfrontend.Clight.
Require Import compcert.export.Clightdefs.

Definition funsig2signature (s : funsig) cc : signature :=
  mksignature (map typ_of_type (map snd (fst s))) (rettype_of_type (snd s)) cc.

Definition typesig2signature (s : typesig) cc : signature :=
  mksignature (map typ_of_type (fst s)) (rettype_of_type (snd s)) cc.

(* NOTE.   ext_link: Strings.String.string -> ident
   represents the mapping from the _name_ of an external function
  (an ASCII string) to the [ident] that's used to represent it in this program module.
  That mapping can be computed from the prog_defs component of the Clight.program
  produced by clightgen.
*)

Definition ef_id_sig (ext_link: Strings.String.string -> ident) ef :=
  match ef with EF_external id sig => Some (ext_link id, sig) | _ => None end.

Section mpred.

Context (Z : Type) `{!heapGS Σ} `{!externalGS Z Σ}.

Section funspecs2jspec.

Variable Espec : juicy_ext_spec(Σ := Σ) Z.

Definition symb2genv_upper_bound (s: Maps.PTree.t block) : block :=
  Pos.succ (fold_right Pos.max  1%positive (map snd (Maps.PTree.elements s))).

Definition symb2genv (ge_s: injective_PTree block) : genv.
    refine (Build_genv (@Genv.mkgenv _ _ nil (proj1_sig ge_s) (Maps.PTree.empty _) (symb2genv_upper_bound (proj1_sig ge_s)) _ _ _) (Maps.PTree.empty _)).
*
intros.
unfold Coqlib.Plt.
apply Pos.lt_le_trans with (Pos.succ b).
apply Pos.lt_succ_r.
apply Pos.le_refl.
unfold symb2genv_upper_bound.
apply -> Pos.succ_le_mono.
apply Maps.PTree.elements_correct in H.
revert H.
induction (Maps.PTree.elements (proj1_sig ge_s)); intros. inv H.
destruct H. subst. simpl.
apply Pos.le_max_l.
simpl.
eapply Pos.le_trans; [  | apply Pos.le_max_r].
auto.
*
intros.
rewrite Maps.PTree.gempty in H. inv H.
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



Definition funspec2pre (ext_link: Strings.String.string -> ident) (A : Type)
  (P: A -> argsEnviron -> mpred)
  (id: ident) (sig : signature) (ef: external_function) x (ge_s: injective_PTree block)
           (tys : list typ) args (z : Z) m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then A else ext_spec_type Espec ef) -> Prop)
  with
    | left _ => fun x' => ouPred_holds (⌜Val.has_type_list args (sig_args (ef_sig ef))⌝ ∧
        (∃ md, state_interp md z) ∗ P x' (filter_genv (symb2genv ge_s), args)) (level m) (m_phi m)
    | right n => fun x' => ext_spec_pre Espec ef x' ge_s tys args z m
  end x.

Definition funspec2post (ext_link: Strings.String.string -> ident) (A : Type)
  (Q: A -> environ -> mpred)
  id sig ef x ge_s (tret : rettype) ret (z : Z) m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then A else ext_spec_type Espec ef) -> Prop)
  with
    | left _ => fun x' => ouPred_holds ((∃ md, state_interp md z) ∗ Q x' (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret)) (level m) (m_phi m)
    | right n => fun x' => ext_spec_post Espec ef x' ge_s tret ret z m
  end x.

Definition funspec2extspec (ext_link: Strings.String.string -> ident) (f : (ident*funspec))
  : external_specification juicy_mem external_function Z :=
  match f with
    | (id, mk_funspec ((params, sigret) as fsig) cc A P Q) =>
      let sig := typesig2signature fsig cc in
      Build_external_specification juicy_mem external_function Z
        (fun ef => if oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) then A else ext_spec_type Espec ef)
        (funspec2pre ext_link A P id sig)
        (funspec2post ext_link A Q id sig)
        (fun rv z m => True%type)
  end.

Definition wf_funspec (f : @funspec Σ) :=
  match f with
    | mk_funspec sig cc A P Q =>
        forall a (ge ge': genv) args,
          Genv.genv_symb ge = Genv.genv_symb ge' ->
          P a (filter_genv ge, args) 
         ⊢ P a (filter_genv ge', args)
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
destruct f; simpl; intros a ge ge' args H.
erewrite make_ext_args_filtergenv; eauto.
Qed.


Program Definition funspec2jspec (ext_link: Strings.String.string -> ident) f : juicy_ext_spec Z :=
  Build_juicy_ext_spec _ (funspec2extspec ext_link f) _ _ _.
Next Obligation.
destruct f; simpl; unfold funspec2pre; simpl; destruct f as [(?, ?)]; simpl; intros.
if_tac [e0|e0].
* destruct e; try discriminate; injection e0 as E; subst i sg; intros m phi.
apply ouPred_mono.
* intros ? ?; auto.
destruct Espec; simpl; apply JE_pre_mono.
Qed.
Next Obligation.
destruct f; simpl; unfold funspec2post; simpl; destruct f as [(?, ?)]; simpl; intros.
if_tac [e0|e0].
* destruct e; try discriminate; injection e0 as E; subst i sg; intros m phi.
apply ouPred_mono.
* intros ? ?; auto.
destruct Espec; simpl; apply JE_post_mono.
Qed.
Next Obligation.
intros ? ? ? ?; destruct f; destruct f as [(?, ?)]; simpl.
intros ?; auto.
Qed.

End funspecs2jspec.

Definition funspecs_norepeat (fs : @funspecs Σ) := list_norepet (map fst fs).

Fixpoint add_funspecs_rec (ext_link: Strings.String.string -> ident) (Espec : juicy_ext_spec Z) (fs : funspecs) :=
  match fs with
    | nil => Espec
    | cons (i,f) fs' => funspec2jspec (add_funspecs_rec ext_link Espec fs') ext_link (i,f)
  end.

Lemma add_funspecs_pre  (ext_link: Strings.String.string -> ident)
              {fs id sig cc A P Q}
              {x: A} {args} Espec tys ge_s :
  let ef := EF_external id (typesig2signature sig cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec sig cc A P Q)) fs ->
  forall z, ⌜Val.has_type_list args (sig_args (ef_sig ef))⌝ ∧
        (∃ md, state_interp md z) ∗ P x (filter_genv (symb2genv ge_s), args) ⊢
  ∃ x' : ext_spec_type (JE_spec _ (add_funspecs_rec ext_link Espec fs)) ef,
    ⌜JMeq x x'⌝ ∧ ext_mpred_pre Z (add_funspecs_rec ext_link Espec fs) ef x' ge_s tys args z.
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1 z.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; unfold funspec2jspec, ext_mpred_pre; simpl.
ouPred.unseal.
destruct sig; unfold funspec2pre; simpl.
split => ??? /=.
rewrite /ouPred_exist_def /mpred_of /= /ouPred_holds /= /ouPred_holds.
if_tac; simpl.
ouPred.unseal; eauto.
exfalso; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ eapply (in_map fst) in H1; apply H1. }
inversion H as [|? ? Ha Hb]; subst.
rewrite IHfs //.
ouPred.unseal.
split => ???.
intros (x' & Hpre).
clear -Ha Hin H1 Hpre; revert Ha Hin H1 Hpre.
unfold funspec2jspec, ext_mpred_pre; simpl.
destruct a; simpl; destruct f as [(?, ?)]; simpl; unfold funspec2pre; simpl.
rewrite /ouPred_exist_def /mpred_of /= /ouPred_holds /= /ouPred_holds.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; exfalso; auto]|].
  done.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_pre_void  (ext_link: Strings.String.string -> ident)
              {fs id sig cc A P Q}
              {x: A}
              {args} Espec tys ge_s :
  let ef := EF_external id (mksignature (map typ_of_type sig) Tvoid cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec (sig, tvoid) cc A P Q)) fs ->
  forall z, ⌜Val.has_type_list args (sig_args (ef_sig ef))⌝ ∧
        (∃ md, state_interp md z) ∗ P x (filter_genv (symb2genv ge_s), args) ⊢
  ∃ x' : ext_spec_type (JE_spec _ (add_funspecs_rec ext_link Espec fs)) ef,
    ⌜JMeq x x'⌝ ∧ ext_mpred_pre Z (add_funspecs_rec ext_link Espec fs) ef x' ge_s tys args z.
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1 z.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; unfold funspec2jspec, ext_mpred_pre; simpl.
ouPred.unseal.
unfold funspec2pre; simpl.
split => ??? /=.
rewrite /ouPred_exist_def /mpred_of /= /ouPred_holds /= /ouPred_holds.
if_tac [e|e].
ouPred.unseal; eauto.
exfalso; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ eapply (in_map fst) in H1; apply H1. }
inversion H as [|? ? Ha Hb]; subst.
rewrite IHfs //.
ouPred.unseal.
split => ???.
intros (x' & Hpre).
clear -Ha Hin H1 Hpre; revert Ha Hin H1 Hpre.
unfold funspec2jspec, ext_mpred_pre; simpl.
destruct a; simpl; destruct f as [(?, ?)]; simpl; unfold funspec2pre; simpl.
rewrite /ouPred_exist_def /mpred_of /= /ouPred_holds /= /ouPred_holds.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; exfalso; auto]|].
  done.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_post_void (ext_link: Strings.String.string -> ident)
  {Espec tret fs id sig cc A P Q x ret z ge_s} :
  let ef := EF_external id (mksignature (map typ_of_type sig) Tvoid cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec (sig, tvoid) cc A P Q)) fs ->
  ext_mpred_post Z (add_funspecs_rec ext_link Espec fs) ef x ge_s tret ret z ⊢
  ∃ (x': A), ⌜JMeq x x'⌝ ∧ (∃ md, state_interp md z) ∗ Q x' (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret).
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
rewrite /ext_mpred_post /= /funspec2jspec /=.
ouPred.unseal.
unfold funspec2post; simpl.
split => ??? /=.
rewrite /mpred_of /= /ouPred_holds /= /ouPred_holds.
if_tac [e|e].
ouPred.unseal.
intros; exists x; done.
exfalso; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ apply (in_map fst) in H1; auto. }
inversion H as [|? ? Ha Hb]; subst.
rewrite /ext_mpred_post /= /funspec2jspec /=.
destruct a; simpl; destruct f as [(?, ?)]; simpl.
rewrite /funspec2post /mpred_of /=.
split => ?? H2 /=.
clear - IHfs Ha Hb Hin H1 H2; revert x IHfs Ha Hin H1.
rewrite /ouPred_holds.
ouPred.unseal.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; exfalso; auto]|].
  done.
* intros ????? Hpre. apply IHfs in Hpre; auto.
}
Qed.

Lemma add_funspecs_post (ext_link: Strings.String.string -> ident) {Espec tret fs id sig cc A P Q x ret z ge_s} :
  let ef := EF_external id (typesig2signature sig cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec sig cc A P Q)) fs ->
  ext_mpred_post Z (add_funspecs_rec ext_link Espec fs) ef x ge_s tret ret z ⊢
  ∃ (x': A), ⌜JMeq x x'⌝ ∧ (∃ md, state_interp md z) ∗ Q x' (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret).
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
destruct sig; simpl.
rewrite /ext_mpred_post /= /funspec2jspec /=.
ouPred.unseal.
clear IHfs H; revert x; unfold funspec2post; simpl.
split => ??? /=.
rewrite /mpred_of /= /ouPred_holds /= /ouPred_holds.
if_tac [e|e].
ouPred.unseal.
intros; exists x; done.
exfalso; auto.
}

{
assert (Hin: In (ext_link id) (map fst fs)).
{ apply (in_map fst) in H1; auto. }
inversion H as [|? ? Ha Hb]; subst.
clear -Ha Hin H1 Hb IHfs; revert x Ha Hin H1 Hb IHfs.
rewrite /ext_mpred_post /= /funspec2jspec /=.
destruct a; simpl; destruct f as [(?, ?)]; simpl; unfold funspec2post; simpl.
rewrite /funspec2post /mpred_of /=.
split => ?? H2 /=.
clear - IHfs Ha Hb Hin H1 H2; revert x IHfs Ha Hin H1.
rewrite /ouPred_holds.
if_tac [e|e].
* injection e as E; subst i; destruct fs; [solve[simpl; intros; exfalso; auto]|].
  done.
* intros. apply IHfs in H; auto.
}
Qed.

End mpred.

(* Maybe skip this step, since we have to fix the oracle type with externalGS.
Definition add_funspecs (Espec : OracleKind) (ext_link: Strings.String.string -> ident) (fs : funspecs) : OracleKind :=
  match Espec with
    | Build_OracleKind ty spec =>
      Build_OracleKind ty (add_funspecs_rec ty ext_link spec fs)
  end.*)

Section semax_ext.

Context `{!heapGS Σ}.
Variable Espec : @OracleKind Σ.
Context `{!externalGS OK_ty Σ}.

Lemma semax_ext' E (ext_link: Strings.String.string -> ident) id sig cc A P Q (fs : funspecs) :
  let f := mk_funspec sig cc A P Q in
  In (ext_link  id,f) fs ->
  funspecs_norepeat fs ->
  ⊢semax_external {| OK_ty := OK_ty; OK_spec := add_funspecs_rec OK_ty ext_link OK_spec fs |}
               E (EF_external id (typesig2signature sig cc)) _ P Q.
Proof.
intros f Hin Hnorepeat.
unfold semax_external.
iIntros (ge ????) "!> !> (%Hargsty & Hp & Hf)".
iIntros "!>" (??) "Hs".
iDestruct (add_funspecs_pre _ _ _ _ (genv_symb_injective ge) with "[Hp Hs]") as (x' Heq) "?".
{ iSplit; first done.
  iFrame; eauto. }
iExists x'; iFrame.
iIntros (???) "Hpost".
iDestruct (add_funspecs_post _ _ (A := A) with "Hpost") as (x'' Heq') "((% & ?) & ?)".
iExists md; iFrame.
assert (x = x'') as -> by (eapply JMeq_eq, JMeq_trans; eauto).
rewrite /filter_genv /Genv.find_symbol symb2genv_ax //.
Qed.

Lemma semax_ext E (ext_link: Strings.String.string -> ident) id sig sig' cc A P Q (fs : funspecs) :
  let f := mk_funspec sig cc A P Q in
  In (ext_link id,f) fs ->
  funspecs_norepeat fs ->
  sig' = typesig2signature sig cc ->
  ⊢semax_external {| OK_ty := OK_ty; OK_spec := add_funspecs_rec OK_ty ext_link OK_spec fs |} E (EF_external id sig') _ P Q .
Proof.
intros; subst.
eapply semax_ext'; eauto.
Qed.

End semax_ext.
