Require Import Coq.Logic.JMeq.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
(*Require Import VST.veric.juicy_mem_ops.*)
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_call.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.external_state.
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
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

Context (Z : Type) `{!VSTGS Z Σ}.

Section funspecs2jspec.

Variable Espec : ext_spec Z.

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

Definition funspec2pre' (A : TypeTree) (P: dtfr (ArgsTT A)) (x : (nat * iResUR Σ * ofe_car (dtfr A))%type) (ge_s: injective_PTree block) sig args z m :=
  let '(n, phi, x') := x in ✓{n} phi /\ Val.has_type_list args sig /\
    ouPred_holds (state_interp m z ∗ P x' (filter_genv (symb2genv ge_s), args)) n phi.

Definition funspec2pre (ext_link: Strings.String.string -> ident) (A : TypeTree)
  (P: dtfr (ArgsTT A))
  (id: ident) (sig : signature) (ef: external_function) x (ge_s: injective_PTree block)
           (tys : list typ) args (z : Z) m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then (nat * iResUR Σ * ofe_car (dtfr A))%type else ext_spec_type Espec ef) -> Prop)
  with
    | left _ => fun x => funspec2pre' A P x ge_s (sig_args (ef_sig ef)) args z m
    | right n => fun x' => ext_spec_pre Espec ef x' ge_s tys args z m
  end x.

Definition funspec2post' (A : TypeTree) (Q: dtfr (AssertTT A)) (x : (nat * iResUR Σ * ofe_car (dtfr A))%type) (ge_s: injective_PTree block) tret ret z m :=
  let '(n, phi, x') := x in ouPred_holds (|==> state_interp m z ∗ Q x' (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret)) n phi.

Definition funspec2post (ext_link: Strings.String.string -> ident) (A : TypeTree)
  (Q: dtfr (AssertTT A))
  id sig ef x ge_s (tret : rettype) ret (z : Z) m : Prop :=
  match oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) as s
  return ((if s then (nat * iResUR Σ * ofe_car (dtfr A))%type else ext_spec_type Espec ef) -> Prop)
  with
    | left _ => fun x => funspec2post' A Q x ge_s tret ret z m
    | right n => fun x' => ext_spec_post Espec ef x' ge_s tret ret z m
  end x.

Definition funspec2extspec (ext_link: Strings.String.string -> ident) (f : (ident*funspec))
  : external_specification mem external_function Z :=
  match f with
    | (id, mk_funspec ((params, sigret) as fsig) cc A E P Q) =>
      let sig := typesig2signature fsig cc in
      Build_external_specification mem external_function Z
        (fun ef => if oi_eq_dec (Some (id, sig)) (ef_id_sig ext_link ef) then (nat * iResUR Σ * dtfr A)%type else ext_spec_type Espec ef)
        (funspec2pre ext_link A P id sig)
        (funspec2post ext_link A Q id sig)
        (fun rv z m => True%type)
  end.

Definition wf_funspec (f : @funspec Σ) :=
  match f with
    | mk_funspec sig cc E A P Q =>
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

#[local] Obligation Tactic := idtac.

Definition funspec2jspec (ext_link: Strings.String.string -> ident) f : ext_spec Z :=
  funspec2extspec ext_link f.

End funspecs2jspec.

Definition funspecs_norepeat (fs : @funspecs Σ) := list_norepet (map fst fs).

Fixpoint add_funspecs_rec (ext_link: Strings.String.string -> ident) (Espec : ext_spec Z) (fs : funspecs) :=
  match fs with
    | nil => Espec
    | cons (i,f) fs' => funspec2jspec (add_funspecs_rec ext_link Espec fs') ext_link (i,f)
  end.

(*Program Definition has_witness {A B} (x : A) (x' : B) : mpred := {| ouPred_holds := λ n phi, exists n' phi',
  n ≤ n' /\ phi' ≼ₒ{n} phi /\ JMeq (n', phi', x) x' |}.
Next Obligation.
Proof.
  intros ???????? (n' & phi' & ? & ? & ?) ??; simpl.
  exists n', phi'; split3; last done.
  - by etrans.
  - eapply ora_orderN_le; last done.
    by etrans.
Qed.*)

Lemma add_funspecs_pre (ext_link: Strings.String.string -> ident)
              {fs id sig cc A E P Q}
              Espec tys ge_s {x} {args} m z :
  let ef := EF_external id (typesig2signature sig cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec sig cc A E P Q)) fs -> ∃ H : ext_spec_type (add_funspecs_rec ext_link Espec fs) ef = (nat * iResUR Σ * dtfr A)%type,
  ext_spec_pre (add_funspecs_rec ext_link Espec fs) ef x ge_s tys args z m =
  funspec2pre' A P (eq_rect _ Datatypes.id x _ H) ge_s (sig_args (ef_sig ef)) args z m.
Proof.
  induction fs; [intros; exfalso; auto|]; intros ?? [-> | H1]; simpl in *.
  - clear IHfs H; unfold funspec2jspec; simpl.
    destruct sig; unfold funspec2pre, funspec2post; simpl in *.
    revert x; if_tac; simpl; last done.
    intros; exists eq_refl; tauto.
  - assert (Hin: In (ext_link id) (map fst fs)).
    { eapply (in_map fst) in H1; apply H1. }
    inversion H as [|? ? Ha Hb]; subst.
    destruct a; simpl; destruct f as [(?, ?)]; simpl; unfold funspec2pre, funspec2post; simpl.
    revert x; simpl; if_tac [e | e].
    { injection e as ?; subst i; destruct fs; [solve [simpl; intros; exfalso; auto]|]; done. }
    intros; apply IHfs; auto.
Qed.

Lemma add_funspecs_post (ext_link: Strings.String.string -> ident)
              {fs id sig cc A E P Q}
              Espec ty ge_s {x} {v} m z :
  let ef := EF_external id (typesig2signature sig cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec sig cc A E P Q)) fs -> ∃ H : ext_spec_type (add_funspecs_rec ext_link Espec fs) ef = (nat * iResUR Σ * dtfr A)%type,
  ext_spec_post (add_funspecs_rec ext_link Espec fs) ef x ge_s ty v z m =
  funspec2post' A Q (eq_rect _ Datatypes.id x _ H) ge_s ty v z m.
Proof.
  induction fs; [intros; exfalso; auto|]; intros ?? [-> | H1]; simpl in *.
  - clear IHfs H; unfold funspec2jspec; simpl.
    destruct sig; unfold funspec2pre, funspec2post; simpl in *.
    revert x; if_tac; simpl; last done.
    intros; exists eq_refl; tauto.
  - assert (Hin: In (ext_link id) (map fst fs)).
    { eapply (in_map fst) in H1; apply H1. }
    inversion H as [|? ? Ha Hb]; subst.
    destruct a; simpl; destruct f as [(?, ?)]; simpl; unfold funspec2pre, funspec2post; simpl.
    revert x; simpl; if_tac [e | e].
    { injection e as ?; subst i; destruct fs; [solve [simpl; intros; exfalso; auto]|]; done. }
    intros; apply IHfs; auto.
Qed.

Lemma add_funspecs_prepost (ext_link: Strings.String.string -> ident)
              {fs id sig cc A E P Q}
              {x: dtfr A} {args} Espec tys ge_s :
  let ef := EF_external id (typesig2signature sig cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec sig cc A E P Q)) fs ->
  forall md z, ⌜Val.has_type_list args (sig_args (ef_sig ef))⌝ ∧
        state_interp md z ∗ P x (filter_genv (symb2genv ge_s), args) ⊢
  ∃ x' : ext_spec_type (add_funspecs_rec ext_link Espec fs) ef,
    ⌜ext_spec_pre (add_funspecs_rec ext_link Espec fs) ef x' ge_s tys args z md⌝ ∧
    (∀ (tret : rettype) (ret : option val) (m' : Memory.mem) z',
       ⌜ext_spec_post (add_funspecs_rec ext_link Espec fs) ef x' ge_s tret ret z' m'⌝
       → |==> state_interp m' z' ∗ ofe_mor_car _ _ Q x (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret)).
Proof.
induction fs; [intros; exfalso; auto|]; intros ef H H1 md z.
destruct H1 as [H1|H1].

{
subst a; simpl in *.
clear IHfs H; unfold funspec2jspec; simpl.
destruct sig; unfold funspec2pre, funspec2post; simpl.
if_tac; simpl; last done.
unfold funspec2pre', funspec2post'; ouPred.unseal.
split => n phi ??.
exists (n, phi, x); split; first done.
intros ????????? Hpost.
rewrite {1}/ouPred_holds /= in Hpost.
eapply ouPred_mono in Hpost; [|done..].
eapply ouPred_mono; eauto.
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
unfold funspec2jspec; simpl.
destruct a; simpl; destruct f as [(?, ?)]; simpl; unfold funspec2pre, funspec2post; simpl.
if_tac [e|e].
* injection e as ?; subst i; destruct fs; [solve [simpl; intros; exfalso; auto]|].
  done.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_prepost_void  (ext_link: Strings.String.string -> ident)
              {fs id sig cc A E P Q}
              {x: dtfr A}
              {args} Espec tys ge_s :
  let ef := EF_external id (mksignature (map typ_of_type sig) Tvoid cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec (sig, tvoid) cc A E P Q)) fs ->
  forall md z, ⌜Val.has_type_list args (sig_args (ef_sig ef))⌝ ∧
        state_interp md z ∗ P x (filter_genv (symb2genv ge_s), args) ⊢
  ∃ x' : ext_spec_type (add_funspecs_rec ext_link Espec fs) ef,
    ⌜ext_spec_pre (add_funspecs_rec ext_link Espec fs) ef x' ge_s tys args z md⌝ ∧
    (∀ (tret : rettype) (ret : option val) (m' : Memory.mem) z',
       ⌜ext_spec_post (add_funspecs_rec ext_link Espec fs) ef x' ge_s tret ret z' m'⌝
       → |==> state_interp m' z' ∗ ofe_mor_car _ _ Q x (make_ext_rval (filter_genv (symb2genv ge_s)) tret ret)).
Proof.
  apply add_funspecs_prepost.
Qed.

End mpred.

(* Maybe skip this step, since we have to fix the oracle type with externalGS.
Definition add_funspecs (Espec : OracleKind) (ext_link: Strings.String.string -> ident) (fs : funspecs) : OracleKind :=
  match Espec with
    | Build_OracleKind ty spec =>
      Build_OracleKind ty (add_funspecs_rec ty ext_link spec fs)
  end.*)

Section semax_ext.

Context {Z : Type} `{!VSTGS Z Σ} {ext_spec0 : ext_spec Z}.

Lemma semax_ext' (ext_link: Strings.String.string -> ident) id sig cc A E P Q (fs : funspecs) :
  let f := mk_funspec sig cc A E P Q in
  In (ext_link  id,f) fs ->
  funspecs_norepeat fs ->
  ⊢semax_external (add_funspecs_rec Z ext_link ext_spec0 fs)
               (EF_external id (typesig2signature sig cc)) _ E P Q.
Proof.
intros f Hin Hnorepeat.
unfold semax_external.
iIntros (ge ????) "!> !> (%Hargsty & Hp & Hf)".
iIntros "!>" (??) "Hs".
iDestruct (add_funspecs_prepost _ _ _ _ (genv_symb_injective ge) with "[$Hp $Hs]") as (x' ?) "Hpost"; [done..|].
iExists x'; iFrame; iSplit; first done.
iIntros (?????); iMod ("Hpost" with "[%]") as "$"; done.
Qed.

Lemma semax_ext (ext_link: Strings.String.string -> ident) id sig sig' cc A E P Q (fs : funspecs) :
  let f := mk_funspec sig cc A E P Q in
  In (ext_link id,f) fs ->
  funspecs_norepeat fs ->
  sig' = typesig2signature sig cc ->
  ⊢semax_external (add_funspecs_rec Z ext_link ext_spec0 fs) (EF_external id sig') _ E P Q.
Proof.
intros; subst.
eapply semax_ext'; eauto.
Qed.

End semax_ext.
