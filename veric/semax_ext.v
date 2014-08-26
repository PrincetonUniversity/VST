Require Import veric.base.
Require Import msl.rmaps.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import sepcomp.extspec.
Require Import veric.juicy_extspec.
Require Import veric.expr. 
Require Import veric.semax.

Definition funsig2signature (s : funsig) : signature :=
  mksignature (map typ_of_type (map snd (fst s))) (Some (typ_of_type (snd s))) cc_default.

Definition ef_id ef :=
  match ef with EF_external id sig => id | _ => 1%positive end.

Section funspecs2jspec.

Variable Z : Type.

Variable Espec : juicy_ext_spec Z.

Definition funspec2types id (A : Type) (ef : external_function) : Type :=
  if ident_eq id (ef_id ef) then A else (ext_spec_type Espec ef).

Parameter symb2genv : forall (ge_s : PTree.t block), genv. (*TODO*)
Axiom symb2genv_ax : forall (ge_s : PTree.t block), Genv.genv_symb (symb2genv ge_s) = ge_s.

Definition funspec2pre (A : Type) P id ef x ge_s (tys : list typ) args (z : Z) m : Prop :=
  match ident_eq id (ef_id ef) as s 
  return ((if s then A else ext_spec_type Espec ef) -> Prop)
  with 
    | left _ => fun x' => P x' (make_ext_args (symb2genv ge_s) 1 args) (m_phi m)
    | right n => fun x' => ext_spec_pre Espec ef x' ge_s tys args z m
  end x.

Definition funspec2post (A : Type) Q id ef x (tret : option typ) ret (z : Z) m : Prop :=
  match ident_eq id (ef_id ef) as s 
  return ((if s then A else ext_spec_type Espec ef) -> Prop)
  with 
    | left _ => fun x' => Q x' (make_ext_rval 1 ret) (m_phi m)
    | right n => fun x' => ext_spec_post Espec ef x' tret ret z m
  end x.

Definition funspec2extspec (f : (ident*funspec)) 
  : external_specification juicy_mem external_function Z :=
  match f with 
    | (id, mk_funspec sig A P Q) =>
      Build_external_specification juicy_mem external_function Z
        (fun ef => if ident_eq id (ef_id ef) then A else ext_spec_type Espec ef)
        (funspec2pre A P id)
        (funspec2post A Q id)
        (fun rv z m => False)
  end.

Definition wf_funspec (f : funspec) :=
  match f with
    | mk_funspec sig A P Q => 
        (forall a rho rho' phi phi', 
        (P a rho phi -> Q a rho' phi' -> 
        forall adr, 
          match phi @ adr with
            | NO _ => True
            | YES _ _ _ _ => True
            | PURE k pp => phi' @ adr = PURE k (preds_fmap (approx (level phi')) pp)
          end))
        /\ (forall a ge ge' n args phi, Genv.genv_symb ge = Genv.genv_symb ge' ->
              (P a (make_ext_args ge n args) phi <-> 
               P a (make_ext_args ge' n args) phi))
  end.

Program Definition funspec2jspec f (wf : wf_funspec (snd f)) : juicy_ext_spec Z :=
  Build_juicy_ext_spec _ (funspec2extspec f) _ _ _ _.
Next Obligation.
destruct f; simpl; unfold funspec2pre; simpl.
simpl in t; revert t.
destruct (ident_eq i (ef_id e)).
* clear wf; subst i; intros t a a' Hage; destruct m; simpl.
solve[apply h; apply age_jm_phi; auto].
* intros ? ? ?; auto.
destruct Espec; simpl; apply JE_pre_hered.
Qed.
Next Obligation.
destruct f; simpl; unfold funspec2post; simpl.
simpl in t; revert t.
destruct (ident_eq i (ef_id e)).
* clear wf; subst i; intros t a a' Hage; destruct m0; simpl.
apply h; apply age_jm_phi; auto.
* intros ? ? ?; auto.
destruct Espec; simpl; apply JE_post_hered.
Qed.
Next Obligation.
intros ? ? ? ?; destruct f; auto.
Qed.
Next Obligation.
destruct f; unfold jspec_pures_sub; simpl; intros.
revert wf; unfold wf_funspec; simpl; intros H2. revert t H H0 H2. 
unfold funspec2pre, funspec2post. 
destruct (ident_eq i (ef_id e)).
* intros. intros adr.
destruct H2 as [H2 _].
specialize (H2 t (make_ext_args (symb2genv ge_s) 1 args) (make_ext_rval 1 rv)). 
apply (H2 (m_phi jm) (m_phi jm') H H0 adr).
* destruct Espec; simpl; intros.
clear H2; eapply (JE_rel e); eauto.
Qed.

End funspecs2jspec.

Inductive wf_funspecs := 
| wf_nil : wf_funspecs
| wf_cons : forall (f : ident*funspec) (wf : wf_funspec (snd f)) (l : wf_funspecs), 
              wf_funspecs.

Fixpoint in_funspecs (f : (ident*funspec)) (fs : wf_funspecs) :=
  match fs with
    | wf_nil => False
    | wf_cons f' wf fs' => f=f' \/ in_funspecs f fs'
  end.

Fixpoint in_funspecs_by_id (f : (ident*funspec)) (fs : wf_funspecs) :=
  match fs with
    | wf_nil => False
    | wf_cons f' wf fs' => fst f=fst f' \/ in_funspecs_by_id f fs'
  end.

Lemma in_funspecs_by_id_lem id f f' fs : 
  in_funspecs_by_id (id,f) fs <-> in_funspecs_by_id (id,f') fs.
Proof.
elim fs; simpl; [split; auto|].
intros [? ?]; simpl; intros H H2 H3; rewrite H3; split; auto.
Qed.

Lemma in_funspecs_in_by_id f fs :
  in_funspecs f fs -> 
  in_funspecs_by_id f fs.
Proof.
elim fs; simpl; auto.
intros [? ?]; simpl; intros ? ? IH.
intros [?|?]. subst. left; auto. right; auto.
Qed.

Fixpoint funspecs_norepeat fs :=
  match fs with
    | wf_nil => True
    | wf_cons f wf fs' => ~in_funspecs_by_id f fs' /\ funspecs_norepeat fs'
  end.

Lemma in_funspecs_wf f fs : in_funspecs f fs -> wf_funspec (snd f).
Proof. induction fs; simpl; inversion 1; try subst f0; auto. Qed.

Fixpoint add_funspecs_rec (Z : Type) (Espec : juicy_ext_spec Z) (fs : wf_funspecs) :=
  match fs with
    | wf_nil => Espec
    | wf_cons (i,f) wf fs' => 
      funspec2jspec Z (add_funspecs_rec Z Espec fs') (i,f) wf
  end.

Require Import JMeq.

Lemma add_funspecs_pre {Z fs id sig A P Q x args m} Espec tys ge_s :
  let ef := EF_external id (funsig2signature sig) in
  funspecs_norepeat fs -> 
  in_funspecs (id, (mk_funspec sig A P Q)) fs -> 
  P x (make_ext_args (symb2genv ge_s) 1%positive args) (m_phi m) ->
  exists x' : ext_spec_type (JE_spec _ (add_funspecs_rec Z Espec fs)) ef, 
    JMeq x x' /\ forall z, ext_spec_pre (add_funspecs_rec Z Espec fs) ef x' ge_s tys args z m.
Proof.
induction fs; [intros; elimtype False; auto|]; intros ef H H1 H2.
destruct H1 as [H1|H1].

{ 
subst f;simpl in *.
clear IHfs H; revert x H2; unfold funspec2pre; simpl.
destruct (ident_eq id id); simpl.
solve[intros x Hp; exists x; auto].
solve[elimtype False; auto]. 
}

{ 
assert (Hin: in_funspecs_by_id (id, mk_funspec sig A P Q) fs). 
{ clear -H1; apply in_funspecs_in_by_id in H1; auto. }
destruct H as [Ha Hb]. 
destruct (IHfs Hb H1 H2) as [x' H3].
clear -Ha Hin H1 H3; revert x' Ha Hin H1 H3.
destruct f; simpl; destruct f; simpl; unfold funspec2pre; simpl.
destruct (ident_eq i id).
* subst i; destruct fs; [solve[simpl; intros; elimtype False; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  rewrite in_funspecs_by_id_lem with (f' := mk_funspec f A0 m0 m1) in Hb.
  elimtype False; auto.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_post {Z Espec tret fs id sig A P Q x ret m z} :
  let ef := EF_external id (funsig2signature sig) in
  funspecs_norepeat fs -> 
  in_funspecs (id, (mk_funspec sig A P Q)) fs -> 
  ext_spec_post (add_funspecs_rec Z Espec fs) ef x tret ret z m -> 
  exists x' : A, 
    JMeq x x' /\ Q x' (make_ext_rval 1%positive ret) (m_phi m).
Proof.
induction fs; [intros; elimtype False; auto|]; intros ef H H1 H2.
destruct H1 as [H1|H1].

{ 
subst f;simpl in *.
clear IHfs H; revert x H2; unfold funspec2post; simpl.
destruct (ident_eq id id); simpl.
solve[intros x Hp; exists x; auto].
solve[elimtype False; auto]. 
}

{ 
assert (Hin: in_funspecs_by_id (id, mk_funspec sig A P Q) fs). 
{ clear -H1; apply in_funspecs_in_by_id in H1; auto. }
destruct H as [Ha Hb]. 
clear -Ha Hin H1 H2 Hb IHfs; revert x Ha Hin H1 H2 Hb IHfs.
destruct f; simpl; destruct f; simpl; unfold funspec2post; simpl.
destruct (ident_eq i id).
* subst i; destruct fs; [solve[simpl; intros; elimtype False; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  rewrite in_funspecs_by_id_lem with (f' := mk_funspec f A0 m0 m1) in Hb.
  elimtype False; auto.
* intros. apply IHfs; auto.
}
Qed.

Definition add_funspecs (Espec : OracleKind) (fs : wf_funspecs) : OracleKind :=
  match Espec with
    | Build_OracleKind ty spec => 
      Build_OracleKind ty (add_funspecs_rec ty spec fs)
  end.

Definition local_funspec (f : funspec) :=
  match f with mk_funspec spec A P Q => 
      (* safety monotonicity *)
      (forall (x : A) rho phi1 phi2 phi, join phi1 phi2 phi -> 
         P x rho phi1 -> P x rho phi)
      (* frame property *)
   /\ (forall (x : A) rho phi1 phi2 phi, join phi1 phi2 phi -> 
         P x rho phi1 -> 
       forall rho' phi', (level phi >= level phi')%nat -> 
         Q x rho' phi' ->
         exists phi1' phi2', 
         join phi1' phi2' phi' /\ age phi2 phi2' /\ Q x rho' phi1')         
  end.

Section semax_ext.

Variable Espec : OracleKind.

Lemma semax_ext id sig A P Q (fs : wf_funspecs) : 
  let f := mk_funspec sig A P Q in
  local_funspec f -> 
  in_funspecs (id,f) fs -> 
  funspecs_norepeat fs -> 
  (forall n, semax_external (add_funspecs Espec fs) (EF_external id (funsig2signature sig)) _ P Q n).
Proof.
intros f Hloc Hin Hnorepeat.
unfold semax_external.
intros n ge x n0 Hlater F ts args jm H jm' H2 H3.
destruct H3 as [s [t [Hjoin [Hp Hf]]]].
cut (P x (make_ext_args ge 1 args) (m_phi jm')). intro Hp'.
destruct Espec.
assert (Hp'': P x (make_ext_args (symb2genv (Genv.genv_symb ge)) 1 args) (m_phi jm')).
{ generalize (in_funspecs_wf _ _ Hin). simpl; intros [Hwf1 Hwf2].
  rewrite Hwf2; eauto.
  rewrite symb2genv_ax; auto. }
destruct (add_funspecs_pre OK_spec ts (Genv.genv_symb ge) Hnorepeat Hin Hp'') 
  as [x' [Heq Hpre]].
simpl.
exists x'.
intros z.
split; [solve[apply Hpre]|].
intros tret ret z' jm2 Hlev jm3 Hnec Hpost.

cut (Q x (make_ext_rval 1 ret) (m_phi jm3)). intro Hq.
unfold f in Hloc.
destruct Hloc as [Hl1 Hl2].
assert (Hlev': (level (m_phi jm') >= level (m_phi jm3))%nat). 
{ cut ((level (m_phi jm2) >= level (m_phi jm3))%nat). omega.
  apply necR_level in Hnec; erewrite <-level_juice_level_phi; eauto. }
destruct (Hl2 _ _ s t (m_phi jm') Hjoin Hp _ _ Hlev' Hq) 
  as [phi' [t' [Hjoin' [Hage' Hq']]]].
exists phi', t'; split; auto.
split; auto. destruct F. simpl in Hf|-*. eapply h in Hf; eauto.

eapply add_funspecs_post in Hpost; eauto.
destruct Hpost as [x'' [Heq' Hq']].
assert (JMeq x x'') by (eapply JMeq_trans; eauto).
solve[apply JMeq_eq in H0; subst; auto].

unfold f in Hloc; destruct Hloc as [Hloc _]. 
solve[eapply Hloc; eauto].
Qed.
  
End semax_ext.  
