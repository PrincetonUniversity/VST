Require Import veric.juicy_base.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.juicy_mem_ops.
Require Import sepcomp.extspec.
Require Import veric.juicy_extspec.
Require Import veric.tycontext. 
Require Import veric.expr2. 
Require Import veric.semax.
Require Import veric.semax_call.

Definition funsig2signature (s : funsig) cc : signature :=
  mksignature (map typ_of_type (map snd (fst s))) (Some (typ_of_type (snd s))) cc.

(* NOTE.   ext_link: Strings.String.string -> ident
   represents the mapping from the _name_ of an external function
  (an ASCII string) to the [ident] that's used to represent it in this program module.
  That mapping can be computed from the prog_defs component of the Clight.program
  produced by clightgen.
*)

Definition ef_id (ext_link: Strings.String.string -> ident) ef :=
  match ef with EF_external id sig => ext_link id | _ => 1%positive end.

Section funspecs2jspec.

Variable Z : Type.

Variable Espec : juicy_ext_spec Z.

Parameter symb2genv : forall (ge_s : PTree.t block), genv. (*TODO*)
Axiom symb2genv_ax : forall (ge_s : PTree.t block), Genv.genv_symb (symb2genv ge_s) = ge_s.

Definition funspec2pre (ext_link: Strings.String.string -> ident) (A : Type) P (ids: list ident) (id: ident) (ef: external_function) x ge_s 
           (tys : list typ) args (z : Z) m : Prop :=
  match ident_eq id (ef_id ext_link ef) as s 
  return ((if s then (rmap*A)%type else ext_spec_type Espec ef) -> Prop)
  with 
    | left _ => fun x' => exists phi0 phi1, join phi0 phi1 (m_phi m) 
                       /\ P (snd x') (make_ext_args (filter_genv (symb2genv ge_s)) ids args) phi0
                       /\ necR (fst x') phi1 
    | right n => fun x' => ext_spec_pre Espec ef x' ge_s tys args z m
  end x.

Definition funspec2post (ext_link: Strings.String.string -> ident)(A : Type) (Q : A -> environ -> mpred) 
                        id ef x ge_s (tret : option typ) ret (z : Z) m : Prop :=
  match ident_eq id (ef_id ext_link ef) as s 
  return ((if s then (rmap*A)%type else ext_spec_type Espec ef) -> Prop)
  with 
    | left _ => fun x' => exists phi0 phi1, join phi0 phi1 (m_phi m) 
                       /\ Q (snd x') (make_ext_rval (filter_genv (symb2genv ge_s))  ret) phi0
                       /\ necR (fst x') phi1 
    | right n => fun x' => ext_spec_post Espec ef x' ge_s tret ret z m
  end x.

Definition funspec2extspec (ext_link: Strings.String.string -> ident) (f : (ident*funspec)) 
  : external_specification juicy_mem external_function Z :=
  match f with 
    | (id, mk_funspec (params, sigret) _ A P Q) =>
      Build_external_specification juicy_mem external_function Z
        (fun ef => if ident_eq id (ef_id ext_link ef) then (rmap*A)%type else ext_spec_type Espec ef)
        (funspec2pre ext_link A P (fst (split params)) id)
        (funspec2post ext_link A Q id)
        (fun rv z m => False)
  end.

Require Import veric.res_predicates.

Local Open Scope pred.

Definition wf_funspec (f : funspec) :=
  match f with
    | mk_funspec sig cc A P Q => 
        forall a (ge ge': genv) n args, 
          Genv.genv_symb ge = Genv.genv_symb ge' ->
          P a (make_ext_args (filter_genv ge) n args) |-- P a (make_ext_args (filter_genv ge') n args)
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

Lemma all_funspecs_wf f : wf_funspec f.
Proof.
destruct f; simpl; intros a ge ge' n args H.
erewrite make_ext_args_symb; eauto.
Qed.

Program Definition funspec2jspec (ext_link: Strings.String.string -> ident) f : juicy_ext_spec Z :=
  Build_juicy_ext_spec _ (funspec2extspec ext_link f) _ _ _.
Next Obligation.
destruct f; simpl; unfold funspec2pre, pureat; simpl; destruct f; simpl; 
  destruct f; simpl; intros.
simpl in t; revert t.
destruct (ident_eq i (ef_id ext_link e)).
* subst i; intros t a a' Hage. 
intros [phi0 [phi1 [Hjoin [Hx Hy]]]].
apply age1_juicy_mem_unpack in Hage.
destruct Hage as [Hage Hdry].
destruct (age1_join2 phi0 Hjoin Hage) as [x' [y' [Hjoin' [Hage' H]]]].
exists x', y'; split; auto.
destruct m. split. eapply h; eauto.
apply (necR_trans (fst t0) phi1 y'); auto.
unfold necR. constructor; auto.
* intros ? ? ?; auto.
destruct Espec; simpl; apply JE_pre_hered.
Qed.
Next Obligation.
destruct f; simpl; unfold funspec2post, pureat; simpl; destruct f; simpl; 
  destruct f; simpl; intros.
simpl in t; revert t.
destruct (ident_eq i (ef_id ext_link e)).
* subst i; intros t a a' Hage; destruct m0; simpl.
intros [phi0 [phi1 [Hjoin [Hx Hy]]]].
apply age1_juicy_mem_unpack in Hage.
destruct Hage as [Hage Hdry].
destruct (age1_join2 phi0 Hjoin Hage) as [x' [y' [Hjoin' [Hage' H]]]].
exists x', y'; split; auto.
split; [solve[eapply h; eauto]|].
apply (necR_trans (fst t0) phi1 y'); auto.
unfold necR. constructor; auto.
* intros ? ? ?; auto.
destruct Espec; simpl; apply JE_post_hered.
Qed.
Next Obligation.
intros ? ? ? ?; destruct f; destruct f; destruct f; simpl.
intros a' Hage; auto.
Qed.

End funspecs2jspec.

Fixpoint in_funspecs (f : (ident*funspec)) (fs : funspecs) :=
  match fs with
    | nil => False
    | cons f' fs' => f=f' \/ in_funspecs f fs'
  end.

Fixpoint in_funspecs_by_id (f : (ident*funspec)) (fs : funspecs) :=
  match fs with
    | nil => False
    | cons f' fs' => fst f=fst f' \/ in_funspecs_by_id f fs'
  end.

Lemma in_funspecs_by_id_lem id f f' fs : 
  in_funspecs_by_id (id,f) fs <-> in_funspecs_by_id (id,f') fs.
Proof.
elim fs; simpl; [split; auto|].
intros [? ?]; simpl; intros H H2; rewrite H2; split; auto.
Qed.

Lemma in_funspecs_in_by_id f fs :
  in_funspecs f fs -> in_funspecs_by_id f fs.
Proof.
elim fs; simpl; auto.
intros [? ?]; simpl; intros ? IH.
intros [?|?]. subst. left; auto. right; auto.
Qed.

Fixpoint funspecs_norepeat fs :=
  match fs with
    | nil => True
    | cons f fs' => ~in_funspecs_by_id f fs' /\ funspecs_norepeat fs'
  end.

Fixpoint add_funspecs_rec (ext_link: Strings.String.string -> ident) (Z : Type) (Espec : juicy_ext_spec Z) (fs : funspecs) :=
  match fs with
    | nil => Espec
    | cons (i,f) fs' => funspec2jspec Z (add_funspecs_rec ext_link Z Espec fs') ext_link (i,f)
  end.

Require Import Coq.Logic.JMeq.

Lemma add_funspecs_pre  (ext_link: Strings.String.string -> ident)
              {Z fs id sig cc A P Q x args m} Espec tys ge_s phi0 phi1 :
  let ef := EF_external id (funsig2signature sig cc) in
  funspecs_norepeat fs -> 
  in_funspecs (ext_link id, (mk_funspec sig cc A P Q)) fs -> 
  join phi0 phi1 (m_phi m) ->
  P x (make_ext_args (filter_genv (symb2genv ge_s)) (fst (split (fst sig))) args) phi0 ->
  exists x' : ext_spec_type (JE_spec _ (add_funspecs_rec ext_link Z Espec fs)) ef, 
    JMeq (phi1,x) x' 
    /\ forall z, ext_spec_pre (add_funspecs_rec ext_link Z Espec fs) ef x' ge_s tys args z m.
Proof.
induction fs; [intros; elimtype False; auto|]; intros ef H H1 H2 Hpre.
destruct H1 as [H1|H1].

{ 
subst a; simpl in *.
clear IHfs H; revert x H2 Hpre; unfold funspec2pre; simpl.
destruct sig; simpl.
destruct (ident_eq (ext_link id) (ext_link id)); simpl.
rewrite fst_split. 
intros x Hjoin Hp. exists (phi1,x). split; eauto.
elimtype False; auto.
}

{ 
assert (Hin: in_funspecs_by_id (ext_link id, mk_funspec sig cc A P Q) fs). 
{ clear -H1; apply in_funspecs_in_by_id in H1; auto. }
destruct H as [Ha Hb]. 
destruct (IHfs Hb H1 H2 Hpre) as [x' H3].
clear -Ha Hin H1 H3; revert x' Ha Hin H1 H3.
destruct a; simpl; destruct f; simpl; destruct f; simpl; unfold funspec2pre; simpl.
destruct (ident_eq i (ext_link id)).
* subst i; destruct fs; [solve[simpl; intros; elimtype False; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  rewrite in_funspecs_by_id_lem with (f' := mk_funspec (l,t) c A0 m0 m1) in Hb.
  elimtype False; auto.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_post (ext_link: Strings.String.string -> ident){Z Espec tret fs id sig cc A P Q x ret m z ge_s} :
  let ef := EF_external id (funsig2signature sig cc) in
  funspecs_norepeat fs -> 
  in_funspecs (ext_link id, (mk_funspec sig cc A P Q)) fs -> 
  ext_spec_post (add_funspecs_rec ext_link Z Espec fs) ef x ge_s tret ret z m -> 
  exists (phi0 phi1 phi1' : rmap) (x' : A), 
       join phi0 phi1 (m_phi m) 
    /\ necR phi1' phi1
    /\ JMeq x (phi1',x') 
    /\ Q x' (make_ext_rval (filter_genv (symb2genv ge_s)) ret) phi0.
Proof.
induction fs; [intros; elimtype False; auto|]; intros ef H H1 Hpost.
destruct H1 as [H1|H1].

{ 
subst a; simpl in *.
clear IHfs H; revert x Hpost; unfold funspec2post; simpl.
destruct sig; simpl.
destruct (ident_eq (ext_link id) (ext_link id)); simpl.
intros x [phi0 [phi1 [Hjoin [Hq Hnec]]]].
exists phi0, phi1, (fst x), (snd x).
split; auto. split; auto. destruct x; simpl in *. split; auto.
elimtype False; auto.
}

{ 
assert (Hin: in_funspecs_by_id (ext_link id, mk_funspec sig cc A P Q) fs). 
{ clear -H1; apply in_funspecs_in_by_id in H1; auto. }
destruct H as [Ha Hb]. 
clear -Ha Hin H1 Hb Hpost IHfs; revert x Ha Hin H1 Hb Hpost IHfs.
destruct a; simpl; destruct f; simpl; unfold funspec2post; simpl.
destruct f; simpl.
destruct (ident_eq i (ext_link id)).
* subst i; destruct fs; [solve[simpl; intros; elimtype False; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  rewrite in_funspecs_by_id_lem with (f' := mk_funspec (l,t) c A0 m0 m1) in Hb.
  elimtype False; auto.
* intros. apply IHfs; auto.
}
Qed.

Definition add_funspecs (Espec : OracleKind) (ext_link: Strings.String.string -> ident) (fs : funspecs) : OracleKind :=
  match Espec with
    | Build_OracleKind ty spec => 
      Build_OracleKind ty (add_funspecs_rec ext_link ty spec fs)
  end.

Section semax_ext.

Variable Espec : OracleKind.

Lemma semax_ext' (ext_link: Strings.String.string -> ident) id sig cc A P Q (fs : funspecs) : 
  let f := mk_funspec sig cc A P Q in
  in_funspecs (ext_link  id,f) fs -> 
  funspecs_norepeat fs -> 
  (forall n, semax_external (add_funspecs Espec ext_link fs) (fst (split (fst sig))) 
               (EF_external id (funsig2signature sig cc)) _ P Q n).
Proof.
intros f Hin Hnorepeat.
unfold semax_external.
intros n ge x n0 Hlater F ts args jm H jm' H2 H3.
destruct H3 as [s [t [Hjoin [Hp Hf]]]].
destruct Espec.
assert (Hp'': P x (make_ext_args (filter_genv (symb2genv (Genv.genv_symb ge))) 
                                 (fst (split (fst sig))) args) s).
{ generalize (all_funspecs_wf f) as Hwf2; intro.
  spec Hwf2 x ge (symb2genv (Genv.genv_symb ge)) (fst (split (fst sig))) args.
  spec Hwf2.
  rewrite symb2genv_ax; auto. 
  apply Hwf2; auto. }
destruct (add_funspecs_pre ext_link OK_spec ts (Genv.genv_symb ge) s t Hnorepeat Hin Hjoin Hp'') 
  as [x' [Heq Hpre]].
simpl.
exists x'.
intros z.
split; [solve[apply Hpre]|].
intros tret ret z' jm2 Hlev jm3 Hnec Hpost.

eapply add_funspecs_post in Hpost; eauto.
destruct Hpost as [phi0 [phi1 [phi1' [x'' [Hjoin' [Hnec' [Hjmeq' Hq']]]]]]].
exists phi0, phi1; split; auto.
assert (JMeq (t,x) (phi1',x'')) by (eapply JMeq_trans; eauto).
assert ((t,x) = (phi1',x'')) by (apply JMeq_eq in H0; auto).
inv H1.
split; auto.
unfold filter_genv, Genv.find_symbol in Hq'|-*.
rewrite symb2genv_ax in Hq'; auto.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma semax_ext (ext_link: Strings.String.string -> ident) id ids sig sig' cc A P Q (fs : funspecs) : 
  let f := mk_funspec sig cc A P Q in
  in_funspecs (ext_link id,f) fs -> 
  funspecs_norepeat fs -> 
  ids = fst (split (fst sig)) -> 
  sig' = funsig2signature sig cc -> 
  (forall n, semax_external (add_funspecs Espec ext_link fs) ids (EF_external id sig') _ P Q n).
Proof.
intros; subst.
apply semax_ext'; auto.
Qed.

End semax_ext.  
