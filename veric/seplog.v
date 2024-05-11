Require Export VST.veric.base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import iris_ora.algebra.gmap_view.
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.address_conflict.
Require Export VST.veric.shares.
Require Import VST.veric.Cop2. (*for definition of tc_val'*)
Require Import Coq.Logic.JMeq.
(* Diagnostic tactic, useful because intuition can be much slower than tauto 
Tactic Notation "intuition" :=
 try (solve [tauto]; idtac "Intuition used where tauto would work");
 Coq.Init.Tauto.intuition.
*)

(*******************material moved here from tycontext.v *******************)

Section mpred.

Context `{!heapGS Σ}.
Local Notation mpred := (@mpred Σ).
Local Notation funspec := (@funspec Σ).
Local Notation assert := (@assert Σ).
Local Notation argsassert := (@argsassert Σ).

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

Inductive tycontext : Type :=
  mk_tycontext : forall (tyc_temps: Maps.PTree.t type)
                        (tyc_vars: Maps.PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: Maps.PTree.t type)
                        (tyc_globsp: Maps.PTree.t funspec)
                        (tyc_annot: Maps.PTree.t Annotation),
                             tycontext.

Definition empty_tycontext : tycontext :=
  mk_tycontext (Maps.PTree.empty _) (Maps.PTree.empty _) Ctypes.Tvoid
         (Maps.PTree.empty _)  (Maps.PTree.empty _) (Maps.PTree.empty _).

Definition temp_types (Delta: tycontext): Maps.PTree.t type :=
  match Delta with mk_tycontext a _ _ _ _ _ => a end.
Definition var_types (Delta: tycontext) : Maps.PTree.t type :=
  match Delta with mk_tycontext _ a _ _ _ _ => a end.
Definition ret_type (Delta: tycontext) : type :=
  match Delta with mk_tycontext _ _ a _ _ _ => a end.
Definition glob_types (Delta: tycontext) : Maps.PTree.t type :=
  match Delta with mk_tycontext _ _ _ a _ _ => a end.
Definition glob_specs (Delta: tycontext) : Maps.PTree.t funspec :=
  match Delta with mk_tycontext _ _ _ _ a _ => a end.
Definition annotations (Delta: tycontext) : Maps.PTree.t Annotation :=
  match Delta with mk_tycontext _ _ _ _ _ a => a end.

(** Creates a typecontext from a function definition **)
(* NOTE:  params start out initialized, temps do not! *)

Definition make_tycontext_t (params: list (ident*type)) (temps : list(ident*type)) :=
fold_right (fun (param: ident*type) => Maps.PTree.set (fst param) (snd param))
 (fold_right (fun (temp : ident *type) tenv => let (id,ty):= temp in Maps.PTree.set id ty tenv)
  (Maps.PTree.empty type) temps) params.

Definition make_tycontext_v (vars : list (ident * type)) :=
 fold_right (fun (var : ident * type) venv => let (id, ty) := var in Maps.PTree.set id ty venv)
   (Maps.PTree.empty type) vars.

Definition make_tycontext_g (V: varspecs) (G: funspecs) :=
 (fold_right (fun (var : ident * funspec) => Maps.PTree.set (fst var) (type_of_funspec (snd var)))
      (fold_right (fun (v: ident * type) => Maps.PTree.set (fst v) (snd v))
         (Maps.PTree.empty _) V)
            G).

Definition make_tycontext_a (anns : list (ident * Annotation)) :=
 fold_right (fun (ia : ident * Annotation) aenv => let (id, a) := ia in Maps.PTree.set id a aenv)
   (Maps.PTree.empty Annotation) anns.

Definition make_tycontext (params: list (ident*type)) (temps: list (ident*type)) (vars: list (ident*type))
                       (return_ty: type)
                       (V: varspecs) (G: funspecs) (A: list (ident*Annotation)):  tycontext :=
 mk_tycontext
   (make_tycontext_t params temps)
   (make_tycontext_v vars)
   return_ty
   (make_tycontext_g V G)
   (make_tycontext_s G)
   (make_tycontext_a A).

(******************* end of material from tycontext.v*)

(*******************material moved here from expr.v *******************)

(** Environment typechecking functions **)

Definition typecheck_temp_environ
(te: tenviron) (tc: Maps.PTree.t type) :=
forall (id : ident) ty , tc !! id = Some ty  -> exists v, Map.get te id = Some v /\ tc_val' ty v.

Definition typecheck_var_environ
(ve: venviron) (tc: Maps.PTree.t type) :=
forall (id : ident) ty, tc !! id = Some ty <-> exists v, Map.get ve id = Some(v,ty).

Definition typecheck_glob_environ
(ge: genviron) (tc: Maps.PTree.t type) :=
forall (id : ident) t, tc !! id = Some t ->
(exists b, Map.get ge id = Some b).

Definition typecheck_environ (Delta: tycontext) (rho : environ) :=
typecheck_temp_environ (te_of rho) (temp_types Delta) /\
typecheck_var_environ  (ve_of rho) (var_types Delta) /\
typecheck_glob_environ (ge_of rho) (glob_types Delta).

Definition local: (environ -> Prop) -> assert := fun l => assert_of (lift1 bi_pure l).

Definition tc_environ (Delta: tycontext) : environ -> Prop :=
   fun rho => typecheck_environ Delta rho.

Definition funsig_tycontext (fs: funsig) : tycontext :=
  make_tycontext (fst fs) nil nil (snd fs) nil nil nil.
(*
Definition funsig_of_funspec (fs: funspec) : funsig :=
 match fs with mk_funspec fsig _ _ _ _ _ _ => fsig end.
*)
Definition ret0_tycon (Delta: tycontext): tycontext :=
  mk_tycontext (Maps.PTree.empty _) (Maps.PTree.empty _) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta).

Definition typesig_of_funspec (fs: funspec) : typesig :=
 match fs with mk_funspec fsig _ _ _ _ _ => fsig end.

Definition rettype_of_funspec (fs: funspec) : type := snd (typesig_of_funspec fs).

Definition rettype_tycontext t := make_tycontext nil nil nil t nil nil nil.

Definition tc_genv g Delta := typecheck_glob_environ g (glob_types Delta).

Definition tc_args (tys: list type) (vals: list val):Prop := Forall2 tc_val' tys vals.

Definition tc_argsenv Delta tys (gargs:argsEnviron):Prop := 
  match gargs with (g, args) => tc_genv g Delta /\ Forall2 tc_val' tys args end.

Lemma fssub_prop1: forall rt ptypes gargs, 
    tc_argsenv (rettype_tycontext rt) ptypes gargs = 
     Forall2 tc_val' ptypes (snd gargs).
intros. destruct gargs. unfold tc_argsenv. simpl.
unfold tc_genv. simpl.
unfold typecheck_glob_environ. apply Axioms.prop_ext; split; intros. apply H.
split; trivial. intros. rewrite Maps.PTree.gempty // in H0.
Qed.

Lemma fssub_prop2: forall rt rho, (local (tc_environ (rettype_tycontext rt)) rho) ⊣⊢ ⌜ve_of rho = Map.empty (block * type)⌝.
intros. unfold local, tc_environ, lift1.
unfold rettype_tycontext, typecheck_environ, typecheck_temp_environ,
typecheck_var_environ, typecheck_glob_environ.
simpl.
destruct rho; simpl. apply bi.pure_iff; split.
- intros [? [? ?]].
apply Map.ext. intros. clear H H1. specialize (H0 x).
destruct (Map.get ve); simpl in *. 
destruct p.  destruct (H0 t); clear H0. clear H.
exfalso. exploit H1. eexists; reflexivity. rewrite Maps.PTree.gempty. congruence.
reflexivity.
- intros U. simpl in *. subst. split3; intros.
 rewrite Maps.PTree.gempty in H; congruence.
 split; intros. rewrite Maps.PTree.gempty in H; congruence.
 destruct H. inv H.
 rewrite Maps.PTree.gempty in H. congruence.
Qed.

Open Scope bi_scope.

(* If we were to require that a non-void-returning function must,
   at a function call, have its result assigned to a temp,
   then we could change "ret0_tycon" to "ret_tycon" in this
   definition (and in NDfunspec_sub). *)
(*
Definition funspec_sub_si_ORIG (f1 f2 : funspec):mpred :=
let Delta2 := rettype_tycontext (snd (typesig_of_funspec f2)) in
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
        !!(tpsig1=tpsig2 /\ cc1=cc2) ∧
    ▷   ! (∀ ts2 :_, ∀ x2:dependent_type_functor_rec ts2 A2 mpred,
             ∀ gargs:genviron * list val,
        ((!!(tc_argsenv Delta2 (fst tpsig2) gargs) ∧ P2 ts2 x2 gargs)
         >=> ∃ ts1:_,  ∃ x1:dependent_type_functor_rec ts1 A1 mpred, ∃ F:_, 
            (F * (P1 ts1 x1 gargs)) ∧
            ∀ rho':_, (     !( ((local (tc_environ (rettype_tycontext (snd tpsig1))) rho') ∧ (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho')))))
    end
end.
Definition funspec_sub_si_AUX1 (f1 f2 : funspec):mpred :=
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
       let Delta := rettype_tycontext (snd tpsig1) in
        !!(tpsig1=tpsig2 /\ cc1=cc2) ∧
        ! (∀ ts2 :_, ∀ x2:dependent_type_functor_rec ts2 A2 mpred,
             ∀ gargs:genviron * list val,
        ((!!(tc_argsenv Delta (fst tpsig1) gargs) ∧ P2 ts2 x2 gargs)
         >=> ∃ ts1:_,  ∃ x1:_, ∃ F:_, 
            (F * (P1 ts1 x1 gargs)) ∧
            ∀ rho':_, (     !( ((local (tc_environ Delta) rho') ∧ (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho')))))
    end
end. 
Lemma fssubAUX1: funspec_sub_si_AUX1 = funspec_sub_si_ORIG.
extensionality fs1; extensionality fs2.
destruct fs1; destruct fs2. destruct t; destruct t0.
apply pred_ext; simpl. 
+ intros ? [? ?]. split; trivial. 
  destruct H. inv H. apply H0. 
+ intros ? [? ?]. split; trivial. 
  destruct H. inv H. apply H0.
Qed.

Definition funspec_sub_si_AUX2 (f1 f2 : funspec):mpred :=
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
        !!(tpsig1=tpsig2 /\ cc1=cc2) ∧
        ! (∀ ts2 :_, ∀ x2:dependent_type_functor_rec ts2 A2 mpred,
             ∀ gargs:genviron * list val,
        ((!!(Forall2 tc_val' (fst tpsig1) (snd gargs)) ∧ P2 ts2 x2 gargs)
         >=> ∃ ts1:_,  ∃ x1:_, ∃ F:_, 
            (F * (P1 ts1 x1 gargs)) ∧
            ∀ rho':_, (     !( ((!!(ve_of rho' = Map.empty (block * type))) ∧ (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho')))))
    end
end. 
Lemma fssubAUX2: funspec_sub_si_AUX2 = funspec_sub_si_ORIG.
rewrite <- fssubAUX1.
extensionality fs1; extensionality fs2.
destruct fs1; destruct fs2. destruct t; destruct t0. simpl.
apply pred_ext; simpl. 
+ intros ? [? ?]. split; trivial. 
  destruct H. inv H. intros ? ? ? ? ? ? ? ?.
  rewrite fssub_prop1 in H2.
  destruct (H0 b b0 b1 y H a' H1 H2) as [ts1 [x1 [FRM [AA BB]]]]; clear H0.
  exists ts1, x1, FRM; split; trivial. simpl; intros.
  apply (BB b2 y0 H0 _ H3); clear BB. rewrite <- (fssub_prop2 t0). apply H4.
+ intros ? [? ?]. split; trivial. 
  destruct H. inv H. intros ? ? ? ? ? ? ? ?.
  rewrite <- (fssub_prop1 t0) in H2.
  destruct (H0 b b0 b1 y H a' H1 H2) as [ts1 [x1 [FRM [AA BB]]]]; clear H0.
  exists ts1, x1, FRM; split; trivial. simpl; intros.
  apply (BB b2 y0 H0 _ H3); clear BB. rewrite (fssub_prop2 t0). apply H4.
Qed.*)

(*fssubAUX2 MOTIVATES the following new definitions of funspec_sub_si and funspec_sub*)
Definition argsHaveTyps (vals:list val) (types: list type): Prop:=
  Forall2 (fun v t => v<>Vundef -> Val.has_type v t) vals (map typ_of_type types).

Definition funspec_sub_si (f1 f2 : funspec) : mpred :=
match f1 with
| mk_funspec tpsig1 cc1 A1 E1 P1 Q1 =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 E2 P2 Q2 =>
        ⌜tpsig1=tpsig2 /\ cc1=cc2⌝ ∧
       ▷ ■ ∀ (x2:dtfr A2) (gargs:genviron * list val),
        ((⌜argsHaveTyps (snd gargs) (fst tpsig1)⌝ ∧ P2 x2 gargs)
         ={E2 x2}=∗ (∃ x1 F, ⌜E1 x1 ⊆ E2 x2⌝ ∧
            (F ∗ (P1 x1 gargs)) ∧
            ∀ rho', (■(((⌜ve_of rho' = Map.empty (block * type)⌝ ∧ (F ∗ (Q1 x1 rho')))
                         -∗ (Q2 x2 rho'))))))
    end
end.

Definition funspec_sub (f1 f2 : funspec): Prop :=
match f1 with
| mk_funspec tpsig1 cc1 A1 E1 P1 Q1 =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 E2 P2 Q2 =>
        (tpsig1=tpsig2 /\ cc1=cc2) /\
        forall (x2:dtfr A2) (gargs:argsEnviron),
        (⌜argsHaveTyps(snd gargs)(fst tpsig1)⌝ ∧ P2 x2 gargs)
         ⊢ |={E2 x2}=> (∃ (x1:dtfr A1) (F:_), ⌜E1 x1 ⊆ E2 x2⌝ ∧
                           (F ∗ (P1 x1 gargs)) ∧
                               (⌜forall rho',
                                           (⌜ve_of rho' = Map.empty (block * type)⌝ ∧
                                                 (F ∗ (Q1 x1 rho')))
                                         ⊢ (Q2 x2 rho')⌝))
    end
end.

Global Instance funspec_sub_si_plain f1 f2 : Plain (funspec_sub_si f1 f2).
Proof. destruct f1, f2; apply _. Qed.

Global Instance funspec_sub_si_absorbing f1 f2 : Absorbing (funspec_sub_si f1 f2).
Proof. destruct f1, f2; simpl; apply _. Qed.

Lemma funspec_sub_sub_si f1 f2: funspec_sub f1 f2 -> ⊢ funspec_sub_si f1 f2.
Proof.
  intros. destruct f1; destruct f2; simpl in *.
  destruct H as [[? ?] H']; subst.
  iSplit; first done.
  iIntros "!> !>" (x2 gargs) "H".
  iMod (H' with "H") as (x1 F HE) "[H' %]".
  iIntros "!>"; iExists x1, F; iFrame.
  iSplit; auto; iSplit; auto.
  iIntros (rho') "!> H".
  by iApply H.
Qed.

Lemma funspec_sub_sub_si' f1 f2: ⌜funspec_sub f1 f2⌝ ⊢ funspec_sub_si f1 f2.
Proof.
  iApply bi.pure_elim'; intros.
  destruct f1; destruct f2; simpl in *.
  destruct H as [[? ?] H']; subst.
  iIntros "?"; iSplit; first done.
  iIntros "!> !>" (x2 gargs) "H".
  iMod (H' with "H") as (x1 F HE) "[H' %]".
  iIntros "!>"; iExists x1, F; iFrame.
  iSplit; auto; iSplit; auto.
  iIntros (rho') "!> H".
  by iApply H.
Qed.

(*
Lemma funspec_sub_early_sub_si f1 f2: funspec_sub_early f1 f2 ⊢ funspec_sub_si f1 f2.
Proof. intros p P. destruct f1; destruct f2; simpl in *.
destruct P as [[? ?] H']; subst. split; [split; trivial |].
intros ts2 x2 rho y WY k YK K c J.
destruct (H' ts2 x2 rho) as [ts1 [x1 [F HF]]]; clear H'.
destruct (HF _ WY _ YK K) as [(? & J' & m' & Hl & ? & ? & HF1) HF2]; eauto; subst.
eexists; split; eauto; exists m'; repeat (split; auto).
exists ts1, x1, F. rewrite Hl; auto.
Qed.
*)

Lemma funspec_sub_refl f: funspec_sub f f.
Proof.
  destruct f; split; [ split3; trivial | intros x2 rho].
  iIntros "[_ P] !>".
  iExists x2, emp%I; iFrame; iPureIntro.
  split3; auto; intros; iIntros "(_ & _ & $)".
Qed.

(* allows to unify A1 A2 first, as P, Q may depend on A *)
Lemma funspec_sub_refl_dep A1 A2 cc1 cc2 sig1 sig2 E1 E2 P1 P2 Q1 Q2 :
  JMeq A1 A2 ->
  cc1 = cc2 ->
  sig1 = sig2 ->
  JMeq E1 E2 ->
  JMeq P1 P2 ->
  JMeq Q1 Q2 ->
  funspec_sub (mk_funspec cc1 sig1 A1 E1 P1 Q1) (mk_funspec cc2 sig2 A2 E2 P2 Q2).
Proof.
intros. subst. apply funspec_sub_refl.
Qed.

Lemma funspec_sub_trans f1 f2 f3: funspec_sub f1 f2 ->
      funspec_sub f2 f3 -> funspec_sub f1 f3.
Proof.
  destruct f1 as [cc1 sig1 A1 E1 P1 Q1]; destruct f2 as [cc2 sig2 A2 E2 P2 Q2]; destruct f3 as [cc3 sig3 A3 E3 P3 Q3].
  intros [(? & ?) H12]; subst sig1 cc1.
  intros [(? & ?) H23]; subst sig2 cc2.
  split; [split3; trivial | intros x rho].
  iIntros "[% H]".
  iMod (H23 with "[$H]") as (x2 F2 HE2) "[[F2 H] %H32]"; first done.
  iMod (fupd_mask_subseteq (E2 x2)) as "Hmask"; first done.
  iMod (H12 with "[$H]") as (x1 F1 HE1) "[[F1 H] %H21]"; first done.
  iMod "Hmask" as "_".
  iIntros "!>"; iExists x1, (F2 ∗ F1)%I.
  iFrame; iPureIntro.
  split3; auto; intros.
  { by etrans. }
  iIntros "(% & [F2 F1] & H)".
  by iApply H32; iFrame "% F2"; iApply H21; iFrame.
Qed.

Lemma funspec_sub_si_refl f: ⊢ funspec_sub_si f f.
Proof.
  apply funspec_sub_sub_si, funspec_sub_refl.
Qed.

Lemma funspec_sub_si_trans f1 f2 f3: funspec_sub_si f1 f2 ∧ funspec_sub_si f2 f3 ⊢
      funspec_sub_si f1 f3.
Proof.
  destruct f1 as [?? A1 E1 P1 Q1]; destruct f2 as [?? A2 E2 P2 Q2]; destruct f3 as [?? A3 E3 P3 Q3].
  unfold funspec_sub_si; simpl.
  iIntros "[[(-> & ->) #H12] [(-> & ->) #H23]]".
  iSplit.
  { iPureIntro; split3; trivial; by etrans. }
  iIntros "!> !>" (x gargs) "[% H]".
  iMod ("H23" with "[$H]") as (x2 F2 HE2) "H"; first done.
  rewrite -plainly_forall; iDestruct "H" as "[[F2 H] #H32]".
  iMod (fupd_mask_subseteq (E2 x2)) as "Hmask"; first done.
  iMod ("H12" with "[$H]") as (x1 F1 HE1) "H"; first done.
  rewrite -plainly_forall; iDestruct "H" as "[[F1 H] #H21]".
  iMod "Hmask" as "_".
  iIntros "!>"; iExists x1, (F2 ∗ F1)%I.
  iFrame; iSplit.
  { iPureIntro; by etrans. }
  iSplit; first done.
  iIntros (rho') "!> (% & [F2 F1] & H)".
  by iApply "H32"; iFrame "% F2"; iApply "H21"; iFrame.
Qed.

Global Instance funspec_sub_si_nonexpansive : NonExpansive2 (funspec_sub_si).
Proof.
  intros ? [?????] [?????] (? & ? & ? & HE1 & HP1 & HQ1) [?????] [?????] (? & ? & ? & HE2 & HP2 & HQ2); subst; simpl in *.
  do 8 f_equiv.
  { rewrite (HP2 _ _) //. }
  rewrite HE2.
  do 6 f_equiv.
  { rewrite HE1 //. }
  f_equiv.
  { rewrite (HP1 _ _) //. }
  do 4 f_equiv.
  { rewrite (HQ1 _ _) //. }
  { rewrite (HQ2 _ _) //. }
Qed.

(*******************end of material moved here from expr.v *******************)

(* Interesting note: in Caesium, they store the function in the ghost state instead of the spec.
   Could we then quantify over a function that meets a spec? *)

Definition funspec_auth m := own(inG0 := funspec_inG) funspec_name (gmap_view_auth (dfrac.DfracOwn 1) m).
Definition know_funspec l (f: funspec) := own(inG0 := funspec_inG) funspec_name (gmap_view_frag l dfrac.DfracDiscarded (funspec_unfold f)).

Definition func_at (f: funspec) (l : address) : mpred := l ↦□ FUN ∗ know_funspec l f.

Global Instance inhabited_typesig : Inhabited typesig := populate ([], Tvoid).
Global Instance inhabited_calling_convention : Inhabited calling_convention := populate cc_default.
Global Instance inhabited_typetree : Inhabited TypeTree := populate Mpred.

Lemma func_at_agree f1 f2 l : ⊢ func_at f1 l -∗ func_at f2 l -∗ ∃ sig cc A E P1 P2 Q1 Q2,
  ▷ (⌜f1 = mk_funspec sig cc A E P1 Q1 ∧ f2 = mk_funspec sig cc A E P2 Q2⌝ ∧ P1 ≡ P2 ∧ Q1 ≡ Q2).
Proof.
  intros; iIntros "(_ & Hf1) (_ & Hf2)".
  iDestruct (own_valid_2 with "Hf1 Hf2") as "H".
  rewrite gmap_view_frag_op_validI later_equivI funspec_equivI; iDestruct "H" as "[_ H]".
  iDestruct "H" as (????????) "H".
  iExists _, _, _, _, _, _, _, _; done.
Qed.

Lemma func_at_auth m f l : ⊢ funspec_auth m -∗ func_at f l -∗ (m !! l)%stdpp ≡ Some (funspec_unfold f).
Proof.
  intros; iIntros "Hm (_ & Hf)".
  iDestruct (own_valid_2 with "Hm Hf") as "H".
  rewrite gmap_view_both_validI bi.and_elim_r //.
Qed.

Definition func_at' (f: funspec) (l: address) : mpred :=
  match f with
   | mk_funspec fsig cc _ _ _ _ => ∃ A E P Q, func_at (mk_funspec fsig cc A E P Q) l
  end.

Global Instance func_at'_persistent f l : Persistent (func_at' f l).
Proof. destruct f; apply _. Qed.

Global Instance func_at'_affine f l : Affine (func_at' f l).
Proof. destruct f; apply _. Qed.

Definition sigcc_at (fsig: typesig) (cc:calling_convention) (l: address) : mpred :=
  ∃ A E P Q, func_at (mk_funspec fsig cc A E P Q) l.

Definition func_ptr_si (f: funspec) (v: val): mpred :=
  ∃ b, ⌜v = Vptr b Ptrofs.zero⌝ ∧ (∃ gs: funspec, funspec_sub_si gs f ∧ func_at gs (b, 0)).

Definition func_ptr (f: funspec) (v: val): mpred :=
  ∃ b, ⌜v = Vptr b Ptrofs.zero⌝ ∧ (∃ gs: funspec, ⌜funspec_sub gs f⌝ ∧ func_at gs (b, 0)).

(*Definition func_ptr_si ge E id (f: funspec) (v: val): mpred :=
  ∃ b, ⌜Map.get ge id = Some b ∧ v = Vptr b Ptrofs.zero⌝ ∧ (∃ gs: funspec, funspec_sub_si E gs f ∧ func_at gs (b, 0)).

Definition func_ptr ge E id (f: funspec) (v: val): mpred :=
  ∃ b, ⌜Map.get ge id = Some b ∧ v = Vptr b Ptrofs.zero⌝ ∧ (∃ gs: funspec, ⌜funspec_sub E gs f⌝ ∧ func_at gs (b, 0)).*)

Lemma func_ptr_fun_ptr_si f v: func_ptr f v ⊢ func_ptr_si f v.
Proof.
  iIntros "H"; iDestruct "H" as (????) "H".
  iExists b; iFrame "%"; iExists gs; iFrame.
  iSplit; auto; by iApply funspec_sub_sub_si'.
Qed.

Lemma func_ptr_si_mono fs gs v:
      funspec_sub_si fs gs ∧ func_ptr_si fs v ⊢ func_ptr_si gs v.
Proof.
  iIntros "H".
  rewrite /func_ptr_si bi.and_exist_l.
  iDestruct "H" as (b) "H".
  rewrite bi.and_comm -bi.and_assoc bi.and_exist_r.
  iDestruct "H" as (? hs) "H".
  iExists b; iFrame "%"; iExists hs.
  rewrite bi.and_comm bi.and_assoc.
  iSplit; last by iDestruct "H" as "[_ $]".
  rewrite (bi.and_comm (funspec_sub_si _ _)).
  iApply funspec_sub_si_trans.
  iDestruct "H" as "[$ _]".
Qed.

Lemma func_ptr_mono fs gs v: funspec_sub fs gs ->
      func_ptr fs v ⊢ func_ptr gs v.
Proof.
  intros; rewrite /func_ptr.
  iIntros "H"; iDestruct "H" as (?? hs ?) "H".
  iExists b; iSplit; first done; iExists hs; iFrame; iPureIntro.
  split; auto; eapply funspec_sub_trans; eauto.
Qed.

Lemma funspec_sub_implies_func_prt_si_mono' fs gs v:
      ⌜funspec_sub fs gs⌝ ∧ func_ptr_si fs v ⊢ func_ptr_si gs v.
Proof.
  iIntros "[% ?]"; iApply func_ptr_si_mono.
  iFrame.
  by iSplit; auto; iApply funspec_sub_sub_si'.
Qed.

Lemma funspec_sub_implies_func_prt_si_mono fs gs v: funspec_sub fs gs ->
      func_ptr_si fs v ⊢ func_ptr_si gs v.
Proof.
  intros.
  iIntros "H"; iApply funspec_sub_implies_func_prt_si_mono'.
  by iFrame.
Qed.

Global Instance func_ptr_si_nonexpansive n : Proper (dist n ==> eq ==> dist n) func_ptr_si.
Proof.
  solve_proper.
Qed.

Lemma type_of_funspec_sub:
  forall fs1 fs2, funspec_sub fs1 fs2 ->
  type_of_funspec fs1 = type_of_funspec fs2.
Proof.
intros.
destruct fs1, fs2; destruct H as [(? & ?) _]. subst; simpl; auto.
Qed.

Lemma type_of_funspec_sub_si fs1 fs2:
  funspec_sub_si fs1 fs2 ⊢ ⌜type_of_funspec fs1 = type_of_funspec fs2⌝.
Proof.
destruct fs1, fs2; simpl.
by iIntros "[(-> & ->) _]".
Qed.

Lemma typesig_of_funspec_sub:
  forall fs1 fs2, funspec_sub fs1 fs2 ->
  typesig_of_funspec fs1 = typesig_of_funspec fs2.
Proof.
intros.
destruct fs1, fs2; destruct H as [[? ?] _]. subst; simpl; auto.
Qed.

Lemma typesig_of_funspec_sub_si fs1 fs2:
  funspec_sub_si fs1 fs2 ⊢ ⌜typesig_of_funspec fs1 = typesig_of_funspec fs2⌝.
Proof.
destruct fs1, fs2; simpl.
by iIntros "[(-> & ->) _]".
Qed.

Lemma typesig_of_funspec_sub_si2 fs1 fs2:
  (True ⊢ funspec_sub_si fs1 fs2) -> typesig_of_funspec fs1 = typesig_of_funspec fs2.
Proof.
intros. rewrite typesig_of_funspec_sub_si -(bi.True_intro emp) in H. by apply ouPred.pure_soundness in H.
Qed.

Lemma funspec_sub_si_ne : forall fs1 fs2, funspec_unfold fs1 ≡ funspec_unfold fs2 ⊢ bi_except_0 (funspec_sub_si fs1 fs2).
Proof.
  intros; iIntros "H".
  rewrite later_equivI funspec_equivI.
  iDestruct "H" as (????????) "H".
  rewrite !bi.later_and.
  iDestruct "H" as "(>(-> & ->) & #(HP & HQ))".
  iSplit; first done.
  iIntros (x gargs).
  iIntros "!> !> !>".
  rewrite !ofe_morO_equivI.
  iSpecialize ("HP" $! x); iSpecialize ("HQ" $! x).
  rewrite !discrete_fun_equivI.
  iSpecialize ("HP" $! gargs).
  iRewrite -"HP"; iIntros "(% & H) !>".
  iExists x, emp; iFrame.
  iSplit; first done; iSplit; first done.
  iIntros (rho) "!> (_ & _ & H)".
  iSpecialize ("HQ" $! rho); iRewrite -"HQ"; done.
Qed.

Program Definition closed_wrt_vars `{Equiv B} (S: ident -> Prop) (F: environ -> B) : Prop :=
  forall rho te',
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     (F rho ≡ F (mkEnviron (ge_of rho) (ve_of rho) te'))%stdpp.

Definition closed_wrt_lvars `{Equiv B} (S: ident -> Prop) (F: environ -> B) : Prop :=
  forall rho ve',
     (forall i, S i \/ Map.get (ve_of rho) i = Map.get ve' i) ->
     (F rho ≡ F (mkEnviron (ge_of rho) ve' (te_of rho)))%stdpp.

Definition not_a_param (params: list (ident * type)) (i : ident) : Prop :=
  ~ In i (map (@fst _ _) params).

Definition is_a_local (vars: list (ident * type)) (i: ident) : Prop :=
  In  i (map (@fst _ _) vars) .

Definition typed_true (t: type) (v: val) : Prop := strict_bool_val v t = Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t = Some false.

Definition subst {A} (x: ident) (v: environ -> val) (P: environ -> A) : environ -> A :=
   fun s => P (env_set s x (v s)).

Lemma func_ptr_isptr: forall spec f, func_ptr spec f ⊢ ⌜val_lemmas.isptr f⌝.
Proof.
  intros.
  unfold func_ptr.
  destruct spec. by iIntros "H"; iDestruct "H" as (b ->) "_".
Qed.
Lemma func_ptr_si_isptr: forall spec f, func_ptr_si spec f ⊢ ⌜val_lemmas.isptr f⌝.
Proof.
  intros.
  unfold func_ptr_si.
  destruct spec. by iIntros "H"; iDestruct "H" as (b ->) "_".
Qed.

Lemma subst_extens:
  forall a v (P Q : assert), (P ⊢ Q) -> assert_of (subst a v P) ⊢ assert_of (subst a v Q).
Proof.
  unfold subst; constructor; intros; simpl.
  apply H.
Qed.

Definition funspecs_assert (FunSpecs: Maps.PTree.t funspec): assert :=
 assert_of (fun rho =>
   (□ (∀ id: ident, ∀ fs:funspec,  ⌜Maps.PTree.get id FunSpecs = Some fs⌝ →
            ∃ b:block,⌜Map.get (ge_of rho) id = Some b⌝ ∧ func_at fs (b,0)) ∗
   (∀ b fsig cc, sigcc_at fsig cc (b, 0) -∗
           ⌜∃ id, Map.get (ge_of rho) id = Some b ∧ ∃ fs, Maps.PTree.get id FunSpecs = Some fs⌝))).
(* We can substantiate this using the authoritative funspecs. *)

Definition globals_only (rho: environ) : environ := (mkEnviron (ge_of rho) (Map.empty _) (Map.empty _)).

Fixpoint make_args (il: list ident) (vl: list val) (rho: environ)  :=
  match il, vl with
  | nil, nil => globals_only rho
  | i::il', v::vl' => env_set (make_args il' vl' rho) i v
   | _ , _ => rho
  end.

Lemma ge_of_make_args:
    forall s a rho, ge_of (make_args s a rho) = ge_of rho.
Proof.
induction s; intros.
 destruct a; auto.
 simpl in *. destruct a0; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

Lemma ve_of_make_args:
    forall s a rho, length s = length a -> ve_of (make_args s a rho) = (Map.empty (block * type)).
Proof.
induction s; intros.
 destruct a; inv H; auto.
 simpl in *. destruct a0; inv H; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

Lemma same_FS_funspecs_assert:
  forall FS1 FS2,
     (forall id, FS1 !! id = FS2 !! id) ->
              funspecs_assert FS1 ⊣⊢ funspecs_assert FS2.
Proof.
assert (forall FS FS' rho,
             (forall id, FS !! id = FS' !! id) ->
             funspecs_assert FS rho ⊢ funspecs_assert FS' rho).
{ intros. rewrite /funspecs_assert.
  iIntros "(#H1 & H2)"; iSplitL "".
  - iIntros "!>" (??); rewrite -H //.
  - setoid_rewrite <- H; done. }
split=> rho; iSplit; iApply H; auto.
Qed.

Lemma funspecs_assert_rho:
  forall G rho rho', ge_of rho = ge_of rho' -> funspecs_assert G rho ⊢ funspecs_assert G rho'.
Proof. rewrite /funspecs_assert /=; intros. rewrite H; auto. Qed.

Definition callingconvention_of_funspec (phi:funspec): calling_convention :=
  match phi with
    mk_funspec sig cc _ _ _ _ => cc
  end.

(*Definition mask_of_funspec (phi:funspec): coPset :=
  match phi with
    mk_funspec _ _ E _ _ _ => E
  end.*)

(*
(************** INTERSECTION OF funspecs -- case ND  ************************)

(* --------------------------------- Binary case: 2 specs only ----------  *)
(*Called ndfs_merge  in hmacdrbg_spec_hmacdrbg.v*)

Definition funspec_intersection_ND fA cA A PA QA (FSA: funspec) (HFSA: FSA = mk_funspec fA cA A PA QA)
                    fB cB B PB QB (FSB: funspec) (HFSB: FSB = mk_funspec fB cB B PB QB): option funspec.
destruct (eq_dec fA fB); subst.
+ destruct (eq_dec cA cB); subst.
  - apply Some. eapply (mk_funspec fB cB (A+B)%type
        (fun x => match x with inl a => PA a | inr b => PB b end)
        (fun x => match x with inl a => QA a | inr b => QB b end)).
  - apply None.
+ apply None.
Defined.

(*The two rules S-inter1 and S-inter2 from page 206 of TAPL*)
Lemma funspec_intersection_ND_sub E {fA cA A PA QA fB cB B PB QB} f1 F1 f2 F2 f
      (I: funspec_intersection_ND fA cA A PA QA f1 F1 fB cB B PB QB f2 F2 = Some f):
  funspec_sub E f f1 /\ funspec_sub E f f2.
Proof.
  subst. unfold funspec_intersection_ND in I.
  destruct (eq_dec fA fB); [subst fB | discriminate].
  destruct (eq_dec cA cB); [subst cB | discriminate]. inv I.
  split.
  + split. split; trivial. intros. iIntros "[% ?] !>".
    iExists (inl x2), emp; iFrame.
    iPureIntro; split; auto; intros.
    iIntros "(? & ? & $)".
  + split. split; trivial. intros. iIntros "[% ?] !>".
    iExists (inr x2), emp; iFrame.
    iPureIntro; split; auto; intros.
    iIntros "(? & ? & $)".
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_intersection_ND_sub3 E {fA cA A PA QA fB cB B PB QB fC cC C PC QC} f1 F1 f2 F2 f
      (I: funspec_intersection_ND fA cA A PA QA f1 F1 fB cB B PB QB f2 F2 = Some f) g
      (G: g = mk_funspec fC cC C PC QC):
  funspec_sub E g f1 -> funspec_sub E g f2 -> funspec_sub E g f.
Proof.
  subst. intros. destruct H as [[? ?] G1]; subst fA cA. destruct H0 as [[? ?] G2]; subst fB cB.
  unfold funspec_intersection_ND in I. simpl in I.
  rewrite !eq_dec_refl in I. inv I. simpl. split; first done. intros.
  destruct x2 as [a | b]; [apply G1 | apply G2].
Qed.

(*-------------------- ND case, specification Sigma families --------------------- *)

Definition funspec_Sigma_ND (sig:typesig) (cc:calling_convention) (I:Type) (A : I -> Type)
           (Pre: forall i, A i -> argsassert)
           (Post: forall i, A i -> assert): funspec.
Proof.
  unshelve eapply (mk_funspec sig cc (sigT A) _ _).
  intros [i Ai]; apply (Pre _ Ai).
  intros [i Ai]; apply (Post _ Ai).
Defined.

(*The two rules S-inter1 and S-inter2 from page 206 of TAPL*)
Lemma funspec_Sigma_ND_sub E fsig cc I A Pre Post i:
  funspec_sub E (funspec_Sigma_ND fsig cc I A Pre Post) (mk_funspec' fsig cc (A i) (Pre i) (Post i)).
Proof.
  unfold funspec_Sigma_ND. split. split; trivial. intros; simpl in *.
  iIntros "[% ?] !>".
  iExists (existT i x2), emp; iFrame.
  iPureIntro; split; auto; intros.
  iIntros "(_ & _ & $)".
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_Sigma_ND_sub3 E fsig cc I A Pre Post g (i:I)
      (HI: forall i, funspec_sub E g (mk_funspec fsig cc (A i) (Pre i) (Post i))):
  funspec_sub E g (funspec_Sigma_ND fsig cc I A Pre Post).
Proof.
  assert (HIi := HI i). destruct g. destruct HIi as [[? ?] Hi]; subst sig cc.
  split. split; trivial.
  simpl; intros. clear i Hi. destruct x2 as [i Ai].
  specialize (HI i). destruct HI as [[_ _] Hi]. apply (Hi Ai gargs).
Qed.

Local Obligation Tactic := idtac.
(*Specialization of funspec_Sigma_ND to binary case, i.e. I=bool*)
Program Definition BinarySigma fsig cc (A B:Type)
        (PA: A -> argsassert) (QA: A -> assert)
        (PB: B -> argsassert) (QB: B -> assert): funspec :=
  funspec_Sigma_ND fsig cc bool _ _ _.
Next Obligation.
  intros sig cc A B PreA PostA PreB PostB x. destruct x. apply A. apply B.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? b X. destruct b; simpl in X. apply (PA X). apply (PB X).
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? b X. destruct b; simpl in X. apply (QA X). apply (QB X).
Defined.

Definition funspecspec_sub_antisym E (f g: funspec):= funspec_sub E f g /\ funspec_sub E g f.
  
Lemma Intersection_BinarySigma E sigA ccA A PA QA fsA PrfA sigB ccB B PB QB fsB PrfB f
      (F:  funspec_intersection_ND sigA ccA A PA QA fsA PrfA sigB ccB B PB QB fsB PrfB = Some f):
  sigA=sigB /\ ccA=ccB /\
  funspecspec_sub_antisym E f (BinarySigma sigA ccA A B PA QA PB QB).
Proof.
  unfold funspec_intersection_ND in F.
  destruct (eq_dec sigA sigB); [ subst sigA; split; trivial | discriminate].
  destruct (eq_dec ccA ccB); [ inv F; split; trivial | discriminate]. 
  split.
  + split. split; trivial. simpl; intros. destruct x2 as [i p].
    iIntros "[% ?] !>". destruct i; simpl in *.
  - iExists (inl p), emp; iFrame. iPureIntro; split; auto; intros.
    iIntros "(_ & _ & $)".
  - iExists (inr p), emp; iFrame. iPureIntro; split; auto; intros.
    iIntros "(_ & _ & $)".
  + split. split; trivial. intros. iIntros "[% ?] !>". destruct x2.
  - iExists (existT (P := BinarySigma_obligation_1 A B) true a), emp; iFrame. iPureIntro; split; auto; intros.
    iIntros "(_ & _ & $)".
  - iExists (existT (P := BinarySigma_obligation_1 A B) false b), emp; iFrame. iPureIntro; split; auto; intros.
    iIntros "(_ & _ & $)".
Qed.

Lemma Intersection_sameSigCC_Some sig cc A PA QA fsA PrfA B PB QB fsB PrfB:
  ~ funspec_intersection_ND sig cc A PA QA fsA PrfA sig cc B PB QB fsB PrfB  = None.
Proof.
  intros N. unfold funspec_intersection_ND in N.
  rewrite !eq_dec_refl in N; trivial. discriminate.
Qed.*)

(*-------------------Bifunctor version, binary case ------------*)

Notation dtfr := (@dtfr Σ).

Definition binarySUMmask {A1 A2}
           (P1: dtfr (MaskTT A1))
           (P2: dtfr (MaskTT A2)) :
    dtfr (MaskTT (@SigType bool (fun b => if b then A1 else A2))).
Proof.
  unshelve econstructor.
  - intros [b B]; destruct b; [apply (P1 B) | apply (P2 B)].
  - intros ? [? ?] [b ?] (? & Heq); simpl in *; subst; simpl in *.
    destruct b; intros; rewrite Heq //.
Defined.

Definition binarySUM {A1 A2}
           (P1: dtfr (AssertTT A1))
           (P2: dtfr (AssertTT A2)) :
    dtfr (AssertTT (@SigType bool (fun b => if b then A1 else A2))).
Proof.
  unshelve econstructor.
  - intros [b B]; destruct b; [apply (P1 B) | apply (P2 B)].
  - intros ? [? ?] [b ?] (? & Heq); simpl in *; subst; simpl in *.
    destruct b; intros; rewrite Heq //.
Defined.

Definition binarySUMArgs {A1 A2}
           (P1: dtfr (ArgsTT A1))
           (P2: dtfr (ArgsTT A2)) :
    dtfr (ArgsTT (@SigType bool (fun b => if b then A1 else A2))).
Proof.
  unshelve econstructor.
  - intros [b B]; destruct b; [apply (P1 B) | apply (P2 B)].
  - intros ? [? ?] [b ?] (? & Heq); simpl in *; subst; simpl in *.
    destruct b; intros; rewrite Heq //.
Defined.

Definition binary_intersection (phi psi: funspec) : option funspec :=
  match phi, psi with
  | mk_funspec f c A1 E1 P1 Q1, mk_funspec f2 c2 A2 E2 P2 Q2 =>
    if eq_dec f f2 then if eq_dec c c2 then
      Some (mk_funspec f c (@SigType bool (fun b => if b then A1 else A2)) (binarySUMmask E1 E2) (binarySUMArgs P1 P2) (binarySUM Q1 Q2))
    else None else None end.

Lemma callconv_of_binary_intersection {phi1 phi2 phi} (BI: binary_intersection phi1 phi2 = Some phi):
      callingconvention_of_funspec phi = callingconvention_of_funspec phi1 /\ 
      callingconvention_of_funspec phi = callingconvention_of_funspec phi2.
Proof. destruct phi1; destruct phi2; destruct phi; simpl in *.
 (*destruct (typesigs_match t t0); [ | discriminate].*) if_tac in BI; [ subst | inv BI].
 if_tac in BI; [ subst | inv BI].
 inv BI; split; trivial.
Qed.

Lemma funspectype_of_binary_intersection {phi1 phi2 phi} (BI: binary_intersection phi1 phi2 = Some phi):
      type_of_funspec phi1 = type_of_funspec phi /\ 
      type_of_funspec phi2 = type_of_funspec phi.
Proof. destruct phi1; destruct phi2; destruct phi; simpl in *. 
 (*remember  (typesigs_match t t0) as b; destruct b; [ | discriminate].*)
 if_tac in BI; [ subst | inv BI].
 if_tac in BI; [ subst | inv BI].
 inv BI. split; trivial.
 (*symmetry in Heqb. clear H4 H5.
 apply typesigs_match_typesigs_eq in Heqb; subst; trivial.*)
Qed.
(*
Lemma binary_intersection_typesigs_match {phi1 phi2 phi} (BI : binary_intersection phi1 phi2 = Some phi):
      typesigs_match (typesig_of_Newfunspec phi1) (typesig_of_Newfunspec phi2) = true.
Proof.
  destruct phi1; destruct phi2. simpl in *.
  destruct (typesigs_match t t0); [ trivial | discriminate].
Qed.
*)
Lemma binary_intersection_typesig {phi1 phi2 phi} (BI : binary_intersection phi1 phi2 = Some phi):
      typesig_of_funspec phi1 = typesig_of_funspec phi.
Proof.
  destruct phi1; destruct phi2. simpl in *.
  if_tac in BI; [ subst | inv BI].
  if_tac in BI; [ subst | inv BI].
  inv BI. trivial.
Qed. 

Lemma binary_intersection_typesigs {phi1 phi2 phi} (BI : binary_intersection phi1 phi2 = Some phi):
      typesig_of_funspec phi1 = typesig_of_funspec phi /\ typesig_of_funspec phi2 = typesig_of_funspec phi.
Proof.
  destruct phi1; destruct phi2. simpl in *.
  if_tac in BI; [ subst | inv BI].
  if_tac in BI; [ subst | inv BI].
  inv BI; split; trivial.
Qed.

Import EqNotations.

Lemma mk_funspec_inj : forall {PROP1} {C1 : Cofe PROP1} {PROP2} {C2 : Cofe PROP2} sig1 sig2 cc1 cc2 A1 A2 E1 E2 P1 P2 Q1 Q2,
  @mk_funspec PROP1 C1 PROP2 C2 sig1 cc1 A1 E1 P1 Q1 = mk_funspec sig2 cc2 A2 E2 P2 Q2 ->
  sig1 = sig2 /\ cc1 = cc2 /\ exists H : A1 = A2, rew E_eq H in E1 = E2 /\ rew pre_eq H in P1 = P2 /\ rew post_eq H in Q1 = Q2.
Proof.
  intros.
  injection H as H; subst.
  repeat split; auto; exists eq_refl; simpl.
  repeat match goal with H : existT _ _ = existT _ _ |- _ => apply inj_pair2 in H end; done.
Qed.

Lemma binaryintersection_sub phi psi omega:
  binary_intersection phi psi = Some omega ->
  funspec_sub omega phi /\ funspec_sub omega psi.
Proof.
  destruct phi as [f1 c1 A1 E1 P1 Q1].
  destruct psi as [f2 c2 A2 E2 P2 Q2].
  destruct omega as [f c A E P Q]. intros.
  simpl in H.
  destruct (eq_dec f1 f2); [subst f2 | inv H].
  destruct (eq_dec c1 c2); [subst c2 | inv H].
  apply Some_inj, mk_funspec_inj in H as (<- & <- & <- & ? & ? & ?).
  simpl in *; subst; split.
  + split; [split3; trivial | intros].
    iIntros "(% & P) !>".
    iExists (existT true x2), emp.
    rewrite bi.emp_sep.
    iSplit; first done.
    iSplit; first done.
    iPureIntro; simpl.
    intros; iIntros "(% & _ & $)".
  + split; [split3; trivial | intros].
    iIntros "(% & P) !>".
    iExists (existT false x2), emp.
    rewrite bi.emp_sep.
    iSplit; first done.
    iSplit; first done.
    iPureIntro; simpl.
    intros; iIntros "(% & _ & $)".
Qed.

Lemma BINARY_intersection_sub3 phi psi omega:
  binary_intersection phi psi = Some omega ->
  forall xi, funspec_sub xi phi -> funspec_sub xi psi -> funspec_sub xi omega.
Proof.
  intros.
  destruct phi as [f1 c1 A1 E1 P1 Q1].
  destruct psi as [f2 c2 A2 E2 P2 Q2].
  destruct omega as [f c A E P Q].
  simpl in H.
  destruct (eq_dec f1 f2); [subst f2 | inv H].
  destruct (eq_dec c1 c2); [subst c2 | inv H].
  apply Some_inj, mk_funspec_inj in H as (<- & <- & <- & ? & ? & ?); simpl in *; subst.
  destruct xi as [f' c' A' E' P' Q'].
  destruct H0 as [(? & ?) ?]; subst f' c'.
  destruct H1 as [(_ & _) ?].
  split; [split3; trivial | intros].
  destruct x2 as [[|] ?]; eauto.
Qed.

(****A variant that is a bit more computational - maybe should replace the original definition above?*)
Definition binary_intersection' {f c A1 E1 P1 Q1 A2 E2 P2 Q2} phi psi
  (Hphi: phi = mk_funspec f c A1 E1 P1 Q1) (Hpsi: psi = mk_funspec f c A2 E2 P2 Q2): funspec :=
  mk_funspec f c (@SigType bool (fun b => if b then A1 else A2)) (@binarySUMmask A1 A2 E1 E2) (@binarySUMArgs A1 A2 P1 P2) (binarySUM Q1 Q2).

Lemma binary_intersection'_sound {f c A1 E1 P1 Q1 A2 E2 P2 Q2} phi psi
  (Hphi: phi = mk_funspec f c A1 E1 P1 Q1) (Hpsi: psi = mk_funspec f c A2 E2 P2 Q2):
    binary_intersection phi psi = Some (binary_intersection' phi psi Hphi Hpsi).
Proof.
  unfold binary_intersection, binary_intersection'. subst phi psi. rewrite !if_true //.
Qed.
Lemma binary_intersection'_complete phi psi tau:
   binary_intersection phi psi = Some tau ->
   exists f c A1 E1 P1 Q1 A2 E2 P2 Q2 Hphi Hpsi,
   tau = @binary_intersection' f c A1 E1 P1 Q1 A2 E2 P2 Q2 phi psi Hphi Hpsi.
Proof.
unfold binary_intersection, binary_intersection'.
destruct phi, psi. do 2 (if_tac; last discriminate).
intros X. inv X.
repeat eexists.
Qed.

Lemma binary_intersection'_sub  {f c A1 E1 P1 Q1 A2 E2 P2 Q2} (phi psi:funspec) Hphi Hpsi:
  funspec_sub (@binary_intersection' f c A1 E1 P1 Q1 A2 E2 P2 Q2 phi psi Hphi Hpsi) phi /\
  funspec_sub (@binary_intersection' f c A1 E1 P1 Q1 A2 E2 P2 Q2 phi psi Hphi Hpsi) psi.
Proof. apply binaryintersection_sub. apply binary_intersection'_sound. Qed.

Lemma binary_intersection'_sub3 {f c A1 E1 P1 Q1 A2 E2 P2 Q2} phi psi Hphi Hpsi:
  forall xi, funspec_sub xi phi -> funspec_sub xi psi -> 
  funspec_sub xi (@binary_intersection' f c A1 E1 P1 Q1 A2 E2 P2 Q2 phi psi Hphi Hpsi).
Proof. intros. eapply BINARY_intersection_sub3. apply binary_intersection'_sound. apply H. apply H0. Qed.

(*-------------------Bifunctor version, general case ------------*)

Definition generalSUMmask {I} (Ai: I -> TypeTree)
           (P: forall i, dtfr (MaskTT (Ai i))):
    dtfr (MaskTT (@SigType I Ai)).
Proof.
  unshelve econstructor.
  - intros [i Hi]. apply (P i Hi).
  - intros ? [? ?] [i ?] (? & Heq); simpl in *; subst; simpl in *.
    rewrite Heq //.
Defined.

Definition generalSUM {I} (Ai: I -> TypeTree)
           (P: forall i, dtfr (AssertTT (Ai i))):
    dtfr (AssertTT (@SigType I Ai)).
Proof.
  unshelve econstructor.
  - intros [i Hi]. apply (P i Hi).
  - intros ? [? ?] [i ?] (? & Heq); simpl in *; subst; simpl in *.
    rewrite Heq //.
Defined.

Definition generalSUMArgs {I} (Ai: I -> TypeTree)
           (P: forall i, dtfr (ArgsTT (Ai i))):
    dtfr (ArgsTT (@SigType I Ai)).
Proof.
  unshelve econstructor.
  - intros [i Hi]. apply (P i Hi).
  - intros ? [? ?] [i ?] (? & Heq); simpl in *; subst; simpl in *.
    rewrite Heq //.
Defined.

Definition WithType_of_funspec (phi:funspec):TypeTree :=
  match phi with
    mk_funspec sig cc A _ _ _ => A
  end.

Definition mask_of_funspec (phi: funspec) : dtfr (MaskTT (WithType_of_funspec phi)) :=
  match phi with mk_funspec _ _ A E _ _ => E end.

Definition Pre_of_funspec (phi: funspec) : dtfr (ArgsTT (WithType_of_funspec phi)) :=
  match phi with mk_funspec _ _ _ A P _ => P end.

Definition Post_of_funspec (phi: funspec) : dtfr (AssertTT (WithType_of_funspec phi)) :=
  match phi with mk_funspec _ _ A _ _ Q => Q end.

Definition intersectionMask {I} phi:
  forall (i : I),
    dtfr (MaskTT (WithType_of_funspec (phi i))).
Proof.
  intros i. destruct (phi i) as  [fi ci A_i Ei Pi Qi]. apply Ei.
Defined.

Definition intersectionPRE {I} phi:
  forall (i : I),
    dtfr (ArgsTT (WithType_of_funspec (phi i))).
Proof.
  intros i. destruct (phi i) as  [fi ci A_i Ei Pi Qi]. apply Pi.
Defined.

Definition intersectionPOST {I} phi:
  forall (i : I),
    dtfr (AssertTT (WithType_of_funspec (phi i))).
Proof.
  intros i. destruct (phi i) as  [fi ci A_i Ei Pi Qi]. apply Qi.
Defined.

Definition iMask {I} phi:
        dtfr (MaskTT (SigType I (fun i => WithType_of_funspec (phi i)))).
Proof. intros. apply (generalSUMmask _ (intersectionMask phi)). Defined.

Definition iPre {I} phi:
        dtfr (ArgsTT (SigType I (fun i => WithType_of_funspec (phi i)))).
Proof. intros. apply (generalSUMArgs _ (intersectionPRE phi)). Defined.

Definition iPost {I} phi:
        dtfr (AssertTT (SigType I (fun i => WithType_of_funspec (phi i)))).
Proof. intros. apply (generalSUM _ (intersectionPOST phi)). Defined.

Definition general_intersection {I sig cc} (phi: I -> funspec) 
           (Hsig: forall i, typesig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc) : funspec.
Proof.
  apply (mk_funspec sig cc
                    (SigType I (fun i => WithType_of_funspec (phi i)))
                    (iMask phi) (iPre phi) (iPost phi)).
Defined.

Lemma generalintersection_sub {I sig cc} (phi: I -> funspec)
           (Hsig: forall i, typesig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc)
           omega:
  general_intersection phi Hsig Hcc = omega ->
  forall i,  funspec_sub omega (phi i).
Proof.
  intros; subst. hnf.
  specialize (Hsig i); specialize (Hcc i); subst.
  remember (phi i) as zz; destruct zz. split; [split3; trivial | intros].
  iIntros "(% & ?) !>".
  assert (exists D: dtfr (WithType_of_funspec (phi i)), JMeq.JMeq x2 D) as (D & HD).
  { rewrite <- Heqzz. simpl. exists x2. constructor. }
  unfold iPre, intersectionPRE, generalSUM.
  iExists (existT i D), emp.
  rewrite bi.emp_sep. iSplit; simpl.
  { unfold intersectionMask.
    destruct (phi i); simpl in *.
    inv Heqzz.
    apply inj_pair2 in H4; subst; auto. }
  iSplit.
  + destruct (phi i).
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5; subst; trivial.
  + iPureIntro; intros; rewrite bi.emp_sep. unfold intersectionPOST.
    iIntros "(% & ?)". destruct (phi i).
    simpl in *; inv Heqzz.
    apply inj_pair2 in H7; subst; trivial.
Qed.

Lemma generalintersection_sub3  {I sig cc}
      (INH: inhabited I) (phi: I -> funspec)
           (Hsig: forall i, typesig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc)
           omega:
  general_intersection phi Hsig Hcc = omega ->
  forall xi, (forall i, funspec_sub xi (phi i)) -> funspec_sub xi omega.
Proof.
  intros. subst. inv INH; rename X into i.
  unfold general_intersection.
  destruct xi as [f c A E P Q].
  split.
  { split.
    + specialize (H0 i); specialize (Hsig i). destruct (phi i); subst; apply H0.
    + specialize (H0 i); specialize (Hcc i). destruct (phi i); subst; apply H0. }
  intros. clear i. destruct x2 as [i Hi].
  specialize (H0 i); specialize (Hsig i); specialize (Hcc i); subst; simpl.
  unfold intersectionMask, intersectionPRE, intersectionPOST.
  forget (phi i) as zz. clear phi.
  destruct zz. simpl in *.
  destruct H0 as [[? ?] H1]; subst.
  apply (H1 Hi gargs).
Qed.

Lemma make_context_t_get: forall {params temps i ty} 
      (T: (make_tycontext_t params temps) !! i = Some ty),
      In i (map fst params ++ map fst temps).
Proof.
  induction params; simpl; intros.
* induction temps; simpl in *. rewrite Maps.PTree.gempty in T; discriminate. 
  destruct a; simpl in *. rewrite Maps.PTree.gsspec in T.
  destruct (peq i i0); subst. left; trivial. right; auto.
* destruct a; simpl in *. rewrite Maps.PTree.gsspec in T.
  destruct (peq i i0); subst. left; trivial.
  right. eapply IHparams. apply T.
Qed.

Lemma tc_temp_environ_elim: forall {params temps trho},
      list_norepet (map fst params ++ map fst temps) ->
      typecheck_temp_environ trho (make_tycontext_t params temps) ->
      forall i ty, In (i,ty) params -> 
      exists v : val, Map.get trho i = Some v /\ tc_val' ty v.
Proof.
  induction params.
  + intros. inv H1.
  + simpl. intros. destruct H1.
    - subst a. simpl in *. apply (H0 i ty). rewrite Maps.PTree.gss; trivial.
    - inv H. apply (IHparams temps); trivial.
      red; intros j ? ?. apply H0. rewrite Maps.PTree.gso; trivial. clear - H4 H.
      intros J; subst. destruct a; simpl in *. apply H4; clear - H.
      apply (make_context_t_get H).
Qed.

Lemma tc_environ_rettype t rho: tc_environ (rettype_tycontext t) (globals_only rho).
Proof.
  unfold rettype_tycontext; simpl. split3; intros; simpl.
  red; intros. rewrite Maps.PTree.gempty in H; congruence.
  split; intros. rewrite Maps.PTree.gempty in H; congruence. destruct H; inv H.
  red; intros. rewrite Maps.PTree.gempty in H; congruence.
Qed.

Lemma tc_environ_rettype_env_set t rho i v:
tc_environ (rettype_tycontext t)
         (env_set (globals_only rho) i v).
Proof.
  unfold rettype_tycontext; simpl. split3; intros; simpl.
  red; intros. rewrite Maps.PTree.gempty in H; congruence.
  split; intros. rewrite Maps.PTree.gempty in H; congruence. destruct H; inv H.
  red; intros. rewrite Maps.PTree.gempty in H; congruence.
Qed.

Lemma funspec_sub_cc phi psi: funspec_sub phi psi ->
      callingconvention_of_funspec phi = callingconvention_of_funspec psi.
Proof. destruct phi; destruct psi; simpl. intros [[_ ?] _]; trivial. Qed.

Lemma funspec_sub_si_cc phi psi: (True ⊢ funspec_sub_si phi psi) ->
      callingconvention_of_funspec phi = callingconvention_of_funspec psi.
Proof.
  destruct phi; destruct psi; simpl. intros.
  rewrite -(bi.True_intro emp) bi.and_elim_l in H. apply ouPred.pure_soundness in H as (? & ?); done.
Qed.

Lemma later_func_ptr_si phi psi (H: True ⊢ funspec_sub_si phi psi) v:
      ▷ (func_ptr_si phi v) ⊢ ▷ (func_ptr_si psi v).
Proof.
  iIntros "H !>".
  iApply func_ptr_si_mono.
  iSplit; auto.
  by iApply H.
Qed.

Lemma later_func_ptr_si' phi psi v:
      ▷ (funspec_sub_si phi psi ∧ func_ptr_si phi v) ⊢ ▷ (func_ptr_si psi v).
Proof.
  iIntros "H !>".
  by iApply func_ptr_si_mono.
Qed.

Lemma func_ptr_emp phi v: func_ptr phi v ⊢ emp.
Proof. iIntros. done. Qed.

Lemma split_func_ptr:  forall fs p, func_ptr fs p ⊣⊢ func_ptr fs p ∗ func_ptr fs p.
Proof.
intros; apply bi.persistent_sep_dup; apply _.
Qed.

End mpred.
