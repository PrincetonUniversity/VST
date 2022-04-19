Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Require Import VST.veric.mpred.
Require Import VST.veric.address_conflict.
Require Export VST.veric.shares.
Require Import VST.veric.Cop2. (*for definition of tc_val'*)
Require Import VST.veric.own.
Require Import VST.veric.invariants.
Require Import VST.veric.fupd.
Import compcert.lib.Maps.

Local Open Scope pred.

(* Diagnostic tactic, useful because intuition can be much slower than tauto 
Tactic Notation "intuition" :=
 try (solve [tauto]; idtac "Intuition used where tauto would work");
 Coq.Init.Tauto.intuition.
*)

Lemma derives_emp_unfash_fash P Q: derives P Q  -> derives emp (unfash (fash (imp P Q))).
Proof. repeat intro. eauto. Qed.

Lemma derives_unfash_fash R P Q: derives P Q  -> derives R (unfash (fash (imp P Q))).
Proof. repeat intro. eauto. Qed.

Lemma eqp_subp : forall (P Q:mpred), P <=> Q |-- P >=> Q.
intros. eapply eqp_subp. trivial. Qed.

(*******************material moved here from tycontext.v *******************)

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

Inductive tycontext : Type :=
  mk_tycontext : forall (tyc_temps: PTree.t type)
                        (tyc_vars: PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: PTree.t type)
                        (tyc_globsp: PTree.t funspec)
                        (tyc_annot: PTree.t Annotation),
                             tycontext.

Definition empty_tycontext : tycontext :=
  mk_tycontext (PTree.empty _) (PTree.empty _) Ctypes.Tvoid
         (PTree.empty _)  (PTree.empty _) (PTree.empty _).

Definition temp_types (Delta: tycontext): PTree.t type :=
  match Delta with mk_tycontext a _ _ _ _ _ => a end.
Definition var_types (Delta: tycontext) : PTree.t type :=
  match Delta with mk_tycontext _ a _ _ _ _ => a end.
Definition ret_type (Delta: tycontext) : type :=
  match Delta with mk_tycontext _ _ a _ _ _ => a end.
Definition glob_types (Delta: tycontext) : PTree.t type :=
  match Delta with mk_tycontext _ _ _ a _ _ => a end.
Definition glob_specs (Delta: tycontext) : PTree.t funspec :=
  match Delta with mk_tycontext _ _ _ _ a _ => a end.
Definition annotations (Delta: tycontext) : PTree.t Annotation :=
  match Delta with mk_tycontext _ _ _ _ _ a => a end.

(** Creates a typecontext from a function definition **)
(* NOTE:  params start out initialized, temps do not! *)

Definition make_tycontext_t (params: list (ident*type)) (temps : list(ident*type)) :=
fold_right (fun (param: ident*type) => PTree.set (fst param) (snd param))
 (fold_right (fun (temp : ident *type) tenv => let (id,ty):= temp in PTree.set id ty tenv)
  (PTree.empty type) temps) params.

Definition make_tycontext_v (vars : list (ident * type)) :=
 fold_right (fun (var : ident * type) venv => let (id, ty) := var in PTree.set id ty venv)
   (PTree.empty type) vars.

Definition make_tycontext_g (V: varspecs) (G: funspecs) :=
 (fold_right (fun (var : ident * funspec) => PTree.set (fst var) (type_of_funspec (snd var)))
      (fold_right (fun (v: ident * type) => PTree.set (fst v) (snd v))
         (PTree.empty _) V)
            G).

Definition make_tycontext_a (anns : list (ident * Annotation)) :=
 fold_right (fun (ia : ident * Annotation) aenv => let (id, a) := ia in PTree.set id a aenv)
   (PTree.empty Annotation) anns.

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
(te: tenviron) (tc: PTree.t type) :=
forall id ty , tc ! id = Some ty  -> exists v, Map.get te id = Some v /\ tc_val' ty v.

Definition typecheck_var_environ
(ve: venviron) (tc: PTree.t type) :=
forall id ty, tc ! id = Some ty <-> exists v, Map.get ve id = Some(v,ty).

Definition typecheck_glob_environ
(ge: genviron) (tc: PTree.t type) :=
forall id  t,  tc ! id = Some t ->
(exists b, Map.get ge id = Some b).

Definition typecheck_environ (Delta: tycontext) (rho : environ) :=
typecheck_temp_environ (te_of rho) (temp_types Delta) /\
typecheck_var_environ  (ve_of rho) (var_types Delta) /\
typecheck_glob_environ (ge_of rho) (glob_types Delta).

Definition local:  (environ -> Prop) -> environ->mpred :=  lift1 prop.

Definition tc_environ (Delta: tycontext) : environ -> Prop :=
   fun rho => typecheck_environ Delta rho.

Definition funsig_tycontext (fs: funsig) : tycontext :=
  make_tycontext (fst fs) nil nil (snd fs) nil nil nil.
(*
Definition funsig_of_funspec (fs: funspec) : funsig :=
 match fs with mk_funspec fsig _ _ _ _ _ _ => fsig end.
*)
Definition ret0_tycon (Delta: tycontext): tycontext :=
  mk_tycontext (PTree.empty _) (PTree.empty _) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta).

Definition typesig_of_funspec (fs: funspec) : typesig :=
 match fs with mk_funspec fsig _ _ _ _ _ _ => fsig end.

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
unfold typecheck_glob_environ. apply prop_ext; split; intros. apply H.
split; trivial. intros. rewrite PTree.gempty in H0. congruence.
Qed.

Lemma fssub_prop2: forall rt rho, (local (tc_environ (rettype_tycontext rt)) rho) = !!(ve_of rho = Map.empty (block * type)).
intros. unfold local, tc_environ, lift1.
unfold rettype_tycontext, typecheck_environ, typecheck_temp_environ,
typecheck_var_environ, typecheck_glob_environ.
simpl.
destruct rho; simpl. apply pred_ext. 
intros u U. simpl in U. simpl. destruct U as [? [? ?]].
apply Map.ext. intros. clear H H1. specialize (H0 x).
destruct (Map.get ve); simpl in *. 
destruct p.  destruct (H0 t); clear H0. clear H.
exfalso. exploit H1. eexists; reflexivity. rewrite PTree.gempty. congruence.
reflexivity.
intros u U. simpl in *. subst. split3; intros.
 rewrite PTree.gempty in H; congruence.
 split; intros. rewrite PTree.gempty in H; congruence.
 destruct H.  inv H.
 rewrite PTree.gempty in H. congruence.
Qed.

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
        !!(tpsig1=tpsig2 /\ cc1=cc2) &&
    |>   ! (ALL ts2 :_, ALL x2:dependent_type_functor_rec ts2 A2 mpred,
             ALL gargs:genviron * list val,
        ((!!(tc_argsenv Delta2 (fst tpsig2) gargs) && P2 ts2 x2 gargs)
         >=> EX ts1:_,  EX x1:dependent_type_functor_rec ts1 A1 mpred, EX F:_, 
            (F * (P1 ts1 x1 gargs)) &&
            ALL rho':_, (     !( ((local (tc_environ (rettype_tycontext (snd tpsig1))) rho') && (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho')))))
    end
end.
Definition funspec_sub_si_AUX1 (f1 f2 : funspec):mpred :=
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
       let Delta := rettype_tycontext (snd tpsig1) in
        !!(tpsig1=tpsig2 /\ cc1=cc2) &&
        ! (ALL ts2 :_, ALL x2:dependent_type_functor_rec ts2 A2 mpred,
             ALL gargs:genviron * list val,
        ((!!(tc_argsenv Delta (fst tpsig1) gargs) && P2 ts2 x2 gargs)
         >=> EX ts1:_,  EX x1:_, EX F:_, 
            (F * (P1 ts1 x1 gargs)) &&
            ALL rho':_, (     !( ((local (tc_environ Delta) rho') && (F * (Q1 ts1 x1 rho')))
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
        !!(tpsig1=tpsig2 /\ cc1=cc2) &&
        ! (ALL ts2 :_, ALL x2:dependent_type_functor_rec ts2 A2 mpred,
             ALL gargs:genviron * list val,
        ((!!(Forall2 tc_val' (fst tpsig1) (snd gargs)) && P2 ts2 x2 gargs)
         >=> EX ts1:_,  EX x1:_, EX F:_, 
            (F * (P1 ts1 x1 gargs)) &&
            ALL rho':_, (     !( ((!!(ve_of rho' = Map.empty (block * type))) && (F * (Q1 ts1 x1 rho')))
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

Notation fupd := (fupd Ensembles.Full_set Ensembles.Full_set).

Section invs.
Context {inv_names : invG}.

Definition funspec_sub_si (f1 f2 : funspec):mpred :=
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
        !!(tpsig1=tpsig2 /\ cc1=cc2) &&
       |>  ! (ALL ts2 :_, ALL x2:dependent_type_functor_rec ts2 A2 mpred,
             ALL gargs:genviron * list val,
        ((!!(argsHaveTyps (snd gargs) (fst tpsig1)) && P2 ts2 x2 gargs)
         >=> fupd (EX ts1:_, EX x1:_, EX F:_, 
            (F * (P1 ts1 x1 gargs)) &&
            ALL rho':_, (     !( ((!!(ve_of rho' = Map.empty (block * type))) && (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho'))))))
    end
end.

Definition funspec_sub (f1 f2 : funspec): Prop :=
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
        (tpsig1=tpsig2 /\ cc1=cc2) /\
        forall ts2 (x2:dependent_type_functor_rec ts2 A2 mpred) (gargs:argsEnviron),
        ((!! (argsHaveTyps(snd gargs)(fst tpsig1)) && P2 ts2 x2 gargs)
         |-- fupd (EX ts1:_,  EX (x1:dependent_type_functor_rec ts1 A1 mpred), EX F:_, 
                           (F * (P1 ts1 x1 gargs)) &&
                               (!! (forall rho',
                                           ((!!(ve_of rho' = Map.empty (block * type))) &&
                                                 (F * (Q1 ts1 x1 rho')))
                                         |-- (Q2 ts2 x2 rho')))))
    end
end.

Lemma funspec_sub_sub_si f1 f2: funspec_sub f1 f2 -> TT |-- funspec_sub_si f1 f2.
Proof.
  intros. destruct f1; destruct f2; simpl in *.
  destruct H as [[? ?] H']; subst. intros w _. split; [split; trivial |].
  intros w' Hw'.
  intros ts2 x2 rho y WY k YK N E K.
  apply H' in K.
  eapply fupd_mono, K.
  repeat (apply exp_derives; intros).
  apply andp_derives; auto.
  intros ? H rho' v KV z VZ Z EZ. apply H; trivial.
Qed.

Lemma funspec_sub_sub_si' f1 f2: !!(funspec_sub f1 f2) |-- funspec_sub_si f1 f2.
Proof. intros w W. apply funspec_sub_sub_si; trivial. Qed.
(*
Lemma funspec_sub_early_sub_si f1 f2: funspec_sub_early f1 f2 |-- funspec_sub_si f1 f2.
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
  destruct f; split; [ split; trivial | intros ts2 x2 rho w [T W]].
  apply fupd_intro.
  exists ts2, x2, emp. rewrite emp_sepcon. split; trivial. hnf; intros. 
  rewrite emp_sepcon. apply andp_left2, derives_refl.
Qed.

Lemma funspec_sub_trans f1 f2 f3: funspec_sub f1 f2 -> 
      funspec_sub f2 f3 -> funspec_sub f1 f3.
Proof.
  destruct f1; destruct f2; destruct f3; intros.
  destruct H as [[? ?] H12]; subst t0 c0.
  destruct H0 as [[? ?] H23]; subst t1 c1.
  split; [ split; trivial | intros ts x rho].
  apply prop_andp_left; intro Hlocal.
  eapply derives_trans.
  { eapply derives_trans, H23; apply andp_right; eauto; intros ??; auto. }
  eapply derives_trans, fupd_trans; apply fupd_mono.
  apply exp_left; intro ts1.
  apply exp_left; intro x1.
  apply exp_left; intro F.
  eapply derives_trans; [apply andp_derives, derives_refl|].
  { eapply sepcon_derives, derives_trans, H12; [apply derives_refl|].
    apply andp_right; eauto; intros ??; auto. }
  rewrite andp_comm, <- normalize.sepcon_andp_prop'.
  eapply derives_trans; [apply fupd_frame_l | apply fupd_mono].
  rewrite exp_sepcon2; apply exp_left; intros ts2.
  rewrite exp_sepcon2; apply exp_left; intros x2.
  rewrite exp_sepcon2; apply exp_left; intros G.
  apply exp_right with ts2; apply exp_right with x2; apply exp_right with (F*G).
  rewrite normalize.sepcon_andp_prop'.
  rewrite (andp_comm _ (!! _)), sepcon_andp_prop.
  rewrite <- andp_assoc, andp_comm; apply andp_derives.
  { rewrite sepcon_assoc; auto. }
  intros ? [H1 H2]; simpl in *.
  intros rho'; eapply derives_trans, H1.
  apply prop_andp_left; intros Hlocal'.
  unfold local; simpl; unfold lift1; simpl.
  apply andp_right; [intros ??; auto|].
  rewrite sepcon_assoc; eapply sepcon_derives, derives_trans, H2; auto.
  apply andp_right; auto; intros ??; auto.
Qed.

Lemma unfash_allp':  forall {A} {agA: ageable A} {EO: Ext_ord A} {B} (f: B -> pred nat),
  @unfash _ agA EO (allp f) = allp (fun x:B => unfash (f x)).
Proof.
intros.
apply pred_ext.
intros ? ? ?.
specialize (H b). auto.
repeat intro. apply (H b).
Qed.

Lemma allp_andp1: forall {A} {agA: ageable A} {EO: Ext_ord A} {B} (P : B -> pred A) Q, (ALL a : B, P a) && Q |-- ALL a : B, P a && Q.
Proof.
  intros; apply allp_right; intro x.
  apply andp_derives; auto.
  apply allp_left with x; auto.
Qed.

Lemma unfash_exp:  forall {A} {agA: ageable A} {EO: Ext_ord A} {B} (f: B -> pred nat),
  @unfash _ agA EO (exp f) = exp (fun x:B => unfash (f x)).
Proof.
intros.
apply pred_ext.
intros ? [? ?]; simpl; eauto.
intros ? [? ?]; simpl in *; eauto.
Qed.

Lemma unfash_andp:  forall {A} {agA: ageable A} {EO: Ext_ord A} (P Q : pred nat),
  @unfash _ agA EO (andp P Q) = andp (unfash P) (unfash Q).
Proof.
intros.
apply pred_ext; intros ? []; split; auto.
Qed.

Lemma allp_sepcon1': forall {A} (P : A -> pred rmap) Q, (ALL x : A, P x) * Q |-- ALL x : A, P x * Q.
Proof.
  intros.
  apply allp_right; intro x.
  apply sepcon_derives; auto.
  apply allp_left with x; auto.
Qed.

Lemma unfash_sepcon: forall P (Q : pred rmap), !P * Q |-- !P.
Proof.
  intros ??? (? & ? & J & ? & ?); simpl in *.
  apply join_level in J as [<- _]; auto.
Qed.

Lemma subp_exp_left: forall {A} G P Q, (forall x, G |-- P x >=> Q) -> G |-- (EX x : A, P x) >=> Q.
Proof.
  repeat intro.
  destruct H4 as [x HP].
  eapply H; eauto.
Qed.

Lemma funspec_sub_si_refl f: TT |-- funspec_sub_si f f.
Proof.
  destruct f; split; [split; trivial |].
  intros a' Ha'.
  clear H. intros ts2 x2 rho.
  intros y Hy z ? Hz Hz' [_ ?]. apply fupd_intro.
  exists ts2, x2, emp; rewrite emp_sepcon. split; auto.
  intros rho' k WK u ? necKU E Z.
  rewrite emp_sepcon in Z. apply Z.
Qed.

Lemma funspec_sub_si_trans f1 f2 f3: funspec_sub_si f1 f2 && funspec_sub_si f2 f3 |--
      funspec_sub_si f1 f3.
Proof. destruct f1; destruct f2; destruct f3.
unfold funspec_sub_si; simpl.
rewrite !andp_assoc; apply prop_andp_left; intros []; subst.
rewrite andp_comm, andp_assoc; apply prop_andp_left; intros []; subst.
apply andp_right; [intros ??; simpl; auto|].
rewrite <- later_andp. apply later_derives.
rewrite <- unfash_andp; apply unfash_derives.
apply allp_right; intros ts.
apply allp_right; intros x.
apply allp_right; intros rho.
eapply derives_trans; [apply allp_andp1|].
apply allp_left with ts.
eapply derives_trans; [apply allp_andp1|].
apply allp_left with x.
eapply derives_trans; [apply allp_andp1|].
apply allp_left with rho.
eapply subp_trans.
{ apply andp_left1.
  rewrite <- (andp_dup (!! argsHaveTyps _ _)) at 2; rewrite andp_assoc; apply subp_andp, derives_refl; apply subp_refl. }
eapply subp_trans.
{ apply andp_left2.
  intros ??. apply prop_andp_subp; intro.
  eapply subp_fupd, H.
  apply subp_exp; intro ts1.
  apply subp_exp; intro x1.
  apply subp_exp; intro F.
  apply allp_left with ts1; apply allp_left with x1; apply allp_left with rho.
  rewrite prop_true_andp by auto.
  apply subp_andp, subp_refl. apply subp_sepcon, derives_refl; apply subp_refl. }
apply derives_trans with TT; auto.
eapply derives_trans, subp_derives, fupd_trans; [|apply derives_refl].
apply subp_fupd.
apply subp_exp_left; intro ts1.
apply subp_exp_left; intro x1.
apply subp_exp_left; intro F.
rewrite <- unfash_allp', andp_comm.
eapply derives_trans, subp_derives, derives_refl; [ | apply andp_derives, fupd_frame_l; apply derives_refl].
eapply derives_trans, subp_derives; [apply subp_fupd | apply fupd_andp_unfash | apply derives_refl].
rewrite exp_sepcon2, exp_andp2; apply subp_exp_left; intro ts2.
rewrite exp_sepcon2, exp_andp2; apply subp_exp_left; intro x2.
rewrite exp_sepcon2, exp_andp2; apply subp_exp_left; intro G.
eapply subp_trans, subp_exp_spec.
eapply subp_trans, subp_exp_spec.
eapply subp_trans, @subp_exp_spec with (x := F*G).
eapply derives_trans, subp_derives, derives_refl; [|apply andp_derives, distrib_sepcon_andp; apply derives_refl].
rewrite andp_comm, andp_assoc; apply subp_andp.
+ rewrite sepcon_assoc; apply subp_refl.
+ rewrite <- unfash_allp'; eapply derives_trans, subp_derives, derives_refl; [|apply andp_derives, derives_refl; rewrite sepcon_comm; apply unfash_sepcon].
  rewrite <- unfash_andp, <- unfash_allp'; intros ? _; apply subp_unfash, derives_subp.
  apply allp_right; intro rho'.
  eapply derives_trans; [apply allp_andp1|].
  apply allp_left with rho'.
  eapply subp_trans.
  { apply andp_left1.
    rewrite <- (andp_dup (!! (ve_of rho' = Map.empty (block * type)))) at 2; rewrite andp_assoc; apply subp_andp; [apply subp_refl|].
    rewrite sepcon_assoc, <- (sepcon_andp_prop F).
    apply subp_sepcon, derives_refl; apply subp_refl. }
  apply andp_left2, allp_left with rho'; auto.
Qed.

(*******************end of material moved here from expr.v *******************)

Definition func_at (f: funspec): address -> pred rmap :=
  match f with
   | mk_funspec fsig cc A P Q _ _ => pureat (SomeP (SpecArgsTT A) (packPQ P Q)) (FUN fsig cc)
  end. 

Definition func_at' (f: funspec) (loc: address) : pred rmap :=
  match f with
   | mk_funspec fsig cc _ _ _ _ _ => EX pp:_, pureat pp (FUN fsig cc) loc
  end.
Definition sigcc_at (fsig: typesig) (cc:calling_convention) (loc: address) : pred rmap :=
  EX pp:_, pureat pp (FUN fsig cc) loc.

Definition func_ptr_si (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, funspec_sub_si gs f && func_at gs (b, 0)).

Definition func_ptr (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, !!(funspec_sub gs f) && func_at gs (b, 0)).

Lemma func_ptr_fun_ptr_si f v: func_ptr f v |-- func_ptr_si f v.
Proof. apply exp_derives; intros b. apply andp_derives; trivial.
 apply exp_derives; intros gs. apply andp_derives; trivial. apply funspec_sub_sub_si'.
Qed.

Lemma func_ptr_si_mono fs gs v: 
      funspec_sub_si fs gs && func_ptr_si fs v |-- func_ptr_si gs v.
Proof. unfold func_ptr_si. rewrite exp_andp2. apply exp_derives; intros b.
  rewrite andp_comm, andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm, exp_andp2. apply exp_derives; intros hs.
  rewrite <- andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm. apply funspec_sub_si_trans.
Qed.

Lemma func_ptr_mono fs gs v: funspec_sub fs gs -> 
      func_ptr fs v |-- func_ptr gs v.
Proof. intros. unfold func_ptr. apply exp_derives; intros b.
  apply andp_derives; trivial. apply exp_derives; intros hs.
  apply andp_derives; trivial.
  intros w W. eapply funspec_sub_trans. apply W. apply H.
Qed.

Lemma funspec_sub_implies_func_prt_si_mono' fs gs v: 
      !!(funspec_sub fs gs) && func_ptr_si fs v |-- func_ptr_si gs v.
Proof.
  eapply derives_trans. 2: apply func_ptr_si_mono.
  apply andp_derives. 2: apply derives_refl. 
  apply funspec_sub_sub_si'. 
Qed.

Lemma funspec_sub_implies_func_prt_si_mono fs gs v: funspec_sub fs gs ->
      func_ptr_si fs v |-- func_ptr_si gs v.
Proof. intros. 
  eapply derives_trans. 2: apply funspec_sub_implies_func_prt_si_mono'. 
  apply andp_right. 2: apply derives_refl. hnf; intros; apply H. 
Qed.

Definition NDmk_funspec (f: typesig) (cc: calling_convention)
  (A: Type) (Pre: A -> argsEnviron -> mpred) (Post: A -> environ -> mpred): funspec :=
  mk_funspec f cc (rmaps.ConstType A) (fun _ => Pre) (fun _ => Post)
             (args_const_super_non_expansive _ _) (const_super_non_expansive _ _).

Lemma type_of_funspec_sub:
  forall fs1 fs2, funspec_sub fs1 fs2 ->
  type_of_funspec fs1 = type_of_funspec fs2.
Proof.
intros.
destruct fs1, fs2; destruct H as [[? ?] _]. subst; simpl; auto.
Qed.

Lemma type_of_funspec_sub_si fs1 fs2:
  funspec_sub_si fs1 fs2 |-- !!(type_of_funspec fs1 = type_of_funspec fs2).
Proof.
intros w W.
destruct fs1, fs2.
destruct W as [[? ?] _]. subst; simpl; auto.
Qed.

Lemma typesig_of_funspec_sub:
  forall fs1 fs2, funspec_sub fs1 fs2 ->
  typesig_of_funspec fs1 = typesig_of_funspec fs2.
Proof.
intros.
destruct fs1, fs2; destruct H as [[? ?] _]. subst; simpl; auto.
Qed.

Lemma typesig_of_funspec_sub_si fs1 fs2:
  funspec_sub_si fs1 fs2 |-- !!(typesig_of_funspec fs1 = typesig_of_funspec fs2).
Proof.
intros w W.
destruct fs1, fs2.
destruct W as [[? ?] _]. subst; simpl; auto.
Qed.

Lemma typesig_of_funspec_sub_si2 fs1 fs2:
  TT |-- funspec_sub_si fs1 fs2  -> typesig_of_funspec fs1 = typesig_of_funspec fs2.
Proof.
intros. exploit (H (empty_rmap 0)). trivial. intros. 
apply typesig_of_funspec_sub_si in H0. apply H0.
Qed.

(* Definition assert: Type := environ -> pred rmap. *)

Bind Scope pred with assert.
Local Open Scope pred.

Definition closed_wrt_vars {B} (S: ident -> Prop) (F: environ -> B) : Prop :=
  forall rho te',
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition closed_wrt_lvars {B} (S: ident -> Prop) (F: environ -> B) : Prop :=
  forall rho ve',
     (forall i, S i \/ Map.get (ve_of rho) i = Map.get ve' i) ->
     F rho = F (mkEnviron (ge_of rho) ve' (te_of rho)).

Definition not_a_param (params: list (ident * type)) (i : ident) : Prop :=
  ~ In i (map (@fst _ _) params).

Definition is_a_local (vars: list (ident * type)) (i: ident) : Prop :=
  In  i (map (@fst _ _) vars) .

Fixpoint sepcon_list {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A} {AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}
   (p: list (pred A)) : pred A :=
 match p with nil => emp | h::t => h * sepcon_list t end.

Definition typed_true (t: type) (v: val)  : Prop := strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t =
                                                   Some false.
(*
Definition subst {A} (x: ident) (v: val) (P: environ -> A) : environ -> A :=
  fun s => P (env_set s x v).
*)
Definition subst {A} (x: ident) (v: environ -> val) (P: environ -> A) : environ -> A :=
   fun s => P (env_set s x (v s)).

Lemma func_ptr_isptr: forall spec f, func_ptr spec f |-- !! val_lemmas.isptr f.
Proof.
  intros.
  unfold func_ptr.
  destruct spec. intros ? ?. destruct H as [b [Hb _]]; simpl in Hb; subst. unfold val_lemmas.isptr; simpl; trivial.
Qed.
Lemma func_ptr_si_isptr: forall spec f, func_ptr_si spec f |-- !! val_lemmas.isptr f.
Proof.
  intros.
  unfold func_ptr_si.
  destruct spec. intros ? ?. destruct H as [b [Hb _]]; simpl in Hb; subst. unfold val_lemmas.isptr; simpl; trivial.
Qed.

Lemma  subst_extens:
 forall a v P Q, (forall rho, P rho |-- Q rho) -> forall rho, subst a v P rho |-- subst a v Q rho.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Lemma approx_sepcon: forall (P Q: mpred) n,
  approx n (P * Q) =
  approx n P *
  approx n Q.
Proof.
  intros.
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    destruct H as [? [y [z [? [? ?]]]]].
    exists y, z; split; auto.
    split; split; auto.
    - apply age_sepalg.join_level in H0.
      lia.
    - apply age_sepalg.join_level in H0.
      lia.
  + intros w ?.
    simpl in *.
    destruct H as [y [z [? [[? ?] [? ?]]]]].
    split.
    - apply age_sepalg.join_level in H.
      lia.
    - exists y, z.
      split; [| split]; auto.
Qed.

Lemma approx_orp n P Q: approx n (orp P Q) = orp (approx n P) (approx n Q).
Proof.
  apply pred_ext; intros w W.
  + destruct W. destruct H0;  [left | right]; split; trivial.
  + destruct W; destruct H; split; trivial. left; trivial. right; trivial.
Qed.

Lemma approx_andp: forall (P Q: mpred) n,
  approx n (P && Q) =
  approx n P &&
  approx n Q.
Proof.
  intros.
  change andp with (@predicates_hered.andp compcert_rmaps.RML.R.rmap _ _) in *.
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    tauto.
  + intros w ?.
    simpl in *.
    tauto.
Qed.

Lemma approx_exp: forall A (P: A -> mpred) n,
  approx n (exp P) =
  EX a: A, approx n (P a).
Proof.
  intros.
(*  change (@exp _ Nveric A) with (@predicates_hered.exp compcert_rmaps.RML.R.rmap _ A) in *. *)
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    firstorder.
  + intros w ?.
    simpl in *.
    firstorder.
Qed.

Lemma approx_allp: forall A (P: A -> mpred) n,
  A ->
  approx n (allp P) =
  ALL a: A, approx n (P a).
Proof.
  intros.
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    firstorder.
  + intros w ?.
    simpl in *.
    firstorder.
Qed.

Lemma approx_jam {B: Type} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l}) (P Q: B -> mpred) n (b : B) :
  approx n (jam S P Q b) =
  jam S (approx n oo P) (approx n oo Q) b.
Proof.
  apply predicates_hered.pred_ext.
  + intros w ?. simpl in *. if_tac; firstorder.
  + intros w ?. simpl in *. if_tac; firstorder.
Qed.

Lemma own_super_non_expansive: forall {RA: ghost.Ghost} n g a pp,
  approx n (own g a pp) = approx n (own g a (preds_fmap (approx n) (approx n) pp)).
Proof.
  intros; unfold own.
  rewrite !approx_exp; f_equal; extensionality v.
  unfold Own.
  rewrite !approx_andp; f_equal.
  apply pred_ext; intros ? [? Hg]; split; auto; simpl in *.
  - destruct Hg; eexists.
    rewrite ghost_fmap_singleton in *; rewrite preds_fmap_fmap.
    rewrite approx_oo_approx', approx'_oo_approx by lia; eauto.
  - rewrite ghost_fmap_singleton in *.
    rewrite preds_fmap_fmap in Hg.
    rewrite approx_oo_approx', approx'_oo_approx in Hg by lia; auto.
Qed.

Lemma invariant_super_non_expansive : forall n N P,
  approx n (invariant N P) = approx n (invariant N (approx n P)).
Proof.
  intros; unfold invariant.
  rewrite !approx_exp; f_equal; extensionality g.
  rewrite !approx_sepcon; f_equal.
  apply own_super_non_expansive.
Qed.

(*
Lemma approx_func_ptr: forall (A: Type) fsig0 cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
  approx n (func_ptr (NDmk_funspec fsig0 cc A P Q) v) = approx n (func_ptr (NDmk_funspec fsig0 cc A (fun a rho => approx n (P a rho)) (fun a rho => approx n (Q a rho))) v).
Proof.
  intros.
  unfold func_ptr.
  rewrite !approx_exp; f_equal; extensionality b.
  rewrite !approx_andp; f_equal.
  unfold func_at, NDmk_funspec.
  simpl.
  apply pred_ext; intros w; simpl; intros [? ?]; split; auto.
  + (*destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros ts2 a rho m WM u necU U. simpl in U.
    exists ts2, a, emp. rewrite emp_sepcon. split; intros; [ apply U | intros rho' k UP j KJ J; hnf].
    rewrite emp_sepcon in J. simpl in J. intuition. apply necR_level in KJ. apply necR_level in necU. omega. *)
    destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros ts2 a rho m WM u necU U. simpl in U.
    exists ts2, a, emp. rewrite emp_sepcon. split; intros; [ apply U | intros rho' k UP j KJ z JZ HZ; hnf].
    rewrite emp_sepcon in HZ. simpl in HZ. intuition. apply necR_level in JZ. apply laterR_level in UP. omega.
  + destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros ts2 a rho m WM u necU U. simpl in U.
    exists ts2, a, emp. rewrite emp_sepcon. split; intros. 
    - apply necR_level in necU. split. omega. apply U.
    - (*intros rho' k UP j KJ J.
      rewrite emp_sepcon in J. simpl in J. apply J. *)
      intros rho' k UP j KJ z JZ HZ. hnf in HZ.
      rewrite emp_sepcon in HZ. simpl in HZ. apply HZ. 
Qed. *)

Lemma approx_bupd: forall n P, approx n (bupd P) = bupd (approx n P).
Proof.
  intros; apply pred_ext.
  - intros ? [? HP] ? J.
    destruct (HP _ J) as (? & ? & m' & ? & ? & ? & ?);
      eexists; split; eauto; eexists; split; eauto; repeat split; auto; lia.
  - intros ? HP.
    destruct (HP nil) as (? & ? & m' & ? & ? & ? & []).
    { eexists; constructor. }
    split; [lia|].
    intros ? J.
    destruct (HP _ J) as (? & ? & m'' & ? & ? & ? & []);
      eexists; split; eauto; eexists; split; eauto; repeat split; auto.
Qed.

Lemma wand_nonexpansive_l: forall P Q n,
  approx n (P -* Q)%pred = approx n (approx n P  -* Q)%pred.
Proof.
  repeat intro.
  apply predicates_hered.pred_ext; intros ? [? Hshift]; split; auto; intros ??????.
  - destruct H2; eauto.
  - eapply Hshift; eauto; split; auto.
    apply necR_level in H0; apply join_level in H1 as []; lia.
Qed.

Lemma wand_nonexpansive_r: forall P Q n,
  approx n (P -* Q)%pred = approx n (P  -* approx n Q)%pred.
Proof.
  repeat intro.
  apply predicates_hered.pred_ext; intros ? [? Hshift]; split; auto; intros ??????.
  - split; eauto.
    apply necR_level in H0; apply join_level in H1 as []; lia.
  - eapply Hshift; eauto.
Qed.

Lemma wand_nonexpansive: forall P Q n,
  approx n (P -* Q)%pred = approx n (approx n P  -* approx n Q)%pred.
Proof.
  intros; rewrite wand_nonexpansive_l, wand_nonexpansive_r; reflexivity.
Qed.

Lemma approx_idem : forall n P, approx n (approx n P) = approx n P.
Proof.
  intros.
  change (approx n (approx n P)) with ((approx n oo approx n) P).
  rewrite approx_oo_approx; auto.
Qed.

Lemma fupd_nonexpansive: forall E1 E2 P n, approx n (fupd.fupd E1 E2 P) = approx n (fupd.fupd E1 E2 (approx n P)).
Proof.
  intros; unfold fupd.
  rewrite wand_nonexpansive; setoid_rewrite wand_nonexpansive at 2.
  f_equal; f_equal.
  rewrite !approx_bupd; f_equal.
  rewrite !approx_orp; f_equal.
  erewrite !approx_sepcon, approx_idem; reflexivity.
Qed.

Lemma approx_prop_andp {P Q:Prop} n:
  approx n (prop (P /\ Q)) = (approx n (prop P)) && (approx n (prop Q)).
Proof.
  apply predicates_hered.pred_ext.
  + intros w ?. simpl in *. destruct H as [? [? ?]]. split; split; trivial.
  + intros w ?. simpl in *. destruct H as [[? ?] [? ?]]. split3; trivial.
Qed.

Lemma approx_prop_all {X} {P: X -> Prop} (y:X) n:
  approx n (prop (forall x, P x)) = ALL x, approx n (prop (P x)).
Proof.
  apply predicates_hered.pred_ext.
  + intros w ? ?. simpl in *. split; apply H.
  + intros w ?. simpl in *. split. apply (H y). intros. apply H.
Qed.

Lemma approx_derives1 {P Q} n:
  approx n (prop (P |-- Q)) |-- (prop (P |-- Q)). 
Proof. intros w ?. simpl in *. apply H. Qed.
Lemma approx_derives2 {P Q} n:
  approx n (prop (P |-- Q)) |-- (prop (approx n P |-- approx n Q)). 
Proof. intros w ? ? ?. simpl in *. destruct H. destruct H0. 
split; trivial. apply H1. trivial.
Qed. 
Lemma approx_derives3 {X} {P Q: X -> pred rmap} n:
  approx n (prop (forall x, P x |-- Q x)) |-- prop (forall x, approx n (P x) |-- approx n (Q x)).
Proof. intros w ? ? ? ?. simpl in *. split. apply H0. apply H. apply H0. Qed.

Lemma approx_derives4 {T1 T2} (P1 P2 Q2 Q1: T1 -> T2 -> mpred) n:
      approx n (! (ALL (S : T1) (s0 : T2), (P1 S s0 >=> P2 S s0 * (Q2 S s0 -* Q1 S s0))))
|-- approx n
      (! (ALL (S : T1) (s0 : T2), (P1 S s0 >=> approx n (P2 S s0) * (approx n (Q2 S s0) -* Q1 S s0)))).
Proof. intros ? [? ?]. split; trivial; simpl in *. intros.
destruct (H0 b b0 _ H1 _ _ H2 H3 H4) as [z1 [z2 [J [Z1 Z2]]]]; clear H0.
do 2 eexists; split3. apply J.
{ split; trivial. apply join_level in J; destruct J.
  apply necR_level in H2. apply ext_level in H3. rewrite H0; clear H0. lia. }
intros. eapply Z2. 3: apply H6. 2: apply H5. apply H0.
Qed.

Lemma approx_derives4_inv {T1 T2} (P1 P2 Q2 Q1: T1 -> T2 -> mpred) n:
    approx n
      (! (ALL (S : T1) (s0 : T2), (P1 S s0 >=> approx n (P2 S s0) * (approx n (Q2 S s0) -* Q1 S s0))))
    |-- approx n (! (ALL (S : T1) (s0 : T2), (P1 S s0 >=> P2 S s0 * (Q2 S s0 -* Q1 S s0)))).
Proof. intros ? [? ?]. split; trivial; simpl in *. intros.
destruct (H0 b b0 _ H1 _ _ H2 H3 H4) as [z1 [z2 [J [Z1 Z2]]]]; clear H0.
do 2 eexists; split3. apply J. apply Z1.
intros. eapply Z2. apply H0. apply H5. split; trivial.
clear Z2 H6. apply join_level in J; destruct J.
apply necR_level in H2.
apply necR_level in H0.
apply join_level in H5; destruct H5. lia.
Qed.

Lemma approx_func_ptr_si_general fs cc (A: TypeTree) P Q 
      (Pne: args_super_non_expansive P) (Qne: super_non_expansive Q) (n: nat)
      aPne aQne  (v: val):
    approx (S n) (func_ptr_si (mk_funspec fs cc A P Q Pne Qne) v) =
    approx (S n) (func_ptr_si (mk_funspec fs cc A
                                          (fun ts a rho => approx n (P ts a rho))
                                          (fun ts a rho => approx n (Q ts a rho)) aPne aQne) v).
Proof.
  intros.
  unfold func_ptr_si.
  rewrite !approx_exp. apply pred_ext; intros w [b W]; exists b.
  + rewrite approx_andp, approx_exp in W. destruct W as [W1 [phi [Lev [Phi PHI]]]].
    rewrite approx_andp, approx_exp. split; trivial.
    exists phi; split3; trivial.
    eapply funspec_sub_si_trans; split. apply Phi. clear Phi PHI; hnf.
    split. split; trivial.
    intros w' Hw' ts2 a rho m WM u ? necU extU [U1 U2]. simpl in U1.
    apply fupd_intro.
    exists ts2, a, emp. rewrite emp_sepcon; split. { apply approx_p in U2; trivial. }
    intros rho' y UY k ? YK EK K. rewrite emp_sepcon in K. simpl in K.
    destruct K; split; auto.
    apply necR_level in necU.  apply necR_level in YK. apply ext_level in extU. apply ext_level in EK.
    apply laterR_level in Hw'. lia.
  + rewrite approx_andp, approx_exp in W. destruct W as [W1 [phi [Lev [Phi PHI]]]].
    rewrite approx_andp, approx_exp. split; trivial.
    exists phi; split3; trivial.
    eapply funspec_sub_si_trans; split. apply Phi. clear Phi PHI; hnf.
    split. split; trivial.
    intros w' Hw' ts2 a rho m WM u ? necU extU [U1 U2]. simpl in U1.
    apply fupd_intro.
    exists ts2, a, emp. rewrite emp_sepcon; split. 
    - apply necR_level in necU. apply ext_level in extU. apply approx_lt; trivial.
      apply laterR_level in Hw'. lia.
    - intros rho' k UP j ? KJ EJ J.
      rewrite emp_sepcon in J. simpl in J. apply J.
Qed.

Lemma approx_func_ptr_si: forall (A: Type) fsig0 cc (P: A -> argsEnviron -> mpred)
                                 (Q: A -> environ -> mpred) (v: val) (n: nat),
    approx (S n) (func_ptr_si (NDmk_funspec fsig0 cc A P Q) v) =
    approx (S n) (func_ptr_si (NDmk_funspec fsig0 cc A
                                            (fun a rho => approx n (P a rho))
                                            (fun a rho => approx n (Q a rho))) v).
Proof. intros. apply approx_func_ptr_si_general. Qed.
(*original proof without relying on approx_func_ptr_si_general:
  intros.
  unfold func_ptr_si.
  rewrite !approx_exp; f_equal; extensionality b.
  rewrite !approx_andp; f_equal.
  unfold func_at, NDmk_funspec.
  simpl.
  apply pred_ext; intros w; simpl; intros [? ?]; split; auto.
  + destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_si_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial. 
    intros w' Hw' ts2 a rho m WM u necU [U1 U2]. simpl in U1.
    apply fupd_intro.
    exists ts2, a, emp. rewrite emp_sepcon; split. { apply approx_p in U2; trivial. }
    intros rho' y UY k YK K. rewrite emp_sepcon in K. simpl in K.
    rewrite <- approx_fupd.
    apply necR_level in necU.  apply necR_level in YK.
    split; [ | apply fupd_intro, K]. apply laterR_level in Hw'. lia.
  + destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_si_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros w' Hw' ts2 a rho m WM u necU [U1 U2]. simpl in U1.
    apply fupd_intro.
    exists ts2, a, emp. rewrite emp_sepcon; split. 
    - apply necR_level in necU. apply approx_lt; trivial.
      apply laterR_level in Hw'. lia.
    - intros rho' k UP j KJ J.
      rewrite emp_sepcon in J. simpl in J. apply fupd_intro, J.
Qed. *)

Definition funspecs_assert (FunSpecs: PTree.t funspec): assert :=
 fun rho =>
   (ALL  id: ident, ALL fs:funspec,  !! (FunSpecs!id = Some fs) -->
              EX b:block,
                   !! (Map.get (ge_of rho) id = Some b) && func_at fs (b,0))
 &&  (ALL  b: block, ALL fsig:typesig, ALL cc: calling_convention, sigcc_at fsig cc (b,0) -->
             EX id:ident, !! (Map.get (ge_of rho) id = Some b)
                             && !! exists fs, FunSpecs!id = Some fs).

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
     (forall id, FS1 ! id = FS2 ! id) ->
              funspecs_assert FS1 = funspecs_assert FS2.
Proof.
assert (forall FS FS' rho,
             (forall id, FS ! id = FS' ! id) ->
             funspecs_assert FS rho |-- funspecs_assert FS' rho).
{ intros. intros w [? ?]. split.
  + intro id. rewrite <- (H id); auto.
  + intros loc sig cc w' ? Hw' Hw'' HH. hnf in H0. destruct (H1 loc sig cc w' _ Hw' Hw'' HH)  as [id ID].
    exists id; rewrite <- (H id); auto. }
intros.
extensionality rho.
apply pred_ext; apply H; intros; auto.
Qed.

Lemma funspecs_assert_rho:
  forall G rho rho', ge_of rho = ge_of rho' -> funspecs_assert G rho |-- funspecs_assert G rho'.
Proof. unfold funspecs_assert; intros. rewrite H; auto. Qed.

(************** INTERSECTION OF funspecs -- case ND  ************************)

(* --------------------------------- Binary case: 2 specs only ----------  *)
(*Called ndfs_merge  in hmacdrbg_spec_hmacdrbg.v*)

Definition funspec_intersection_ND fA cA A PA QA FSA (HFSA: FSA = NDmk_funspec fA cA A PA QA) 
                    fB cB B PB QB FSB (HFSB: FSB = NDmk_funspec fB cB B PB QB): option funspec.
destruct (eq_dec fA fB); subst.
+ destruct (eq_dec cA cB); subst.
  - apply Some. eapply (NDmk_funspec fB cB (A+B) 
         (fun x => match x with inl a => PA a | inr b => PB b end)
         (fun x => match x with inl a => QA a | inr b => QB b end)).
  - apply None.
+ apply None.
Defined.

(*The two rules S-inter1 and S-inter2 from page 206 of TAPL*)
Lemma funspec_intersection_ND_sub {fA cA A PA QA fB cB B PB QB} f1 F1 f2 F2 f
      (I: funspec_intersection_ND fA cA A PA QA f1 F1 fB cB B PB QB f2 F2 = Some f):
  funspec_sub f f1 /\ funspec_sub f f2.
Proof.
  subst. unfold funspec_intersection_ND in I. unfold NDmk_funspec in I.
  destruct (eq_dec fA fB); [subst fB | discriminate].
  destruct (eq_dec cA cB); [subst cB | discriminate]. inv I.
  split.
  + split. split; trivial. intros. simpl. intros w [W1 W2].
    apply fupd_intro. exists ts2, (inl x2), emp. rewrite emp_sepcon.
    split. trivial. simpl; intros. rewrite emp_sepcon.
    apply andp_left2, derives_refl.
  + split. split; trivial. intros. simpl. intros w [W1 W2].
    apply fupd_intro. exists ts2, (inr x2), emp. rewrite emp_sepcon.
    split. trivial. simpl; intros. rewrite emp_sepcon.
    apply andp_left2, derives_refl.
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_intersection_ND_sub3 {fA cA A PA QA fB cB B PB QB fC cC C PC QC} f1 F1 f2 F2 f
      (I: funspec_intersection_ND fA cA A PA QA f1 F1 fB cB B PB QB f2 F2 = Some f) g
      (G: g = NDmk_funspec fC cC C PC QC):
  funspec_sub g f1 -> funspec_sub g f2 -> funspec_sub g f.
Proof.
  subst. intros. destruct H as [[? ?] G1]; subst fA cA. destruct H0 as [[? ?] G2]; subst fB cB.
  unfold funspec_intersection_ND in I. simpl in I.
  do 2 rewrite if_true in I; trivial. inv I. simpl. split. split; trivial. intros.
  destruct x2 as [a | b]; [ apply (G1 nil) | apply (G2 nil)].
Qed.

(*-------------------- ND case, specification Sigma families --------------------- *)

Definition funspec_Sigma_ND (sig:typesig) (cc:calling_convention) (I:Type) (A : I -> Type)
           (Pre: forall i, A i -> argsEnviron -> mpred)
           (Post: forall i, A i -> environ -> mpred): funspec.
Proof.
  apply (NDmk_funspec sig cc (sigT A)).
  intros [i Ai] rho; apply (Pre _ Ai rho).
  intros [i Ai] rho; apply (Post _ Ai rho). 
Defined.

(*The two rules S-inter1 and S-inter2 from page 206 of TAPL*)
Lemma funspec_Sigma_ND_sub fsig cc I A Pre Post i:
  funspec_sub (funspec_Sigma_ND fsig cc I A Pre Post) (NDmk_funspec fsig cc (A i) (Pre i) (Post i)).
Proof.
  unfold funspec_Sigma_ND. split. split; trivial. intros; simpl in *.
  eapply derives_trans, fupd_intro.
  exists ts2, (existT A i x2), emp. rewrite emp_sepcon.
  split. apply H. simpl; intros. rewrite emp_sepcon.
  intros u U. apply U.
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_Sigma_ND_sub3 fsig cc I A Pre Post g (i:I)
      (HI: forall i,  funspec_sub g (NDmk_funspec fsig cc (A i) (Pre i) (Post i))):
  funspec_sub g (funspec_Sigma_ND fsig cc I A Pre Post).
Proof.
  assert (HIi := HI i). destruct g. destruct HIi as [[? ?] Hi]; subst t c.
  split. split; trivial.
  simpl; intros. clear i Hi. destruct x2 as [i Ai].
  specialize (HI i). destruct HI as [[_ _] Hi]. apply (Hi ts2 Ai gargs).
Qed.

(*Specialization of funspec_Sigma_ND to binary case, i.e. I=bool*)
Program Definition BinarySigma fsig cc (A B:Type)
        (PA: A -> argsEnviron -> mpred) (QA: A -> environ -> mpred)
        (PB: B -> argsEnviron -> mpred) (QB: B -> environ -> mpred): funspec :=
  funspec_Sigma_ND fsig cc bool _ _ _.
Next Obligation.
  intros sig cc A B PreA PostA PreB PostB x. destruct x. apply A. apply B.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? b X rho. destruct b; simpl in X. apply (PA X rho). apply (PB X rho).
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? b X rho. destruct b; simpl in X. apply (QA X rho). apply (QB X rho).
Defined.

Definition funspecspec_sub_antisym (f g: funspec):= funspec_sub f g /\ funspec_sub g f.
  
Lemma Intersection_BinarySigma sigA ccA A PA QA fsA PrfA sigB ccB B PB QB fsB PrfB f
      (F:  funspec_intersection_ND sigA ccA A PA QA fsA PrfA sigB ccB B PB QB fsB PrfB  = Some f):
  sigA=sigB /\ ccA=ccB /\
  funspecspec_sub_antisym f (BinarySigma sigA ccA A B PA QA PB QB).
Proof.
  unfold funspec_intersection_ND in F.
  destruct (eq_dec sigA sigB); [ subst sigA; split; trivial | discriminate].
  destruct (eq_dec ccA ccB); [ inv F; split; trivial | discriminate]. 
  split.
  + split. split; trivial. simpl; intros. destruct x2 as [i p].
    eapply derives_trans, fupd_intro. destruct i; simpl in *.
  - exists ts2, (inl p), emp. rewrite emp_sepcon. split; simpl. apply H.
    intros. rewrite emp_sepcon. intros u U; apply U.
  - exists ts2, (inr p), emp. rewrite emp_sepcon. split; simpl. apply H.
    intros. rewrite emp_sepcon. intros u U; apply U.
    + split. split; trivial. intros. intros u [L U]. destruct x2.
  - apply fupd_intro. exists ts2, (existT (BinarySigma_obligation_1 A B) true a), emp.
    rewrite emp_sepcon. simpl; split. apply U. intros. rewrite emp_sepcon.
    apply andp_left2, derives_refl.
  - apply fupd_intro. exists ts2, (existT (BinarySigma_obligation_1 A B) false b), emp.
    rewrite emp_sepcon. simpl; split. apply U. intros. rewrite emp_sepcon.
    apply andp_left2, derives_refl.
Qed.

Lemma Intersection_sameSigCC_Some sig cc A PA QA fsA PrfA B PB QB fsB PrfB:
  ~ funspec_intersection_ND sig cc A PA QA fsA PrfA sig cc B PB QB fsB PrfB  = None.
Proof.
  intros N. unfold funspec_intersection_ND in N.
  do 2 rewrite if_true in N; trivial. discriminate.
Qed.

(*-------------------Bifunctor version, binary case ------------*)

Definition binarySUM {A1 A2}
           (P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred)
           (P2: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred):
  forall ts : list Type, 
    (dependent_type_functor_rec ts (AssertTT (@SigType bool (fun b => if b then A1 else A2)))) mpred.
Proof.
  intros ts X rho. specialize (P1 ts). specialize (P2 ts). 
  simpl in *. destruct X as [b B]; destruct b; simpl in B.
  apply (P1 B rho). apply (P2 B rho). 
Defined.

Lemma binarySUM_ne {A1 A2}
           {P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred}
           {P2: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred}
           (P1_ne: super_non_expansive P1) (P2_ne: super_non_expansive P2):
  super_non_expansive (binarySUM P1 P2).
Proof.
  hnf; simpl; intros. unfold binarySUM. destruct x as [b B].
  destruct b; simpl in B. apply P1_ne. apply P2_ne. 
Qed.

Definition binarySUMArgs {A1 A2}
           (P1: forall ts : list Type, (dependent_type_functor_rec ts (ArgsTT A1)) mpred)
           (P2: forall ts : list Type, (dependent_type_functor_rec ts (ArgsTT A2)) mpred):
  forall ts : list Type, 
    (dependent_type_functor_rec ts (ArgsTT (@SigType bool (fun b => if b then A1 else A2)))) mpred.
Proof.
  intros ts X rho. specialize (P1 ts). specialize (P2 ts). 
  simpl in *. destruct X as [b B]; destruct b; simpl in B.
  apply (P1 B rho). apply (P2 B rho). 
Defined.

Lemma binarySUMArgs_ne {A1 A2}
           {P1: forall ts : list Type, (dependent_type_functor_rec ts (ArgsTT A1)) mpred}
           {P2: forall ts : list Type, (dependent_type_functor_rec ts (ArgsTT A2)) mpred}
           (P1_ne: args_super_non_expansive P1) (P2_ne: args_super_non_expansive P2):
  args_super_non_expansive (binarySUMArgs P1 P2).
Proof.
  hnf; simpl; intros. unfold binarySUMArgs. destruct x as [b B].
  destruct b; simpl in B. apply P1_ne. apply P2_ne. 
Qed.

Definition binary_intersection (phi psi:funspec): option funspec.
  destruct phi as [f c A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct (eq_dec f f2); [subst f2 | apply None].
  destruct (eq_dec c c2); [subst c2 | apply None].
  remember (binarySUMArgs P1 P2) as P.
  remember (binarySUM Q1 Q2) as Q.
  apply Some. apply (mk_funspec f c _ P Q).
  subst P; apply (binarySUMArgs_ne P1_ne P2_ne).
  subst Q; apply (binarySUM_ne Q1_ne Q2_ne).
Defined.

Definition callingconvention_of_funspec (phi:funspec):calling_convention :=
  match phi with
    mk_funspec sig cc A P Q Pne Qne => cc
  end.

Lemma callconv_of_binary_intersection {phi1 phi2 phi} (BI: binary_intersection phi1 phi2 = Some phi):
      callingconvention_of_funspec phi = callingconvention_of_funspec phi1 /\ 
      callingconvention_of_funspec phi = callingconvention_of_funspec phi2.
Proof. destruct phi1; destruct phi2; destruct phi; simpl in *.
 (*destruct (typesigs_match t t0); [ | discriminate].*) if_tac in BI; [ subst | inv BI].
 if_tac in BI; inv BI; split; trivial.
Qed.

Lemma funspectype_of_binary_intersection {phi1 phi2 phi} (BI: binary_intersection phi1 phi2 = Some phi):
      type_of_funspec phi1 = type_of_funspec phi /\ 
      type_of_funspec phi2 = type_of_funspec phi.
Proof. destruct phi1; destruct phi2; destruct phi; simpl in *. 
 (*remember  (typesigs_match t t0) as b; destruct b; [ | discriminate].*)
 if_tac in BI; [ subst | inv BI].
 if_tac in BI; inv BI. split; trivial.
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
  if_tac in BI; [ inv BI | discriminate]. trivial.
Qed. 

Lemma binary_intersection_typesigs {phi1 phi2 phi} (BI : binary_intersection phi1 phi2 = Some phi):
      typesig_of_funspec phi1 = typesig_of_funspec phi /\ typesig_of_funspec phi2 = typesig_of_funspec phi.
Proof.
  destruct phi1; destruct phi2. simpl in *.
  if_tac in BI; [ subst | inv BI].
  if_tac in BI; [ inv BI | discriminate]; split; trivial.
Qed.
 
Lemma binaryintersection_sub phi psi omega:
  binary_intersection phi psi = Some omega ->
  funspec_sub omega phi /\ funspec_sub omega psi.
Proof.
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne]. intros.
  simpl in H.
  destruct (eq_dec f1 f2); [ subst f2 | inv H]. 
  destruct (eq_dec c1 c2); inv H.
  apply inj_pair2 in H5. apply inj_pair2 in H4. subst P Q. split.
  + split; [split; reflexivity | intros].
    eapply derives_trans, fupd_intro. exists ts2.
    fold (@dependent_type_functor_rec ts2) in *.
    simpl in H; destruct H.
    exists (existT _ true x2), emp.
    rewrite emp_sepcon.
    split. apply H0.
    simpl. intros rho'; rewrite emp_sepcon. apply andp_left2, derives_refl.
  + split; [split; reflexivity | intros].
    eapply derives_trans, fupd_intro. exists ts2.
    fold (@dependent_type_functor_rec ts2) in *.
    simpl in H; destruct H.
    exists (existT _ false x2), emp.
    rewrite emp_sepcon.
    split. apply H0.
    simpl. intros rho'; rewrite emp_sepcon. apply andp_left2, derives_refl.
Qed.

Lemma BINARY_intersection_sub3  phi psi omega:
  binary_intersection phi psi = Some omega ->
  forall xi, funspec_sub xi phi -> funspec_sub xi psi -> funspec_sub xi omega.
Proof.
  intros. 
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne].
  simpl in H.
  destruct (eq_dec f1 f2); [ subst f2 | inv H]. 
  destruct (eq_dec c1 c2); inv H.
  apply inj_pair2 in H6. apply inj_pair2 in H7. subst P Q.
  destruct xi as [f' c' A' P' Q' P_ne' Q_ne'].
  destruct H0 as [[? ?] ?]; subst f' c'.
  destruct H1 as [[_ _] ?]. 
  split; [ split; reflexivity | intros]. simpl in x2.
  specialize (H ts2). specialize (H2 ts2). 
  fold (@dependent_type_functor_rec ts2) in *. simpl typesig_of_funspec in *.
  destruct x2 as [b Hb]; destruct b; eauto.
Qed.

(****A variant that is a bit more computational - maybe should replace the original definition above?*)
Program Definition binary_intersection' {f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne} phi psi 
  (Hphi: phi = mk_funspec f c A1 P1 Q1 P1_ne Q1_ne) (Hpsi: psi = mk_funspec f c A2 P2 Q2 P2_ne Q2_ne): funspec :=
  mk_funspec f c _ (@binarySUMArgs A1 A2 P1 P2) (binarySUM Q1 Q2) _ _.

Next Obligation. intros. apply (binarySUMArgs_ne P1_ne P2_ne). Qed.
Next Obligation. intros. apply (binarySUM_ne Q1_ne Q2_ne). Qed.

Lemma binary_intersection'_sound {f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne} phi psi
      (Hphi: phi = mk_funspec f c A1 P1 Q1 P1_ne Q1_ne) (Hpsi: psi = mk_funspec f c A2 P2 Q2 P2_ne Q2_ne):
   binary_intersection phi psi = Some(binary_intersection' phi psi Hphi Hpsi).
Proof.
unfold binary_intersection, binary_intersection'. subst phi psi. rewrite 2 if_true by trivial. f_equal. f_equal.
  apply proof_irr. apply proof_irr.
Qed.
Lemma binary_intersection'_complete phi psi tau:
   binary_intersection phi psi = Some tau ->
   exists f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne Hphi Hpsi,
   tau = @binary_intersection' f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne phi psi Hphi Hpsi.
Proof.
unfold binary_intersection, binary_intersection'.
destruct phi; destruct psi. if_tac. 2: discriminate. if_tac. 2: discriminate. 
intros X. inv X. 
do 14 eexists. reflexivity. f_equal. 
  apply proof_irr. apply proof_irr.
Qed.

Lemma binary_intersection'_sub  {f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne} (phi psi:funspec) Hphi Hpsi:
  funspec_sub (@binary_intersection' f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne phi psi Hphi Hpsi) phi /\
  funspec_sub (@binary_intersection' f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne phi psi Hphi Hpsi) psi.
Proof. apply binaryintersection_sub. apply binary_intersection'_sound. Qed.

Lemma binary_intersection'_sub3 {f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne} phi psi Hphi Hpsi:
  forall xi, funspec_sub xi phi -> funspec_sub xi psi -> 
  funspec_sub xi (@binary_intersection' f c A1 P1 Q1 P1_ne Q1_ne A2 P2 Q2 P2_ne Q2_ne phi psi Hphi Hpsi).
Proof. intros. eapply BINARY_intersection_sub3. apply binary_intersection'_sound. apply H. apply H0. Qed.

(*-------------------Bifunctor version, general case ------------*)

Definition generalSUM {I} (Ai: I -> TypeTree)
           (P: forall i ts, (dependent_type_functor_rec ts (AssertTT (Ai i))) mpred):  forall ts : list Type, 
    (dependent_type_functor_rec ts (AssertTT (@SigType I Ai))) mpred.
Proof. intros ts [i Hi] rho. simpl in *. apply (P i ts Hi rho). Defined. 

Lemma generalSUM_ne {I} (Ai: I -> TypeTree) P
      (P_ne: forall i,  super_non_expansive (P i)):
  super_non_expansive (generalSUM Ai P).
Proof.
  hnf; simpl; intros. unfold generalSUM. destruct x as [i Hi].
  apply P_ne. 
Qed.

Definition generalSUMArgs {I} (Ai: I -> TypeTree)
           (P: forall i ts, (dependent_type_functor_rec ts (ArgsTT (Ai i))) mpred):  forall ts : list Type, 
    (dependent_type_functor_rec ts (ArgsTT (@SigType I Ai))) mpred.
Proof. intros ts [i Hi] rho. simpl in *. apply (P i ts Hi rho). Defined. 

Lemma generalSUMArgs_ne {I} (Ai: I -> TypeTree) P
      (P_ne: forall i, args_super_non_expansive (P i)):
  args_super_non_expansive (generalSUMArgs Ai P).
Proof.
  hnf; simpl; intros. unfold generalSUMArgs. destruct x as [i Hi].
  apply P_ne. 
Qed.

Definition WithType_of_funspec (phi:funspec):TypeTree :=
  match phi with
    mk_funspec sig cc A P Q Pne Qne => A
  end.

Definition intersectionPRE {I} phi:
  forall (i : I) (ts : list Type),
    (dependent_type_functor_rec ts (ArgsTT (WithType_of_funspec (phi i)))) mpred.
Proof.
  intros i. destruct (phi i) as  [fi ci A_i Pi Qi Pi_ne Qi_ne]. apply Pi. 
Defined.

Definition intersectionPOST {I} phi:
  forall (i : I) (ts : list Type),
    (dependent_type_functor_rec ts (AssertTT (WithType_of_funspec (phi i)))) mpred.
Proof.
  intros i. destruct (phi i) as  [fi ci A_i Pi Qi Pi_ne Qi_ne]. apply Qi. 
Defined.

Definition iPre {I} phi:
forall ts : list Type,
        (dependent_type_functor_rec ts
           (ArgsTT (SigType I (fun i : I => WithType_of_funspec (phi i)))))
          mpred.
Proof. intros. apply (generalSUMArgs _ (intersectionPRE phi)). Defined.

Definition iPost {I} phi:
forall ts : list Type,
        (dependent_type_functor_rec ts
           (AssertTT (SigType I (fun i : I => WithType_of_funspec (phi i)))))
          mpred.
Proof. intros. apply (generalSUM _ (intersectionPOST phi)). Defined.

Lemma iPre_ne {I} (phi: I -> funspec): args_super_non_expansive (iPre phi).
Proof.
  unfold iPre. apply generalSUMArgs_ne.
  intros. unfold intersectionPRE. simpl. destruct (phi i); trivial.
Qed.

Lemma iPost_ne {I} (phi: I -> funspec): super_non_expansive (iPost phi).
Proof.
  unfold iPost. apply generalSUM_ne.
  intros. unfold intersectionPOST. simpl. destruct (phi i); trivial.
Qed.

Definition general_intersection {I sig cc} (phi: I -> funspec) 
           (Hsig: forall i, typesig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc): funspec.
Proof.
  apply (mk_funspec sig cc
                    ((@SigType I (fun i => WithType_of_funspec (phi i))))
                    (iPre phi) (iPost phi)).
  apply iPre_ne.
  apply iPost_ne.
Defined.

Lemma generalintersection_sub {I sig cc} (phi: I -> funspec) 
           (Hsig: forall i, typesig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc) omega:
  general_intersection phi Hsig Hcc = omega ->
  forall i,  funspec_sub omega (phi i).
Proof.
  intros; subst. hnf. simpl typesig_of_funspec in *.
  specialize (Hsig i); specialize (Hcc i); subst.
  unfold  general_intersection; simpl.
  remember (phi i) as zz; destruct zz. split; [ split; reflexivity | intros].
  eapply derives_trans, fupd_intro.
  exists ts2. simpl in H; destruct H.
  assert (exists D: (dependent_type_functor_rec ts2 (WithType_of_funspec (phi i))) mpred,
         JMeq.JMeq x2 D).
  { rewrite <- Heqzz. simpl. exists x2. constructor. }
  destruct H1 as [D HD].
  unfold iPre, intersectionPRE, generalSUM. 
  exists (existT _ i D), emp.  
  rewrite emp_sepcon. split; simpl.
  + remember (phi i) as pp. destruct pp.
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5 ; apply inj_pair2 in H6; subst P0 Q0.
    inv HD. apply inj_pair2 in H1; subst; trivial. 
  + intros; rewrite emp_sepcon. unfold intersectionPOST.
    intros x [X1 X2]. destruct (phi i).
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5; apply inj_pair2 in H6; subst P0 Q0.
    inv HD. apply inj_pair2 in H1; subst; trivial. 
Qed.

Lemma generalintersection_sub3  {I sig cc}
      (INH: inhabited I) (phi: I -> funspec) 
           (Hsig: forall i, typesig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc) lia:
  general_intersection phi Hsig Hcc = lia ->
  forall xi, (forall i, funspec_sub xi (phi i)) -> funspec_sub xi lia.
Proof.
  intros. subst. inv INH; rename X into i.
  unfold general_intersection. 
  destruct xi as [f c A P Q P_ne Q_ne].
  split.
  { split. 
    + specialize (H0 i); specialize (Hsig i). destruct (phi i); subst; apply H0.
    + specialize (H0 i); specialize (Hcc i). destruct (phi i); subst; apply H0. }
  intros. simpl. simpl in x2. clear i. destruct x2 as [i Hi]. simpl.
  specialize (H0 i); specialize (Hsig i); specialize (Hcc i); subst; simpl.
  unfold intersectionPRE, intersectionPOST.
  forget (phi i) as zz. clear phi.
  destruct zz. simpl in *.
  destruct H0 as [[? ?] ?]; subst.
  apply (H1 ts2 Hi gargs). 
Qed.

Lemma make_context_t_get: forall {params temps i ty} 
      (T: (make_tycontext_t params temps) ! i = Some ty),
      In i (map fst params ++ map fst temps).
Proof.
  induction params; simpl; intros.
* induction temps; simpl in *. rewrite PTree.gempty in T; discriminate. 
  destruct a; simpl in *. rewrite PTree.gsspec in T.
  destruct (peq i i0); subst. left; trivial. right; auto.
* destruct a; simpl in *. rewrite PTree.gsspec in T.
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
    - subst a. simpl in *. apply (H0 i ty). rewrite PTree.gss; trivial.
    - inv H. apply (IHparams temps); trivial.
      red; intros j ? ?. apply H0. rewrite PTree.gso; trivial. clear - H4 H.
      intros J; subst. destruct a; simpl in *. apply H4; clear - H.
      apply (make_context_t_get H).
Qed.

Lemma tc_environ_rettype t rho: tc_environ (rettype_tycontext t) (globals_only rho).
Proof.
  unfold rettype_tycontext; simpl. split3; intros; simpl.
  red; intros. rewrite PTree.gempty in H; congruence.
  split; intros. rewrite PTree.gempty in H; congruence. destruct H; inv H.
  red; intros. rewrite PTree.gempty in H; congruence.
Qed.

Lemma tc_environ_rettype_env_set t rho i v:
tc_environ (rettype_tycontext t)
         (env_set (globals_only rho) i v).
Proof.
  unfold rettype_tycontext; simpl. split3; intros; simpl.
  red; intros. rewrite PTree.gempty in H; congruence.
  split; intros. rewrite PTree.gempty in H; congruence. destruct H; inv H.
  red; intros. rewrite PTree.gempty in H; congruence.
Qed.

Lemma funspec_sub_cc phi psi: funspec_sub phi psi ->
      callingconvention_of_funspec phi = callingconvention_of_funspec psi.
Proof. destruct phi; destruct psi; simpl. intros [[_ ?] _]; trivial. Qed.

Lemma funspec_sub_si_cc phi psi: TT |-- funspec_sub_si phi psi ->
      callingconvention_of_funspec phi = callingconvention_of_funspec psi.
Proof. destruct phi; destruct psi; simpl. intros.
 destruct (H (empty_rmap 0)) as [[_ ?] _]; simpl; trivial. Qed.

Lemma later_func_ptr_si phi psi (H: TT |-- funspec_sub_si phi psi) v:
      |> (func_ptr_si phi v) |-- |> (func_ptr_si psi v).
Proof. apply box_derives. apply exp_derives. intros b.
  apply andp_derives; trivial. apply exp_derives. intros tau.
  apply andp_derives; trivial. 
  eapply derives_trans. 2: eapply funspec_sub_si_trans with (f2:=phi).
  apply andp_right. trivial.
  eapply derives_trans. 2: apply H. trivial.
Qed.

Lemma later_func_ptr_si' phi psi v:
      |> (funspec_sub_si phi psi && func_ptr_si phi v) |-- |> (func_ptr_si psi v).
Proof. apply box_derives. intros m [M1 M2].
  destruct M2 as [b [? [gs [GS1 GS2]]]]. exists b; split; trivial.
  exists gs; split; trivial. clear GS2 H b v.
  apply funspec_sub_si_trans with (f2:=phi). split; trivial.
Qed.

Lemma eqp_refl : forall (G : Triv) P, G |-- (P <=> P).
Proof.
  intros; rewrite andp_dup; apply subp_refl.
Qed.

Lemma eqp_andp : forall (G : Triv) (P P' Q Q' : mpred)
  (HP : (G |-- P <=> P')) (HQ : (G |-- Q <=> Q')), G |-- (P && Q <=> P' && Q').
Proof.
  intros. red; intros. specialize (HP _ H). specialize (HQ _ H).
  split; simpl; intros ? ? ? ? [X Y]; split.
  - eapply (HP y); eauto.
  - eapply (HQ y); eauto.
  - eapply (HP y); eauto.
  - eapply (HQ y); eauto.
Qed.
Lemma eqp_sepcon : forall (G : Triv) (P P' Q Q' : mpred)
  (HP : (G |-- P <=> P')) (HQ : (G |-- Q <=> Q')), (G |-- P * Q <=> P' * Q').
Proof.
  intros. red; intros. specialize (HP _ H). specialize (HQ _ H).
  split; simpl; intros ? ? ? ? [a1 [a2 [Ja [A1 A2]]]].
  - pose proof (necR_level _ _ H1).
    pose proof (ext_level _ _ H2).
    destruct (join_level _ _ _ Ja).
    eapply HP in A1; [| | apply necR_refl | reflexivity]; [|lia].
    eapply HQ in A2; [| | apply necR_refl | reflexivity]; [|lia].
    eauto.
  - pose proof (necR_level _ _ H1).
    pose proof (ext_level _ _ H2).
    destruct (join_level _ _ _ Ja).
    eapply HP in A1; [| | apply necR_refl | reflexivity]; [|lia].
    eapply HQ in A2; [| | apply necR_refl | reflexivity]; [|lia].
    eauto.
Qed.


Lemma fash_func_ptr_ND:
 forall fsig cc (A: Type) 
             (Pre Pre': A -> argsEnviron -> mpred) (Post Post': A -> environ -> mpred) v,
   ALL a:A,
         (ALL rho:argsEnviron, fash (Pre' a rho --> Pre a rho)) &&
         (ALL rho:environ, fash (Post a rho --> Post' a rho))
   |-- fash (func_ptr_si (NDmk_funspec fsig cc A Pre Post) v --> 
                  func_ptr_si (NDmk_funspec fsig cc A Pre' Post') v).
Proof.
intros.
unfold func_ptr_si.
apply subp_exp; intro b.
apply subp_andp.
apply subp_refl.
intros ? ? ? ? ? ? ? ? [gs [? ?]].
exists gs. split; auto.
eapply funspec_sub_si_trans.
split.
eassumption.
clear gs H3 H4.
split.
split; auto.
intros ? ? ? ? ? ? ? ? ? ? ? [? ?].
apply fupd_intro.
exists nil, b1, emp.
rewrite emp_sepcon.
split.
destruct (H b1) as [Hpre _].
eapply (Hpre b2); auto.
apply necR_level in H1, H5. apply ext_level in H2, H6. apply laterR_level in H3. lia.
intros ? ? ? ? ? ? ? [? Hpost].
rewrite emp_sepcon in Hpost.
destruct (H b1) as [_ Hpost'].
eapply (Hpost' b3); auto.
apply necR_level in H1, H5, H10. apply ext_level in H2, H6, H11. apply laterR_level in H3. lia.
Qed.


(*
Lemma eqp_andp : forall (G : Triv) (P P' Q Q' : mpred)
  (HP : (G |-- P <=> P')%logic) (HQ : (G |-- Q <=> Q')%logic), G |-- (P && Q <=> P' && Q')%logic.
Proof.
  intros.
  rewrite fash_andp in HP, HQ |- *.
  apply andp_right; apply subp_andp; auto; intros ? Ha; destruct (HP _ Ha), (HQ _ Ha); auto.
Qed.

Lemma eqp_exp : forall (A : Type) (NA : NatDed A) (IA : Indir A) (RecIndir : RecIndir A)
    (G : Triv) (B : Type) (X Y : B -> A),
  (forall x : B, (G |-- X x <=> Y x)%logic) ->
  G |-- ((EX x : _, X x) <=> (EX x : _, Y x))%logic.
Proof.
  intros.
  rewrite fash_andp; apply andp_right; apply subp_exp; intro x; specialize (H x); rewrite fash_andp in H;
    intros ? Ha; destruct (H _ Ha); auto.
Qed.*)(*Print funspec.

Definition MkPred {T A} (B: T -> mpred): forall ts : list Type, dependent_type_functor_rec ts (ArgsTT A) mpred.
Proof. simpl; intros. Check dependent_type_functor_rec. unfold dependent_type_functor_rec in X. simpl.

Lemma funcptr_contr {T : Type} (B1 B2 : T -> mpred) (x : T ) (v : val) sig cc A
                    (pre : forall ts : list Type, dependent_type_functor_rec ts A mpred -> argsEnviron -> (T -> mpred) -> mpred)
                    (post: (T -> mpred) -> forall ts : list Type, dependent_type_functor_rec ts (AssertTT A) mpred)
                     P1ne Q1ne P2ne Q2ne :
predicates_hered.box predicates_hered.laterM (B1 x <=> B2 x)
|-- func_ptr_si (mk_funspec sig cc A (fun ts x q a => pre ts x q B1) (post (fun rho : T => |> B1 rho))P1ne Q1ne) v <=> 
    func_ptr_si (mk_funspec sig cc A (fun ts x q a => pre ts x q B2) (post (fun rho : T => |> B2 rho)) P2ne Q2ne) v. 
Proof. unfold func_ptr_si. red. intros a Ha m AM. split; intros k MK [b [Hb [gs [B GS]]]].
+ exists b. split; trivial. exists gs; split; [ eapply funspec_sub_si_trans | trivial].
  split. apply B. clear GS B gs Hb v b.
  split. split; trivial.
  intros q kq ts2 xs2 gargs r RR p2 rp2 [Args Hp2]. simpl in Ha.
  exists ts2, xs2, emp; split.
  - rewrite emp_sepcon.
    assert ((fun rho : T => |> B1 rho) =(fun rho : T => |> B2 rho) ).
    { extensionality t.  simpl in pre.
Lemma funcptr_contr {T : Type} (B1 B2 : T -> mpred) (x : T ) (v : val) sig cc A
                    (pre : (T -> mpred) -> forall ts : list Type, dependent_type_functor_rec ts (ArgsTT A) mpred)
                    (post: (T -> mpred) -> forall ts : list Type, dependent_type_functor_rec ts (AssertTT A) mpred)
                     P1ne Q1ne P2ne Q2ne :
predicates_hered.box predicates_hered.laterM (B1 x <=> B2 x)
|-- func_ptr_si (mk_funspec sig cc A (pre (fun rho : T => |> B1 rho)) (post (fun rho : T => |> B1 rho)) P1ne Q1ne) v <=> 
    func_ptr_si (mk_funspec sig cc A (pre (fun rho : T => |> B2 rho)) (post (fun rho : T => |> B2 rho)) P2ne Q2ne) v. 
Proof. unfold func_ptr_si. red. intros a Ha m AM. split; intros k MK [b [Hb [gs [B GS]]]].
+ exists b. split; trivial. exists gs; split; [ eapply funspec_sub_si_trans | trivial].
  split. apply B. clear GS B gs Hb v b.
  split. split; trivial.
  intros q kq ts2 xs2 gargs r RR p2 rp2 [Args Hp2]. simpl in Ha.
  exists ts2, xs2, emp; split.
  - rewrite emp_sepcon.
    assert ((fun rho : T => |> B1 rho) =(fun rho : T => |> B2 rho) ).
    { extensionality t. admit.
    rewrite H. trivial.


Lemma funcptr_contr {T : Type} (B1 B2 : T -> mpred) (x : T ) (v : val) (f : (T -> mpred) -> funspec)
      (HsigCC: forall x y, typesig_of_funspec (f x) = typesig_of_funspec (f y)
                        /\ callingconvention_of_funspec (f x) = callingconvention_of_funspec (f y)):
predicates_hered.box predicates_hered.laterM (B1 x <=> B2 x)
|-- func_ptr_si (f (fun rho : T => |> B1 rho)) v <=> func_ptr_si (f (fun rho : T => |> B2 rho)) v. 
Proof. unfold func_ptr_si. red. intros a Ha m AM. split; intros k MK [b [Hb [gs [B GS]]]].
+ exists b. split; trivial. exists gs; split; [ eapply funspec_sub_si_trans | trivial].
  split. apply B. clear GS B gs Hb v b.
  destruct (HsigCC B1 B2). destruct (HsigCC B1 (fun t => |> B1 t) ). destruct (HsigCC B2 (fun t => |> B2 t) ).
  clear HsigCC. rewrite H in *; rewrite H0 in *. clear H H0.
  rewrite H1 in *; rewrite H2 in *. clear H1 H2.
  remember (f (fun rho : T => |> B1 rho)) as phi1. 
  remember (f (fun rho : T => |> B2 rho)) as phi2.
  destruct phi1 as [sig1 cc1 A1 P1 Q1 P1ne Q1ne].
  destruct phi2 as [sig2 cc2 A2 P2 Q2 P2ne Q2ne]. simpl in *. subst. split. split; trivial.
  intros q kq ts2 xs2 gargs r RR p2 rp2 [Args Hp2]
  destruct H2. unfold funspec_sub_si. red. intros x. simpl. simpl in B. Hm. red. apply eqp_exp.
(f :T -> funspec):
predicates_hered.box predicates_hered.laterM (B1 x <=> B2 x)
|-- func_ptr_si (f (fun t => |> B1)) v <=> func_ptr_si (f (|> B2)) v.

 0
Lemma funcptr_contr {T : Type} (B1 B2 : T * val -> mpred)
      (f : (T * val -> mpred) -> funspec)
      (HsigCC: forall x y, typesig_of_funspec (f x) = typesig_of_funspec (f y)
                        /\ callingconvention_of_funspec (f x) = callingconvention_of_funspec (f y))
      (v : val):
predicates_hered.allp (fun x : T * val => |> B1 x <=> |> B2 x) |-- func_ptr (f B1) v <=> func_ptr (f B2) v.
Proof.
unfold func_ptr. apply subp_eqp; apply subp_exp; intros b.
+ apply subp_andp.
  - red; intros. red. intros u AU w UW; trivial.
  - intros n N u NU w UW [gs [Sub FuncAt]]. exists gs. split; trivial.
    simpl; simpl in Sub. clear FuncAt.
    eapply funspec_sub_trans. apply Sub. clear Sub gs. simpl in N.
    remember (f B1) as phi1; remember (f B2) as phi2.
    specialize (HsigCC B1 B2). rewrite <- Heqphi1, <- Heqphi2 in HsigCC.
    destruct phi1 as [t1 c1 A1 P1 Q1 P1ne Q1ne].
    destruct phi2 as [t2 c2 A2 P2 Q2 P2ne Q2ne]. simpl. simpl in HsigCC; destruct HsigCC.
    subst t2 c2. split; [ split; trivial | intros].
    intros m [M1 M2]. 
Search func_ptr_si.
Check (HORec_sub). 
    destruct gargs as [ge args]; simpl in *.
    destruct t as [argtypes rt]; simpl in *.
Search HOcontractive. Print argsEnviron.
Check (HORec_sub). (predicates_hered.allp (fun x : T * val => |> B1 x <=> |> B2 x)) (T * val)).
(fun x f z => func_ptr 
























    Print funspec_sub. do_funspec_sub. Search  red in Sub simpl in Sub. destruct Sub. intros r. eapply eqp_prop. andp_subp. eapply prop_andp_subp. normalize.
eapply (allp_left v).*)

End invs.
