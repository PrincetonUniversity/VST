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
Import compcert.lib.Maps.

Local Open Scope pred.

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
  mk_tycontext (PTree.empty _) (PTree.empty _) Tvoid
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

Definition funsig_of_funspec (fs: funspec) : funsig :=
 match fs with mk_funspec fsig _ _ _ _ _ _ => fsig end.

Definition ret0_tycon (Delta: tycontext): tycontext :=
  mk_tycontext (PTree.empty _) (PTree.empty _) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta).

(* If we were to require that a non-void-returning function must,
   at a function call, have its result assigned to a temp,
   then we could change "ret0_tycon" to "ret_tycon" in this
   definition (and in NDfunspec_sub). *)

Definition funspec_sub_si (f1 f2 : funspec):mpred :=
let Delta := funsig_tycontext (funsig_of_funspec f1) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        !!(fsig1 = fsig2 /\ cc1=cc2) &&
        ! (ALL ts2 :_, ALL x2:_, ALL rho:_,
        (((local (tc_environ Delta) rho) && (P2 ts2 x2 rho))
         >=> bupd (EX ts1:_,  EX x1:_, EX F:_, 
            (F * (P1 ts1 x1 rho)) &&
            ALL rho':_, (     !( ((local (tc_environ (ret0_tycon Delta)) rho') && (F * (Q1 ts1 x1 rho')))
                         >=> bupd (Q2 ts2 x2 rho'))))))
    end
end.

Definition funspec_sub_early (f1 f2 : funspec):mpred :=
let Delta := funsig_tycontext (funsig_of_funspec f1) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        !!(fsig1 = fsig2 /\ cc1=cc2) &&
        ! (ALL ts2 :_, ALL x2:_, ALL rho:_, EX ts1:_,  EX x1:_, EX F:_,
        (((local (tc_environ Delta) rho) && (P2 ts2 x2 rho))
         >=> bupd (*EX ts1:_,  EX x1:_, EX F:_, *)
            (F * (P1 ts1 x1 rho)) &&
            ALL rho':_, (     !( ((local (tc_environ (ret0_tycon Delta)) rho') && (F * (Q1 ts1 x1 rho')))
                         >=> bupd (Q2 ts2 x2 rho')))))
    end
end.

Definition funspec_sub (f1 f2 : funspec):Prop :=
let Delta := funsig_tycontext (funsig_of_funspec f1) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        fsig1 = fsig2 /\ cc1=cc2 /\
        forall (ts2 : list Type) x2 rho,
               ((local (tc_environ Delta) rho) && (P2 ts2 x2 rho))
           |-- bupd
               (EX ts1:_,  EX x1:_, EX F:_, 
                           (F * (P1 ts1 x1 rho)) &&
                               (!! (forall rho',
                                           ((local (tc_environ (ret0_tycon Delta)) rho') &&
                                                 (F * (Q1 ts1 x1 rho')))
                                         |--
                                           bupd (Q2 ts2 x2 rho'))))
    end
end.

Lemma funspec_sub_sub_si f1 f2: funspec_sub f1 f2 -> TT |-- funspec_sub_si f1 f2.
Proof. intros. destruct f1; destruct f2; simpl in *.
destruct H as [? [? H']]; subst. intros w _. split; [split; trivial |].
intros ts2 x2 rho y WY k YK K c J.
destruct (H' ts2 x2 rho _ K c J) as (c' & J' & m' & ? & ? & ? & H''); subst.
destruct H'' as [ts1 [x1 [F [HF1 HF2]]]]; clear H'.
eexists; split; eauto; exists m'; repeat (split; auto).
exists ts1, x1, F; split; trivial.
intros rho' v KV z VZ Z. hnf in HF2. apply HF2; trivial.
Qed.
Lemma funspec_sub_sub_si' f1 f2: !!(funspec_sub f1 f2) |-- funspec_sub_si f1 f2.
Proof. intros w W. apply funspec_sub_sub_si; trivial.
Qed.

Lemma funspec_sub_early_sub_si f1 f2: funspec_sub_early f1 f2 |-- funspec_sub_si f1 f2.
Proof. intros p P. destruct f1; destruct f2; simpl in *.
destruct P as [[? ?] H']; subst. split; [split; trivial |].
intros ts2 x2 rho y WY k YK K c J.
destruct (H' ts2 x2 rho) as [ts1 [x1 [F HF]]]; clear H'.
destruct (HF _ WY _ YK K) as [(? & J' & m' & Hl & ? & ? & HF1) HF2]; eauto; subst.
eexists; split; eauto; exists m'; repeat (split; auto).
exists ts1, x1, F. rewrite Hl; auto.
Qed.

Lemma funspec_sub_refl f: funspec_sub f f.
Proof. destruct f; split; [ trivial | split; [trivial | intros ts2 x2 rho w [T W]]].
apply bupd_intro.
exists ts2, x2, emp. rewrite emp_sepcon. split; trivial. hnf; intros. 
rewrite emp_sepcon. apply andp_left2, bupd_intro.
Qed.

Lemma funspec_sub_trans f1 f2 f3: funspec_sub f1 f2 -> 
      funspec_sub f2 f3 -> funspec_sub f1 f3.
Proof. destruct f1; destruct f2; destruct f3; intros.
destruct H as [? [? H12]]; subst f0 c0.
destruct H0 as [? [? H23]]; subst f1 c1.
split; [ trivial | split; [ trivial | intros ts x rho]].
apply prop_andp_left; intro Hlocal.
eapply derives_trans.
{ eapply derives_trans, H23; apply andp_right; eauto; intros ??; auto. }
eapply derives_trans, bupd_trans; apply bupd_mono.
apply exp_left; intro ts1.
apply exp_left; intro x1.
apply exp_left; intro F.
eapply derives_trans; [apply andp_derives, derives_refl|].
{ eapply sepcon_derives, derives_trans, H12; [apply derives_refl|].
  apply andp_right; eauto; intros ??; auto. }
rewrite andp_comm, <- normalize.sepcon_andp_prop'.
eapply derives_trans; [apply bupd_frame_l | apply bupd_mono].
rewrite exp_sepcon2; apply exp_left; intros ts2.
rewrite exp_sepcon2; apply exp_left; intros x2.
rewrite exp_sepcon2; apply exp_left; intros G.
apply exp_right with ts2; apply exp_right with x2; apply exp_right with (F*G).
rewrite normalize.sepcon_andp_prop'.
rewrite (andp_comm _ (!! _)), sepcon_andp_prop.
rewrite <- andp_assoc, andp_comm; apply andp_derives.
{ rewrite sepcon_assoc; auto. }
intros ? [H1 H2]; simpl in *.
intros rho'; eapply derives_trans, bupd_trans.
eapply derives_trans, bupd_mono, H1.
apply prop_andp_left; intros Hlocal'.
unfold local; simpl; unfold lift1; simpl.
rewrite bupd_andp_prop; apply andp_right; [intros ??; auto|].
eapply derives_trans, bupd_frame_l.
rewrite sepcon_assoc; eapply sepcon_derives, derives_trans, H2; auto.
apply andp_right; auto; intros ??; auto.
Qed.

Lemma funspec_sub_early_refl f: TT |-- funspec_sub_early f f.
Proof. destruct f; split; [ split; trivial | clear H]. intros ts2 x2 rho.
exists ts2, x2, emp. intros y AY m YM [M1 M2]. rewrite emp_sepcon. split; [apply bupd_intro; trivial|].
intros rho' k WK u necKU U. rewrite emp_sepcon in U. apply bupd_intro, U.
Qed.

Lemma unfash_allp:  forall {A} {agA: ageable A} {B} (f: B -> pred nat),
  @unfash _ agA (allp f) = allp (fun x:B => unfash (f x)).
Proof.
intros.
apply pred_ext.
intros ? ? ?.
specialize (H b). auto.
repeat intro. apply (H b).
Qed.

Lemma allp_andp1 : forall {A} {agA: ageable A} {B} (P : B -> pred A) Q, (ALL a : B, P a) && Q |-- ALL a : B, P a && Q.
Proof.
  intros; apply allp_right; intro x.
  apply andp_derives; auto.
  apply allp_left with x; auto.
Qed.

Lemma unfash_exp:  forall {A} {agA: ageable A} {B} (f: B -> pred nat),
  @unfash _ agA (exp f) = exp (fun x:B => unfash (f x)).
Proof.
intros.
apply pred_ext.
intros ? [? ?]; simpl; eauto.
intros ? [? ?]; simpl in *; eauto.
Qed.

Lemma unfash_andp:  forall {A} {agA: ageable A} (P Q : pred nat),
  @unfash _ agA (andp P Q) = andp (unfash P) (unfash Q).
Proof.
intros.
apply pred_ext; intros ? []; split; auto.
Qed.

Lemma allp_sepcon1: forall {A} P Q, (ALL x : A, P x) * Q |-- ALL x : A, P x * Q.
Proof.
  intros.
  apply allp_right; intro x.
  apply sepcon_derives; auto.
  apply allp_left with x; auto.
Qed.

(* up *)
Lemma bupd_allp: forall {A} P, bupd (ALL x : A, P x) |-- ALL x : A, bupd (P x).
Proof.
  intros.
  apply allp_right; intro x.
  apply bupd_mono, allp_left with x; auto.
Qed.

Lemma bupd_unfash: forall P, bupd (! P) |-- ! P.
Proof.
  repeat intro; simpl in *.
  destruct (H (core (ghost_of a))) as (? & ? & ? & <- & ? & ? & ?); auto.
  rewrite ghost_core; eexists; constructor.
Qed.

Lemma bupd_andp_unfash: forall P Q, bupd (!P && Q) = !P && bupd Q.
Proof.
  intros; apply pred_ext.
  - apply andp_right.
    + eapply derives_trans; [apply bupd_mono, andp_left1, derives_refl|].
      apply bupd_unfash.
    + apply bupd_mono, andp_left2, derives_refl.
  - intros ? [? HQ] ? J.
    destruct (HQ _ J) as (? & ? & a' & Hl & ? & ? & ?); subst.
    eexists; split; eauto.
    exists a'; repeat (split; auto).
    simpl in *.
    rewrite Hl; auto.
Qed.

Lemma unfash_sepcon: forall P Q, !P * Q |-- !P.
Proof.
  intros ??? (? & ? & J & ? & ?); simpl in *.
  apply join_level in J as [<- _]; auto.
Qed.

Lemma subp_exp_left: forall {A} G P Q, (forall x, G |-- P x >=> Q) -> G |-- (EX x : A, P x) >=> Q.
Proof.
  repeat intro.
  destruct H3 as [x HP].
  eapply H; eauto.
Qed.

Lemma funspec_sub_early_trans f1 f2 f3: funspec_sub_early f1 f2 && funspec_sub_early f2 f3 |--
      funspec_sub_early f1 f3.
Proof. destruct f1; destruct f2; destruct f3.
unfold funspec_sub_early; simpl.
rewrite !andp_assoc; apply prop_andp_left; intros []; subst.
rewrite andp_comm, andp_assoc; apply prop_andp_left; intros []; subst.
apply andp_right; [intros ??; simpl; auto|].
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
rewrite exp_andp1; apply exp_left; intro ts1.
rewrite exp_andp1; apply exp_left; intro x1.
rewrite exp_andp1; apply exp_left; intro F.
rewrite andp_comm; eapply derives_trans; [apply allp_andp1|].
apply allp_left with ts1.
eapply derives_trans; [apply allp_andp1|].
apply allp_left with x1.
eapply derives_trans; [apply allp_andp1|].
apply allp_left with rho.
rewrite exp_andp1; apply exp_left; intro ts2.
rewrite exp_andp1; apply exp_left; intro x2.
rewrite exp_andp1; apply exp_left; intro G.
apply exp_right with ts2; apply exp_right with x2; apply exp_right with (F*G).
eapply subp_trans.
{ apply andp_left2.
  rewrite <- (andp_dup (local _ _)) at 2; rewrite andp_assoc; apply subp_andp, derives_refl; apply subp_refl. }
eapply subp_trans.
{ apply andp_left1.
  unfold local at 3; unfold lift1 at 1; simpl.
  rewrite <- andp_assoc, <- bupd_andp_prop.
  rewrite <- sepcon_andp_prop, (sepcon_comm F).
  eapply subp_andp, subp_refl; apply subp_bupd, subp_sepcon, subp_refl; apply derives_refl. }
apply derives_trans with TT; auto.
rewrite <- (andp_dup (bupd _)), andp_assoc; apply subp_andp.
+ eapply derives_trans, subp_derives, bupd_trans; [apply subp_refl|].
  apply bupd_mono.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply andp_left1, derives_refl|].
  rewrite sepcon_assoc; eapply derives_trans, bupd_frame_l.
  rewrite sepcon_comm; auto.
+ intros ? _; apply derives_subp.
  apply allp_right; intro rho'.
  eapply derives_trans.
  { eapply derives_trans, allp_andp1.
     apply andp_derives, derives_refl.
     eapply derives_trans, bupd_allp.
     apply bupd_mono; eapply derives_trans, allp_sepcon1. apply sepcon_derives, derives_refl; apply andp_left2, derives_refl. }
  apply allp_left with rho'.
  rewrite andp_comm; eapply derives_trans; [apply allp_andp1|].
  apply allp_left with rho'.
  eapply derives_trans; [apply andp_derives, bupd_mono, unfash_sepcon; apply derives_refl|].
  eapply derives_trans; [apply andp_derives, bupd_unfash; apply derives_refl|].
  rewrite <- unfash_andp; apply unfash_derives.
  eapply subp_trans.
  { apply andp_left2.
    rewrite <- (andp_dup (local _ _)) at 2; rewrite andp_assoc; apply subp_andp; [apply subp_refl|].
    unfold local, lift1; simpl.
    rewrite sepcon_assoc, <- (sepcon_andp_prop F).
    apply subp_sepcon, derives_refl; apply subp_refl. }
  eapply derives_trans, subp_derives, bupd_trans.
  2: { eapply andp_derives, bupd_frame_l; apply derives_refl. }
  unfold local at 3; unfold lift1; simpl.
  rewrite <- bupd_andp_prop; apply subp_bupd.
  apply andp_left1; auto.
Qed.

Lemma funspec_sub_si_refl f: TT |-- funspec_sub_si f f.
Proof. destruct f; split; [ split; trivial | clear H; intros ts2 x2 rho].
intros ?????; apply bupd_intro.
exists ts2, x2, emp; rewrite emp_sepcon. split. apply H1. 
intros rho' k WK u necKU Z.
rewrite emp_sepcon in Z. apply bupd_intro, Z.
Qed.

Lemma funspec_sub_si_trans f1 f2 f3: funspec_sub_si f1 f2 && funspec_sub_si f2 f3 |--
      funspec_sub_si f1 f3.
Proof. destruct f1; destruct f2; destruct f3.
unfold funspec_sub_si; simpl.
rewrite !andp_assoc; apply prop_andp_left; intros []; subst.
rewrite andp_comm, andp_assoc; apply prop_andp_left; intros []; subst.
apply andp_right; [intros ??; simpl; auto|].
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
  rewrite <- (andp_dup (local _ _)) at 2; rewrite andp_assoc; apply subp_andp, derives_refl; apply subp_refl. }
eapply subp_trans.
{ apply andp_left2.
  unfold local at 3; unfold lift1 at 1; simpl.
  rewrite <- bupd_andp_prop; apply subp_bupd.
  rewrite exp_andp2; apply subp_exp; intro ts1.
  rewrite exp_andp2; apply subp_exp; intro x1.
  rewrite exp_andp2; apply subp_exp; intro F.
  apply allp_left with ts1; apply allp_left with x1; apply allp_left with rho.
  rewrite <- andp_assoc, <- sepcon_andp_prop.
  apply subp_andp, subp_refl; apply subp_sepcon, derives_refl; apply subp_refl. }
apply derives_trans with TT; auto.
eapply derives_trans, subp_derives, bupd_trans; [|apply derives_refl].
apply subp_bupd.
apply subp_exp_left; intro ts1.
apply subp_exp_left; intro x1.
apply subp_exp_left; intro F.
rewrite <- unfash_allp, andp_comm.
eapply derives_trans, subp_derives, derives_refl; [|apply andp_derives, bupd_frame_l; apply derives_refl].
rewrite <- bupd_andp_unfash; apply subp_bupd.
rewrite exp_sepcon2, exp_andp2; apply subp_exp_left; intro ts2.
rewrite exp_sepcon2, exp_andp2; apply subp_exp_left; intro x2.
rewrite exp_sepcon2, exp_andp2; apply subp_exp_left; intro G.
eapply subp_trans, subp_exp_spec.
eapply subp_trans, subp_exp_spec.
eapply subp_trans, subp_exp_spec with (x0 := F*G).
eapply derives_trans, subp_derives, derives_refl; [|apply andp_derives, distrib_sepcon_andp; apply derives_refl].
rewrite andp_comm, andp_assoc; apply subp_andp.
+ rewrite sepcon_assoc; apply subp_refl.
+ rewrite <- unfash_allp; eapply derives_trans, subp_derives, derives_refl; [|apply andp_derives, derives_refl; rewrite sepcon_comm; apply unfash_sepcon].
  rewrite <- unfash_andp, <- unfash_allp; intros ? _; apply subp_unfash, derives_subp.
  apply allp_right; intro rho'.
  eapply derives_trans; [apply allp_andp1|].
  apply allp_left with rho'.
  eapply subp_trans.
  { apply andp_left1.
    rewrite <- (andp_dup (local _ _)) at 2; rewrite andp_assoc; apply subp_andp; [apply subp_refl|].
    unfold local, lift1; simpl.
    rewrite sepcon_assoc, <- (sepcon_andp_prop F).
    apply subp_sepcon, derives_refl; apply subp_refl. }
  eapply derives_trans, subp_derives, bupd_trans.
  2: { eapply andp_derives, bupd_frame_l; apply derives_refl. }
  unfold local at 3; unfold lift1; simpl.
  rewrite <- bupd_andp_prop; apply subp_bupd.
  apply andp_left2, allp_left with rho'; auto.
Qed.

(*******************end of material moved here from expr.v *******************)

Definition func_at (f: funspec): address -> pred rmap :=
  match f with
   | mk_funspec fsig cc A P Q _ _ => pureat (SomeP (SpecTT A) (packPQ P Q)) (FUN fsig cc)
  end. 

Definition func_at' (f: funspec) (loc: address) : pred rmap :=
  match f with
   | mk_funspec fsig cc _ _ _ _ _ => EX pp:_, pureat pp (FUN fsig cc) loc
  end.
Definition sigcc_at (fsig: funsig) (cc:calling_convention) (loc: address) : pred rmap :=
  EX pp:_, pureat pp (FUN fsig cc) loc.

Definition func_ptr_si (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, funspec_sub_si gs f && func_at gs (b, 0)).

Definition func_ptr_early (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, funspec_sub_early gs f && func_at gs (b, 0)).

Definition func_ptr (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, !!(funspec_sub gs f) && func_at gs (b, 0)).

Lemma func_ptr_early_func_ptr_si f v: func_ptr_early f v |-- func_ptr_si f v.
Proof. apply exp_derives; intros b. apply andp_derives; trivial.
 apply exp_derives; intros gs. apply andp_derives; trivial. apply funspec_sub_early_sub_si.
Qed.

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

Lemma func_ptr_early_mono fs gs v: 
      funspec_sub_early fs gs && func_ptr_early fs v |-- func_ptr_early gs v.
Proof.  unfold func_ptr_early. rewrite exp_andp2. apply exp_derives; intros b.
  rewrite andp_comm, andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm, exp_andp2. apply exp_derives; intros hs.
  rewrite <- andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm. apply funspec_sub_early_trans.
Qed.

Lemma func_ptr_mono fs gs v: funspec_sub fs gs -> 
      func_ptr fs v |-- func_ptr gs v.
Proof. intros. unfold func_ptr. apply exp_derives; intros b.
  apply andp_derives; trivial. apply exp_derives; intros hs.
  apply andp_derives; trivial.
  intros w W. eapply funspec_sub_trans. apply W. apply H.
Qed.

Lemma funspec_sub_early_implies_func_prt_si_mono fs gs v: 
      funspec_sub_early fs gs && func_ptr_si fs v |-- func_ptr_si gs v.
Proof. 
  eapply derives_trans. 2: apply func_ptr_si_mono.
  apply andp_derives. 2: apply derives_refl. apply funspec_sub_early_sub_si.
Qed.

Lemma funspec_sub_implies_func_prt_si_mono' fs gs v: 
      !!(funspec_sub fs gs) && func_ptr_si fs v |-- func_ptr_si gs v.
Proof.
  eapply derives_trans. 2: apply func_ptr_si_mono.
  apply andp_derives. 2: apply derives_refl. 
Search funspec_sub funspec_sub_si. apply funspec_sub_sub_si'. 
Qed.

Lemma funspec_sub_implies_func_prt_si_mono fs gs v: funspec_sub fs gs ->
      func_ptr_si fs v |-- func_ptr_si gs v.
Proof. intros. 
  eapply derives_trans. 2: apply funspec_sub_implies_func_prt_si_mono'. 
  apply andp_right. 2: apply derives_refl. hnf; intros; apply H. 
Qed.

Definition NDmk_funspec (f: funsig) (cc: calling_convention)
  (A: Type) (Pre Post: A -> environ -> mpred): funspec :=
  mk_funspec f cc (rmaps.ConstType A) (fun _ => Pre) (fun _ => Post)
             (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Lemma type_of_funspec_sub:
  forall fs1 fs2, funspec_sub fs1 fs2 ->
  type_of_funspec fs1 = type_of_funspec fs2.
Proof.
intros.
destruct fs1, fs2; destruct H as [? [? _]]. subst; simpl; auto.
Qed.

Lemma type_of_funspec_sub_si fs1 fs2:
  funspec_sub_si fs1 fs2 |-- !!(type_of_funspec fs1 = type_of_funspec fs2).
Proof.
intros w W.
destruct fs1, fs2. destruct W as [[? ?] _]. subst; simpl; auto.
Qed.

Lemma type_of_funspec_sub_early fs1 fs2:
  funspec_sub_early fs1 fs2 |-- !!(type_of_funspec fs1 = type_of_funspec fs2).
Proof.
eapply derives_trans. apply funspec_sub_early_sub_si. apply type_of_funspec_sub_si.
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

Fixpoint sepcon_list {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A} {AgeA: Age_alg A}
   (p: list (pred A)) : pred A :=
 match p with nil => emp | h::t => h * sepcon_list t end.

Definition typed_true (t: type) (v: val)  : Prop := strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t =
                                                   Some false.

Definition subst {A} (x: ident) (v: val) (P: environ -> A) : environ -> A :=
  fun s => P (env_set s x v).

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
Lemma func_ptr_early_isptr: forall spec f, func_ptr_early spec f |-- !! val_lemmas.isptr f.
Proof.
  intros.
  unfold func_ptr_early.
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
  change sepcon with predicates_sl.sepcon in *.
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    destruct H as [? [y [z [? [? ?]]]]].
    exists y, z; split; auto.
    split; split; auto.
    - apply age_sepalg.join_level in H0.
      omega.
    - apply age_sepalg.join_level in H0.
      omega.
  + intros w ?.
    simpl in *.
    destruct H as [y [z [? [[? ?] [? ?]]]]].
    split.
    - apply age_sepalg.join_level in H.
      omega.
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
  change andp with (@predicates_hered.andp compcert_rmaps.RML.R.rmap _) in *.
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
  - rewrite <- ghost_of_approx, Hg.
    rewrite !ghost_fmap_singleton, !preds_fmap_fmap.
    rewrite approx_oo_approx, approx_oo_approx', approx'_oo_approx by omega; auto.
  - rewrite ghost_fmap_singleton in *.
    rewrite preds_fmap_fmap in Hg.
    rewrite approx_oo_approx', approx'_oo_approx in Hg by omega; auto.
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
      eexists; split; eauto; eexists; split; eauto; repeat split; auto; omega.
  - intros ? HP.
    destruct (HP nil) as (? & ? & m' & ? & ? & ? & []).
    { eexists; constructor. }
    split; [omega|].
    intros ? J.
    destruct (HP _ J) as (? & ? & m'' & ? & ? & ? & []);
      eexists; split; eauto; eexists; split; eauto; repeat split; auto.
Qed.

Lemma approx_func_ptr_early: forall (A: Type) fsig0 cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
  approx n (func_ptr_early (NDmk_funspec fsig0 cc A P Q) v) = approx n (func_ptr_early (NDmk_funspec fsig0 cc A (fun a rho => approx n (P a rho)) (fun a rho => approx n (Q a rho))) v).
Proof.
  intros.
  unfold func_ptr_early.
  rewrite !approx_exp; f_equal; extensionality b.
  rewrite !approx_andp; f_equal.
  unfold func_at, NDmk_funspec.
  simpl.
  apply pred_ext; intros w; simpl; intros [? [g [G ?]]]; split; auto.
  + exists g. split; trivial. destruct g; clear H0; hnf; hnf in G; destruct G; split; trivial.
    intros ts x rho. destruct (H1 ts x rho) as [ts1 [x1 [F HF]]]; clear H1.
    exists ts1, x1, F. hnf; intros y Y z YZ [Z1 Z2]; specialize (HF _ Y _ YZ). apply approx_p in Z2.
    destruct HF as [HF1 HF2]. { split; trivial. }
    split. apply HF1. intros rho' u YU m UM M. specialize (HF2 rho' u YU m UM M).
    rewrite <- approx_bupd; split; auto.
    apply necR_level in UM. apply necR_level in YZ. omega.
  + exists g; split; trivial. destruct g; clear H0; hnf; hnf in G; destruct G; split; trivial.
    intros ts x rho. destruct (H1 ts x rho) as [ts1 [x1 [F HF]]]; clear H1.
    exists ts1, x1, F. hnf; intros y Y z YZ [Z1 Z2]; specialize (HF _ Y _ YZ).
    destruct HF as [HF1 HF2]. { split; trivial. apply approx_lt; trivial. apply necR_level in YZ. omega. }
    split. apply HF1. intros rho' u YU m UM M. specialize (HF2 rho' u YU m UM M).
    rewrite <- approx_bupd in HF2; apply HF2.
Qed.

Lemma approx_func_ptr_si: forall (A: Type) fsig0 cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
  approx n (func_ptr_si (NDmk_funspec fsig0 cc A P Q) v) = approx n (func_ptr_si (NDmk_funspec fsig0 cc A (fun a rho => approx n (P a rho)) (fun a rho => approx n (Q a rho))) v).
Proof.
  intros.
  unfold func_ptr_si.
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
    eapply funspec_sub_si_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial. 
    intros ts2 a rho m WM u necU [U1 U2]. simpl in U1.
    apply bupd_intro.
    exists ts2, a, emp. rewrite emp_sepcon; split. { apply approx_p in U2; trivial. }
    intros rho' y UY k YK K. rewrite emp_sepcon in K. simpl in K.
    rewrite <- approx_bupd.
    apply necR_level in necU.  apply necR_level in YK. split; [ omega | apply bupd_intro, K]. 
  + destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_si_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros ts2 a rho m WM u necU [U1 U2]. simpl in U1.
    apply bupd_intro.
    exists ts2, a, emp. rewrite emp_sepcon; split. 
    - apply necR_level in necU. apply approx_lt; trivial; omega.
    - intros rho' k UP j KJ J.
      rewrite emp_sepcon in J. simpl in J. apply bupd_intro, J.
Qed. 

Definition funspecs_assert (FunSpecs: PTree.t funspec): assert :=
 fun rho =>
   (ALL  id: ident, ALL fs:funspec,  !! (FunSpecs!id = Some fs) -->
              EX b:block,
                   !! (Map.get (ge_of rho) id = Some b) && func_at fs (b,0))
 &&  (ALL  b: block, ALL fsig:funsig, ALL cc: calling_convention, sigcc_at fsig cc (b,0) -->
             EX id:ident, !! (Map.get (ge_of rho) id = Some b)
                             && !! exists fs, FunSpecs!id = Some fs).

Definition globals_only (rho: environ) : environ := (mkEnviron (ge_of rho) (Map.empty _) (Map.empty _)).

Fixpoint make_args (il: list ident) (vl: list val) (rho: environ)  :=
  match il, vl with
  | nil, nil => globals_only rho
  | i::il', v::vl' => env_set (make_args il' vl' rho) i v
   | _ , _ => rho
  end.

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
  + intros loc sig cc w' Hw' HH. hnf in H0. destruct (H1 loc sig cc w' Hw' HH)  as [id ID].
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
  + split. trivial. split. trivial. intros. simpl. intros w [W1 W2].
    apply bupd_intro. exists ts2, (inl x2), emp. rewrite emp_sepcon.
    split. trivial. simpl; intros. rewrite emp_sepcon.
    apply andp_left2, bupd_intro.
  + split. trivial. split. trivial. intros. simpl. intros w [W1 W2].
    apply bupd_intro. exists ts2, (inr x2), emp. rewrite emp_sepcon.
    split. trivial. simpl; intros. rewrite emp_sepcon.
    apply andp_left2, bupd_intro.
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_intersection_ND_sub3 {fA cA A PA QA fB cB B PB QB fC cC C PC QC} f1 F1 f2 F2 f
      (I: funspec_intersection_ND fA cA A PA QA f1 F1 fB cB B PB QB f2 F2 = Some f) g
      (G: g = NDmk_funspec fC cC C PC QC):
  funspec_sub g f1 -> funspec_sub g f2 -> funspec_sub g f.
Proof.
  subst. intros. destruct H as [? [? G1]]; subst fA cA. destruct H0 as [? [? G2]]; subst fB cB.
  unfold funspec_intersection_ND in I. simpl in I.
  do 2 rewrite if_true in I; trivial. inv I. simpl. split. trivial. split. trivial. intros.
  destruct x2 as [a | b]; auto.
Qed.

(*-------------------- ND case, specification Sigma families --------------------- *)

Definition funspec_Sigma_ND (sig:funsig) (cc:calling_convention) (I:Type) (A : I -> Type)
           (Pre Post: forall i, A i -> environ -> mpred): funspec.
Proof.
  apply (NDmk_funspec sig cc (sigT A)).
  intros [i Ai] rho; apply (Pre _ Ai rho).
  intros [i Ai] rho; apply (Post _ Ai rho). 
Defined.

(*The two rules S-inter1 and S-inter2 from page 206 of TAPL*)
Lemma funspec_Sigma_ND_sub fsig cc I A Pre Post i:
  funspec_sub (funspec_Sigma_ND fsig cc I A Pre Post) (NDmk_funspec fsig cc (A i) (Pre i) (Post i)).
Proof.
  unfold funspec_Sigma_ND. split. trivial. split. trivial. intros; simpl in *.
  eapply derives_trans, bupd_intro.
  exists ts2, (existT A i x2), emp. rewrite emp_sepcon.
  split. apply H. simpl; intros. rewrite emp_sepcon.
  intros u U. apply bupd_intro, U.
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_Sigma_ND_sub3 fsig cc I A Pre Post g (i:I)
      (HI: forall i,  funspec_sub g (NDmk_funspec fsig cc (A i) (Pre i) (Post i))):
  funspec_sub g (funspec_Sigma_ND fsig cc I A Pre Post).
Proof.
  assert (HIi := HI i). destruct g. destruct HIi as [? [? Hi]]; subst f c.
  split. trivial. split. trivial.
  simpl; intros. clear i Hi. destruct x2 as [i Ai].
  specialize (HI i). destruct HI as [_ [_ Hi]]. apply (Hi ts2 Ai rho).
Qed.

(*Specialization of funspec_Sigma_ND to binary case, i.e. I=bool*)
Program Definition BinarySigma fsig cc (A B:Type)
        (PA QA: A -> environ ->mpred) (PB QB:B -> environ -> mpred): funspec :=
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
  + split. trivial. split. trivial. simpl; intros. destruct x2 as [i p].
    eapply derives_trans, bupd_intro. destruct i; simpl in *.
  - exists ts2, (inl p), emp. rewrite emp_sepcon. split; simpl. apply H.
    intros. rewrite emp_sepcon. intros u U; apply bupd_intro, U.
  - exists ts2, (inr p), emp. rewrite emp_sepcon. split; simpl. apply H.
    intros. rewrite emp_sepcon. intros u U; apply bupd_intro, U. 
    + split. trivial. split. trivial. intros. intros u [L U]. destruct x2.
  - apply bupd_intro. exists ts2, (existT (BinarySigma_obligation_1 A B) true a), emp.
    rewrite emp_sepcon. simpl; split. apply U. intros. rewrite emp_sepcon.
    apply andp_left2, bupd_intro.
  - apply bupd_intro. exists ts2, (existT (BinarySigma_obligation_1 A B) false b), emp.
    rewrite emp_sepcon. simpl; split. apply U. intros. rewrite emp_sepcon.
    apply andp_left2, bupd_intro.
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

Definition binary_intersection (phi psi:funspec): option funspec.
  destruct phi as [f c A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct (eq_dec f f2); [subst f2 | apply None].
  destruct (eq_dec c c2); [subst c2 | apply None].
  remember (binarySUM P1 P2) as P.
  remember (binarySUM Q1 Q2) as Q.
  apply Some. apply (mk_funspec f c _ P Q).
  subst P; apply (binarySUM_ne P1_ne P2_ne).
  subst Q; apply (binarySUM_ne Q1_ne Q2_ne).
Defined.

Lemma binaryintersection_sub phi psi omega:
  binary_intersection phi psi = Some omega ->
  funspec_sub omega phi /\  funspec_sub omega psi.
Proof.
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne]. intros.
  simpl in H.
  destruct (eq_dec f1 f2); [ subst f2 | inv H]. 
  destruct (eq_dec c1 c2); inv H.
  apply inj_pair2 in H5. apply inj_pair2 in H4. subst P Q. split.
  + split3; try solve [reflexivity]; intros. eapply derives_trans, bupd_intro. exists ts2.
    fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
    simpl in H; destruct H.
    exists (existT _ true x2), emp.
    rewrite emp_sepcon.
    split. apply H0.
    simpl. intros rho'; rewrite emp_sepcon. apply andp_left2; apply bupd_intro.
  + split3; try solve [reflexivity]; intros. eapply derives_trans, bupd_intro. exists ts2.
    fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
    simpl in H; destruct H.
    exists (existT _ false x2), emp.
    rewrite emp_sepcon.
    split. apply H0.
    simpl. intros rho'; rewrite emp_sepcon. apply andp_left2; apply bupd_intro.
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
  destruct H0 as [? [? ?]]; subst f' c'.
  destruct H1 as [_ [_ ?]]. 
  split3; try solve [reflexivity]; intros. simpl in x2.
  specialize (H ts2). specialize (H2 ts2). 
  fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
  destruct x2 as [b Hb]; destruct b; eauto.
Qed. 

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

Definition callingconvention_of_funspec (phi:funspec):calling_convention :=
  match phi with
    mk_funspec sig cc A P Q Pne Qne => cc
  end.

Definition WithType_of_funspec (phi:funspec):TypeTree :=
  match phi with
    mk_funspec sig cc A P Q Pne Qne => A
  end.

Definition intersectionPRE {I} phi:
  forall (i : I) (ts : list Type),
    (dependent_type_functor_rec ts (AssertTT (WithType_of_funspec (phi i)))) mpred.
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
           (AssertTT (SigType I (fun i : I => WithType_of_funspec (phi i)))))
          mpred.
Proof. intros. apply (generalSUM _ (intersectionPRE phi)). Defined.

Definition iPost {I} phi:
forall ts : list Type,
        (dependent_type_functor_rec ts
           (AssertTT (SigType I (fun i : I => WithType_of_funspec (phi i)))))
          mpred.
Proof. intros. apply (generalSUM _ (intersectionPOST phi)). Defined.

Lemma iPre_ne {I} (phi: I -> funspec): super_non_expansive (iPre phi).
Proof.
  unfold iPre. apply generalSUM_ne.
  intros. unfold intersectionPRE. simpl. destruct (phi i); trivial.
Qed.

Lemma iPost_ne {I} (phi: I -> funspec): super_non_expansive (iPost phi).
Proof.
  unfold iPost. apply generalSUM_ne.
  intros. unfold intersectionPOST. simpl. destruct (phi i); trivial.
Qed.

Definition general_intersection {I sig cc} (phi: I -> funspec) 
           (Hsig: forall i, funsig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc): funspec.
Proof.
  apply (mk_funspec sig cc
                    ((@SigType I (fun i => WithType_of_funspec (phi i))))
                    (iPre phi) (iPost phi)).
  apply iPre_ne.
  apply iPost_ne.
Defined.

Lemma generalintersection_sub {I sig cc} (phi: I -> funspec) 
           (Hsig: forall i, funsig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc) omega:
  general_intersection phi Hsig Hcc = omega ->
  forall i,  funspec_sub omega (phi i).
Proof.
  intros; subst. hnf. simpl funsig_of_funspec in *.
  specialize (Hsig i); specialize (Hcc i); subst.
  unfold  general_intersection; simpl.
  remember (phi i) as zz; destruct zz; intros; split3; try reflexivity; intros.
  eapply derives_trans, bupd_intro.
  exists ts2. simpl in H; destruct H.
  assert (exists D: (dependent_type_functor_rec ts2 (WithType_of_funspec (phi i))) mpred,
         JMeq.JMeq x2 D).
  { rewrite <- Heqzz. simpl. exists x2. constructor. }
  destruct H1 as [D HD].
  unfold iPre, intersectionPRE, generalSUM. 
  exists (existT _ i D), emp.  
  rewrite emp_sepcon. split; simpl.
  + remember (phi i). destruct f0.
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5; apply inj_pair2 in H6; subst P0 Q0.
    inv HD. apply inj_pair2 in H1; subst; trivial. 
  + intros; rewrite emp_sepcon. unfold intersectionPOST.
    intros x [X1 X2]. destruct (phi i).
    apply bupd_intro.
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5; apply inj_pair2 in H6; subst P0 Q0.
    inv HD. apply inj_pair2 in H1; subst; trivial. 
Qed.

Lemma generalintersection_sub3  {I sig cc}
      (INH: inhabited I) (phi: I -> funspec) 
           (Hsig: forall i, funsig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc) omega:
  general_intersection phi Hsig Hcc = omega ->
  forall xi, (forall i, funspec_sub xi (phi i)) -> funspec_sub xi omega.
Proof.
  intros. subst. inv INH; rename X into i.
  unfold general_intersection. 
  destruct xi as [f c A P Q P_ne Q_ne].
  split3.
  { specialize (H0 i); specialize (Hsig i). destruct (phi i); subst; apply H0. }
  { specialize (H0 i); specialize (Hcc i). destruct (phi i); subst; apply H0. }
  intros. simpl. simpl in x2. clear i. destruct x2 as [i Hi]. simpl.
  specialize (H0 i); specialize (Hsig i); specialize (Hcc i); subst; simpl.
  unfold intersectionPRE, intersectionPOST.
  forget (phi i) as zz. clear phi.
  destruct zz. simpl in *.
  destruct H0 as [? [? ?]]; subst.
  apply (H1 ts2 Hi rho). 
Qed.