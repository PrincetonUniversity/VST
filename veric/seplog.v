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

Definition funspec_sub (f1 f2 : funspec):mpred :=
let Delta := funsig_tycontext (funsig_of_funspec f1) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        !!(fsig1 = fsig2 /\ cc1=cc2) &&
        ! (ALL ts2 :_, ALL x2:_, ALL rho:_,
        (((local (tc_environ Delta) rho) && (P2 ts2 x2 rho))
         >=> EX ts1:_,  EX x1:_, EX F:_, 
            (F * (P1 ts1 x1 rho)) &&
            ALL rho':_, (     !( ((local (tc_environ (ret0_tycon Delta)) rho') && (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho')))))
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
         >=> (*EX ts1:_,  EX x1:_, EX F:_, *)
            (F * (P1 ts1 x1 rho)) &&
            ALL rho':_, (     !( ((local (tc_environ (ret0_tycon Delta)) rho') && (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho')))))
    end
end.

Definition funspec_sub_weak (f1 f2 : funspec):Prop :=
let Delta := funsig_tycontext (funsig_of_funspec f1) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        fsig1 = fsig2 /\ cc1=cc2 /\
        forall (ts2 : list Type) x2 rho,
               ((local (tc_environ Delta) rho) && (P2 ts2 x2 rho))
           |--
               (EX ts1:_,  EX x1:_, EX F:_, 
                           (F * (P1 ts1 x1 rho)) &&
                               (!! (forall rho',
                                           ((local (tc_environ (ret0_tycon Delta)) rho') &&
                                                 (F * (Q1 ts1 x1 rho')))
                                         |--
                                           (Q2 ts2 x2 rho'))))
    end
end.

Lemma Weak_Full f1 f2: funspec_sub_weak f1 f2 -> TT |-- funspec_sub f1 f2.
Proof. intros. destruct f1; destruct f2; simpl in *.
destruct H as [? [? H']]; subst. intros w _. split; [split; trivial |].
intros ts2 x2 rho y WY k YK K.
destruct (H' ts2 x2 rho _ K) as [ts1 [x1 [F [HF1 HF2]]]]; clear H'.
exists ts1, x1, F; split; trivial.
intros rho' v KV z VZ Z. hnf in HF2. apply HF2; trivial.
Qed.
Lemma Weak_Full' f1 f2: !!(funspec_sub_weak f1 f2) |-- funspec_sub f1 f2.
Proof. intros w W. apply Weak_Full; trivial.
Qed.

Lemma Early_Full f1 f2: funspec_sub_early f1 f2 |-- funspec_sub f1 f2.
Proof. intros p P. destruct f1; destruct f2; simpl in *.
destruct P as [[? ?] H']; subst. split; [split; trivial |].
intros ts2 x2 rho y WY k YK K.
destruct (H' ts2 x2 rho) as [ts1 [x1 [F HF]]]; clear H'.
exists ts1, x1, F. apply (HF _ WY _ YK K).
Qed.

Lemma funspec_sub_weak_refl f: funspec_sub_weak f f.
Proof. destruct f; split; [ trivial | split; [trivial | intros ts2 x2 rho w [T W]]].
exists ts2, x2, emp. rewrite emp_sepcon. split; trivial. hnf; intros. 
rewrite emp_sepcon. apply andp_left2; trivial.
Qed.

Lemma funspec_sub_weak_trans f1 f2 f3: funspec_sub_weak f1 f2 -> 
      funspec_sub_weak f2 f3 -> funspec_sub_weak f1 f3.
Proof. destruct f1; destruct f2; destruct f3; intros.
destruct H as [? [? H12]]; subst f0 c0.
destruct H0 as [? [? H23]]; subst f1 c1.
split; [ trivial | split; [ trivial | intros ts x rho m M]]; simpl in M.
destruct (H23 ts x rho _ M) as [ts1 [x1 [F [X23 Y23]]]]; clear H23; hnf in Y23.
destruct X23 as [m1 [m2 [JM [M1 M2]]]]; destruct (join_level _ _ _ JM) as [Lev_m1 Lev_m2].
destruct (H12 ts1 x1 rho m2) as [ts2 [x2 [G [X12 Y12]]]]; clear H12; try hnf in Y12.
{ split; simpl; [ apply M | trivial]. }
exists ts2, x2, (F*G); split.
+ rewrite sepcon_assoc. exists m1, m2; auto.
+ intros rho'. simpl. unfold local, lift1.
   specialize (derives_extract_prop (tc_environ (ret0_tycon (funsig_tycontext f)) rho')
              (sepcon (sepcon F G) (Q ts2 x2 rho')) (Q1 ts x rho')). intros.
   unfold seplog.derives in H. apply H; clear H. simpl. intros.
   eapply derives_trans. 2: apply Y23. clear Y23.
   unfold local, lift1; simpl.  rewrite <- sepcon_andp_prop, sepcon_assoc.
   apply sepcon_derives; trivial. apply andp_right.
   intros w W; apply H.
   eapply derives_trans. 2: apply Y12. simpl. apply prop_andp_right; trivial.
Qed.

Lemma funspec_sub_early_refl f: TT |-- funspec_sub_early f f.
Proof. destruct f; split; [ split; trivial | clear H]. intros ts2 x2 rho.
exists ts2, x2, emp. intros y AY m YM [M1 M2]. rewrite emp_sepcon. split; trivial.
intros rho' k WK u necKU U. rewrite emp_sepcon in U. apply U.
Qed.

Lemma funspec_sub_early_trans f1 f2 f3: funspec_sub_early f1 f2 && funspec_sub_early f2 f3 |--
      funspec_sub_early f1 f3.
Proof. destruct f1; destruct f2; destruct f3.
intros w [[X H12] [Y H23]]; destruct X; subst; destruct Y; subst; split; [split; trivial|].
intros ts x rho. 
destruct (H23 ts x rho) as [ts1 [x1 [F X23]]]; clear H23. hnf in X23.
destruct (H12 ts1 x1 rho) as [ts3 [x3 [G X12]]]; clear H12. hnf in X12.
exists ts3, x3, (F * G). intros y WY m YM M.
destruct (X23 _ WY _ YM M) as [A23 B23]; clear X23.
destruct A23 as [m1 [m2 [JM [M1 M2]]]]; destruct (join_level _ _ _ JM) as [Lev_m1 Lev_m2].
assert (Wm2: (level w >= level m2)%nat) by (apply necR_level in YM; omega).
specialize (X12 _ Wm2 _ (necR_refl _)). destruct X12 as [A12 B12].
{ destruct M as [HM1 HM2]; simpl in HM1. split; simpl; trivial. }
split.
+ rewrite sepcon_assoc. exists m1, m2; auto. 
+ intros rho' k MK v KV [Z V]. rewrite sepcon_assoc in V.
  destruct V as [v1 [v2 [JV [V1 V2]]]]; destruct (join_level _ _ _ JV) as [Lev_v1 Lev_v2].
  assert (M2v2: (level m2 >= level v2)%nat) by (apply necR_level in KV; omega).
  specialize (B12 rho' _ M2v2 _ (necR_refl _)). spec B12.
  { split; trivial. }
  assert (Mv: (level m >= level v)%nat) by (apply necR_level in KV; omega).
  apply (B23 rho' _ Mv _ (necR_refl _)). split; [ trivial | exists v1, v2; auto].
Qed.

Lemma funspec_sub_refl f: TT |-- funspec_sub f f.
Proof. destruct f; split; [ split; trivial | clear H; intros ts2 x2 rho].
exists ts2, x2, emp; rewrite emp_sepcon. split. apply H1. 
intros rho' k WK u necKU Z. 
rewrite emp_sepcon in Z. apply Z.
Qed.

Lemma funspec_sub_trans f1 f2 f3: funspec_sub f1 f2 && funspec_sub f2 f3 |--
      funspec_sub f1 f3.
Proof. destruct f1; destruct f2; destruct f3.
intros w [[X H12] [Y H23]]; destruct X; subst; destruct Y; subst; split; [split; trivial|].
intros ts x rho y WY m YM M. 
destruct (H23 ts x rho _ WY _ YM M) as [ts1 [x1 [F [A23 B23]]]]; clear H23. hnf in B23.
destruct A23 as [m1 [m2 [JM [M1 M2]]]]; destruct (join_level _ _ _ JM) as [Lev_m1 Lev_m2].
assert (Wm2: (level w >= level m2)%nat) by (apply necR_level in YM; omega).
destruct (H12 ts1 x1 rho _ Wm2 _ (necR_refl _)) as [ts3 [x3 [G [A12 B12]]]]; clear H12.
{ split; trivial; apply M. }
exists ts3, x3, (F * G); split.
+ rewrite sepcon_assoc. exists m1, m2; auto.
+ intros rho' k MK v KV [Z V]. rewrite sepcon_assoc in V.
  destruct V as [v1 [v2 [JV [V1 V2]]]]; destruct (join_level _ _ _ JV) as [Lev_v1 Lev_v2].
  assert (M2v2: (level m2 >= level v2)%nat) by (apply necR_level in KV; omega).
  specialize (B12 rho' _ M2v2 _ (necR_refl _)). spec B12.
  { split; trivial. }
  assert (Mv: (level m >= level v)%nat) by (apply necR_level in KV; omega).
  apply (B23 rho' _ Mv _ (necR_refl _)). split; [ trivial | exists v1, v2; auto].
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

Definition func_ptr (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, funspec_sub gs f && func_at gs (b, 0)).

Definition func_ptr_early (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, funspec_sub_early gs f && func_at gs (b, 0)).

Definition func_ptr_weak (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, !!(funspec_sub_weak gs f) && func_at gs (b, 0)).

Lemma func_ptr_early_full f v: func_ptr_early f v |-- func_ptr f v.
Proof. apply exp_derives; intros b. apply andp_derives; trivial.
 apply exp_derives; intros gs. apply andp_derives; trivial. apply Early_Full.
Qed.

Lemma func_ptr_weak_full f v: func_ptr_weak f v |-- func_ptr f v.
Proof. apply exp_derives; intros b. apply andp_derives; trivial.
 apply exp_derives; intros gs. apply andp_derives; trivial. apply Weak_Full'.
Qed.

Lemma funspec_subsume_func_ptr_derives fs gs v: 
      funspec_sub fs gs && func_ptr fs v |-- func_ptr gs v.
Proof. unfold func_ptr. rewrite exp_andp2. apply exp_derives; intros b.
  rewrite andp_comm, andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm, exp_andp2. apply exp_derives; intros hs.
  rewrite <- andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm. apply funspec_sub_trans.
Qed.

Lemma funspec_subsume_early_func_ptr_derives fs gs v: 
      funspec_sub_early fs gs && func_ptr fs v |-- func_ptr gs v.
Proof. eapply derives_trans. 2: apply (funspec_subsume_func_ptr_derives fs).
  apply andp_derives; trivial. apply Early_Full.
Qed.

Lemma funspec_subsume_early_func_ptr_early_derives fs gs v: 
      funspec_sub_early fs gs && func_ptr_early fs v |-- func_ptr_early gs v.
Proof. unfold func_ptr_early. rewrite exp_andp2. apply exp_derives; intros b.
  rewrite andp_comm, andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm, exp_andp2. apply exp_derives; intros hs.
  rewrite <- andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm. apply funspec_sub_early_trans.
Qed.

Lemma funspec_subsume_weak_func_ptr_derives fs gs v: funspec_sub_weak fs gs -> 
      func_ptr fs v |-- func_ptr gs v.
Proof. intros. unfold func_ptr. apply exp_derives; intros b.
  apply andp_derives; trivial. apply exp_derives; intros hs.
  apply andp_derives; trivial. apply Weak_Full in H. 
  intros w W. eapply funspec_sub_trans. split. apply W. apply H; trivial.
Qed.

Lemma funspec_subsume_weak_func_ptr_weak_derives fs gs v: funspec_sub_weak fs gs -> 
      func_ptr_weak fs v |-- func_ptr_weak gs v.
Proof. intros. unfold func_ptr_weak. apply exp_derives; intros b.
  apply andp_derives; trivial. apply exp_derives; intros hs.
  apply andp_derives; trivial. 
  intros w W. eapply funspec_sub_weak_trans; [ apply W | apply H].
Qed.

Definition NDmk_funspec (f: funsig) (cc: calling_convention)
  (A: Type) (Pre Post: A -> environ -> mpred): funspec :=
  mk_funspec f cc (rmaps.ConstType A) (fun _ => Pre) (fun _ => Post)
             (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Lemma type_of_funspec_sub:
  forall fs1 fs2, funspec_sub_weak fs1 fs2 ->
  type_of_funspec fs1 = type_of_funspec fs2.
Proof.
intros.
destruct fs1, fs2; destruct H as [? [? _]]. subst; simpl; auto.
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
    apply approx_lt; trivial. apply necR_level in UM. apply necR_level in YZ. omega.
  + exists g; split; trivial. destruct g; clear H0; hnf; hnf in G; destruct G; split; trivial.
    intros ts x rho. destruct (H1 ts x rho) as [ts1 [x1 [F HF]]]; clear H1.
    exists ts1, x1, F. hnf; intros y Y z YZ [Z1 Z2]; specialize (HF _ Y _ YZ).
    destruct HF as [HF1 HF2]. { split; trivial. apply approx_lt; trivial. apply necR_level in YZ. omega. }
    split. apply HF1. intros rho' u YU m UM M. specialize (HF2 rho' u YU m UM M).
    apply approx_p in HF2. trivial.
Qed.

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
    intros ts2 a rho m WM u necU [U1 U2]. simpl in U1.
    exists ts2, a, emp. rewrite emp_sepcon; split. { apply approx_p in U2; trivial. } 
    intros rho' y UY k YK K; hnf; intros. rewrite emp_sepcon in K. simpl in K.
    apply necR_level in necU.  apply necR_level in YK. split; [ omega | apply K]. 
  + destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros ts2 a rho m WM u necU [U1 U2]. simpl in U1.
    exists ts2, a, emp. rewrite emp_sepcon; split. 
    - apply necR_level in necU. apply approx_lt; trivial; omega.
    - intros rho' k UP j KJ J.
      rewrite emp_sepcon in J. simpl in J. apply J.
Qed. 

Definition funspecs_assert (FunSpecs: PTree.t funspec): assert :=
 fun rho =>
   (ALL  id: ident, ALL fs:funspec,  !! (FunSpecs!id = Some fs) -->
              EX b:block,
                   !! (Map.get (ge_of rho) id = Some b) && func_at fs (b,0))
 &&  (ALL  b: block, (*WAS: ALL fs:funspec, WAS:func_at' fs (b,0) -->*)
             (*NOW:*) ALL fsig:funsig, ALL cc: calling_convention, sigcc_at fsig cc (b,0) -->
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