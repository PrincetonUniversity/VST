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

Definition funspec_sub_si (f1 f2 : funspec):mpred :=
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

Definition funspec_sub (f1 f2 : funspec):Prop :=
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

Lemma funspec_sub_sub_si f1 f2: funspec_sub f1 f2 -> TT |-- funspec_sub_si f1 f2.
Proof. intros. destruct f1; destruct f2; simpl in *.
destruct H as [? [? H']]; subst. intros w _. split; [split; trivial |].
intros ts2 x2 rho y WY k YK K.
destruct (H' ts2 x2 rho _ K) as [ts1 [x1 [F [HF1 HF2]]]]; clear H'.
exists ts1, x1, F; split; trivial.
intros rho' v KV z VZ Z. hnf in HF2. apply HF2; trivial.
Qed.
Lemma funspec_sub_sub_si' f1 f2: !!(funspec_sub f1 f2) |-- funspec_sub_si f1 f2.
Proof. intros w W. apply funspec_sub_sub_si; trivial.
Qed.

Lemma funspec_sub_early_sub_si f1 f2: funspec_sub_early f1 f2 |-- funspec_sub_si f1 f2.
Proof. intros p P. destruct f1; destruct f2; simpl in *.
destruct P as [[? ?] H']; subst. split; [split; trivial |].
intros ts2 x2 rho y WY k YK K.
destruct (H' ts2 x2 rho) as [ts1 [x1 [F HF]]]; clear H'.
exists ts1, x1, F. apply (HF _ WY _ YK K).
Qed.

Lemma funspec_sub_refl f: funspec_sub f f.
Proof. destruct f; split; [ trivial | split; [trivial | intros ts2 x2 rho w [T W]]].
exists ts2, x2, emp. rewrite emp_sepcon. split; trivial. hnf; intros. 
rewrite emp_sepcon. apply andp_left2; trivial.
Qed.

Lemma funspec_sub_trans f1 f2 f3: funspec_sub f1 f2 -> 
      funspec_sub f2 f3 -> funspec_sub f1 f3.
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

Lemma funspec_sub_si_refl f: TT |-- funspec_sub_si f f.
Proof. destruct f; split; [ split; trivial | clear H; intros ts2 x2 rho].
exists ts2, x2, emp; rewrite emp_sepcon. split. apply H1. 
intros rho' k WK u necKU Z. 
rewrite emp_sepcon in Z. apply Z.
Qed.

Lemma funspec_sub_si_trans f1 f2 f3: funspec_sub_si f1 f2 && funspec_sub_si f2 f3 |--
      funspec_sub_si f1 f3.
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
    exists ts2, a, emp. rewrite emp_sepcon; split. { apply approx_p in U2; trivial. } 
    intros rho' y UY k YK K; hnf; intros. rewrite emp_sepcon in K. simpl in K.
    apply necR_level in necU.  apply necR_level in YK. split; [ omega | apply K]. 
  + destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_si_trans; split. apply SUBS. clear SUBS H0; hnf.
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
    exists ts2, (inl x2), emp. rewrite emp_sepcon.
    split. trivial. simpl; intros. rewrite emp_sepcon.
    intros u U. apply U.                                      
  + split. trivial. split. trivial. intros. simpl. intros w [W1 W2].
    exists ts2, (inr x2), emp. rewrite emp_sepcon.
    split. trivial. simpl; intros. rewrite emp_sepcon.
    intros u U. apply U.
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

(*-------------------- ND case, specification families --------------------- *)

Definition funspec_Pi_ND (sig:funsig) (cc:calling_convention) (I:Type) (A : I -> Type)
           (Pre Post: forall i, A i -> environ -> mpred): funspec.
Proof.
  apply (NDmk_funspec sig cc (sigT A)).
  intros [i Ai] rho; apply (Pre _ Ai rho).
  intros [i Ai] rho; apply (Post _ Ai rho). 
Defined.

(*The two rules S-inter1 and S-inter2 from page 206 of TAPL*)
Lemma funspec_Pi_ND_sub fsig cc I A Pre Post i:
  funspec_sub (funspec_Pi_ND fsig cc I A Pre Post) (NDmk_funspec fsig cc (A i) (Pre i) (Post i)).
Proof.
  unfold funspec_Pi_ND. split. trivial. split. trivial. intros; simpl in *. 
  exists ts2, (existT A i x2), emp. rewrite emp_sepcon.
  split. apply H. simpl; intros. rewrite emp_sepcon.
  intros u U. apply U.                                      
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_Pi_ND_sub3 fsig cc I A Pre Post g (i:I)
      (HI: forall i,  funspec_sub g (NDmk_funspec fsig cc (A i) (Pre i) (Post i))):
  funspec_sub g (funspec_Pi_ND fsig cc I A Pre Post).
Proof.
  assert (HIi := HI i). destruct g. destruct HIi as [? [? Hi]]; subst f c.
  split. trivial. split. trivial.
  simpl; intros. clear i Hi. destruct x2 as [i Ai].
  specialize (HI i). destruct HI as [_ [_ Hi]]. apply (Hi ts2 Ai rho).
Qed.

(*Specialization of funspec_Pi_ND to binary case, i.e. I=bool*)
Program Definition BinaryPi fsig cc (A B:Type)
        (PA QA: A -> environ ->mpred) (PB QB:B -> environ -> mpred): funspec :=
  funspec_Pi_ND fsig cc bool _ _ _.
Proof.
  Next Obligation.
    intros sig cc A B PA QA PB QB x. destruct x. apply A. apply B.
  Defined.
  Next Obligation.
    intros ? ? ? ? ? ? ? ? b X rho. destruct b; simpl in X. apply (PA X rho). apply (PB X rho).
  Defined.
  Next Obligation.
    intros ? ? ? ? ? ? ? ? b X rho. destruct b; simpl in X. apply (QA X rho). apply (QB X rho).
  Defined.

Definition funspecspec_sub_antisym (f g: funspec):= funspec_sub f g /\ funspec_sub g f.
  
Lemma Intersection_BinaryPi sigA ccA A PA QA fsA PrfA sigB ccB B PB QB fsB PrfB f
      (F:  funspec_intersection_ND sigA ccA A PA QA fsA PrfA sigB ccB B PB QB fsB PrfB  = Some f):
  sigA=sigB /\ ccA=ccB /\
  funspecspec_sub_antisym f (BinaryPi sigA ccA A B PA QA PB QB).
Proof.
  unfold funspec_intersection_ND in F.
  destruct (eq_dec sigA sigB); [ subst sigA; split; trivial | discriminate].
  destruct (eq_dec ccA ccB); [ inv F; split; trivial | discriminate]. 
  split.
  + split. trivial. split. trivial. simpl; intros. destruct x2 as [i p].
    destruct i; simpl in *.
  - exists ts2, (inl p), emp. rewrite emp_sepcon. split; simpl. apply H.
    intros. rewrite emp_sepcon. intros u U; apply U.
  - exists ts2, (inr p), emp. rewrite emp_sepcon. split; simpl. apply H.
    intros. rewrite emp_sepcon. intros u U; apply U. 
    + split. trivial. split. trivial. intros. intros u [L U]. destruct x2.
  - exists ts2, (existT (BinaryPi_obligation_1 A B) true a), emp.
    rewrite emp_sepcon. simpl; split. apply U. intros. rewrite emp_sepcon.
    intros w W. apply W.
  -  exists ts2, (existT (BinaryPi_obligation_1 A B) false b), emp.
     rewrite emp_sepcon. simpl; split. apply U. intros. rewrite emp_sepcon.
     intros w W. apply W.
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
    (dependent_type_functor_rec ts (AssertTT (ProdType A1 A2))) mpred.
Proof.
  intros ts X rho. specialize (P1 ts). specialize (P2 ts). 
  apply (EX b:bool, if b then P1 (fst X) rho else P2 (snd X) rho).
Defined.

Lemma binarySUM_ne {A1 A2}
           {P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred}
           {P2: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred}
           (P1_ne: super_non_expansive P1) (P2_ne: super_non_expansive P2):
  super_non_expansive (binarySUM P1 P2).
Proof.
  hnf; simpl; intros. unfold binarySUM. rewrite 2 approx_exp.
  specialize (P1_ne n ts (fst x) rho).
  specialize (P2_ne n ts (snd x) rho).  unfold dependent_type_functor_rec in P1_ne, P2_ne. 
  apply pred_ext; apply exp_derives; intros b; destruct b; first[ rewrite P1_ne; trivial | rewrite P2_ne; trivial].
Qed.

Definition binary_intersection (phi psi:funspec): option funspec.
  destruct phi as [f c A1 P1 Q1 P1_ne Q1_ne]. destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct (eq_dec f f2); [subst f2 | apply None].
  destruct (eq_dec c c2); [subst c2 | apply None].
  remember (binarySUM P1 P2) as P.
  remember (binarySUM Q1 Q2) as Q.
  apply Some. apply (mk_funspec f c (ProdType A1 A2) P Q).
  subst P; apply (binarySUM_ne P1_ne P2_ne).
  subst Q; apply (binarySUM_ne Q1_ne Q2_ne).
Defined.
(*
Lemma binaryintersection_Pi_sub phi psi omega:
  binary_intersection phi psi = Some omega ->
  funspec_sub omega phi /\  funspec_sub omega psi.
Proof.
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne]. intros.
  destruct (eq_dec f1 f2); [ simpl in H; rewrite if_true in H; subst f2 | inv H]. 
  destruct (eq_dec c1 c2); [ simpl in H; subst c2 | inv H]. inv H.
  apply inj_pair2 in H5. apply inj_pair2 in H4. subst P Q. split.
  + split. trivial. split. trivial. intros. exists ts2. fold (@dependent_type_functor_rec ts2) in *.
    simpl. simpl in H; destruct H. Check dependent_type_functor_rec.  Search functor. (*Print fsig: forall I : Type, (I -> functor) -> functor*)
    BoolFunctor A1 A2 := fun ts fsig bool (fun b => if b then DTF1 ts A1 else DTF ts A2)
    Search fpair.
    assert (PP2 := P2 ts2). simpl in PP2.
    exists ts2. destruct H as [TCE HP1].
    Print dependent_type_functor_rec.
    remember (dependent_type_functor_rec ts2 (AssertTT (ProdType A1 A2))) as FUNC. simpl in HeqFUNC.
    unfold ffunc in HeqFUNC. simpl in HeqFUNC.
    assert (X: FUNC mpred). subst FUNC. simpl. admit.  exists X. FUNC. rho).
    Check assert (XX:= P2 ts2). simpl in XX. simpl in x2. Check (x2, P2 ts2).
    Definition TRIV ts2 A1 A2
               (x2 : ((fix dtfr (T : TypeTree) : functor :=
           match T with
           | ConstType A => fconst A
           | Mpred => fidentity
           | DependentType n => fconst (nth n ts2 unit)
           | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
           | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
           | PiType I0 f => fpi (fun i : I0 => dtfr (f i))
           | ListType T0 => flist (dtfr T0)
           end) A1) mpred) (r: (dependent_type_functor_rec nil (AssertTT A2)) mpred):
      (fpair
        ((fix dtfr (T : TypeTree) : functor :=
            match T with
            | ConstType A => fconst A
            | Mpred => fidentity
            | DependentType n => fconst (nth n ts2 unit)
            | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
            | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
            | PiType I0 f0 => fpi (fun i : I0 => dtfr (f0 i))
            | ListType T0 => flist (dtfr T0)
            end) A1)
        ((fix dtfr (T : TypeTree) : functor :=
            match T with
            | ConstType A => fconst A
            | Mpred => fidentity
            | DependentType n => fconst (nth n ts2 unit)
            | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
            | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
            | PiType I0 f0 => fpi (fun i : I0 => dtfr (f0 i))
            | ListType T0 => flist (dtfr T0)
            end) A2)) mpred.
      Proof. Print fpair. constructor. apply x2. unfold dependent_type_functor_rec in r. simpl in r. hnf in r. apply r. simpl. hnf. simpl. eapply ConstType. econstructor. apply fidentity.  Search functor. apply (fun x => emp:mpred). . (fix dtfr (T : TypeTree) : functor :=
             match T with
             | ConstType A => fconst A
             | Mpred => fidentity
             | DependentType n => fconst (nth n ts2 unit)
             | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
             | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
             | PiType I0 f0 => fpi (fun i : I0 => dtfr (f0 i))
             | ListType T0 => flist (dtfr T0)
             end) A2) mpred. simpl. Check Check (AssertTT A1). exists (fpair (fconst(AssertTT A1) (fconst unit))). Search functor. eexists.
    exists emp. rewrite emp_sepcon. split. unfold binarySUM.  exists true. _sum. Search emp.
  [unfold binary_intersection. split. trivial. split. trivial. intros; simpl in *. 
  exists ts2. Check (@existT). i). x2). , emp. rewrite emp_sepcon.
  split. apply H. simpl; intros. rewrite emp_sepcon.
  intros u U. apply U.                                      
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma binaryfunspec_Pi_sub3 fsig cc I A Pre Post g (i:I)
      (HI: forall i,  funspec_sub g (NDmk_funspec fsig cc (A i) (Pre i) (Post i))):
  funspec_sub g (funspec_Pi_ND fsig cc I A Pre Post).
Proof.
  assert (HIi := HI i). destruct g. destruct HIi as [? [? Hi]]; subst f c.
  split. trivial. split. trivial.
  simpl; intros. clear i Hi. destruct x2 as [i Ai].
  specialize (HI i). destruct HI as [_ [_ Hi]]. apply (Hi ts2 Ai rho).
Qed.*) (*
Definition binarySUM {A1 A2}
           (P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred)
           (P2: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred):
  forall ts : list Type,
    (dependent_type_functor_rec ts (AssertTT (PiType bool (fun b : bool => if b then A1 else A2)))) mpred.
Proof.
  intros ts. specialize (P1 ts). specialize (P2 ts). simpl in *. intros X rho.
  apply (EX b:bool, if b then P1 (X true) rho else P2 (X false) rho).
Defined.

Lemma binarySUM_ne {A1 A2}
           {P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred}
           {P2: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred}
           (P1_ne: super_non_expansive P1) (P2_ne: super_non_expansive P2):
  super_non_expansive (binarySUM P1 P2).
Proof.
  hnf; simpl; intros. unfold binarySUM. rewrite 2 approx_exp.
  specialize (P1_ne n ts (x true) rho).
  specialize (P2_ne n ts (x false) rho).
  apply pred_ext; apply exp_derives; intros b; destruct b; first [ rewrite P1_ne; trivial | rewrite P2_ne; trivial].
Qed.
Definition binary_intersection (phi psi:funspec): option funspec.
  destruct phi as [f c A1 P1 Q1 P1_ne Q1_ne]. destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct (eq_dec f f2); [subst f2 | apply None].
  destruct (eq_dec c c2); [subst c2 | apply None].
  remember (binarySUM P1 P2) as P.
  remember (binarySUM Q1 Q2) as Q.
  apply Some. Check (mk_funspec f c). Print TypeTree. (PiType bool (fun b => if b then A1 else A2)) P Q).
  subst P; apply (binarySUM_ne P1_ne P2_ne).
  subst Q; apply (binarySUM_ne Q1_ne Q2_ne).
Defined.

Lemma binaryintersection_Pi_sub phi psi omega:
  binary_intersection phi psi = Some omega ->
  funspec_sub omega phi /\  funspec_sub omega psi.
Proof.
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne]. simpl; intros.
  destruct (eq_dec f1 f2); [ simpl in H; subst f2 | inv H].
  destruct (eq_dec c1 c2); [ simpl in H; subst c2 | inv H]. inv H.
  split.
  + split. trivial. split. trivial. intros. apply inj_pair2 in H5. apply inj_pair2 in H4. subst P Q.
    exists ts2. simpl in *. destruct H as [TCE HP1].
    exists (
    exists emp. split.
  [unfold binary_intersection. split. trivial. split. trivial. intros; simpl in *. 
  exists ts2. Check (@existT). i). x2). , emp. rewrite emp_sepcon.
  split. apply H. simpl; intros. rewrite emp_sepcon.
  intros u U. apply U.                                      
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma binaryfunspec_Pi_sub3 fsig cc I A Pre Post g (i:I)
      (HI: forall i,  funspec_sub g (NDmk_funspec fsig cc (A i) (Pre i) (Post i))):
  funspec_sub g (funspec_Pi_ND fsig cc I A Pre Post).
Proof.
  assert (HIi := HI i). destruct g. destruct HIi as [? [? Hi]]; subst f c.
  split. trivial. split. trivial.
  simpl; intros. clear i Hi. destruct x2 as [i Ai].
  specialize (HI i). destruct HI as [_ [_ Hi]]. apply (Hi ts2 Ai rho).
Qed.*)
  
(* ------------------------- Bifunctor version, non-binary case ---------*)
(*
Definition SUM {I A} (Pi: forall i ts,   (dependent_type_functor_rec ts (AssertTT (A i))) mpred):
  forall ts : list Type, (dependent_type_functor_rec ts (AssertTT (PiType I A))) mpred.
Proof.
  intros ts X rho.
  apply (EX i:I, Pi i ts (X i) rho).
Defined.

Lemma SUM_ne {I A} {Pi: forall i ts, (dependent_type_functor_rec ts (AssertTT (A i))) mpred}
           (P_ne: forall i, super_non_expansive (Pi i)):
  super_non_expansive (@SUM I A Pi).
Proof.
  hnf; simpl; intros. unfold SUM; rewrite 2 approx_exp.
  apply pred_ext; apply exp_derives; intros i; rewrite (P_ne i n ts (x i) rho); trivial.
Qed.

Definition funspec_Pi (sig:funsig) (cc:calling_convention) (I:Type) (A : I -> TypeTree)
           (Pre Post: forall i, (forall ts, (dependent_type_functor_rec ts (AssertTT (A i))) mpred))
           (Pre_ne: forall i, super_non_expansive (Pre i))
           (Post_ne: forall i, super_non_expansive (Post i)): funspec.
Proof.
  (*HERE -- shouldn't this be a sigma type?*)
  eapply (mk_funspec sig cc (PiType I A)). apply (SUM_ne Pre_ne). apply (SUM_ne Post_ne).
Defined.

Lemma SUM_binarySUM {A1 A2}
      (P: forall (b:bool) (ts:list Type), (dependent_type_functor_rec ts (AssertTT (if b then A1 else A2))) mpred):
  @binarySUM A1 A2 (P true) (P false) = @SUM bool (fun b => if b then A1 else A2) P.
Proof.
  unfold binarySUM, SUM. extensionality ts X rho. 
  apply pred_ext; apply exp_left; intros b; apply (exp_right b); destruct b; trivial.
Qed. 
*)
(*HERE The two rules S-inter1 and S-inter2 from page 206 of TAPL
Lemma funspec_Pi_sub fsig cc I A Pre Post Pre_ne Post_ne i:
  funspec_sub (funspec_Pi fsig cc I A Pre Post Pre_ne Post_ne)
              (mk_funspec fsig cc (A i) (Pre i) (Post i) (Pre_ne i) (Post_ne i)).
Proof.
  unfold funspec_Pi. split. trivial. split. trivial. intros; simpl in *. 
  exists ts2. Check (@existT). i). x2). , emp. rewrite emp_sepcon.
  split. apply H. simpl; intros. rewrite emp_sepcon.
  intros u U. apply U.                                      
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_Pi_sub3 fsig cc I A Pre Post g (i:I)
      (HI: forall i,  funspec_sub g (NDmk_funspec fsig cc (A i) (Pre i) (Post i))):
  funspec_sub g (funspec_Pi_ND fsig cc I A Pre Post).
Proof.
  assert (HIi := HI i). destruct g. destruct HIi as [? [? Hi]]; subst f c.
  split. trivial. split. trivial.
  simpl; intros. clear i Hi. destruct x2 as [i Ai].
  specialize (HI i). destruct HI as [_ [_ Hi]]. apply (Hi ts2 Ai rho).
Qed.*)


(*----------------------------- Quarry ------------------------------
Definition sum_pred {A B} (P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A)) mpred)
  (P2 : forall ts : list Type, (dependent_type_functor_rec ts (AssertTT B)) mpred):
  forall ts : list Type,
  (dependent_type_functor_rec ts
     (AssertTT (PiType (unit + unit) (fun x : unit + unit => match x with
                                                             | inl a => A
                                                             | inr b => B
                                                             end)))) mpred.
Proof.
  simpl. intros ts i rho.
assert (iL := i (inl tt)).
assert (iR := i (inr tt)). clear i. simpl in *.
specialize (P1 ts iL rho). (*use a different ts here -- tl ts, or ((unit + unit)%type)::ts?*)
specialize (P2 ts iR rho).
apply
  
Definition ndfs_intersection fA cA A PA QA FSA (HFSA: FSA = mk_funspec fA cA A PA QA) 
                    fB cB B PB QB FSB (HFSB: FSB = mk_funspec fB cB B PB QB): option funspec.
destruct (eq_dec fA fB); subst.
+ destruct (eq_dec cA cB); subst.
  - apply Some.
    eapply (mk_funspec fB cB (PiType (unit + unit) (fun x => match x with inl _ => A | inr _ => B end)) PA).
    Print NDmk_funspec.
         (fun x => if match x with  then PA a else PB b)).
         (fun x => match x with inl a => QA a | inr b => QB b end)).
  - apply None.
+ apply None.
Defined.

       

Definition identtype_eqdec: forall (x y : ident * type), {x = y}+{x <> y}.
Proof.
  destruct x as [i1 t1]. destruct y as [i2 t2].
  destruct (ident_eq i1 i2); [ subst i2|].
  + destruct (type_eq t1 t2); [ left; subst t2; reflexivity | right ].
    intros N. inv N. apply n; reflexivity.
  + right. intros N. inv N. apply n; reflexivity.
Defined.

Definition funsig_eqdec: forall (x y : funsig), {x = y}+{x <> y}.
Proof.
  destruct x as [args1 ret1]. destruct y as [args2 ret2].
  destruct (type_eq ret1 ret2).
+ subst. destruct (list_eq_dec identtype_eqdec args1 args2). left; subst; reflexivity.
  right; intros N; inv N. apply n; reflexivity.
+ right. intros N; inv N. apply n; reflexivity.
Defined.
Lemma funspec_sub_merge {fA cA A PA QA fB cB B PB QB} f1 F1 f2 F2 f
      (I: ndfs_merge fA cA A PA QA f1 F1 fB cB B PB QB f2 F2 = Some f): funspec_sub f1 f.
Proof.
  subst. unfold ndfs_merge in I.
  destruct (eq_dec fA fB); [subst fB | discriminate].
  destruct (eq_dec cA cB); [subst cB | discriminate]. inv I.
  split. trivial. split. trivial. intros. simpl. intros w [W1 W2].
  destruct x2.
  + exists ts2, a, emp. rewrite emp_sepcon.  split. trivial. simpl; intros. rewrite emp_sepcon.
    intros u U. apply U.
  + exists ts2, b. emp. rewrite emp_sepcon.  split. trivial. simpl; intros. rewrite emp_sepcon.
    intros u U. apply U.
  + simpl in *. assert (X:= x2 true); simpl in X. exists ts2, X. simpl in *.
  assert (PT := P ts2 true). ] | discriminate]. inv I. 2:{
  destruct I.
Parameter mysig:funsig.
Parameter mycc:calling_convention.
Parameter myA1: TypeTree.
Parameter myA2: TypeTree.
Parameter myPre1 myPost1:  forall ts : list Type, (dependent_type_functor_rec ts (AssertTT myA1)) mpred.
Parameter myPre2 myPost2:  forall ts : list Type, (dependent_type_functor_rec ts (AssertTT myA2)) mpred.
Definition myA:TypeTree := PiType bool (fun b : bool => if b then myA1 else myA2).

Definition myPre: forall ts : list Type, (dependent_type_functor_rec (*(bool::ts)*)ts (AssertTT myA)) mpred.
Proof. unfold myA; intros; simpl; intros X rho.
Print dependent_type_functor_rec .
       simpl.
       
Definition sum_pred {A1 A2} (P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred)
  (P2 : forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred):
  forall ts : list Type,
              (dependent_type_functor_rec ts (AssertTT (PiType bool (fun b : bool => if b then A1 else A2)))) mpred.
Proof.
  simpl. intros ts A rho. specialize (P1 ts); specialize (P2 ts). simpl in P1, P2.
  apply (orp (P1 (A true) rho) (P2 (A false) rho)).
Defined.

Definition sum_pred' {A1 A2} (P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred)
  (P2 : forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred) (b:bool):
  forall ts : list Type,
              (dependent_type_functor_rec ts (AssertTT (PiType bool (fun b : bool => if b then A1 else A2)))) mpred.
Proof.
  simpl. intros ts A rho. specialize (P1 ts); specialize (P2 ts). simpl in P1, P2.
  specialize (A b).
  destruct b. apply (P1 A rho).  apply (P2 A rho). 
Defined.
*)