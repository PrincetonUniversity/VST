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

Definition subsume_funspec (f1 f2 : funspec):mpred :=
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
            ALL rho':_,
                      !( ((local (tc_environ (ret0_tycon Delta)) rho') && (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho'))))
    end
end.

(* If we were to require that a non-void-returning function must,
   at a function call, have its result assigned to a temp,
   then we could change "ret0_tycon" to "ret_tycon" in this
   definition (and in NDsubsume_funspec). *)

Definition subsume_funspec_weak (f1 f2 : funspec):Prop :=
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

Lemma FSimplies f1 f2: subsume_funspec_weak f1 f2 -> TT |-- subsume_funspec f1 f2.
Proof. intros. destruct f1; destruct f2; simpl in *.
destruct H as [? [? H']]; subst. intros w _. split; [split; trivial |].
intros ts2 x2 rho u WU m necMU M.
destruct (H' ts2 x2 rho _ M) as [ts1 [x1 [F [HF IMP]]]]; clear H'.
exists ts1, x1, F; split; trivial. intros rho'; simpl; intros.
apply IMP. simpl; trivial.
Qed.

Lemma subsume_funspec_trans f1 f2 f3: subsume_funspec f1 f2 && subsume_funspec f2 f3 |--
      subsume_funspec f1 f3.
Proof. unfold subsume_funspec in *. destruct f1; destruct f2; destruct f3.
intros w [[X H12] [Y H23]]; destruct X; subst; destruct Y; subst; split; [split; trivial|].
intros ts2 x2 rho u WU m necM M. 
destruct (H23 ts2 x2 rho _ WU _ necM M) as [ts1 [x1 [F [[m1 [m2 [J [HF HP0]]]] IMP23]]]]; clear H23.
destruct (join_level _ _ _ J) as [M1 M2]. specialize (necR_level _ _ necM); intros L.
destruct M as [TC _]. destruct (nec_join4 _ _ _ _ J necM) as [u1 [u2 [JU [necU1 necU2]]]].
assert (WU2: (level w >= level u2)%nat). { apply join_level in JU; destruct JU as [_ JU2]. rewrite JU2; trivial. }
destruct (H12 ts1 x1 rho _ WU2 m2 necU2) as [ts3 [x3 [G [HG IMP12]]]]; clear H12.
+ split; trivial.
+ exists ts3, x3, (F*G); split. 
  - rewrite sepcon_assoc. exists m1, m2; split; [trivial | split; trivial].
  - intros rho' k MK v necKV [V1 V2]. eapply (IMP23 rho' _ MK _ necKV). split. apply V1.
    rewrite sepcon_assoc in V2. destruct V2 as [v1 [v2 [JV [HV1 HV2]]]].
    exists v1, v2; split; [trivial | split; [trivial |]].
    destruct (nec_join4 _ _ _ _ JV necKV) as [k1 [k2 [JK [necK1 necK2]]]].
    eapply (IMP12 rho' k2); trivial.
    * destruct (join_level _ _ _ JK) as [_ K2]. rewrite M2, K2; trivial. 
    * split; trivial.
Qed.

Lemma subsume_funspec_refl f: TT |-- subsume_funspec f f.
Proof. destruct f; split; [ split; trivial | clear H; intros ts2 x2 rho m AM w necW [W1 W2]].
exists ts2, x2, emp; rewrite emp_sepcon. split; trivial.
intros rho' k WK u necKU U.
rewrite emp_sepcon in U. apply U.
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
  EX b: block, !! (v = Vptr b Ptrofs.zero) && func_at f (b, 0).

Definition NDmk_funspec (f: funsig) (cc: calling_convention)
  (A: Type) (Pre Post: A -> environ -> mpred): funspec :=
  mk_funspec f cc (rmaps.ConstType A) (fun _ => Pre) (fun _ => Post)
             (const_super_non_expansive _ _) (const_super_non_expansive _ _).

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
  + rewrite H0.
    f_equal.
    f_equal.
    extensionality ts a.
    extensionality prepost rho.
    unfold packPQ; destruct prepost; simpl.
    - change (approx (level w) (approx n (P a rho))) with
        ((approx (level w) oo (approx n)) (P a rho)).
      rewrite approx_oo_approx' by omega.
      auto.
    - change (approx (level w) (approx n (Q a rho))) with
        ((approx (level w) oo (approx n)) (Q a rho)).
      rewrite approx_oo_approx' by omega.
      auto.
  + rewrite H0.
    f_equal.
    f_equal.
    extensionality ts a.
    extensionality prepost rho.
    unfold packPQ; destruct prepost; simpl.
    - change (approx (level w) (approx n (P a rho))) with
        ((approx (level w) oo (approx n)) (P a rho)).
      rewrite approx_oo_approx' by omega.
      auto.
    - change (approx (level w) (approx n (Q a rho))) with
        ((approx (level w) oo (approx n)) (Q a rho)).
      rewrite approx_oo_approx' by omega.
      auto.
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