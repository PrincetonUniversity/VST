Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.

(*Clight-specific Imports*)
Require Import VST.veric.Clight_lemmas. 
Require Import VST.veric.align_mem.

Require Export VST.veric.lift.

Require Export VST.veric.mpred.

Fixpoint modifiedvars' (c: statement) (S: idset) : idset :=
 match c with
 | Sset id e => insert_idset id S
 | Sifthenelse _ c1 c2 => modifiedvars' c1 (modifiedvars' c2 S)
 | Scall (Some id) _ _ => insert_idset id S
 | Sbuiltin (Some id) _ _ _ => insert_idset id S
 | Ssequence c1 c2 =>  modifiedvars' c1 (modifiedvars' c2 S)
 | Sloop c1 c2 => modifiedvars' c1 (modifiedvars' c2 S)
 | Sswitch e cs => modifiedvars_ls cs S
 | Slabel _ c => modifiedvars' c S
 | _ => S
 end
 with
 modifiedvars_ls (cs: labeled_statements) (S: idset) : idset :=
 match cs with
 | LSnil => S
 | LScons _ c ls => modifiedvars' c (modifiedvars_ls ls S)
 end.

Definition isOK {A} (P: Errors.res A) := match P with Errors.OK _ => true | _ => false end.

Lemma modifiedvars'_union:
 forall id c S,
  isSome ((modifiedvars' c S) ! id) <->
  (isSome ((modifiedvars' c idset0) ! id ) \/ isSome (S ! id))
with modifiedvars_ls_union:
 forall id c S,
  isSome ((modifiedvars_ls c S) ! id) <->
  (isSome ((modifiedvars_ls c idset0) ! id ) \/ isSome (S ! id)).
Proof.
intro id.
 assert (IS0: ~ isSome (idset0 ! id)). unfold idset0, isSome.
 rewrite PTree.gempty; auto.
 induction c; try destruct o; simpl; intros;
 try solve [clear - IS0; intuition];
 try solve [unfold insert_idset; destruct (eq_dec i id);
  [subst; repeat rewrite PTree.gss; simpl; clear; intuition
  |  repeat rewrite PTree.gso by auto; simpl; clear - IS0; intuition ]];
 try solve [rewrite IHc1; rewrite IHc1 with (S := modifiedvars' c2 idset0);
                rewrite IHc2; clear - IS0; intuition].
 apply modifiedvars_ls_union.
 apply IHc.

intro id.
 assert (IS0: ~ isSome (idset0 ! id)). unfold idset0, isSome.
 rewrite PTree.gempty; auto.
 induction c; simpl; intros.
 clear - IS0; intuition.
 rewrite modifiedvars'_union.
 rewrite modifiedvars'_union with (S := modifiedvars_ls _ _).
 rewrite IHc. clear; intuition.
Qed.

Definition modifiedvars (c: statement) (id: ident) :=
   isSome ((modifiedvars' c idset0) ! id).

Definition type_of_global (ge: Clight.genv) (b: block) : option type :=
  match Genv.find_var_info ge b with
  | Some gv => Some gv.(gvar_info)
  | None =>
      match Genv.find_funct_ptr ge b with
      | Some fd => Some(type_of_fundef fd)
      | None => None
      end
  end.

Definition filter_genv (ge: Clight.genv) : genviron :=
    Genv.find_symbol ge.

Definition make_tenv (te : Clight.temp_env) : tenviron := fun id => PTree.get id te.

Definition make_venv (te : Clight.env) : venviron := fun id => PTree.get id te.

Definition construct_rho ge ve te:= mkEnviron ge (make_venv ve) (make_tenv te) .

Definition empty_environ (ge: Clight.genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

(** Definitions related to function specifications and return assertions **)
Inductive exitkind : Type := EK_normal | EK_break | EK_continue | EK_return.

Instance EqDec_exitkind: EqDec exitkind.
Proof.
hnf. intros.
decide equality.
Defined.

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

(** Declaration of type context for typechecking **)
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

Definition func_tycontext' (func: function) (Delta: tycontext) : tycontext :=
 mk_tycontext
   (make_tycontext_t (fn_params func) (fn_temps func))
   (make_tycontext_v (fn_vars func))
   (fn_return func)
   (glob_types Delta)
   (glob_specs Delta)
   (annotations Delta).

Definition func_tycontext (func: function) (V: varspecs) (G: funspecs) (A:list (ident * Annotation)): tycontext :=
  make_tycontext (func.(fn_params)) (func.(fn_temps)) (func.(fn_vars)) (func.(fn_return)) V G A.

Definition nofunc_tycontext (V: varspecs) (G: funspecs) : tycontext :=
   make_tycontext nil nil nil Tvoid V G nil.

Ltac try_false :=
try  solve[exists false; rewrite orb_false_r; eauto].

Lemma list_norepet_rev:
  forall A (l: list A), list_norepet (rev l) = list_norepet l.
Proof.
induction l; simpl; auto.
apply prop_ext; split; intros.
apply list_norepet_app in H.
destruct H as [? [? ?]].
rewrite IHl in H.
constructor; auto.
eapply list_disjoint_notin with (a::nil).
apply list_disjoint_sym; auto.
intros x y ? ? ?; subst.
contradiction (H1 y y); auto.
rewrite <- In_rev; auto.
simpl; auto.
rewrite list_norepet_app.
inv H.
split3; auto.
rewrite IHl; auto.
repeat constructor.
intro Hx. inv Hx.
intros x y ? ? ?; subst.
inv H0.
rewrite <- In_rev in H; contradiction.
auto.
Qed.

Definition sub_option {A} (x y: option A) :=
 match x with Some x' => y = Some x' | None => True end.

Lemma sub_option_eqv: forall {A} (x y: option A),
  x = y <-> sub_option x y /\ sub_option y x.
Proof.
  intros.
  destruct x, y; split; intros; try congruence.
  + inversion H.
    simpl.
    split; reflexivity.
  + simpl in H; destruct H.
    inversion H.
    reflexivity.
  + simpl in H; destruct H.
    inversion H.
  + simpl in H; destruct H.
    inversion H0.
  + simpl.
    tauto.
Qed.

Lemma sub_option_refl: forall {A} (x: option A), sub_option x x.
Proof.
  intros.
  destruct x; simpl.
  + reflexivity.
  + exact I.
Qed.

Lemma sub_option_trans: forall {A} (x y z: option A), sub_option x y -> sub_option y z -> sub_option x z.
Proof.
  intros.
  destruct x, y, z;
  inversion H;
  subst;
  inversion H0;
  subst.
  + reflexivity.
  + exact I.
  + exact I.
  + exact I.
Qed.

Lemma sub_option_spec: forall {A} (T1 T2: PTree.t A),
  (forall id, sub_option (T1 ! id) (T2 ! id)) ->
  forall id co, T1 ! id = Some co -> T2 ! id = Some co.
Proof.
  intros.
  specialize (H id).
  destruct (T1 ! id), (T2 ! id); inversion H; inversion H0.
  reflexivity.
Qed.

Definition Annotation_sub (A1 A2: option Annotation):Prop := 
  match A1, A2 with
    _, None => True
  | Some (StrongAnnotation _), Some (WeakAnnotation _) => True
  | Some (StrongAnnotation X), Some (StrongAnnotation Y) => X=Y (*maybe have entailment here?*)
  | X, Y => X=Y 
  end.

Lemma Annotation_sub_trans a1 a2 a3: Annotation_sub a1 a2 -> 
      Annotation_sub a2 a3 -> Annotation_sub a1 a3.
Proof. unfold Annotation_sub.
  destruct a1; destruct a2.
+ destruct a; destruct a0; simpl; intros.
  - inv H; trivial.
  - inv H. 
  - destruct a3; trivial. inv H0; trivial.
  - subst. trivial.
+ destruct a; trivial; intros; destruct a3; trivial; discriminate.
+ discriminate.
+ trivial.
Qed.

Lemma Annotation_sub_refl a: Annotation_sub a a. 
Proof. unfold Annotation_sub. destruct a; trivial. destruct a; trivial. Qed.

Lemma Annotation_sub_antisymm a b: Annotation_sub a b -> Annotation_sub b a -> a=b.
Proof. intros.
destruct a; destruct b; simpl in *; trivial; try discriminate.
destruct a; destruct a0; subst; trivial. inv H0; trivial. 
Qed.

Definition tycontext_sub (Delta Delta' : tycontext) : Prop :=
 (forall id, match (temp_types Delta) ! id,  (temp_types Delta') ! id with
                 | None, _ => True
                 | Some t, None => False
                 | Some t, Some t' => t=t'
                end)
 /\ (forall id, (var_types Delta) ! id = (var_types Delta') ! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, sub_option ((glob_types Delta) ! id) ((glob_types Delta') ! id))
 /\ (forall id, sub_option ((glob_specs Delta) ! id) ((glob_specs Delta') ! id))
 /\ (forall id, Annotation_sub ((annotations Delta) ! id) ((annotations Delta') ! id)).

Definition tycontext_eqv (Delta Delta' : tycontext) : Prop :=
 (forall id, (temp_types Delta) ! id = (temp_types Delta') ! id)
 /\ (forall id, (var_types Delta) ! id = (var_types Delta') ! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, (glob_types Delta) ! id = (glob_types Delta') ! id)
 /\ (forall id, (glob_specs Delta) ! id = (glob_specs Delta') ! id)
 /\ (forall id, (annotations Delta) ! id = (annotations Delta') ! id).

Lemma tycontext_eqv_spec: forall Delta Delta',
  tycontext_eqv Delta Delta' <-> tycontext_sub Delta Delta' /\ tycontext_sub Delta' Delta.
Proof.
  intros.
  unfold tycontext_sub, tycontext_eqv.
  split; [intros [? [? [? [? [? ?]]]]] | intros [[? [? [? [? [? ?]]]]] [? [? [? [? [? ?]]]]]]];
  repeat split; intros;
  try assumption;
  try (symmetry; assumption);
  try
  solve [
    apply sub_option_eqv;
    try split;
    try rewrite H; try rewrite H0; try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4;
    try apply sub_option_refl; try reflexivity;
    auto
    ].
  + clear - H.
    specialize (H id).
    destruct ((temp_types Delta) ! id) as [? |], ((temp_types Delta') ! id) as [? |];
    inversion H; auto.
  + rewrite H4. apply Annotation_sub_refl.
  + clear - H.
    specialize (H id).
    destruct ((temp_types Delta) ! id) as [? |], ((temp_types Delta') ! id) as [? |];
    inversion H; auto.
  + rewrite H4. apply Annotation_sub_refl.
  + clear - H H5.
    specialize (H id).
    specialize (H5 id).
    destruct ((temp_types Delta) ! id) as [? |], ((temp_types Delta') ! id) as [? |];
    inversion H; inversion H5; auto.
  + clear - H4 H10. apply Annotation_sub_antisymm; auto.
Qed.

Lemma tycontext_sub_refl:
 forall Delta, tycontext_sub Delta Delta.
Proof.
  intros. destruct Delta as [T V r G S].
  unfold tycontext_sub.
  intuition.
  + unfold sub_option. unfold temp_types. simpl.
    destruct (T ! id) as [? |]; split; auto; destruct b; auto.
  + apply sub_option_refl.
  + apply sub_option_refl.
  + apply Annotation_sub_refl.
Qed.

Lemma tycontext_sub_trans:
 forall Delta1 Delta2 Delta3,
  tycontext_sub Delta1 Delta2 -> tycontext_sub Delta2 Delta3 ->
  tycontext_sub Delta1 Delta3.
Proof.
  intros ? ? ? [G1 [G2 [G3 [G4 [G5 G6]]]]] [H1 [H2 [H3 [H4 [H5 H6]]]]].
  repeat split.
  * intros. specialize (G1 id); specialize (H1 id).
    destruct ((temp_types Delta1) ! id); auto.
    destruct ((temp_types Delta2) ! id);
      try contradiction.
    destruct ((temp_types Delta3) ! id); try contradiction.
    destruct G1, H1; split; subst; auto.
  * intros. specialize (G2 id); specialize (H2 id); congruence.
  * congruence.
  * intros. eapply sub_option_trans; eauto.
  * intros. eapply sub_option_trans; eauto.
  * intros. eapply Annotation_sub_trans; eauto.
Qed.

Definition binop_stable cenv op a1 a2 : bool :=
match op with
  | Cop.Oadd => match Cop.classify_add (typeof a1) (typeof a2) with
                    | Cop.add_case_pi t _ => complete_type cenv t
                    | Cop.add_case_ip _ t => complete_type cenv t
                    | Cop.add_case_pl t => complete_type cenv t
                    | Cop.add_case_lp t => complete_type cenv t
                    | Cop.add_default => true
            end
  | Cop.Osub => match Cop.classify_sub (typeof a1) (typeof a2) with
                    | Cop.sub_case_pi t _ => complete_type cenv t
                    | Cop.sub_case_pl t => complete_type cenv t
                    | Cop.sub_case_pp t => complete_type cenv t
                    | Cop.sub_default => true
            end
  | _ => true
  end.

Section STABILITY.

Variables env env': composite_env.
Hypothesis extends: forall id co, env!id = Some co -> env'!id = Some co.

Lemma binop_stable_stable: forall b e1 e2,
  binop_stable env b e1 e2 = true ->
  binop_stable env' b e1 e2 = true.
Proof.
  intros.
  destruct b; unfold binop_stable in H |- *; auto.
  + destruct (Cop.classify_add (typeof e1) (typeof e2));
    try (eapply (complete_type_stable env env'); eauto).
     auto.
  + destruct (Cop.classify_sub (typeof e1) (typeof e2));
    try (eapply (complete_type_stable env env'); eauto).
     auto.
Qed.

Lemma Cop_Sem_add_ptr_int_stable ty si u v (H:complete_type env ty = true):
  Cop.sem_add_ptr_int env ty si u v =
  Cop.sem_add_ptr_int env' ty si u v.
Proof. unfold Cop.sem_add_ptr_int.
  destruct u; destruct v; trivial; erewrite <- sizeof_stable; eauto.
Qed.

Lemma Cop_Sem_add_ptr_long_stable ty u v (H:complete_type env ty = true):
  Cop.sem_add_ptr_long env ty u v =
  Cop.sem_add_ptr_long env' ty u v.
Proof. unfold Cop.sem_add_ptr_long.
  destruct u; destruct v; trivial; erewrite <- sizeof_stable; eauto.
Qed.

Lemma Cop_sem_binary_operation_stable:
  forall b v1 e1 v2 e2 m,
  binop_stable env b e1 e2 = true ->
  Cop.sem_binary_operation env b v1 (typeof e1) v2 (typeof e2) m =
    Cop.sem_binary_operation env' b v1 (typeof e1) v2 (typeof e2) m.
Proof.
  intros.
  unfold binop_stable in H.
  destruct b; try auto.
  + simpl.
    unfold Cop.sem_add.
    destruct (Cop.classify_add (typeof e1) (typeof e2)), v1, v2;
    try (erewrite <- Cop_Sem_add_ptr_int_stable; eauto);
    try (erewrite <- Cop_Sem_add_ptr_long_stable; eauto);
(*    try (eapply (complete_type_stable env env'); eauto);*)
    try erewrite <- sizeof_stable; eauto.
  + simpl.
    unfold Cop.sem_sub.
    destruct (Cop.classify_sub (typeof e1) (typeof e2)), v1, v2;
    try erewrite <- sizeof_stable; eauto.
Qed.

Lemma field_offset_stable: forall i id co ofs,
  composite_env_consistent env ->
  env ! i = Some co ->
  field_offset env id (co_members co) = Errors.OK ofs ->
  field_offset env' id (co_members co) = Errors.OK ofs.
Proof.
  unfold field_offset.
  generalize 0.
  intros.
  destruct (H i co H0) as [HH _ _ _].
  revert z H1.
  clear H H0.
  induction (co_members co); intros.
  + simpl in H1 |- *.
    inversion H1.
  + simpl in H1 |- *.
    destruct a.
    simpl in HH.
    rewrite andb_true_iff in HH.
    if_tac.
    - rewrite alignof_stable with (env := env) by tauto. assumption.
    - rewrite alignof_stable with (env := env) by tauto.
      rewrite sizeof_stable with (env := env) by tauto.
      apply IHm; try tauto.
Qed.

End STABILITY.

Section TYCON_SUB.
Variables Delta Delta': tycontext.
Hypothesis extends: tycontext_sub Delta Delta'.

Lemma func_tycontext'_sub: forall f,
  tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta').
Proof.
  intros.
  unfold func_tycontext'.
  unfold tycontext_sub in *.
  destruct extends as [? [? [? [? [? ?]]]]].
  repeat split; simpl.
  + intros.
    destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! id) as [? |].
    - auto.
    - exact I.
  + auto.
  + auto.
  + auto.
Qed.

End TYCON_SUB.

Section TYCON_EQUIV.

Variable Delta Delta': tycontext.
Hypothesis equiv: tycontext_eqv Delta Delta'.

Lemma func_tycontext'_eqv: forall f,
  tycontext_eqv (func_tycontext' f Delta) (func_tycontext' f Delta').
Proof.
  intro.
  rewrite tycontext_eqv_spec in *.
  split; apply func_tycontext'_sub; tauto.
Qed.

End TYCON_EQUIV.

Lemma tycontext_eqv_symm:
  forall Delta Delta', tycontext_eqv Delta Delta' ->  tycontext_eqv Delta' Delta.
Proof.
intros.
destruct H as [? [? [? [? [? ?]]]]]; repeat split; auto.
Qed.

Lemma tycontext_eqv_sub:
  forall Delta Delta', tycontext_eqv Delta Delta' ->
         tycontext_sub Delta Delta'.
Proof.
intros.
destruct H as [? [? [? [? [? ?]]]]].
repeat split; intros; auto.
rewrite H; auto.
destruct ((temp_types Delta') ! id); auto.
rewrite H2. destruct ((glob_types Delta') ! id); simpl; auto.
rewrite H3. destruct ((glob_specs Delta') ! id); simpl; auto.
rewrite H4. apply Annotation_sub_refl.
Qed.

Record ret_assert : Type := {
 RA_normal: environ->mpred;
 RA_break: environ->mpred;
 RA_continue: environ->mpred;
 RA_return: option val -> environ->mpred
}.

Lemma modifiedvars_Slabel l c: modifiedvars (Slabel l c) = modifiedvars c.
Proof. reflexivity. Qed.

Lemma modifiedvars_computable: forall c (te1 te2: Map.t val), exists te,
  (forall i, modifiedvars c i -> Map.get te1 i = Map.get te i) /\
  (forall i, modifiedvars c i \/ Map.get te2 i = Map.get te i).
Proof.
  intros.
  unfold modifiedvars.
  exists (fun i => match (modifiedvars' c idset0) ! i with Some _ => Map.get te1 i | None => Map.get te2 i end).
  split; intros.
  + unfold Map.get.
    destruct ((modifiedvars' c idset0) ! i); simpl; [auto | inv H].
  + unfold Map.get.
    destruct ((modifiedvars' c idset0) ! i); simpl; [left; apply I | auto].
Qed.

Lemma modifiedvars_Sifthenelse b c1 c2 id: modifiedvars (Sifthenelse b c1 c2) id <-> modifiedvars c1 id \/ modifiedvars c2 id.
Proof.
  unfold modifiedvars.
  simpl.
  rewrite modifiedvars'_union.
  reflexivity.
Qed.

Lemma modifiedvars_Sloop c1 c2 id: modifiedvars (Sloop c1 c2) id <-> modifiedvars c1 id \/ modifiedvars c2 id.
Proof.
  unfold modifiedvars.
  simpl.
  rewrite modifiedvars'_union.
  reflexivity.
Qed.

Lemma modifiedvars_Ssequence c1 c2 id: modifiedvars (Ssequence c1 c2) id <-> modifiedvars c1 id \/ modifiedvars c2 id.
Proof.
  unfold modifiedvars.
  simpl.
  rewrite modifiedvars'_union.
  reflexivity.
Qed.

Lemma modifiedvars_ls_eq: forall sl, modifiedvars_ls sl = modifiedvars' (seq_of_labeled_statement sl).
Proof.
  intros.
  induction sl; auto.
  destruct o; simpl;
  rewrite IHsl; auto.
Qed.  

Lemma modifiedvars_Sswitch e sl n id: modifiedvars (seq_of_labeled_statement (select_switch (Int.unsigned n) sl)) id -> modifiedvars (Sswitch e sl) id.
Proof.
  unfold modifiedvars.
  simpl.
  unfold select_switch.
  destruct (select_switch_case (Int.unsigned n) sl) eqn:?H.
  + revert l H; induction sl; simpl; intros.
    - inv H.
    - rewrite modifiedvars'_union.
      destruct o; [| right; eapply IHsl; eauto].
      if_tac in H; [| right; eapply IHsl; eauto].
      inv H.
      simpl in H0.
      rewrite modifiedvars'_union in H0; auto.
      rewrite modifiedvars_ls_eq; auto.
  + revert H; induction sl; simpl; intros.
    - auto.
    - rewrite modifiedvars'_union.
      destruct o; [if_tac in H |].
      * inv H.
      * right; apply IHsl; auto.
      * simpl in H0.
        rewrite modifiedvars'_union in H0; auto.
        rewrite modifiedvars_ls_eq; auto.
Qed.
