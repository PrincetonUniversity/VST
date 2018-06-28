Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.address_conflict.
Require Export VST.veric.shares.
Require Export VST.veric.mapsto_memory_block.

Local Open Scope pred.

Definition func_at (f: funspec): address -> pred rmap :=
  match f with
   | mk_funspec fsig cc A P Q _ _ => pureat (SomeP (SpecTT A) (packPQ P Q)) (FUN fsig cc)
  end.

Definition func_at' (f: funspec) (loc: address) : pred rmap :=
  match f with
   | mk_funspec fsig cc _ _ _ _ _ => EX pp:_, pureat pp (FUN fsig cc) loc
  end.

Definition func_ptr (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && func_at f (b, 0).

Definition NDmk_funspec (f: base.funsig) (cc: calling_convention)
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

Definition precondition_closed (f: function) {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred) : Prop :=
 forall ts x,
  closed_wrt_vars (not_a_param (fn_params f)) (P ts x) /\
  closed_wrt_lvars (is_a_local (fn_vars f)) (P ts x).

(*Definition expr_true (e: Clight.expr) (rho: environ): Prop :=
  bool_val (eval_expr e rho) (Clight.typeof e) = Some true.*)

Definition typed_true (t: type) (v: val)  : Prop := strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t =
Some false.

Definition expr_true {CS: compspecs} e := lift1 (typed_true (typeof e)) (eval_expr e).

Definition expr_false {CS: compspecs} e := lift1 (typed_false (typeof e)) (eval_expr e).

Definition subst {A} (x: ident) (v: val) (P: environ -> A) : environ -> A :=
   fun s => P (env_set s x v).
(*
Definition fun_assert:
  forall (fml: funsig) cc (A: TypeTree)
   (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap))
   (v: val) , pred rmap :=
  res_predicates.fun_assert.
*)
Definition eval_lvar (id: ident) (ty: type) (rho: environ) :=
 match Map.get (ve_of rho) id with
| Some (b, ty') => if eqb_type ty ty' then Vptr b Ptrofs.zero else Vundef
| None => Vundef
end.

Definition var_block (sh: Share.t) {cs: compspecs} (idt: ident * type) (rho: environ): mpred :=
  !! (sizeof (snd idt) <= Int.max_unsigned) &&
  (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho).

Fixpoint sepcon_list {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A} {AgeA: Age_alg A}
   (p: list (pred A)) : pred A :=
 match p with nil => emp | h::t => h * sepcon_list t end.

Definition stackframe_of {cs: compspecs} (f: Clight.function) : assert :=
  fold_right (fun P Q rho => P rho * Q rho) (fun rho => emp) (map (fun idt => var_block Share.top idt) (Clight.fn_vars f)).

Lemma stackframe_of_eq : forall {cs: compspecs}, stackframe_of =
        fun f rho => fold_right sepcon emp (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).
Proof.
  intros.
 extensionality f rho.
 unfold stackframe_of.
 forget (fn_vars f) as vl.
 induction vl; simpl; auto.
 rewrite IHvl; auto.
Qed.

(*
Definition stackframe_of (f: Clight.function) : assert :=
  fun rho => sepcon_list (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).
*)

Lemma  subst_extens:
 forall a v P Q, (forall rho, P rho |-- Q rho) -> forall rho, subst a v P rho |-- subst a v Q rho.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition tc_formals (formals: list (ident * type)) : environ -> Prop :=
     fun rho => tc_vals (map (@snd _ _) formals) (map (fun xt => (eval_id (fst xt) rho)) formals).

Program Definition close_precondition (params vars: list (ident * type)) (P: environ -> pred rmap) (rho: environ) : pred rmap :=
 fun phi =>
   exists ve', exists te',
   (forall i, In i (map (@fst _ _) params) -> Map.get te' i = Map.get (te_of rho) i) /\
   (forall i, In i (map (@fst _ _) vars) \/ Map.get ve' i = Map.get (ve_of rho) i) /\
   app_pred (P (mkEnviron (ge_of rho) ve' te')) phi.
Next Obligation.
intros.
intro; intros.
destruct H0 as [ve' [te' [? [? ?]]]]; exists ve',te'; split3; auto.
eapply pred_hereditary; eauto.
Qed.

Lemma close_precondition_i:
  forall params vars P rho,
  P rho |-- close_precondition params vars P rho.
Proof.
intros.
intros ? ?.
hnf. exists (ve_of rho), (te_of rho).
split3; auto.
destruct rho; apply H.
Qed.

Lemma close_precondition_e:
   forall f (A: TypeTree) (P:  forall ts, dependent_type_functor_rec ts (AssertTT A) mpred),
    precondition_closed f P ->
  forall ts x rho,
   close_precondition (fn_params f) (fn_vars f) (P ts x) rho |-- P ts x rho.
Proof.
intros.
intros ? ?.
destruct H0 as [ve' [te' [? [? ?]]]].
destruct (H ts x).
rewrite (H3 _ te').
rewrite (H4 _ ve').
simpl.
apply H2.
intros.
simpl.
destruct (H1 i); auto.
intros.
unfold not_a_param.
destruct (In_dec ident_eq i (map (@fst _ _) (fn_params f))); auto.
right; symmetry; apply H0; auto.
Qed.

Definition bind_args (formals vars: list (ident * type)) (P: environ -> pred rmap) : assert :=
          fun rho => !! tc_formals formals rho && close_precondition formals vars P rho.

Definition globals_only (rho: environ) : environ := (mkEnviron (ge_of rho) (Map.empty _) (Map.empty _)).

Definition ret_temp : ident := 1%positive.

Fixpoint make_args (il: list ident) (vl: list val) (rho: environ)  :=
  match il, vl with
  | nil, nil => globals_only rho
  | i::il', v::vl' => env_set (make_args il' vl' rho) i v
   | _ , _ => rho
 end.

Definition get_result1 (ret: ident) (rho: environ) : environ :=
   make_args (ret_temp::nil) (eval_id ret rho :: nil) rho.

Definition get_result (ret: option ident) : environ -> environ :=
 match ret with
 | None => make_args nil nil
 | Some x => get_result1 x
 end.

Definition bind_ret (vl: option val) (t: type) (Q: assert) : assert :=
     match vl, t with
     | None, Tvoid => fun rho => Q (make_args nil nil rho)
     | Some v, _ => fun rho => !! (tc_val t v) &&
                               Q (make_args (ret_temp::nil) (v::nil) rho)
     | _, _ => fun rho => FF
     end.

Definition funassert (Delta: tycontext): assert :=
 fun rho =>
   (ALL  id: ident, ALL fs:funspec,  !! ((glob_specs Delta)!id = Some fs) -->
              EX b:block,
                   !! (Map.get (ge_of rho) id = Some b) && func_at fs (b,0))
   &&
   (ALL  b: block, ALL fs:funspec, func_at' fs (b,0) -->
             EX id:ident, !! (Map.get (ge_of rho) id = Some b)
               && !! exists fs, (glob_specs Delta)!id = Some fs).

(* Unfortunately, we need core_load in the interface as well as address_mapsto,
  because the converse of 'mapsto_core_load' lemma is not true.  The reason is
  that core_load could imply partial ownership of the four bytes of the word
  using different shares that don't have a common core, whereas address_mapsto
  requires the same share on all four bytes. *)
(*
Record ret_assert : Type := {
 RA_normal: assert;
 RA_break: assert;
 RA_continue: assert;
 RA_return: option val -> assert
}.
*)
Definition proj_ret_assert (Q: ret_assert) (ek: exitkind) (vl: option val) : assert :=
 match ek with
 | EK_normal => fun rho => !! (vl = None) && RA_normal Q rho
 | EK_break => fun rho => !! (vl = None) && RA_break Q rho
 | EK_continue => fun rho => !! (vl = None) && RA_continue Q rho
 | EK_return => RA_return Q vl
 end.

(* Definition ret_assert := exitkind -> option val -> assert. *)

Definition overridePost  (Q: assert)  (R: ret_assert) :=
 match R with 
  {| RA_normal := _; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Q; RA_break := b; RA_continue := c; RA_return := r |}
 end.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) :=
  {| RA_normal := fun rho => EX x:A, (R x).(RA_normal) rho;
     RA_break := fun rho => EX x:A, (R x).(RA_break) rho;
     RA_continue := fun rho => EX x:A, (R x).(RA_continue) rho;
     RA_return := fun vl rho => EX x:A, (R x).(RA_return) vl rho
   |}.

Definition normal_ret_assert (Q: assert) : ret_assert :=
  {| RA_normal := Q; RA_break := seplog.FF; RA_continue := seplog.FF; RA_return := fun _ => seplog.FF |}.

Definition frame_ret_assert (R: ret_assert) (F: assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := fun rho => n rho * F rho; 
     RA_break := fun rho => b rho * F rho; 
     RA_continue := fun rho => c rho * F rho;
     RA_return := fun vl rho => r vl rho * F rho |}
 end.

Definition switch_ret_assert (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := seplog.FF; 
     RA_break := n; 
     RA_continue := c;
     RA_return := r |}
 end.

Require Import VST.msl.normalize.

Lemma normal_ret_assert_derives:
 forall P Q rho,
  P rho |-- Q rho ->
  forall ek vl, proj_ret_assert (normal_ret_assert P) ek vl rho 
            |-- proj_ret_assert (normal_ret_assert Q) ek vl rho.
Proof.
 intros.
 destruct ek; normalize. destruct vl; simpl; normalize.
Qed.
Hint Resolve normal_ret_assert_derives.

Lemma normal_ret_assert_FF:
  forall ek vl rho, proj_ret_assert (normal_ret_assert (fun rho => FF)) ek vl rho = FF.
Proof.
intros.
destruct ek; simpl; normalize.
Qed.

Lemma frame_normal:
  forall P F,
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (fun rho => P rho * F rho).
Proof.
intros.
unfold normal_ret_assert; simpl.
f_equal; simpl; try solve [extensionality rho; normalize].
extensionality vl rho; normalize.
Qed.

Definition loop1_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n; 
     RA_continue := Inv;
     RA_return := r |}
 end.

Definition loop2_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n;
     RA_continue := seplog.FF;
     RA_return := r |}
 end.

Lemma frame_for1:
  forall Q R F,
   frame_ret_assert (loop1_ret_assert Q R) F =
   loop1_ret_assert (fun rho => Q rho * F rho) (frame_ret_assert R F).
Proof.
intros.
destruct R; simpl; auto.
Qed.

Lemma frame_loop1:
  forall Q R F,
   frame_ret_assert (loop2_ret_assert Q R) F =
   loop2_ret_assert (fun rho => Q rho * F rho) (frame_ret_assert R F).
Proof.
intros.
destruct R; simpl; auto.
f_equal; extensionality; normalize.
Qed.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; unfold overridePost, normal_ret_assert.
f_equal.
Qed.

Hint Rewrite normal_ret_assert_FF frame_normal frame_for1 frame_loop1
                 overridePost_normal: normalize.

Definition function_body_ret_assert (ret: type) (Q: assert) : ret_assert :=
 {| RA_normal := seplog.FF;
    RA_break := seplog.FF; 
    RA_continue := seplog.FF;
    RA_return := fun vl => bind_ret vl ret Q |}.

Lemma same_glob_funassert:
  forall Delta1 Delta2,
     (forall id, (glob_specs Delta1) ! id = (glob_specs Delta2) ! id) ->
              funassert Delta1 = funassert Delta2.
Proof.
assert (forall Delta Delta' rho,
             (forall id, (glob_specs Delta) ! id = (glob_specs Delta') ! id) ->
             funassert Delta rho |-- funassert Delta' rho).
intros.
unfold funassert.
intros w [? ?]; split.
clear H1; intro id. rewrite <- (H id); auto.
intros loc fs w' Hw' H4; destruct (H1 loc fs w' Hw' H4)  as [id H3].
exists id; rewrite <- (H id); auto.
intros.
extensionality rho.
apply pred_ext; apply H; intros; auto.
Qed.

Lemma funassert_exit_tycon: forall c Delta ek,
     funassert (exit_tycon c Delta ek) = funassert Delta.
Proof.
intros.
apply same_glob_funassert.
intro.
unfold exit_tycon; simpl. destruct ek; auto.
rewrite glob_specs_update_tycon. auto.
Qed.

(*
Lemma strict_bool_val_sub : forall v t b,
 strict_bool_val v t = Some b ->
  Cop.bool_val v t = Some b.
Proof.
  intros. destruct v; destruct t; simpl in *; auto; try congruence;
   unfold Cop.bool_val, Cop.classify_bool; simpl.
  destruct i0; auto.
  f_equal. destruct (Int.eq i Int.zero); try congruence. inv H. reflexivity.
  f_equal. destruct (Int.eq i Int.zero); try congruence. inv H. reflexivity.
  f_equal. destruct (Int.eq i Int.zero); try congruence. inv H. reflexivity.
  destruct f0; inv  H; auto.
  destruct f0; inv  H; auto.
Qed.
*)

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
