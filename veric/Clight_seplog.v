Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Require Import VST.veric.mpred.
Require Import VST.veric.address_conflict.
Require Export VST.veric.shares.

Require Export VST.veric.seplog.

Require Export VST.veric.mapsto_memory_block.

Local Open Scope pred.

Require Import compcert.cfrontend.Clight. 
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.binop_lemmas2.
Require Export VST.veric.Clight_mapsto_memory_block.

Local Open Scope pred.

(*Definition expr_true (e: Clight.expr) (rho: environ): Prop :=
  bool_val (eval_expr e rho) (Clight.typeof e) = Some true.*)

Definition expr_true {CS: compspecs} e := lift1 (typed_true (typeof e)) (eval_expr e).

Definition expr_false {CS: compspecs} e := lift1 (typed_false (typeof e)) (eval_expr e).

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
  !! (sizeof (snd idt) <= Ptrofs.max_unsigned) &&
  (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho).

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

Lemma  subst_derives:
 forall a v P Q, (forall rho, P rho |-- Q rho) -> forall rho, subst a v P rho |-- subst a v Q rho.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition tc_formals (formals: list (ident * type)) : environ -> Prop :=
     fun rho => tc_vals (map (@snd _ _) formals) (map (fun xt => (eval_id (fst xt) rho)) formals).

(*This definition, and lemma close_precondition_i below, could be moved to general_seplog*)
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

Definition precondition_closed (f: function) {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred) : Prop :=
 forall ts x,
  closed_wrt_vars (not_a_param (fn_params f)) (P ts x) /\
  closed_wrt_lvars (is_a_local (fn_vars f)) (P ts x).

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


Definition ret_temp : ident := 1%positive.

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

Definition funassert (Delta: tycontext): assert := funspecs_assert (glob_specs Delta).

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
 | EK_normal => RA_normal Q
 | EK_break => RA_break Q
 | EK_continue => RA_continue Q
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

Definition conj_ret_assert (R: ret_assert) (F: assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := fun rho => n rho && F rho; 
     RA_break := fun rho => b rho && F rho; 
     RA_continue := fun rho => c rho && F rho;
     RA_return := fun vl rho => r vl rho && F rho |}
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
 destruct ek; normalize.
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

Lemma proj_frame:
  forall P F ek vl,
    proj_ret_assert (frame_ret_assert P F) ek vl = fun rho => F rho * proj_ret_assert P ek vl rho.
Proof.
  intros.
  extensionality rho.
  rewrite sepcon_comm.
  destruct ek; simpl; destruct P; auto.
Qed.

Lemma proj_conj:
  forall P F ek vl,
    proj_ret_assert (conj_ret_assert P F) ek vl = fun rho => F rho && proj_ret_assert P ek vl rho.
Proof.
  intros.
  extensionality rho.
  rewrite andp_comm.
  destruct ek; simpl; destruct P; auto.
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
Proof. intros; eapply same_FS_funspecs_assert; trivial. Qed.
