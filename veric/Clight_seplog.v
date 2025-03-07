Require Export VST.veric.base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.address_conflict.
Require Export VST.veric.shares.

Require Export VST.veric.seplog.

Require Export VST.veric.mapsto_memory_block.

Require Import compcert.cfrontend.Clight.
Require Import VST.veric.tycontext.
Require Import VST.veric.lifting_expr.
Require Import VST.veric.expr2.
Require Export VST.veric.Clight_mapsto_memory_block.

Definition mkEnv g ids vals : environ := 
      let n := Nat.min (length ids) (length vals) in
      make_args (firstn n ids) (firstn n vals) (mkEnviron g empty empty).

Lemma ge_of_mkEnv {g v vals}: ge_of (mkEnv g v vals) = g.
Proof. apply ge_of_make_args. Qed.


Definition expr_true {CS: compspecs} e := lift1 (typed_true (typeof e)) (eval_expr e).

Definition expr_false {CS: compspecs} e := lift1 (typed_false (typeof e)) (eval_expr e).

Definition eval_lvar (id: ident) (ty: type) (rho: environ) :=
 match lookup id (ve_of rho) with
| Some (b, ty') => if eqb_type ty ty' then Vptr b Ptrofs.zero else Vundef
| None => Vundef
end.

Section mpred.

Context `{!heapGS Σ} `{!envGS Σ}.

Local Notation assert := (@assert Σ).

Definition var_block (sh: Share.t) {cs: compspecs} (idt: ident * type): assert :=
  ⌜sizeof (snd idt) <= Ptrofs.max_unsigned⌝ ∧
  ∃ b, lvar (fst idt) (snd idt) b ∗ ⎡memory_block sh (sizeof (snd idt)) (Vptr b Ptrofs.zero)⎤.

Definition stackframe_of {cs: compspecs} (f: Clight.function) : assert :=
  fold_right bi_sep emp (map (fun idt => var_block Share.top idt) (Clight.fn_vars f)).

(*Lemma subst_derives:
 forall a v (P Q : assert), (P ⊢ Q) -> assert_of (subst a v P) ⊢ assert_of (subst a v Q).
Proof.
  exact subst_extens.
Qed.*)

Definition tc_formals (formals: list (ident * type)) : assert :=
  ∃ vals, ([∗ list] i;v ∈ map fst formals;vals, temp i v) ∧
    ⌜tc_vals (map snd formals) vals⌝.

(*This definition, and some lemmas below, could be moved to general_seplog*)

Definition close_precondition (bodyparams: list ident) 
    (P: list val -> mpred) : assert :=
 ∃ vals, ⌜Forall (fun v : val => v <> Vundef) vals⌝ ∧
   ([∗ list] i;v ∈ bodyparams;vals, temp i v) ∗ ⎡P vals⎤.

(*Definition precondition_closed (fs: list (ident*type)) {A}
  (P: A -> assert) : Prop :=
 forall x,
  closed_wrt_vars (not_a_param fs) (P x) /\
  closed_wrt_lvars (fun _ => True%type) (P x).

Lemma close_precondition_e':
   forall al (P: argsassert) (rho: environ),
   close_precondition al P rho ⊢
   ∃ vals,
     ⌜map (Map.get (te_of rho)) al = map Some vals /\
        Forall (fun v : val => v <> Vundef) vals⌝ ∧
   P (ge_of rho, vals).
Proof. trivial. Qed. *)

Global Instance close_precondition_proper p : Proper (pointwise_relation _ base.equiv ==> base.equiv) (close_precondition p).
Proof. solve_proper. Qed.

Lemma Forall_eval_id_get: forall {vals: list val} (V:Forall (fun v : val => v = Vundef -> False) vals), 
  forall ids rho, map (fun i => lookup i (te_of rho)) ids = map Some vals <-> map (fun i : ident => eval_id i rho) ids = vals.
Proof.
induction vals; simpl; intros; split; intros; destruct ids; inv H; simpl in *; trivial.
+ inv V. destruct (IHvals H4 ids rho) as [X _]. rewrite (X H2); clear X H2. f_equal.
  unfold eval_id; rewrite H1; simpl; trivial.
+ inv V. destruct (IHvals H2 ids rho) as [_ X]. rewrite X; clear X; trivial. f_equal.
  clear - H1. unfold eval_id, force_val in *.
  destruct (lookup i (te_of rho)); trivial. elim H1; trivial.
Qed.

(*Lemma close_precondition_eval_id ids P rho:
   close_precondition ids P rho ⊣⊢
   ∃ vals:_,
     ⌜map (fun i => eval_id i rho) ids = vals /\
        Forall (fun v : val => v <> Vundef) vals⌝ ∧
   P (ge_of rho, vals).
Proof.
unfold close_precondition.
apply bi.exist_proper; intros vals; apply bi.and_proper; last done; apply bi.pure_proper; intuition;
  apply (Forall_eval_id_get); trivial.
Qed.*)

Definition bind_args (bodyparams: list (ident * type)) (P: list val -> mpred) : assert :=
  <absorb> tc_formals bodyparams
     ∧ close_precondition (map fst bodyparams) P.

Definition ret_temp : ident := 1%positive.

Definition get_result1 (ret: ident) (rho: environ) : environ :=
   make_args (ret_temp::nil) (eval_id ret rho :: nil) rho.

Definition get_result (ret: option ident) : environ -> environ :=
 match ret with
 | None => make_args nil nil
 | Some x => get_result1 x
 end.

(* Instead of making a fake ret_temp, let's just have the postcondition take the
   return value as an argument. *)
Definition bind_ret (vl: option val) (t: type) (Q: option val → assert) : assert :=
  ⌜match vl with None => t = Tvoid | Some v => tc_val t v end⌝ ∧ Q vl.

Definition funassert (Delta: tycontext): mpred := funspecs_assert (glob_specs Delta).

(* Unfortunately, we need core_load in the interface as well as address_mapsto,
  because the converse of 'mapsto_core_load' lemma is not true.  The reason is
  that core_load could imply partial ownership of the four bytes of the word
  using different shares that don't have a common core, whereas address_mapsto
  requires the same share on all four bytes. *)

Definition proj_ret_assert (Q: ret_assert) (ek: exitkind) (vl: option val) : assert :=
 match ek with
 | EK_normal => ⌜vl=None⌝ ∧ RA_normal Q
 | EK_break => ⌜vl=None⌝ ∧ RA_break Q
 | EK_continue => ⌜vl=None⌝ ∧ RA_continue Q
 | EK_return => RA_return Q vl
 end.

Definition overridePost  (Q: assert)  (R: ret_assert) :=
  {| RA_normal := Q; RA_break := RA_break R; RA_continue := RA_continue R; RA_return := RA_return R |}.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) :=
  {| RA_normal := ∃ x:A, (R x).(RA_normal);
     RA_break := ∃ x:A, (R x).(RA_break);
     RA_continue := ∃ x:A, (R x).(RA_continue);
     RA_return := fun vl => ∃ x:A, (R x).(RA_return) vl
   |}.

Definition normal_ret_assert (Q: assert) : ret_assert :=
  {| RA_normal := Q; RA_break := False; RA_continue := False; RA_return := fun _ => False |}.

Definition frame_ret_assert (R: ret_assert) (F: assert) : ret_assert :=
  {| RA_normal := RA_normal R ∗ F;
     RA_break := RA_break R ∗ F;
     RA_continue := RA_continue R ∗ F;
     RA_return := fun vl => RA_return R vl ∗ F |}.

Definition conj_ret_assert (R: ret_assert) (F: assert) : ret_assert :=
  {| RA_normal := RA_normal R ∧ F;
     RA_break := RA_break R ∧ F;
     RA_continue := RA_continue R ∧ F;
     RA_return := fun vl => RA_return R vl ∧ F |}.

Definition switch_ret_assert (R: ret_assert) : ret_assert :=
  {| RA_normal := False; 
     RA_break := RA_normal R;
     RA_continue := RA_continue R;
     RA_return := RA_return R |}.

Lemma normal_ret_assert_derives:
 forall P Q,
  (P ⊢ Q) ->
  forall ek vl, proj_ret_assert (normal_ret_assert P) ek vl
            ⊢ proj_ret_assert (normal_ret_assert Q) ek vl.
Proof.
  intros.
  destruct ek; simpl; auto.
  rewrite H //.
Qed.

Lemma normal_ret_assert_False:
  forall ek vl, proj_ret_assert (normal_ret_assert False) ek vl ⊣⊢ False.
Proof.
intros.
destruct ek; simpl; auto; by rewrite bi.and_False.
Qed.

Lemma frame_normal:
  forall P F, base.equiv (frame_ret_assert (normal_ret_assert P) F) (normal_ret_assert (P ∗ F)).
Proof.
intros.
unfold normal_ret_assert; simpl.
split3; last split; simpl; auto; intros; rewrite bi.sep_False //.
Qed.

Lemma pure_and_sep_assoc: forall {PROP} P (Q R : bi_car PROP), ⌜P⌝ ∧ Q ∗ R ⊣⊢ (⌜P⌝ ∧ Q) ∗ R.
Proof.
  intros; apply bi.persistent_and_sep_assoc; apply _.
Qed.

Lemma proj_frame:
  forall P F ek vl,
    proj_ret_assert (frame_ret_assert P F) ek vl ⊣⊢ F ∗ proj_ret_assert P ek vl.
Proof.
  intros.
  rewrite bi.sep_comm.
  destruct ek; simpl; rewrite ?pure_and_sep_assoc //.
Qed.

Lemma proj_conj:
  forall P F ek vl,
    proj_ret_assert (conj_ret_assert P F) ek vl ⊣⊢ F ∧ proj_ret_assert P ek vl.
Proof.
  intros.
  rewrite bi.and_comm.
  destruct ek; simpl; rewrite /= ?assoc //.
Qed.

Definition loop1_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
  {| RA_normal := Inv;
     RA_break := RA_normal R;
     RA_continue := Inv;
     RA_return := RA_return R |}.

Definition loop2_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
  {| RA_normal := Inv;
     RA_break := RA_normal R;
     RA_continue := False;
     RA_return := RA_return R |}.

Lemma frame_for1:
  forall Q R F,
   (frame_ret_assert (loop1_ret_assert Q R) F =
    loop1_ret_assert (Q ∗ F) (frame_ret_assert R F))%stdpp.
Proof.
intros. reflexivity.
Qed.

Lemma frame_loop1:
  forall Q R F,
   (frame_ret_assert (loop2_ret_assert Q R) F ≡
    loop2_ret_assert (Q ∗ F) (frame_ret_assert R F))%stdpp.
Proof.
split3; last split; try done; simpl.
apply bi.sep_False.
Qed.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; reflexivity.
Qed.

Definition function_body_ret_assert (ret: type) (Q: option val → assert) : ret_assert :=
 {| RA_normal := bind_ret None ret Q;
    RA_break := False; 
    RA_continue := False;
    RA_return := fun vl => bind_ret vl ret Q |}.

Lemma same_glob_funassert:
  forall Delta1 Delta2,
     (forall id, (glob_specs Delta1) !! id = (glob_specs Delta2) !! id) ->
              funassert Delta1 ⊣⊢ funassert Delta2.
Proof. intros; iSplit; iApply same_FS_funspecs_assert; auto. Qed.

Global Instance bind_ret_proper vl t : Proper (pointwise_relation _ base.equiv ==> base.equiv) (bind_ret vl t).
Proof. solve_proper. Qed.

Global Instance function_body_ret_assert_proper ret : Proper (pointwise_relation _ base.equiv ==> base.equiv) (function_body_ret_assert ret).
Proof.
  intros ???; split3; last split; simpl; solve_proper.
Qed.

Global Instance normal_ret_assert_proper : Proper (base.equiv ==> base.equiv) normal_ret_assert.
Proof.
  intros ???; split3; last split; simpl; try done.
Qed.

Global Instance frame_ret_assert_proper : Proper (base.equiv ==> base.equiv ==> base.equiv) frame_ret_assert.
Proof.
  intros ?? H ?? H'; split3; last split; simpl; intros; rewrite H'; f_equiv; apply H.
Qed.

Global Instance existential_ret_assert_proper {A} : Proper (pointwise_relation A base.equiv ==> base.equiv) existential_ret_assert.
Proof.
  intros ???; split3; last split; simpl; intros; do 2 f_equiv; apply H.
Qed.

End mpred.

#[export] Hint Resolve normal_ret_assert_derives : core.
#[export] Hint Rewrite @normal_ret_assert_False @frame_normal @frame_for1 @frame_loop1
                 @overridePost_normal: normalize.
