Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.seplog.
Require Import VST.veric.tycontext.
Require Import VST.veric.Cop2.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.Clight_seplog.

(* VeriC's assertions are functions environ -> mpred. *)

Section assert.

Context `{!heapGS Σ}.

  Definition env_index : biIndex := {| bi_index_type := environ; bi_index_rel := eq |}.
  Definition assert `{!heapGS Σ} := monPred env_index (iPropI Σ).

  Program Definition assert_of `{!heapGS Σ} (P : environ -> mpred) : assert := {| monPred_at := P |}.

  (* asserts used in the precondition *)
  Definition argsEnviron_index : biIndex := {| bi_index_type := argsEnviron |}.
  Definition argsassert  := monPred argsEnviron_index mpred.
  
  Definition argsassert' := argsEnviron -> mpred.
  Program Definition argsassert_of (P : argsassert') : argsassert := {| monPred_at := P |}.
  Global Coercion argsassert_of : argsassert' >-> argsassert.

  Definition post_index : biIndex := {| bi_index_type := option val |}.
  Definition postassert := monPred post_index mpred.
  Definition postassert' := (option val) -> mpred.
  Program Definition postassert_of (P : postassert') : postassert := {| monPred_at := P |}.
  Global Coercion postassert_of : postassert' >-> postassert.

  Lemma assert_of_at : forall (P : assert), assert_of (monPred_at P) ⊣⊢ P.
  Proof. done. Qed.

  Lemma argsassert_of_at : forall (P : argsassert), argsassert_of (monPred_at P) ⊣⊢ P.
  Proof. done. Qed.

  Lemma postassert_of_at : forall (P : postassert), postassert_of (monPred_at P) ⊣⊢ P.
  Proof. done. Qed.

  Definition NDmk_funspec (sig : typesig) (cc : calling_convention) A (P : A -> argsassert) (Q : A -> postassert) : funspec :=
    mk_funspec sig cc (ConstType A) (λne a, ⊤) (λne (a : leibnizO A), (P a) : _ -d> mpred) (λne (a : leibnizO A), (Q a) : _ -d> mpred).

Lemma subst_derives:
  forall a v (P Q : assert), (P ⊢ Q) -> assert_of (subst a v P) ⊢ assert_of (subst a v Q).
Proof.
  unfold subst; constructor; intros; simpl.
  apply H.
Qed.

Definition local (P : environ -> Prop) : assert := assert_of (λ rho, ⌜P rho⌝).

#[global] Instance local_absorbing P : Absorbing (local P).
Proof. apply monPred_absorbing, _. Qed.

#[global] Instance local_persistent P : Persistent (local P).
Proof. apply monPred_persistent, _. Qed.

Definition var_block (sh: Share.t) {cs: compspecs} (idt: ident * type): assert :=
  ⌜sizeof (snd idt) <= Ptrofs.max_unsigned⌝ ∧
  assert_of (fun rho => (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho)).

Definition stackframe_of {cs: compspecs} (f: Clight.function) : assert :=
  [∗ list] idt ∈ Clight.fn_vars f, var_block Share.top idt.

Definition tc_formals (formals: list (ident * type)) : environ -> Prop :=
     fun rho => tc_vals (map (@snd _ _) formals) (map (fun xt => (eval_id (fst xt) rho)) formals).

Definition close_precondition (bodyparams: list ident) 
    (P: argsassert) : assert :=
 assert_of (fun rho => ∃ vals,
   ⌜map (λ i, lookup i (te_of rho)) bodyparams = map Some vals /\
      Forall (fun v : val => v <> Vundef) vals⌝ ∧
   P (ge_of rho, vals)).

Global Instance close_precondition_proper p : Proper (base.equiv ==> base.equiv) (close_precondition p).
Proof.
  intros ?? H.
  split => rho; solve_proper.
Qed.

Definition bind_args (bodyparams: list (ident * type)) (P: argsassert) : assert :=
  local (tc_formals bodyparams)
     ∧ close_precondition (map fst bodyparams) P.

Record ret_assert : Type := {
 RA_normal: assert;
 RA_break: assert;
 RA_continue: assert;
 RA_return: option val -> assert
}.

Global Instance ret_assert_equiv : Equiv (ret_assert) := fun a b =>
  (RA_normal a ⊣⊢ RA_normal b) /\ (RA_break a ⊣⊢ RA_break b) /\
  (RA_continue a ⊣⊢ RA_continue b) /\ (forall v, RA_return a v ⊣⊢ RA_return b v).

Global Instance ret_assert_equivalence : Equivalence (@base.equiv ret_assert _).
Proof.
  split.
  - intros ?; hnf; auto.
  - intros ?? (? & ? & ? & ?); split3; last split; intros; auto.
    rewrite -H2 //.
  - intros ??? (? & ? & ? & ?) (? & ? & ? & ?); split3; last split; intros; etrans; eauto.
Qed.

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

Definition bind_ret (vl: option val) (t: type) (Q: postassert) : assert :=
     match vl, t with
     | None, Tvoid => ⎡Q None⎤
     | Some v, _ => ⌜tc_val t v⌝ ∧ ⎡Q (Some v)⎤
     | _, _ => False
     end.

Definition function_body_ret_assert (ret: type) (Q: postassert) : ret_assert :=
 {| RA_normal := bind_ret None ret Q;
    RA_break := False;
    RA_continue := False;
    RA_return := fun vl => bind_ret vl ret Q |}.

Global Instance bind_ret_proper vl t : Proper (base.equiv ==> base.equiv) (bind_ret vl t).
Proof. solve_proper. Qed.

Global Instance function_body_ret_assert_proper ret : Proper (base.equiv ==> base.equiv) (function_body_ret_assert ret).
Proof.
  intros ???; split3; last split; simpl; try done.
  - destruct ret; try done.
    f_equiv; apply H.
  - intros; rewrite H //.
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

End assert.
