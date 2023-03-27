Require Export VST.veric.base.
Require Import VST.veric.res_predicates.

Require Import VST.veric.mpred.
Require Import VST.veric.address_conflict.
Require Export VST.veric.shares.

Require Export VST.veric.seplog.

Require Export VST.veric.mapsto_memory_block.

Require Import compcert.cfrontend.Clight.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.binop_lemmas2.
Require Export VST.veric.Clight_mapsto_memory_block.

Definition mkEnv g ids vals : environ := 
      let n := Nat.min (length ids) (length vals) in
      make_args (firstn n ids) (firstn n vals) (mkEnviron g (Map.empty (block * type)) (Map.empty val)).

Lemma ge_of_mkEnv {g v vals}: ge_of (mkEnv g v vals) = g.
Proof. apply ge_of_make_args. Qed.


Definition expr_true {CS: compspecs} e := lift1 (typed_true (typeof e)) (eval_expr e).

Definition expr_false {CS: compspecs} e := lift1 (typed_false (typeof e)) (eval_expr e).

Definition eval_lvar (id: ident) (ty: type) (rho: environ) :=
 match Map.get (ve_of rho) id with
| Some (b, ty') => if eqb_type ty ty' then Vptr b Ptrofs.zero else Vundef
| None => Vundef
end.

Section mpred.

Context `{!heapGS Σ}.

Definition var_block (sh: Share.t) {cs: compspecs} (idt: ident * type) (rho: environ): mpred :=
  ⌜sizeof (snd idt) <= Ptrofs.max_unsigned⌝ ∧
  (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho).

Definition stackframe_of {cs: compspecs} (f: Clight.function) : environ -> mpred :=
  fold_right (fun P Q rho => P rho ∗ Q rho) (fun rho => emp) (map (fun idt => var_block Share.top idt) (Clight.fn_vars f)).

Lemma stackframe_of_eq : forall {cs: compspecs}, stackframe_of =
        fun f rho => fold_right bi_sep emp (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).
Proof.
  intros.
  extensionality f rho.
  unfold stackframe_of.
  forget (fn_vars f) as vl.
  induction vl; simpl; auto.
  rewrite IHvl; auto.
Qed.

Lemma  subst_derives:
 forall a v (P Q : environ -> mpred), (forall rho, P rho ⊢ Q rho) -> forall rho, subst a v P rho ⊢ subst a v Q rho.
Proof.
  exact subst_extens.
Qed.

Definition tc_formals (formals: list (ident * type)) : environ -> Prop :=
     fun rho => tc_vals (map (@snd _ _) formals) (map (fun xt => (eval_id (fst xt) rho)) formals).

(*This definition, and some lemmas below, could be moved to general_seplog*)

Definition close_precondition (bodyparams: list ident) 
    (P: argsEnviron -> mpred) (rho:environ) : mpred :=
 ∃ vals,
   ⌜map (Map.get (te_of rho)) bodyparams = map Some vals /\
      Forall (fun v : val => v <> Vundef) vals⌝ ∧
   P (ge_of rho, vals).

Definition precondition_closed (fs: list (ident*type)) {A}
  (P: A -> environ -> mpred) : Prop :=
 forall x,
  closed_wrt_vars (not_a_param fs) (P x) /\
  closed_wrt_lvars (fun _ => True%type) (P x).

Lemma close_precondition_e':
   forall al (P: argsEnviron -> mpred) (rho: environ),
   close_precondition al P rho ⊢ 
   ∃ vals,
     ⌜map (Map.get (te_of rho)) al = map Some vals /\
        Forall (fun v : val => v <> Vundef) vals⌝ ∧
   P (ge_of rho, vals).
Proof. trivial. Qed.

Lemma Forall_eval_id_get: forall {vals: list val} (V:Forall (fun v : val => v = Vundef -> False) vals), 
  forall ids rho, map (Map.get (te_of rho)) ids = map Some vals <-> map (fun i : ident => eval_id i rho) ids = vals.
Proof.
induction vals; simpl; intros; split; intros; destruct ids; inv H; simpl in *; trivial.
+ inv V. destruct (IHvals H4 ids rho) as [X _]. rewrite (X H2); clear X H2. f_equal.
  unfold eval_id; rewrite H1; simpl; trivial.
+ inv V. destruct (IHvals H2 ids rho) as [_ X]. rewrite X; clear X; trivial. f_equal.
  clear - H1. unfold eval_id, force_val in *.
  destruct (Map.get (te_of rho) p); trivial. elim H1; trivial.
Qed.

Lemma close_precondition_eval_id ids P rho:
   close_precondition ids P rho ⊣⊢
   ∃ vals:_,
     ⌜map (fun i => eval_id i rho) ids = vals /\
        Forall (fun v : val => v <> Vundef) vals⌝ ∧
   P (ge_of rho, vals).
Proof.
unfold close_precondition.
apply bi.exist_proper; intros vals; apply bi.and_proper; last done; apply bi.pure_proper; intuition;
  apply (Forall_eval_id_get); trivial.
Qed. 

Definition bind_args (bodyparams: list (ident * type)) (P: genviron * list val -> mpred) : environ -> mpred :=
  fun rho => ⌜tc_formals bodyparams rho⌝
     ∧ close_precondition (map fst bodyparams) P rho.

Definition ret_temp : ident := 1%positive.

Definition get_result1 (ret: ident) (rho: environ) : environ :=
   make_args (ret_temp::nil) (eval_id ret rho :: nil) rho.

Definition get_result (ret: option ident) : environ -> environ :=
 match ret with
 | None => make_args nil nil
 | Some x => get_result1 x
 end.

Definition bind_ret (vl: option val) (t: type) (Q: environ -> mpred) : environ -> mpred :=
     match vl, t with
     | None, Tvoid => fun rho => Q (make_args nil nil rho)
     | Some v, _ => fun rho => ⌜tc_val t v⌝ ∧
                               Q (make_args (ret_temp::nil) (v::nil) rho)
     | _, _ => fun rho => False
     end.

Definition funassert (Delta: tycontext): assert := funspecs_assert (glob_specs Delta).

(* Unfortunately, we need core_load in the interface as well as address_mapsto,
  because the converse of 'mapsto_core_load' lemma is not true.  The reason is
  that core_load could imply partial ownership of the four bytes of the word
  using different shares that don't have a common core, whereas address_mapsto
  requires the same share on all four bytes. *)

Definition proj_ret_assert (Q: ret_assert) (ek: exitkind) (vl: option val) : environ -> mpred :=
 match ek with
 | EK_normal => fun rho => ⌜vl=None⌝ ∧ RA_normal Q rho
 | EK_break => fun rho => ⌜vl=None⌝ ∧ RA_break Q rho
 | EK_continue => fun rho => ⌜vl=None⌝ ∧ RA_continue Q rho
 | EK_return => RA_return Q vl
 end.

Definition overridePost  (Q: environ -> mpred)  (R: ret_assert) :=
 match R with 
  {| RA_normal := _; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Q; RA_break := b; RA_continue := c; RA_return := r |}
 end.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) :=
  {| RA_normal := fun rho => ∃ x:A, (R x).(RA_normal) rho;
     RA_break := fun rho => ∃ x:A, (R x).(RA_break) rho;
     RA_continue := fun rho => ∃ x:A, (R x).(RA_continue) rho;
     RA_return := fun vl rho => ∃ x:A, (R x).(RA_return) vl rho
   |}.

Definition normal_ret_assert (Q: environ -> mpred) : ret_assert :=
  {| RA_normal := Q; RA_break _ := False; RA_continue _ := False; RA_return _ := fun _ => False |}.

Definition frame_ret_assert (R: ret_assert) (F: environ -> mpred) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := fun rho => n rho ∗ F rho; 
     RA_break := fun rho => b rho ∗ F rho; 
     RA_continue := fun rho => c rho ∗ F rho;
     RA_return := fun vl rho => r vl rho ∗ F rho |}
 end.

Definition conj_ret_assert (R: ret_assert) (F: environ -> mpred) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := fun rho => n rho ∧ F rho; 
     RA_break := fun rho => b rho ∧ F rho; 
     RA_continue := fun rho => c rho ∧ F rho;
     RA_return := fun vl rho => r vl rho ∧ F rho |}
 end.

Definition switch_ret_assert (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal _ := False; 
     RA_break := n; 
     RA_continue := c;
     RA_return := r |}
 end.

Lemma normal_ret_assert_derives:
 forall P Q rho,
  (P rho ⊢ Q rho) ->
  forall ek vl, proj_ret_assert (normal_ret_assert P) ek vl rho 
            ⊢ proj_ret_assert (normal_ret_assert Q) ek vl rho.
Proof.
  intros.
  destruct ek; simpl; auto.
  by rewrite H.
Qed.

Lemma normal_ret_assert_False:
  forall ek vl rho, proj_ret_assert (normal_ret_assert (fun rho => False)) ek vl rho ⊣⊢ False.
Proof.
intros.
destruct ek; simpl; auto; by rewrite bi.and_False.
Qed.

(* Do we care about the kind of equivalence? Should this be an assert? *)
Global Instance ret_assert_equiv : Equiv ret_assert := fun a b =>
  (forall e, RA_normal a e ⊣⊢ RA_normal b e) /\ (forall e, RA_break a e ⊣⊢ RA_break b e) /\
  (forall e, RA_continue a e ⊣⊢ RA_continue b e) /\ (forall v e, RA_return a v e ⊣⊢ RA_return b v e).

Lemma frame_normal:
  forall P F,
   ret_assert_equiv (frame_ret_assert (normal_ret_assert P) F) (normal_ret_assert (fun rho => P rho ∗ F rho)).
Proof.
intros.
unfold normal_ret_assert; simpl.
split3; last split; simpl; auto; intros; by rewrite bi.sep_False.
Qed.

Lemma pure_and_sep_assoc: forall P (Q R : mpred), ⌜P⌝ ∧ Q ∗ R ⊣⊢ (⌜P⌝ ∧ Q) ∗ R.
Proof.
  intros; iSplit.
  - iIntros "($ & $ & $)".
  - iIntros "(($ & $) & $)".
Qed.

Lemma proj_frame:
  forall P F ek vl rho,
    proj_ret_assert (frame_ret_assert P F) ek vl rho ⊣⊢ F rho ∗ proj_ret_assert P ek vl rho.
Proof.
  intros.
  rewrite bi.sep_comm.
  destruct ek; simpl; destruct P; auto; simpl; apply pure_and_sep_assoc.
Qed.

Lemma proj_conj:
  forall P F ek vl rho,
    proj_ret_assert (conj_ret_assert P F) ek vl rho ⊣⊢ F rho ∧ proj_ret_assert P ek vl rho.
Proof.
  intros.
  rewrite bi.and_comm.
  destruct ek; simpl; destruct P; auto; simpl; by rewrite assoc.
Qed.

Definition loop1_ret_assert (Inv: environ -> mpred) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n; 
     RA_continue := Inv;
     RA_return := r |}
 end.

Definition loop2_ret_assert (Inv: environ -> mpred) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n;
     RA_continue _ := False;
     RA_return := r |}
 end.

Lemma frame_for1:
  forall Q R F,
   frame_ret_assert (loop1_ret_assert Q R) F =
   loop1_ret_assert (fun rho => Q rho ∗ F rho) (frame_ret_assert R F).
Proof.
intros.
destruct R; simpl; auto.
Qed.

Lemma frame_loop1:
  forall Q R F,
   ret_assert_equiv (frame_ret_assert (loop2_ret_assert Q R) F)
   (loop2_ret_assert (fun rho => Q rho ∗ F rho) (frame_ret_assert R F)).
Proof.
intros.
destruct R; unfold ret_assert_equiv; simpl.
split3; last split; auto.
intros; by rewrite bi.sep_False.
Qed.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; unfold overridePost, normal_ret_assert.
f_equal.
Qed.

Definition function_body_ret_assert (ret: type) (Q: environ -> mpred) : ret_assert :=
 {| RA_normal := bind_ret None ret Q;
    RA_break _ := False; 
    RA_continue _ := False;
    RA_return := fun vl => bind_ret vl ret Q |}.

Lemma same_glob_funassert:
  forall Delta1 Delta2,
     (forall id, (glob_specs Delta1) !! id = (glob_specs Delta2) !! id) ->
              funassert Delta1 ⊣⊢ funassert Delta2.
Proof. intros; eapply same_FS_funspecs_assert; trivial. Qed.

End mpred.

#[export] Hint Resolve normal_ret_assert_derives : core.
(*#[export] Hint Rewrite normal_ret_assert_False frame_normal frame_for1 frame_loop1
                 overridePost_normal: normalize.*)
