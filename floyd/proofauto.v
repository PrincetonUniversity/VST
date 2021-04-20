From compcert Require Export common.AST cfrontend.Ctypes cfrontend.Clight.
Export Cop.
Require Export VST.floyd.base2.
Require Export VST.floyd.functional_base.
Require Export VST.floyd.client_lemmas.
Require Export VST.floyd.go_lower.
Require Export VST.floyd.closed_lemmas.
Require Export VST.floyd.compare_lemmas.
Require Export VST.floyd.semax_tactics.
Require Export VST.floyd.entailer.
Require Export VST.floyd.forward. (* must come after entailer because of Ltac override *)
Require Export VST.floyd.subsume_funspec.
Require Export VST.floyd.call_lemmas.
Require Export VST.floyd.forward_lemmas.
Require Export VST.floyd.for_lemmas.
Require Export VST.floyd.nested_pred_lemmas.
Require Export VST.floyd.nested_field_lemmas.
Require Export VST.floyd.efield_lemmas.
Require Export VST.floyd.mapsto_memory_block.
Require Export VST.floyd.aggregate_type.
Require VST.floyd.aggregate_pred. Export floyd.aggregate_pred.aggregate_pred.
Require Export VST.floyd.reptype_lemmas.
Require Export VST.floyd.simpl_reptype.
Require Export VST.floyd.data_at_rec_lemmas.
Require Export VST.floyd.field_at.
Require Export VST.floyd.field_at_wand.
Require Export VST.floyd.field_compat.
Require Export VST.floyd.stronger.
Require Export VST.floyd.loadstore_mapsto.
Require Export VST.floyd.loadstore_field_at.
Require Export VST.floyd.nested_loadstore.
Require Export VST.floyd.local2ptree_denote.
Require Export VST.floyd.local2ptree_eval.
Require Export VST.floyd.local2ptree_typecheck.
Require Export VST.floyd.proj_reptype_lemmas.
Require Export VST.floyd.replace_refill_reptype_lemmas.
Require Export VST.floyd.sc_set_load_store.
Require Export VST.floyd.unfold_data_at.
Require Export VST.floyd.globals_lemmas.
Require Export VST.floyd.diagnosis.
Require Export VST.floyd.freezer.
Require Export VST.floyd.deadvars.
Require Export VST.floyd.hints.
Require Export VST.floyd.Clightnotations.
Require Export VST.floyd.data_at_list_solver.
Require Export VST.floyd.data_at_lemmas.
Require VST.msl.iter_sepcon.
Require VST.msl.wand_frame.
Require VST.msl.wandQ_frame.
Require VST.floyd.linking.

(*funspec scope is the default, so remains open.
  User who wnt ot use old funspecs should 
  "Require Import Require Import VST.floyd.Funspec_old_Notation."
  Global Close Scope funspec_scope.*)

Arguments semax {CS} {Espec} Delta Pre%assert cmd%C Post%assert.
Export ListNotations.
Export Clight_Cop2.
 
Hint Rewrite add_repr mul_repr sub_repr : entailer_rewrite.
Hint Rewrite ptrofs_add_repr ptrofs_mul_repr ptrofs_sub_repr : entailer_rewrite.
Hint Rewrite mul64_repr add64_repr sub64_repr or64_repr and64_repr : entailer_rewrite.
Hint Rewrite neg_repr neg64_repr : entailer_rewrite.
Hint Rewrite ptrofs_to_int_repr: entailer_rewrite norm.
Hint Rewrite ptrofs_to_int64_repr using reflexivity: entailer_rewrite norm.

Lemma Vptrofs_unfold_false: 
Archi.ptr64 = false -> Vptrofs = fun x => Vint (Ptrofs.to_int x).
Proof.
intros. unfold Vptrofs.
extensionality x.
rewrite H.
auto.
Qed.

Lemma Vptrofs_unfold_true: 
Archi.ptr64 = true -> Vptrofs = fun x => Vlong (Ptrofs.to_int64 x).
Proof.
intros. unfold Vptrofs.
extensionality x.
rewrite H.
auto.
Qed.

Lemma modu_repr: forall x y, 
   0 <= x <= Int.max_unsigned ->
   0 <= y <= Int.max_unsigned ->
  Int.modu (Int.repr x) (Int.repr y) = Int.repr (x mod y).
Proof.
intros. unfold Int.modu. rewrite !Int.unsigned_repr by auto. auto.
Qed.
Hint Rewrite modu_repr using rep_lia : entailer_rewrite norm.

Hint Rewrite Vptrofs_unfold_false using reflexivity: entailer_rewrite norm.
Hint Rewrite Vptrofs_unfold_true using reflexivity: entailer_rewrite norm.

#[export] Hint Extern 1 (Vundef = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = Vundef) => reflexivity : cancel.
#[export] Hint Extern 1 (repeat Vundef _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = repeat _ Vundef) => reflexivity : cancel.
#[export] Hint Extern 1 (Vundef :: _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = Vundef :: _) => reflexivity : cancel.
#[export] Hint Extern 1 (@nil _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = @nil _) => reflexivity : cancel.

Instance Inhabitant_mpred : Inhabitant mpred := @FF mpred Nveric.
Instance Inhabitant_share : Inhabitant share := Share.bot.

Arguments deref_noload ty v / .
Arguments nested_field_array_type {cs} t gfs lo hi / .
Arguments nested_field_type {cs} t gfs / .  (* redundant? *)
Arguments nested_field_offset {cs} t gfs / .  (* redundant? *)
Arguments Z.mul !x !y.
Arguments Z.sub !m !n.
Arguments Z.add !x !y.
Global Transparent peq.
Global Transparent Archi.ptr64.

#[export] Hint Resolve readable_Ers : core.

Ltac EExists_unify1 x P :=
 match P with
 | ?P1 /\ ?P2 => first [EExists_unify1 x P1 | EExists_unify1 x P2]
 | ?A = ?B =>
  match A with context [x] =>
  pattern (A=B);
  let y := fresh "y" in match goal with |- ?F _ => set (y:=F) end;
  autorewrite with entailer_rewrite;
  first  [subst x; match goal with |- _ (?A' = ?B') => unify A' B' end
  | match goal with
  | x:= ?u |- _ (Vint (Int.repr (x - ?i)) = Vint (Int.repr ?j)) =>
        unify u (j+i); subst x
  | x:= ?u |- _ (Vint (Int.repr (x + ?i)) = Vint (Int.repr ?j)) =>
        unify u (j-i); subst x
  | x:= ?u |- _ (Vlong (Int64.repr (x - ?i)) = Vlong (Int64.repr ?j)) =>
        unify u (j+i); subst x
  | x:= ?u |- _ (Vlong (Int64.repr (x + ?i)) = Vlong (Int64.repr ?j)) =>
        unify u (j-i); subst x
  end];
  subst y; cbv beta
  end
end.

Ltac EExists_unify := 
  let T := fresh "T"  in
  let x := fresh "x" in
  evar (T:Type); evar (x:T); subst T; 
  Exists x;
  match goal with
  | |- _ |-- !! ?P && _ => EExists_unify1 x P
  | |- _ |-- !! ?P => EExists_unify1 x P
  end.

Ltac simpl_implicit :=
  simpl projT1.

Ltac step :=
  first
  [ progress Intros
  | let x := fresh "x" in Intros x
  | progress simpl_implicit
  | progress autorewrite with sublist in *|-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | forward
  | forward_if
  | forward_call
  | rep_lia | cstring' | Zlength_solve
  | match goal with |- ENTAIL _, _ |-- _ =>  go_lower end
  | EExists_unify
  | cstring1
  | deadvars!
  | solve [match goal with |- @derives mpred _ _ _ => cancel end]
  | solve [entailer!; try cstring']
  | list_solve
  ].

Tactic Notation "step!"  :=
  first
  [ progress Intros
  | let x := fresh "x" in
    Intros x
  | progress simpl_implicit
  | progress autorewrite with sublist in * |-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | forward
  | forward_if
  | forward_call
  | rep_lia
  | cstring'
  | Zlength_solve
  | EExists
  | cstring1
  | deadvars!
  | progress_entailer
  (* | match goal with |- _ /\ _ => split end *)
  | list_solve
  ].

Tactic Notation "info_step!" :=
  first
  [ progress Intros; idtac "Intros."
  | let x := fresh "x" in
    Intros x;
    idtac "Intros x."
  | progress simpl_implicit; idtac "simpl_implicit."
  | progress autorewrite with sublist in * |-; idtac "autorewrite with sublist in * |-."
  | progress autorewrite with sublist; idtac "autorewrite with sublist."
  | progress autorewrite with norm; idtac "autorewrite with norm."
  | forward; idtac "forward."
  | forward_if; idtac "forward_if."
  | forward_call; idtac "forward_call."
  | rep_lia; idtac "rep_lia."
  | cstring'; idtac "cstring'."
  | Zlength_solve; idtac "Zlength_solve."
  | EExists; idtac "EExists."
  | cstring1; idtac "cstring1."
  | deadvars!; idtac "deadvars!."
  | progress_entailer; idtac "progress_entailer."
  (* | match goal with |- _ /\ _ => split end; idtac "split." *)
  | list_solve; idtac "list_solve."
  ].

(* A better way to deal with sem_cast_i2bool *)
Lemma sem_cast_i2bool_of_bool : forall (b : bool),
  sem_cast_i2bool (Val.of_bool b) = Some (Val.of_bool b).
Proof.
  destruct b; auto.
Qed.
Hint Rewrite sem_cast_i2bool_of_bool : norm.

#[export] Hint Extern 1 (@eq Z _ _) => Zlength_solve : Zlength_solve.
#[export] Hint Extern 1 (@eq _ _ _) => f_equal : f_equal.

Lemma computable_sizeof: forall cs x, computable x -> computable (@sizeof cs x).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_sizeof : computable.

Lemma computable_Ctypes_sizeof: forall cs x, computable x -> computable (@Ctypes.sizeof cs x).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Ctypes_sizeof : computable.

Lemma computable_alignof: forall cs x, computable x -> computable (@alignof cs x).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_alignof : computable.

Lemma computable_Ctypes_alignof: forall cs x, computable x -> computable (@Ctypes.alignof cs x).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Ctypes_alignof : computable.

Lemma computable_Tint: forall sz s a, computable (Tint sz s a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tint : computable.

Lemma computable_Tlong: forall s a, computable (Tlong s a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tlong : computable.

Lemma computable_Tarray: forall t i a, computable t -> computable i -> computable (Tarray t i a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tarray : computable.

Lemma computable_Tstruct: forall i a, computable i -> computable (Tstruct i a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tstruct : computable.

Lemma computable_Tunion: forall i a, computable i -> computable (Tunion i a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tunion : computable.

Lemma computable_Tpointer: forall t a, computable t -> computable (Tpointer t a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tpointer : computable.

Lemma computable_tptr: forall t, computable t -> computable (tptr t).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_tptr : computable.


(* a little bit of profiling infrastructure . . .
Tactic Notation "entailer" "!" := time "ent2" entbang.
Ltac entailer := time "ent1" floyd.entailer.entailer.
*)

Ltac gather_prop ::=
(* autorewrite with gather_prop_core;  (* faster to do this first *)*)
 autorewrite with gather_prop.

#[export] Hint Resolve Clight_mapsto_memory_block.tc_val_pointer_nullval : core.
#[export] Hint Resolve mapsto_memory_block.tc_val_pointer_nullval : core.
