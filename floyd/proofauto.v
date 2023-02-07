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
Require Export VST.floyd.step.
Require Export VST.floyd.fastforward.
Require Export VST.floyd.finish.
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
 
#[export] Hint Rewrite add_repr mul_repr sub_repr : entailer_rewrite.
#[export] Hint Rewrite ptrofs_add_repr ptrofs_mul_repr ptrofs_sub_repr : entailer_rewrite.
#[export] Hint Rewrite mul64_repr add64_repr sub64_repr or64_repr and64_repr : entailer_rewrite.
#[export] Hint Rewrite neg_repr neg64_repr : entailer_rewrite.
#[export] Hint Rewrite ptrofs_to_int_repr: entailer_rewrite norm.
#[export] Hint Rewrite ptrofs_to_int64_repr using reflexivity: entailer_rewrite norm.
#[export] Hint Rewrite eqb_type_refl : entailer_rewrite.

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
#[export] Hint Rewrite modu_repr using rep_lia : entailer_rewrite norm.

#[export] Hint Rewrite Vptrofs_unfold_false using reflexivity: entailer_rewrite norm.
#[export] Hint Rewrite Vptrofs_unfold_true using reflexivity: entailer_rewrite norm.

#[export] Hint Extern 1 (Vundef = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = Vundef) => reflexivity : cancel.
#[export] Hint Extern 1 (repeat Vundef _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = repeat _ Vundef) => reflexivity : cancel.
#[export] Hint Extern 1 (Vundef :: _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = Vundef :: _) => reflexivity : cancel.
#[export] Hint Extern 1 (@nil _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = @nil _) => reflexivity : cancel.

#[export] Instance Inhabitant_mpred : Inhabitant mpred := @FF mpred Nveric.
#[export] Instance Inhabitant_share : Inhabitant share := Share.bot.

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

(* A better way to deal with sem_cast_i2bool *)
Lemma sem_cast_i2bool_of_bool : forall (b : bool),
  sem_cast_i2bool (Val.of_bool b) = Some (bool2val b).
Proof.
  destruct b; auto.
Qed.
#[export] Hint Rewrite sem_cast_i2bool_of_bool : norm.

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

(*
Ltac eapply_clean_LOCAL_right_spec'' R ::=
  lazymatch R with
  | context [@data_at ?CS _ _ _ _] => eapply_clean_LOCAL_right_spec' CS
  | context [@field_at ?CS _ _ _ _ _] => eapply_clean_LOCAL_right_spec' CS
  | context [@data_at_ ?CS _ _ _] => eapply_clean_LOCAL_right_spec' CS
  | context [@field_at_ ?CS _ _ _ _] => eapply_clean_LOCAL_right_spec' CS
  | _ => 
  match R with context [?CS] => 
     lazymatch type of CS with compspecs =>
       eapply_clean_LOCAL_right_spec' CS || fail 1
     end
  | _ => eapply_clean_LOCAL_right_spec' emptyCS
  end
 end.

Ltac eapply_clean_LOCAL_right_spec'' R :=
   eapply_clean_LOCAL_right_spec' emptyCS.
*)


