Require Import Coqlib.
Require Import Integers.
Require Import Values. 
Require Import Memory.
Require Import Events.
Require Import Globalenvs. 
Require Import Op.

(*Generalizations of some lemmas from Op.v.*)
Section EVAL_INJECT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Hypothesis globals: meminj_preserves_globals genv f.
Variable sp1: block.
Variable sp2: block.
Variable delta: Z.
Hypothesis sp_inj: f sp1 = Some(sp2, delta).

Lemma eval_addressing_inject':
  forall addr vl1 vl2 v1 ofs,
  val_list_inject f vl1 vl2 ->
  eval_addressing genv (Vptr sp1 ofs) addr vl1 = Some v1 ->
  exists v2, 
     eval_addressing genv (Vptr sp2 ofs) (shift_stack_addressing (Int.repr delta) addr) vl2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. 
  rewrite eval_shift_stack_addressing. simpl.
  eapply eval_addressing_inj with (sp1 := Vptr sp1 ofs); eauto.
  eapply symbol_address_inject; trivial.
Qed.
Lemma eval_operation_inject':
  forall op vl1 vl2 v1 m1 m2 ofs,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_operation genv (Vptr sp1 ofs) op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv (Vptr sp2 ofs) (shift_stack_operation (Int.repr delta) op) vl2 m2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. 
  rewrite eval_shift_stack_operation. simpl.
  eapply eval_operation_inj with (sp1 := Vptr sp1 ofs) (m1 := m1); eauto.
  eapply symbol_address_inject; trivial.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.
End EVAL_INJECT.

Section EVAL_INJECT2.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Variable sp1: val.
Variable sp2: val.
Hypothesis sp_inj: val_inject f sp1 sp2 .
Hypothesis PG: meminj_preserves_globals genv f.
Variable vl1: list val.
Variable vl2: list val.
Hypothesis VL: val_list_inject f vl1 vl2.

Lemma eval_operation_inject'':
  forall op v1 m1 m2,
  Mem.inject f m1 m2 ->
  eval_operation genv sp1 op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv sp2 op vl2 m2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros.
  eapply eval_operation_inj.
  eapply symbol_address_inject; trivial.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  eassumption. eassumption. eassumption.
Qed.

Hypothesis SPVundef: sp1<>Vundef.
Hypothesis SPPtr: forall b ofs, sp1<>Vptr b ofs.

Lemma eval_addressing_sp_scalar:
  forall addr v1,
  eval_addressing genv sp1 addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp2 addr vl2 = Some v2
             /\ val_inject f v1 v2.
Proof.
  intros.
  destruct addr; destruct vl1; simpl in H; try inv H; simpl; trivial.
    destruct l; inv H1. inv VL. inv H3. 
       eexists; split. reflexivity.
       eapply val_add_inject; eauto. 
    destruct l; inv H1. destruct l; inv H0. inv VL. inv H3. inv H5.
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
       eapply val_add_inject; eauto.
    destruct l; inv H1. inv VL. inv H3. 
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
       inv H1; try econstructor.
    destruct l; inv H1. destruct l; inv H0. inv VL. inv H3. inv H5. 
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
       eapply val_add_inject; eauto.
       inv H2; try econstructor.
    inv VL. 
       eexists; split. reflexivity.
         eapply symbol_address_inject; trivial.
    destruct l; inv H1. inv VL. inv H3.
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
         eapply symbol_address_inject; trivial.
    destruct l; inv H1. inv VL. inv H3.
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
         eapply symbol_address_inject; trivial.
         inv H1; try econstructor.
    inv VL. 
       eexists; split. reflexivity.
       eapply val_add_inject; eauto.
Qed.
(*
Hypothesis globals: meminj_preserves_globals genv f.

Lemma eval_operation_inject'':
  forall op vl1 vl2 v1 m1 m2,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_operation genv sp1 op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv sp2 op vl2 m2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros.
  eapply eval_operation_inj.
  eapply symbol_address_inject; trivial.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  eassumption. eassumption. eassumption.
Qed.
*)
End EVAL_INJECT2.