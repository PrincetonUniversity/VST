(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)
(* and a few modifications... *)
(** Arithmetic and logical operators for the Compcert C and Clight languages *)

(*In this file, only Clight-independent (but possibly Ctypes-dependent) notions are defined.
  Maybe rename file to CommonOp.v ?*)

Require Import VST.veric.base.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.val_lemmas.

(** Computational version of type_eq **)

Definition eqb_option {A} (f: A -> A -> bool) (x y: option A) : bool :=
  match x, y with
  | None, None => true
  | Some x' , Some y' => f x' y'
 | _, _ => false
  end.

Definition eqb_attr (a b: attr) : bool :=
 match a, b with
 | mk_attr av an, mk_attr bv bn => eqb av bv && eqb_option N.eqb an bn
 end.

Definition eqb_floatsize (a b: floatsize) : bool :=
 match a , b with
 | F32, F32 => true
 | F64, F64 => true
 | _, _ => false
 end.

Definition eqb_ident : ident -> ident -> bool := Pos.eqb.

Definition eqb_intsize (a b: intsize) : bool :=
 match a , b with
 | I8, I8 => true
 | I16, I16 => true
 | I32, I32 => true
 | IBool, IBool => true
 | _, _ => false
 end.

Definition eqb_signedness (a b : signedness) :=
 match a, b with
 | Signed, Signed => true
 | Unsigned, Unsigned => true
 | _, _ => false
 end.

Definition eqb_calling_convention (a b: calling_convention) :=
 andb (eqb (cc_vararg a) (cc_vararg b))
     (andb  (eqb (cc_unproto a) (cc_unproto b))
      (eqb (cc_structret a) (cc_structret b))).

Fixpoint eqb_type (a b: type) {struct a} : bool :=
 match a, b with
 | Tvoid, Tvoid => true
 | Tint ia sa aa, Tint ib sb ab => andb (eqb_intsize ia ib)
                                                    (andb (eqb_signedness sa sb) (eqb_attr aa ab))
 | Tlong sa aa, Tlong sb ab => andb (eqb_signedness sa sb) (eqb_attr aa ab)
 | Tfloat sa aa, Tfloat sb ab => andb (eqb_floatsize sa sb) (eqb_attr aa ab)
 | Tpointer ta aa, Tpointer tb ab => andb (eqb_type ta tb) (eqb_attr aa ab)
 | Tarray ta sa aa, Tarray tb sb ab => andb (eqb_type ta tb)
                                                                   (andb (Zeq_bool sa sb) (eqb_attr aa ab))
 | Tfunction sa ta ca, Tfunction sb tb cb =>
       andb (andb (eqb_typelist sa sb) (eqb_type ta tb)) (eqb_calling_convention ca cb)
 | Tstruct ia aa, Tstruct ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | Tunion ia aa, Tunion ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | _, _ => false
 end
with eqb_typelist (a b: typelist)  {struct a}: bool :=
  match a, b with
  | Tcons ta ra, Tcons tb rb => andb (eqb_type ta tb) (eqb_typelist ra rb)
  | Tnil, Tnil => true
  | _ , _ => false
  end.

Scheme eqb_type_sch := Induction for type Sort Prop
  with eqb_typelist_sch := Induction for  typelist Sort Prop.

Definition eqb_member (it1 it2: ident * type): bool :=
  eqb_ident (fst it1) (fst it2) && eqb_type (snd it1) (snd it2).

Definition eqb_su (su1 su2: struct_or_union): bool :=
  match su1, su2 with
  | Struct, Struct
  | Union, Union => true
  | _, _ => false
  end.

Lemma eqb_intsize_spec: forall i j, eqb_intsize i j = true <-> i=j.
Proof. destruct i,j; simpl; split; intro; congruence. Qed.
Lemma eqb_floatsize_spec: forall i j, eqb_floatsize i j = true <-> i=j.
Proof. destruct i,j; simpl; split; intro; congruence. Qed.
Lemma eqb_signedness_spec: forall i j, eqb_signedness i j = true <-> i=j.
Proof. destruct i,j; simpl; split; intro; congruence. Qed.
Lemma eqb_attr_spec: forall i j, eqb_attr i j = true <-> i=j.
Proof.
  destruct i as [[ | ] [ | ]]; destruct j as [[ | ] [ | ]];
   simpl; split; intro; try rewrite N.eqb_eq in *; try congruence.
Qed.
Lemma eqb_ident_spec: forall i j, eqb_ident i j = true <-> i=j.
Proof.
 intros. unfold eqb_ident.
 apply Pos.eqb_eq.
Qed.

Lemma eqb_type_spec: forall a b, eqb_type a b = true <-> a=b.
Proof.
apply (eqb_type_sch
           (fun a => forall b, eqb_type a b = true <-> a=b)
          (fun a => forall b, eqb_typelist a b = true <-> a=b));
  destruct b; simpl;
   split; intro;
   repeat rewrite andb_true_iff in *;
   try rewrite eqb_intsize_spec in *;
   try rewrite eqb_floatsize_spec in *;
   try rewrite eqb_signedness_spec in *;
   try rewrite eqb_attr_spec in *;
   try rewrite eqb_ident_spec in *;
   try rewrite <- Zeq_is_eq_bool in *;
   repeat match goal with H: _ /\ _ |- _  => destruct H end;
   repeat split; subst; f_equal; try  congruence;
    try solve [apply H; auto];
    try solve [inv H0; apply H; auto].
*  apply H0; auto.
*  clear - H2; destruct c as [[|] [|] [|]]; destruct c0 as [[|] [|] [|]]; inv H2; auto.
*  inv H1; apply H; auto.
*  inv H1; apply H0; auto.
*   inv H1; destruct c0 as [[|] [|] [|]]; reflexivity.
*  apply H0; auto.
*   inv H1; apply H; auto.
*   inv H1; apply H0; auto.
Qed.

Lemma eqb_type_true: forall a b, eqb_type a b = true -> a=b.
Proof.
intros. apply eqb_type_spec; auto.
Qed.

Lemma eqb_type_false: forall a b, eqb_type a b = false <-> a<>b.
Proof.
intros.
pose proof (eqb_type_spec a b).
destruct (eqb_type a b);
split; intro; try congruence.
destruct H. rewrite H in H0 by auto. congruence.
intro; subst.
destruct H; try congruence.
spec H1; auto. congruence.
Qed.

Lemma eqb_type_refl: forall a, eqb_type a a = true.
Proof.
intros. apply eqb_type_spec; auto.
Qed.

Lemma eqb_member_spec: forall a b, eqb_member a b = true <-> a=b.
Proof.
  intros.
  unfold eqb_member.
  rewrite andb_true_iff.
  rewrite eqb_ident_spec.
  rewrite eqb_type_spec.
  destruct a, b; simpl.
  split.
  + intros [? ?]; subst; auto.
  + intros.
    inv H; auto.
Qed.

Lemma eqb_su_spec: forall a b, eqb_su a b = true <-> a=b.
Proof.
  intros.
  destruct a,b; split; simpl; intros; try congruence.
Qed.


Definition log2_sizeof_pointer : N := 
  ltac:(let n := eval compute in 
  (N.log2 (Z.to_N (@sizeof (PTree.empty _) (Tpointer Tvoid noattr))))
   in exact (n)).

Definition int_or_ptr_type : type :=
  Tpointer Tvoid {| attr_volatile := false; attr_alignas := Some log2_sizeof_pointer |}.


(** The following describes types that can be interpreted as a boolean:
  integers, floats, pointers.  It is used for the semantics of
  the [!] and [?] operators, as well as the [if], [while], [for] statements. *)

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Definition bool_val_i (v : val) : option bool :=
match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | _ => None
      end.

Definition bool_val_p (v : val) : option bool :=
match v with
      | Vint n => if Archi.ptr64 then None else Some (negb (Int.eq n Int.zero))
      | Vlong n => if Archi.ptr64 then Some (negb (Int64.eq n Int64.zero)) else None
      | Vptr b ofs => Some true
      | _ => None
      end.

Definition bool_val_s (v : val) : option bool :=
 match v with
      | Vsingle f => Some (negb (Float32.cmp Ceq f Float32.zero))
      | _ => None
      end.

Definition bool_val_f (v : val) : option bool :=
 match v with
      | Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
      | _ => None
      end.

Definition bool_val_l (v : val) : option bool :=
 match v with
      | Vlong n => Some (negb (Int64.eq n Int64.zero))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else Some true
      | _ => None
      end.

Definition bool_val (t: type) : val -> option bool :=
  match t with
  | Tint _ _ _ => bool_val_i
  | Tpointer _ _ => if  eqb_type t int_or_ptr_type then (fun _ => None) else bool_val_p
  | Tfloat F64 _ => bool_val_f
  | Tfloat F32 _ => bool_val_s
  | Tlong _ _ => bool_val_l
  | _ => fun v => None
  end.



(*************** from veric.expr.v   **********************)

Definition size_t := if Archi.ptr64 then Tlong Unsigned noattr else Tint I32 Unsigned noattr.

Definition is_int (sz: intsize) (sg: signedness) (v: val) :=
  match v with
  | Vint i =>
    match sz, sg with
    | I8, Signed => Byte.min_signed <= Int.signed i <= Byte.max_signed
    | I8, Unsigned => Int.unsigned i <= Byte.max_unsigned
    | I16, Signed => -two_p (16-1) <= Int.signed i <= two_p (16-1) -1
    | I16, Unsigned => Int.unsigned i <= two_p 16 - 1
    | I32, _ => True
    | IBool, _ => i = Int.zero \/ i = Int.one
    end
  | _ => False
  end.

Definition tc_val (ty: type) : val -> Prop :=
 match ty with
 | Tint sz sg _ => is_int sz sg
 | Tlong _ _ => is_long
 | Tfloat F64 _ => is_float
 | Tfloat F32 _ => is_single
 | Tpointer _ _ => if eqb_type ty int_or_ptr_type then is_pointer_or_integer else is_pointer_or_null
 | Tarray _ _ _ | Tfunction _ _ _ => is_pointer_or_null
 | Tstruct _ _ => isptr
 | Tunion _ _ => isptr
 | _ => fun _ => False
 end.

Definition tc_val' t v := v <> Vundef -> tc_val t v.

Fixpoint tc_vals (ty: list type) (v: list val) : Prop :=
 match v, ty with
 | v1::vs , t1::ts => tc_val t1 v1 /\ tc_vals ts vs
 | nil, nil => True
 | _, _ => False
end.

Lemma tc_val_Vundef:
  forall t, ~tc_val t Vundef.
Proof.
intros.
intro. hnf in H.
destruct t; try contradiction.
destruct f; try contradiction.
destruct (eqb_type _ _) in H; try contradiction.
Qed.

Lemma tc_val'_Vundef:
  forall t, tc_val' t Vundef.
Proof.
  intros.
  intro; congruence.
Qed.

Lemma tc_val_tc_val':
  forall t v, tc_val t v -> tc_val' t v.
Proof.
  intros.
  intro; auto.
Qed.

Lemma tc_val_has_type (ty : type) (v : val) :
  tc_val ty v ->
  Val.has_type v (typ_of_type ty).
Proof.
  destruct ty eqn:?, v eqn:?;
  try solve [simpl; auto; try destruct f; auto];
  try solve [unfold tc_val, is_pointer_or_null;
    try simple_if_tac; try solve [simpl; auto; intros; contradiction];
    simpl; unfold Tptr; intros; try subst i;
    destruct Archi.ptr64; try contradiction; subst; auto];
  simpl; unfold Tptr; destruct Archi.ptr64; auto.
Qed.

Arguments bool_val t / v  : simpl nomatch.
