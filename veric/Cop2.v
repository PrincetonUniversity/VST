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
Import compcert.lib.Maps.

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
 andb (eqb_option Z.eqb (cc_vararg a) (cc_vararg b))
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
       andb (andb (eqb_list eqb_type sa sb) (eqb_type ta tb)) (eqb_calling_convention ca cb)
 | Tstruct ia aa, Tstruct ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | Tunion ia aa, Tunion ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | _, _ => false
 end.  

(*  The following would work, but it would (probably) compute a lot slower in Coq: 
Definition eqb_type (a b: type) := proj_sumbool (type_eq a b).
*)

Definition eqb_member (it1 it2: member): bool :=
  match it1, it2 with
  | Member_plain i1 t1, Member_plain i2 t2 => eqb_ident i1 i2 && eqb_type t1 t2
  | Member_bitfield i1 sz1 sg1 a1 w1 b1, Member_bitfield i2 sz2 sg2 a2 w2 b2 =>
      eqb_ident i1 i2 && eqb_intsize sz1 sz2 && eqb_signedness sg1 sg2 
      && eqb_attr a1 a2 && Z.eqb w1 w2 && Bool.eqb b1 b2
  | _, _ => false
  end.

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

Lemma eqb_calling_convention_refl: forall cc, eqb_calling_convention cc cc = true.
Proof.
destruct cc; simpl; auto.
unfold eqb_calling_convention; simpl.
rewrite ?eqb_reflx.
simpl. rewrite andb_true_r.
destruct cc_vararg; simpl; auto.
apply Z.eqb_eq; auto.
Qed.

Lemma eqb_calling_convention_prop: forall cc1 cc2, eqb_calling_convention cc1 cc2 = true -> cc1=cc2.
Proof.
clear.
intros.
unfold eqb_calling_convention in H.
destruct cc1,cc2; simpl in *.
apply andb_prop in H. destruct H.
apply andb_prop in H0. destruct H0.
apply eqb_prop in H0.
apply eqb_prop in H1.
subst.
destruct cc_vararg, cc_vararg0; inv H; auto.
apply Z.eqb_eq in H1; subst.
auto.
Qed.

Lemma eqb_type_refl: forall a, eqb_type a a = true.
Proof.
 fix REC 1.
destruct a; simpl; intros; rewrite ?andb_true_iff; repeat split; auto;
try apply eqb_intsize_spec; 
try apply eqb_floatsize_spec; 
try apply eqb_signedness_spec;
try apply eqb_attr_spec;  
try apply Zaux.Zeq_bool_diag;
try apply eqb_calling_convention_refl;
try apply eqb_ident_spec;
auto.
induction l; simpl; intros; auto.
rewrite andb_true_iff; split; auto.
Qed.

Lemma eqb_type_spec: forall a b, eqb_type a b = true <-> a=b.
Proof.
 fix REC 1.
intros.
destruct a,b; simpl; split; auto; try discriminate;
 rewrite ?andb_true_iff; intro; 
 repeat match goal with
 | H: _ /\ _ |- _ => destruct H 
 | H: eqb_intsize _ _ = true |- _ => apply eqb_intsize_spec in H
 | H: eqb_signedness _ _ = true |- _ => apply eqb_signedness_spec in H
 | H: eqb_attr _ _ = true |- _ => apply eqb_attr_spec in H
 | H: eqb_floatsize _ _ = true |- _ => apply eqb_floatsize_spec in H
 | H: eqb_calling_convention _ _ = true |- _ => apply eqb_calling_convention_prop in H
 | H: Zeq_bool _ _ = true |- _ => apply Zeq_bool_eq in H
 | H: eqb_ident _ _ = true |- _ => apply eqb_ident_spec in H
 | H: eqb_type _ _ = true |- _ => apply REC in H
 | H: Tint _ _ _ = _ |- _ => inv H
 | H: Tlong _ _ = _ |- _ => inv H
 | H: Tfloat _ _ = _ |- _ => inv H
 | H: Tpointer _ _ = _ |- _ => inv H
 | H: Tarray _ _ _ = _ |- _ => inv H
 | H: Tstruct _ _ = _ |- _ => inv H
 | H: Tunion _ _ = _ |- _ => inv H
 | H: Tfunction _ _ _ = _ |- _ => inv H
 end;
 subst;
 repeat split; repeat f_equal; auto;
 try apply <- eqb_intsize_spec;
 try apply <- eqb_signedness_spec;
 try apply <- eqb_attr_spec;
 try apply <- eqb_floatsize_spec;
 try apply <- eqb_ident_spec;
 try apply Zaux.Zeq_bool_true;
 try apply eqb_calling_convention_refl;
 try apply eqb_type_refl;
 auto.
-
clear - H REC.
revert l0 H; induction l; destruct l0; simpl; intros; auto; try discriminate.
rewrite andb_true_iff in H. destruct H.
f_equal; auto.
apply REC; auto.
-
induction l0; simpl; auto.
rewrite andb_true_iff.
split; auto.
apply eqb_type_refl.
Qed.

(* for alternate eqb_type 
Lemma eqb_type_spec: forall a b, eqb_type a b = true <-> a=b.
Proof.
intros.
unfold eqb_type.
destruct (type_eq _ _); try tauto.
split; intros. inv H. contradiction.
Qed.
*)

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

Lemma eqb_member_spec: forall a b, eqb_member a b = true <-> a=b.
Proof.
  intros.
  destruct a,b; simpl; try solve [split; intro; congruence];
  rewrite ?andb_true_iff, ?eqb_ident_spec, ?eqb_type_spec, ?eqb_intsize_spec, ?eqb_signedness_spec, 
   ?eqb_attr_spec, ?Z.eqb_eq, ?eqb_true_iff.
  split; intro.
  destruct H; subst; auto. inv H; auto.
  split; intro.
  destruct H as [[[[[??]?]?]?]?]; subst. auto. inv H; auto 9.
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
