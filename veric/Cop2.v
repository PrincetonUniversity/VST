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

Require Import veric.base.

(** * Type classification and semantics of operators. *)

(** Most C operators are overloaded (they apply to arguments of various
  types) and their semantics depend on the types of their arguments.
  The following [classify_*] functions take as arguments the types
  of the arguments of an operation.  They return enough information
  to resolve overloading for this operator applications, such as
  ``both arguments are floats'', or ``the first is a pointer
  and the second is an integer''.  This classification is used in the
  compiler (module [Cshmgen]) to resolve overloading statically.

  The [sem_*] functions below compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  The corresponding [classify_*] function is first called on the 
  types of the arguments to resolve static overloading.  It is then
  followed by a case analysis on the values of the arguments. *)

(** ** Casts and truth values *)

Definition sem_cast_neutral (v : val) : option val :=
match v with
      | Vint _ | Vptr _ _ => Some v
      | _ => None
      end.

Definition sem_cast_i2i sz2 si2 (v : val) : option val :=
match v with
      | Vint i => Some (Vint (Cop.cast_int_int sz2 si2 i))
      | _ => None
      end.

Definition sem_cast_f2f sz2(v : val) : option val :=
match v with
      | Vfloat f => Some (Vfloat (Cop.cast_float_float sz2 f))
      | _ => None
      end.

Definition sem_cast_i2f si1 sz2 (v : val) : option val :=
      match v with
      | Vint i => Some (Vfloat (Cop.cast_int_float si1 sz2 i))
      | _ => None
      end.


Definition sem_cast_f2i sz2 si2 (v : val) : option val :=
match v with
      | Vfloat f =>
          match Cop.cast_float_int si2 f with
          | Some i => Some (Vint (Cop.cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end.

Definition sem_cast_f2bool (v : val) : option val :=
  match v with
    | Vfloat f =>
      Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
    | _ => None
  end.

Definition sem_cast_p2bool (v : val) : option val :=
 match v with
      | Vint i => Some (Vint (Cop.cast_int_int IBool Signed i))
      | Vptr _ _ => Some (Vint Int.one)
      | _ => None
      end.

Definition sem_cast_l2l (v : val) : option val :=
 match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end.

Definition sem_cast_i2l si (v : val) : option val :=
 match v with
      | Vint n => Some(Vlong (Cop.cast_int_long si n))
      | _ => None
      end.

Definition sem_cast_l2i sz si (v : val) : option val :=
match v with
      | Vlong n => Some(Vint (Cop.cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => None
      end.

Definition sem_cast_l2bool (v : val) : option val :=
 match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | _ => None
      end.

Definition sem_cast_l2f si1 sz2 (v : val) : option val :=
 match v with
      | Vlong i => Some (Vfloat (Cop.cast_long_float si1 sz2 i))
      | _ => None
      end.

Definition sem_cast_f2l si2 (v : val) : option val :=
 match v with
      | Vfloat f =>
          match Cop.cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end.

Definition sem_cast_struct id1 fld1 id2 fld2 (v : val) : option val :=
match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
      | _ => None
      end.

Definition sem_cast_union id1 fld1 id2 fld2 (v : val) : option val :=
 match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
      | _ => None
      end.


Definition sem_cast (t1 t2: type) : val -> option val :=
  match Cop.classify_cast t1 t2 with
  | Cop.cast_case_neutral => sem_cast_neutral
  | Cop.cast_case_i2i sz2 si2 => sem_cast_i2i sz2 si2      
  | Cop.cast_case_f2f sz2 => sem_cast_f2f sz2      
  | Cop.cast_case_i2f si1 sz2 => sem_cast_i2f si1 sz2
  | Cop.cast_case_f2i sz2 si2 => sem_cast_f2i sz2 si2
  | Cop.cast_case_f2bool => sem_cast_f2bool      
  | Cop.cast_case_p2bool => sem_cast_p2bool
  | Cop.cast_case_l2l => sem_cast_l2l     
  | Cop.cast_case_i2l si => sem_cast_i2l si     
  | Cop.cast_case_l2i sz si => sem_cast_l2i sz si      
  | Cop.cast_case_l2bool => sem_cast_l2bool     
  | Cop.cast_case_l2f si1 sz2 => sem_cast_l2f si1 sz2     
  | Cop.cast_case_f2l si2 => sem_cast_f2l si2     
  | Cop.cast_case_struct id1 fld1 id2 fld2 => sem_cast_struct id1 fld1 id2 fld2      
  | Cop.cast_case_union id1 fld1 id2 fld2 => sem_cast_union id1 fld1 id2 fld2     
  | Cop.cast_case_void =>
      fun v => Some v
  | Cop.cast_case_default =>
      fun v => None
  end.

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

Definition bool_val_f (v : val) : option bool :=
 match v with
      | Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
      | _ => None
      end.

Definition bool_val_p (v : val) : option bool :=
match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | Vptr b ofs => Some true
      | _ => None
      end.

Definition bool_val_l (v : val) : option bool :=
 match v with
      | Vlong n => Some (negb (Int64.eq n Int64.zero))
      | _ => None
      end.


Definition bool_val (t: type) : val -> option bool :=
  match Cop.classify_bool t with
  | Cop.bool_case_i => bool_val_i       
  | Cop.bool_case_f => bool_val_f  
  | Cop.bool_case_p => bool_val_p 
  | Cop.bool_case_l => bool_val_l      
  | bool_default => fun v => None
  end.

(** Common-sense relation between Boolean value and casting to [_Bool] type. *)

(** ** Unary operators *)

(** *** Boolean negation *)

Definition sem_notbool_i (v : val) : option val :=
match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | _ => None
      end.

Definition sem_notbool_f (v : val) : option val :=
      match v with
      | Vfloat f => Some (Val.of_bool (Float.cmp Ceq f Float.zero))
      | _ => None
      end.

Definition sem_notbool_p (v : val) : option val :=
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _ _ => Some Vfalse
      | _ => None
      end.

Definition sem_notbool_l (v : val) : option val :=
      match v with
      | Vlong n => Some (Val.of_bool (Int64.eq n Int64.zero))
      | _ => None
      end.


Definition sem_notbool (t: type) : val -> option val :=
  match Cop.classify_bool t with
  | Cop.bool_case_i => sem_notbool_i      
  | Cop.bool_case_f => sem_notbool_f
  | Cop.bool_case_p => sem_notbool_p
  | Cop.bool_case_l => sem_notbool_l
  | bool_default => fun v => None
  end.

(** *** Opposite *)


Definition sem_neg_i (v: val) : option val :=
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end.

Definition sem_neg_f (v: val) : option val :=
       match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end.

Definition sem_neg_l (v: val) : option val :=
      match v with
      | Vlong n => Some (Vlong (Int64.neg n))
      | _ => None
      end.

Definition sem_neg (t: type) : val -> option val :=
  match Cop.classify_neg t with
  | Cop.neg_case_i sg => sem_neg_i
  | Cop.neg_case_f => sem_neg_f
  | Cop.neg_case_l sg => sem_neg_l
  | neg_default => fun v => None
  end.

(** *** Bitwise complement *)

Definition sem_notint_i (v:val) : option val :=
      match v with
      | Vint n => Some (Vint (Int.not n))
      | _ => None
      end.

Definition sem_notint_l (v:val) : option val :=
      match v with
      | Vlong n => Some (Vlong (Int64.not n))
      | _ => None
      end.

Definition sem_notint (t: type)  : val -> option val :=
  match Cop.classify_notint t with
  | Cop.notint_case_i sg => sem_notint_i
  | Cop.notint_case_l sg => sem_notint_l
  | notint_default => fun v => None
  end.

Definition sem_binarith
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (t1: type) (t2: type) (v1: val) (v2: val)  : option val :=
  let c := Cop.classify_binarith t1 t2 in
  let t := Cop.binarith_type c in
  match sem_cast t1 t v1 with
  | None => None
  | Some v1' =>
  match sem_cast t2 t v2 with
  | None => None
  | Some v2' =>
  match Cop.classify_binarith t1 t2 with
  | Cop.bin_case_i sg =>
      match v1', v2' with
      | Vint n1, Vint n2 => sem_int sg n1 n2
      | _,  _ => None
      end
  | Cop.bin_case_f =>
      match v1', v2' with
      | Vfloat n1, Vfloat n2 => sem_float n1 n2
      | _,  _ => None
      end
  | Cop.bin_case_l sg =>
      match v1', v2' with
      | Vlong n1, Vlong n2 => sem_long sg n1 n2
      | _,  _ => None
      end
  | bin_default => None
  end end end.

(** *** Addition *)

Definition sem_add_pi ty (v1 v2 : val) : option val :=
match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
        Some (Vptr b1 (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end.
Definition sem_add_ip ty (v1 v2 : val) : option val :=
 match v1,v2 with
      | Vint n1, Vptr b2 ofs2 => 
        Some (Vptr b2 (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n1)))
      | _,  _ => None
      end.
 
Definition sem_add_pl ty (v1 v2 : val) : option val :=
match v1,v2 with
      | Vptr b1 ofs1, Vlong n2 => 
        let n2 := Int.repr (Int64.unsigned n2) in
        Some (Vptr b1 (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end.

Definition sem_add_lp ty (v1 v2 : val) : option val :=
match v1,v2 with
      | Vlong n1, Vptr b2 ofs2 => 
        let n1 := Int.repr (Int64.unsigned n1) in
        Some (Vptr b2 (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n1)))
      | _,  _ => None
      end.

Definition sem_add_default t1 t2 (v1 v2 : val) : option val :=
sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
        t1 t2 v1 v2.

Definition sem_add (t1:type) (t2:type) :  val->val->option val :=
  match Cop.classify_add t1 t2 with 
  | Cop.add_case_pi ty _ =>  sem_add_pi ty
  | Cop.add_case_ip ty _ => sem_add_ip ty   (**r integer plus pointer *)
  | Cop.add_case_pl ty _ => sem_add_pl ty   (**r pointer plus long *)
  | Cop.add_case_lp ty _ => sem_add_lp ty   (**r long plus pointer *)
  | add_default => sem_add_default t1 t2      
  end.

(** *** Subtraction *)

Definition sem_sub_pi ty (v1 v2 : val) : option val :=
match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
          Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end.

Definition sem_sub_pl ty (v1 v2 : val) : option val :=
 match v1,v2 with
      | Vptr b1 ofs1, Vlong n2 => 
          let n2 := Int.repr (Int64.unsigned n2) in
          Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end.

Definition sem_sub_pp ty (v1 v2 : val) : option val :=
match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if eq_block b1 b2 then
            if Int.eq (Int.repr (sizeof ty)) Int.zero then None
            else Some (Vint (Int.divu (Int.sub ofs1 ofs2) (Int.repr (sizeof ty))))
          else None
      | _, _ => None
      end.

Definition sem_sub_default t1 t2 (v1 v2 : val) : option val :=
 sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
        t1 t2 v1 v2.
Definition sem_sub (t1:type) (t2:type) : val -> val -> option val :=
  match Cop.classify_sub t1 t2 with
  | Cop.sub_case_pi ty attr => sem_sub_pi ty  (**r pointer minus integer *)
  | Cop.sub_case_pl ty attr => sem_sub_pl ty  (**r pointer minus long *)
  | Cop.sub_case_pp ty => sem_sub_pp ty       (**r pointer minus pointer *)
  | sub_default => sem_sub_default t1 t2     
  end.
 
(** *** Multiplication, division, modulus *)

Definition sem_mul (t1:type) (t2:type) (v1:val)  (v2: val)  : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    t1 t2 v1 v2.

Definition sem_div (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.divs n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.divu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.divs n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.divu n1 n2))
      end)
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    t1 t2 v1 v2.

Definition sem_mod (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.mods n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.modu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.mods n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.modu n1 n2))
      end)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_and (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_or (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_xor (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    t1 t2 v1 v2.

(** *** Shifts *)

(** Shifts do not perform the usual binary conversions.  Instead,
  each argument is converted independently, and the signedness
  of the result is always that of the first argument. *)

Definition sem_shift_ii sem_int (sg:signedness) v1 v2 : option val :=
      match v1, v2 with
      | Vint n1, Vint n2 => 
          if Int.ltu n2 Int.iwordsize
          then Some(Vint(sem_int sg n1 n2)) else None
      | _, _ => None
      end.

Definition sem_shift_il sem_int (sg:signedness) v1 v2 : option val :=
match v1, v2 with
      | Vint n1, Vlong n2 => 
          if Int64.ltu n2 (Int64.repr 32)
          then Some(Vint(sem_int sg n1 (Int64.loword n2))) else None
      | _, _ => None
      end.

Definition sem_shift_li sem_long (sg:signedness) v1 v2 : option val :=
match v1, v2 with
      | Vlong n1, Vint n2 => 
          if Int.ltu n2 Int64.iwordsize'
          then Some(Vlong(sem_long sg n1 (Int64.repr (Int.unsigned n2)))) else None
      | _, _ => None
      end.

Definition sem_shift_ll sem_long (sg:signedness) v1 v2 : option val :=
 match v1, v2 with
      | Vlong n1, Vlong n2 => 
          if Int64.ltu n2 Int64.iwordsize
          then Some(Vlong(sem_long sg n1 n2)) else None
      | _, _ => None
      end.

Definition sem_shift
    (t1: type) (t2: type) (sem_int: signedness -> int -> int -> int)
    (sem_long: signedness -> int64 -> int64 -> int64) : val -> val -> option val :=
  match Cop.classify_shift t1 t2 with
  | Cop.shift_case_ii sg => sem_shift_ii sem_int sg 
  | Cop.shift_case_il sg => sem_shift_il sem_int sg
  | Cop.shift_case_li sg => sem_shift_li sem_long sg 
  | Cop.shift_case_ll sg => sem_shift_ll sem_long sg 
  | shift_default => fun v1 v2 => None
  end.

Definition sem_shl (t1:type) (t2:type) (v1:val) (v2: val)  : option val :=
  sem_shift  t1 t2
    (fun sg n1 n2 => Int.shl n1 n2)
    (fun sg n1 n2 => Int64.shl n1 n2)
    v1 v2.

Definition sem_shr (t1:type) (t2:type) (v1:val) (v2: val)  : option val :=
  sem_shift  t1 t2
    (fun sg n1 n2 => match sg with Signed => Int.shr n1 n2 | Unsigned => Int.shru n1 n2 end)
    (fun sg n1 n2 => match sg with Signed => Int64.shr n1 n2 | Unsigned => Int64.shru n1 n2 end)
    v1 v2.

(** *** Comparisons *)

Definition sem_cmp_pp c(valid_pointer : block -> Z -> bool) v1 v2 := 
option_map Val.of_bool (Val.cmpu_bool valid_pointer c v1 v2).

Definition sem_cmp_pl c (valid_pointer : block -> Z -> bool) v1 v2 :=
 match v2 with
      | Vlong n2 => 
          let n2 := Int.repr (Int64.unsigned n2) in
          option_map Val.of_bool (Val.cmpu_bool valid_pointer c v1 (Vint n2))
      | _ => None
      end.

Definition sem_cmp_lp c (valid_pointer : block -> Z -> bool) v1 v2   :=
      match v1 with
      | Vlong n1 => 
          let n1 := Int.repr (Int64.unsigned n1) in
          option_map Val.of_bool (Val.cmpu_bool valid_pointer c (Vint n1) v2)
      | _ => None
      end.

Definition sem_cmp_default c t1 t2 := 
 sem_binarith
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float.cmp c n1 n2)))
        t1 t2 .

Definition sem_cmp (c:comparison)
                  (t1: type) (t2: type) (valid_pointer : block -> Z -> bool) 
                  : val -> val ->  option val :=
  match Cop.classify_cmp t1 t2 with
  | Cop.cmp_case_pp => sem_cmp_pp c valid_pointer       
  | Cop.cmp_case_pl => sem_cmp_pl c valid_pointer    
  | Cop.cmp_case_lp => sem_cmp_lp c valid_pointer
  | Cop.cmp_default => sem_cmp_default c t1 t2     
  end.


(** * Combined semantics of unary and binary operators *)

Definition sem_unary_operation
            (op: Cop.unary_operation) (ty: type) (v: val): option val :=
  match op with
  | Cop.Onotbool => sem_notbool ty v 
  | Cop.Onotint => sem_notint ty v 
  | Cop.Oneg => sem_neg ty v 
  end.

(*Removed memory from sem_cmp calls/args*)
Definition sem_binary_operation'
    (op: Cop.binary_operation)
    (t1:type) (t2: type) (valid_pointer : block -> Z -> bool) : val -> val -> option val :=
  match op with
  | Cop.Oadd => sem_add t1 t2
  | Cop.Osub => (fun v1 v2 => sem_sub t1 t2 v1 v2)
  | Cop.Omul => sem_mul t1 t2
  | Cop.Omod => sem_mod t1 t2
  | Cop.Odiv => sem_div t1 t2 
  | Cop.Oand => sem_and t1 t2
  | Cop.Oor  => sem_or t1 t2 
  | Cop.Oxor  => sem_xor t1 t2 
  | Cop.Oshl => sem_shl t1 t2 
  | Cop.Oshr  => sem_shr t1 t2   
  | Cop.Oeq => sem_cmp Ceq t1 t2 valid_pointer
  | Cop.One => sem_cmp Cne t1 t2 valid_pointer
  | Cop.Olt => sem_cmp Clt t1 t2 valid_pointer
  | Cop.Ogt => sem_cmp Cgt t1 t2 valid_pointer
  | Cop.Ole => sem_cmp Cle t1 t2 valid_pointer
  | Cop.Oge => sem_cmp Cge t1 t2 valid_pointer
  end.

Definition sem_binary_operation   (op: Cop.binary_operation)
    (t1:type) (t2: type) (m : mem) : val -> val -> option val :=
sem_binary_operation' op t1 t2 (Mem.valid_pointer m).

Definition sem_incrdecr (id: Cop.incr_or_decr) (ty: type) (v: val)  :=
  match id with
  | Cop.Incr => sem_add ty type_int32s v (Vint Int.one) 
  | Decr => sem_sub ty type_int32s v (Vint Int.one) 
  end.

(*We can always simplify if the types are known *)
Arguments sem_cast !t1 !t2 / v : simpl nomatch.
Arguments bool_val t / v  : simpl nomatch.
Arguments sem_notbool t / v  : simpl nomatch.
Arguments sem_neg t / v : simpl nomatch.
Arguments sem_notint t / v : simpl nomatch.
Arguments sem_add !t1 !t2 / v1 v2 : simpl nomatch.
Arguments sem_sub !t1 !t2 / v1 v2 : simpl nomatch.
Arguments sem_shift !t1 !t2 _ _  / v1 v2 : simpl nomatch.
Arguments sem_shl !t1 !t2  / v1 v2 : simpl nomatch.
Arguments sem_shr !t1 !t2  / v1 v2 : simpl nomatch.
Arguments sem_cmp c !t1 !t2 / _ v1 v2 : simpl nomatch.
Arguments sem_unary_operation op ty / v : simpl nomatch.
Arguments sem_binary_operation' op !t1 !t2 / valid_pointer v1 v2 : simpl nomatch.
Arguments sem_binary_operation op !t1 !t2 / m v1 v2 : simpl nomatch.



