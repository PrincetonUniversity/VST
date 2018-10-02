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

(* This file extends Cop2 by Clight-dependent notions*)

Require Export VST.veric.Cop2.
Require Import VST.veric.Clight_base.
Require Import VST.veric.tycontext.

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

Definition sem_cast_pointer (v : val) : option val := Some v.

Definition sem_cast_i2i sz2 si2 (v : val) : option val :=
match v with
      | Vint i => Some (Vint (Cop.cast_int_int sz2 si2 i))
      | _ => None
      end.

Definition sem_cast_i2bool (v: val) : option val := 
      match v with
      | Vint n =>
          Some(Vint(if Int.eq n Int.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if Archi.ptr64 then None else Some Vone
      | _ => None
      end.

Definition sem_cast_l2bool (v: val) : option val :=
      match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else Some Vone
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

Definition sem_cast_struct id1 id2 (v : val) : option val :=
match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end.

Definition sem_cast_union id1 id2 (v : val) : option val :=
match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end.

Definition sem_cast_f2f (v: val) : option val :=
      match v with
      | Vfloat f => Some (Vfloat f)
      | _ => None
      end.

Definition sem_cast_s2s (v: val) : option val :=
      match v with
      | Vsingle f => Some (Vsingle f)
      | _ => None
      end.

Definition sem_cast_s2f (v: val) : option val :=
      match v with
      | Vsingle f => Some (Vfloat (Float.of_single f))
      | _ => None
      end.

 Definition sem_cast_f2s (v: val) : option val :=
      match v with
      | Vfloat f => Some (Vsingle (Float.to_single f))
      | _ => None
      end.

 Definition sem_cast_i2f si1 (v: val) : option val :=
      match v with
      | Vint i => Some (Vfloat (Cop.cast_int_float si1 i))
      | _ => None
      end.

 Definition sem_cast_i2s si1 (v: val) : option val :=
      match v with
      | Vint i => Some (Vsingle (Cop.cast_int_single si1 i))
      | _ => None
      end.

 Definition sem_cast_f2i sz2 si2 (v: val) : option val :=
      match v with
      | Vfloat f =>
          match Cop.cast_float_int si2 f with
          | Some i => Some (Vint (Cop.cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end.

Definition sem_cast_s2i sz2 si2 (v: val) : option val :=
      match v with
      | Vsingle f =>
          match Cop.cast_single_int si2 f with
          | Some i => Some (Vint (Cop.cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end.

Definition sem_cast_f2bool (v: val) : option val :=
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end.

Definition sem_cast_s2bool (v: val) : option val :=
      match v with
      | Vsingle f =>
          Some(Vint(if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => None
      end.

 Definition sem_cast_l2f si1 (v: val) : option val :=
      match v with
      | Vlong i => Some (Vfloat (Cop.cast_long_float si1 i))
      | _ => None
      end.

 Definition sem_cast_l2s si1 (v: val) : option val :=
      match v with
      | Vlong i => Some (Vsingle (Cop.cast_long_single si1 i))
      | _ => None
      end.

 Definition sem_cast_f2l si2 (v: val) : option val :=
      match v with
      | Vfloat f =>
          match Cop.cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end.

Definition sem_cast_s2l si2 (v: val) : option val :=
      match v with
      | Vsingle f =>
          match Cop.cast_single_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end.

Definition classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with
  (* To [void] *)
  | Tvoid, _ => cast_case_void
  (* To [_Bool] *)
  | Tint IBool _ _, Tint _ _ _ => cast_case_i2bool
  | Tint IBool _ _, Tlong _ _ => cast_case_l2bool
  | Tint IBool _ _, Tfloat F64 _ => cast_case_f2bool
  | Tint IBool _ _, Tfloat F32 _ => cast_case_s2bool
  | Tint IBool _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => 
    if eqb_type tfrom int_or_ptr_type then cast_case_default 
    else if Archi.ptr64 then cast_case_l2bool else cast_case_i2bool
  (* To [int] other than [_Bool] *)
  | Tint sz2 si2 _, Tint _ _ _ =>
      if Archi.ptr64 then cast_case_i2i sz2 si2
      else if intsize_eq sz2 I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
  | Tint sz2 si2 _, Tlong _ _ => cast_case_l2i sz2 si2
  | Tint sz2 si2 _, Tfloat F64 _ => cast_case_f2i sz2 si2
  | Tint sz2 si2 _, Tfloat F32 _ => cast_case_s2i sz2 si2
  | Tint sz2 si2 _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
      if eqb_type tfrom int_or_ptr_type then cast_case_default 
      else if Archi.ptr64 then cast_case_l2i sz2 si2
      else if intsize_eq sz2 I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
  (* To [long] *)
  | Tlong _ _, Tlong _ _ =>
      if Archi.ptr64 then cast_case_pointer else cast_case_l2l
  | Tlong _ _, Tint sz1 si1 _ => cast_case_i2l si1
  | Tlong si2 _, Tfloat F64 _ => cast_case_f2l si2
  | Tlong si2 _, Tfloat F32 _ => cast_case_s2l si2
  | Tlong si2 _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
      if eqb_type tfrom int_or_ptr_type 
              then cast_case_default 
      else if Archi.ptr64 
         then cast_case_pointer 
         else cast_case_i2l si2
  (* To [float] *)
  | Tfloat F64 _, Tint sz1 si1 _ => cast_case_i2f si1
  | Tfloat F32 _, Tint sz1 si1 _ => cast_case_i2s si1
  | Tfloat F64 _, Tlong si1 _ => cast_case_l2f si1
  | Tfloat F32 _, Tlong si1 _ => cast_case_l2s si1
  | Tfloat F64 _, Tfloat F64 _ => cast_case_f2f
  | Tfloat F32 _, Tfloat F32 _ => cast_case_s2s
  | Tfloat F64 _, Tfloat F32 _ => cast_case_s2f
  | Tfloat F32 _, Tfloat F64 _ => cast_case_f2s
  (* To pointer types *)
  | Tpointer _ _, Tint _ _ _ =>
      if eqb_type tto int_or_ptr_type 
      then cast_case_default 
      else if Archi.ptr64 then cast_case_i2l Unsigned 
      else cast_case_pointer
  | Tpointer _ _, Tlong _ _ =>
      if eqb_type tto int_or_ptr_type 
      then cast_case_default 
      else if Archi.ptr64 then cast_case_pointer else cast_case_l2i I32 Unsigned
  | Tpointer _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => 
       if eqb (eqb_type tto int_or_ptr_type) (eqb_type tfrom int_or_ptr_type)
       then cast_case_pointer
       else cast_case_default
  (* To struct or union types *)
  | Tstruct id2 _, Tstruct id1 _ => cast_case_struct id1 id2
  | Tunion id2 _, Tunion id1 _ => cast_case_union id1 id2
  (* Catch-all *)
  | _, _ => cast_case_default
  end.

Arguments classify_cast tfrom tto / .

Definition sem_cast (t1 t2: type): val -> option val := 
  match classify_cast t1 t2 with
  | cast_case_pointer => sem_cast_pointer
  | Cop.cast_case_i2i sz2 si2 => sem_cast_i2i sz2 si2
  | Cop.cast_case_f2f => sem_cast_f2f
  | Cop.cast_case_s2s => sem_cast_s2s
  | Cop.cast_case_s2f => sem_cast_s2f
  | Cop.cast_case_f2s => sem_cast_f2s
  | Cop.cast_case_i2f si1 => sem_cast_i2f si1
  | Cop.cast_case_i2s si1 => sem_cast_i2s si1
  | Cop.cast_case_f2i sz2 si2 => sem_cast_f2i sz2 si2
  | Cop.cast_case_s2i sz2 si2 => sem_cast_s2i sz2 si2
  | Cop.cast_case_i2bool => sem_cast_i2bool
  | Cop.cast_case_l2bool => sem_cast_l2bool
  | Cop.cast_case_f2bool => sem_cast_f2bool
  | Cop.cast_case_s2bool => sem_cast_s2bool
  | Cop.cast_case_l2l => sem_cast_l2l
  | Cop.cast_case_i2l si => sem_cast_i2l si
  | Cop.cast_case_l2i sz si => sem_cast_l2i sz si
  | Cop.cast_case_l2f si1 => sem_cast_l2f si1
  | Cop.cast_case_l2s si1 => sem_cast_l2s si1
  | Cop.cast_case_f2l si2 => sem_cast_f2l si2
  | Cop.cast_case_s2l si2 => sem_cast_s2l si2
  | Cop.cast_case_struct id1 id2 => sem_cast_struct id1 id2
  | Cop.cast_case_union id1 id2 => sem_cast_union id1 id2
  | Cop.cast_case_void =>
      fun v => Some v
  | Cop.cast_case_default =>
      fun v => None
 end.

(** Common-sense relation between Boolean value and casting to [_Bool] type. *)

(** ** Unary operators *)

(** *** Boolean negation *) 

Definition sem_notbool (t: type) (v: val) : option val :=
  option_map (fun b => Val.of_bool (negb b)) (Cop2.bool_val t v).

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

Definition sem_neg_s (v: val) : option val :=
       match v with
      | Vsingle f => Some (Vsingle (Float32.neg f))
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
  | Cop.neg_case_s => sem_neg_s
  | Cop.neg_case_l sg => sem_neg_l
  | neg_default => fun v => None
  end.

Definition sem_absfloat_i sg (v: val) : option val :=
  match v with
      | Vint n => Some (Vfloat (Float.abs (Cop.cast_int_float sg n)))
      | _ => None
      end.

Definition sem_absfloat_f (v: val) :=
     match v with
      | Vfloat f => Some (Vfloat (Float.abs f))
      | _ => None
      end.

Definition sem_absfloat_s (v: val) :=
      match v with
      | Vsingle f => Some (Vfloat (Float.abs (Float.of_single f)))
      | _ => None
      end.

Definition sem_absfloat_l sg v :=
      match v with
      | Vlong n => Some (Vfloat (Float.abs (Cop.cast_long_float sg n)))
      | _ => None
      end.

Definition sem_absfloat (ty: type)  : val -> option val :=
  match Cop.classify_neg ty with
  | Cop.neg_case_i sg => sem_absfloat_i sg
  | Cop.neg_case_f => sem_absfloat_f
  | Cop.neg_case_s => sem_absfloat_s
   | Cop.neg_case_l sg => sem_absfloat_l sg
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

Definition both_int (f: int -> int -> option val) (cast1 cast2: val -> option val) (v1 v2: val) :=
 match cast1 v1, cast2 v2 with Some (Vint v1'), Some (Vint v2') => f v1' v2' | _, _ => None end.

Definition both_long (f: int64 -> int64 -> option val) (cast1 cast2: val -> option val) (v1 v2: val) :=
 match cast1 v1, cast2 v2 with Some (Vlong v1'), Some (Vlong v2') => f v1' v2' | _, _ => None end.

Definition both_float (f: float -> float -> option val) (cast1 cast2: val -> option val) (v1 v2: val) :=
 match cast1 v1, cast2 v2 with Some (Vfloat v1'), Some (Vfloat v2') => f v1' v2' | _, _ => None end.

Definition both_single (f: float32 -> float32 -> option val) (cast1 cast2: val -> option val) (v1 v2: val) :=
 match cast1 v1, cast2 v2 with Some (Vsingle v1'), Some (Vsingle v2') => f v1' v2' | _, _ => None end.


Definition sem_binarith
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (sem_single: float32 -> float32 -> option val)
    (t1: type) (t2: type)
   : forall (v1: val) (v2: val), option val := 
  let c := Cop.classify_binarith t1 t2 in
  let t := Cop.binarith_type c in
  match c with
  | Cop.bin_case_i sg => both_int (sem_int sg) (sem_cast t1 t) (sem_cast t2 t)
  | Cop.bin_case_f => both_float (sem_float) (sem_cast t1 t) (sem_cast t2 t)
  | Cop.bin_case_s => both_single (sem_single) (sem_cast t1 t) (sem_cast t2 t)
  | Cop.bin_case_l sg => both_long (sem_long sg) (sem_cast t1 t) (sem_cast t2 t)
  | bin_default => fun _ _ => None
  end.

Definition sem_add_ptr_int {CS: compspecs} ty si v1 v2 :=
 Cop.sem_add_ptr_int cenv_cs ty si v1 v2.

Definition sem_add_int_ptr {CS: compspecs} ty si v1 v2 :=
 Cop.sem_add_ptr_int cenv_cs ty si v2 v1.

Definition sem_add_ptr_long {CS: compspecs} ty v1 v2 :=
 Cop.sem_add_ptr_long cenv_cs ty v1 v2.

Definition sem_add_long_ptr {CS: compspecs} ty v1 v2 :=
 Cop.sem_add_ptr_long cenv_cs ty v2 v1.

(** *** Addition *)
Definition sem_add {CS: compspecs} (t1:type) (t2:type):  val->val->option val :=
  match classify_add t1 t2 with
  | add_case_pi ty si =>             (**r pointer plus integer *)
      sem_add_ptr_int ty si
  | add_case_pl ty =>                (**r pointer plus long *)
      sem_add_ptr_long ty
  | add_case_ip si ty =>             (**r integer plus pointer *)
      sem_add_int_ptr ty si
  | add_case_lp ty =>                (**r long plus pointer *)
      sem_add_long_ptr ty
  | add_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.add n1 n2)))
        t1 t2
  end.

(** *** Subtraction *)

Definition sem_sub_pi {CS: compspecs} (ty:type) (si: signedness) (v1 v2 : val) : option val :=
      match v1, v2 with
      | Vptr b1 ofs1, Vint n2 =>
          let n2 := ptrofs_of_int si n2 in
          Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ty)) n2)))
      | Vint n1, Vint n2 =>
          if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | Vlong n1, Vint n2 =>
          let n2 := cast_int_long si n2 in
          if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof ty)) n2))) else None
      | _,  _ => None
      end.

Definition sem_sub_pl {CS: compspecs} (ty:type) (v1 v2 : val) : option val := 
      match v1, v2 with
      | Vptr b1 ofs1, Vlong n2 =>
          let n2 := Ptrofs.of_int64 n2 in
          Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ty)) n2)))
      | Vint n1, Vlong n2 =>
          let n2 := Int.repr (Int64.unsigned n2) in
          if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | Vlong n1, Vlong n2 =>
          if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof ty)) n2))) else None
      | _,  _ => None
      end.

Definition sem_sub_pp {CS: compspecs} (ty:type) (v1 v2 : val) : option val :=
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if eq_block b1 b2 then
            let sz := sizeof ty in
            if zlt 0 sz && zle sz Ptrofs.max_signed
            then Some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
            else None
          else None
      | _, _ => None
      end.

Definition sem_sub_default (t1 t2:type) (v1 v2 : val) : option val :=
 sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.sub n1 n2)))
        t1 t2 v1 v2.

Definition sem_sub {CS: compspecs} (t1:type) (t2:type) : val -> val -> option val :=
  match Cop.classify_sub t1 t2 with
  | Cop.sub_case_pi ty si=> sem_sub_pi  ty si  (**r pointer minus integer *)
  | Cop.sub_case_pl ty => sem_sub_pl  ty  (**r pointer minus long *)
  | Cop.sub_case_pp ty => sem_sub_pp ty       (**r pointer minus pointer *)
  | sub_default => sem_sub_default t1 t2
  end.

(** *** Multiplication, division, modulus *)

Definition sem_mul (t1:type) (t2:type) (v1:val)  (v2: val)  : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
    t1 t2 v1 v2.

Definition sem_div (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint (match sg with | Signed => Int.divs | Unsigned => Int.divu end n1 n2)))
    (fun sg n1 n2 => Some(Vlong (match sg with | Signed => Int64.divs | Unsigned => Int64.divu end n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.div n1 n2)))
    t1 t2 v1 v2.

Definition sem_mod (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint (match sg with | Signed => Int.mods | Unsigned => Int.modu end n1 n2)))
    (fun sg n1 n2 => Some(Vlong (match sg with | Signed => Int64.mods | Unsigned => Int64.modu end n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_and (t1:type) (t2:type) (v1:val) (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_or (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_xor (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

(** *** Shifts *)

(** Shifts do not perform the usual binary conversions.  Instead,
  each argument is converted independently, and the signedness
  of the result is always that of the first argument. *)

Definition sem_shift_ii sem_int (sg:signedness) v1 v2 : option val :=
      match v1, v2 with
      | Vint n1, Vint n2 =>
          (*if Int.ltu n2 Int.iwordsize
          then*) Some(Vint(sem_int sg n1 n2)) (*else None*)
      | _, _ => None
      end.

Definition sem_shift_il sem_int (sg:signedness) v1 v2 : option val :=
match v1, v2 with
      | Vint n1, Vlong n2 =>
          (*if Int64.ltu n2 (Int64.repr 32)
          then *) Some(Vint(sem_int sg n1 (Int64.loword n2))) (*else None*)
      | _, _ => None
      end.

Definition sem_shift_li sem_long (sg:signedness) v1 v2 : option val :=
match v1, v2 with
      | Vlong n1, Vint n2 =>
          (*if Int.ltu n2 Int64.iwordsize'
          then *) Some(Vlong(sem_long sg n1 (Int64.repr (Int.unsigned n2)))) (*else None*)
      | _, _ => None
      end.

Definition sem_shift_ll sem_long (sg:signedness) v1 v2 : option val :=
 match v1, v2 with
      | Vlong n1, Vlong n2 =>
          (*if Int64.ltu n2 Int64.iwordsize
          then *) Some(Vlong(sem_long sg n1 n2)) (*else None*)
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

(*  obsolete since CompCert 3.0
Definition cast_out_long (v: val) : val :=
  match v with
  | Vlong l => Vint (Int.repr (Int64.unsigned l))
  | _ => v
  end.
*)
Definition true2 (b : block) (i : Z) := true.

Definition sem_cmp_pp c v1 v2 :=
  option_map Val.of_bool
   (if Archi.ptr64
    then Val.cmplu_bool true2 c v1 v2
    else Val.cmpu_bool true2 c v1 v2).

Definition sem_cmp_pi si c v1 v2 :=
      match v2 with
      | Vint n2 => sem_cmp_pp c v1 (Vptrofs (ptrofs_of_int si n2))
      | Vptr _ _ => if Archi.ptr64 then None else sem_cmp_pp c v1 v2
      | _ => None
      end.

Definition sem_cmp_ip si c v1 v2 :=
      match v1 with
      | Vint n1 => sem_cmp_pp c (Vptrofs (ptrofs_of_int si n1)) v2
      | Vptr _ _ => if Archi.ptr64 then None else sem_cmp_pp c v1 v2
      | _ => None
      end.

Definition sem_cmp_pl c v1 v2 :=
      match v2 with
      | Vlong n2 => sem_cmp_pp c v1 (Vptrofs (Ptrofs.of_int64 n2))
      | Vptr _ _ => if Archi.ptr64 then sem_cmp_pp c v1 v2 else None
      | _ => None
      end.

Definition sem_cmp_lp c v1 v2 := 
      match v1 with
      | Vlong n1 => sem_cmp_pp c (Vptrofs (Ptrofs.of_int64 n1)) v2
      | Vptr _ _ => if Archi.ptr64 then sem_cmp_pp c v1 v2 else None
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
        (fun n1 n2 =>
            Some(Val.of_bool(Float32.cmp c n1 n2)))
        t1 t2 .

Definition sem_cmp (c:comparison) (t1: type) (t2: type) : val -> val ->  option val :=
  match Cop.classify_cmp t1 t2 with
  | Cop.cmp_case_pp => 
     if orb (eqb_type t1 int_or_ptr_type) (eqb_type t2 int_or_ptr_type) 
            then (fun _ _ => None)
     else sem_cmp_pp c
  | Cop.cmp_case_pi si => 
     if eqb_type t1 int_or_ptr_type
            then (fun _ _ => None)
     else sem_cmp_pi si c
  | Cop.cmp_case_ip si => 
     if eqb_type t2 int_or_ptr_type
            then (fun _ _ => None)
     else sem_cmp_ip si c
  | Cop.cmp_case_pl => 
     if eqb_type t1 int_or_ptr_type
            then (fun _ _ => None)
     else sem_cmp_pl c
  | Cop.cmp_case_lp => 
     if eqb_type t2 int_or_ptr_type
            then (fun _ _ => None)
     else sem_cmp_lp c
  | Cop.cmp_default => sem_cmp_default c t1 t2
  end.

(** * Combined semantics of unary and binary operators *)

Definition sem_unary_operation
            (op: Cop.unary_operation) (ty: type) (v: val): option val :=
  match op with
  | Cop.Onotbool => sem_notbool ty v
  | Cop.Onotint => sem_notint ty v
  | Cop.Oneg => sem_neg ty v
  | Cop.Oabsfloat => sem_absfloat ty v
  end.

(*Removed memory from sem_cmp calls/args*)
Definition sem_binary_operation'
    {CS: compspecs} (op: Cop.binary_operation)
    (t1:type) (t2: type) : val -> val -> option val :=
  match op with
  | Cop.Oadd => sem_add t1 t2
  | Cop.Osub => sem_sub t1 t2
  | Cop.Omul => sem_mul t1 t2
  | Cop.Omod => sem_mod t1 t2
  | Cop.Odiv => sem_div t1 t2
  | Cop.Oand => sem_and t1 t2
  | Cop.Oor  => sem_or t1 t2
  | Cop.Oxor  => sem_xor t1 t2
  | Cop.Oshl => sem_shl t1 t2
  | Cop.Oshr  => sem_shr t1 t2
  | Cop.Oeq => sem_cmp Ceq t1 t2
  | Cop.One => sem_cmp Cne t1 t2
  | Cop.Olt => sem_cmp Clt t1 t2
  | Cop.Ogt => sem_cmp Cgt t1 t2
  | Cop.Ole => sem_cmp Cle t1 t2
  | Cop.Oge => sem_cmp Cge t1 t2
  end.

Definition sem_incrdecr {CS: compspecs} (id: Cop.incr_or_decr) (ty: type)  (valid_pointer : block -> Z -> bool)  (v: val)  :=
  match id with
  | Cop.Incr => sem_add ty type_int32s v (Vint Int.one)
  | Decr => sem_sub ty type_int32s v (Vint Int.one)
  end.

(*We can always simplify if the types are known *)
Arguments Cop.classify_cast tfrom tto / .
Arguments Cop.classify_bool ty / .
Arguments Cop.classify_neg ty / .
Arguments Cop.classify_notint ty / .
Arguments Cop.classify_binarith ty1 ty2 / .
Arguments Cop.classify_add ty1 ty2 / .
Arguments Cop.classify_sub ty1 ty2 / .
Arguments Cop.classify_shift ty1 ty2 / .
Arguments Cop.classify_cmp ty1 ty2 / .
Arguments Cop.classify_fun ty / .
Arguments sem_cast t1 t2 / v : simpl nomatch.
(*moved to Cop2: Arguments bool_val t / v  : simpl nomatch.*)
Arguments sem_notbool t / v  : simpl nomatch.
Arguments sem_neg t / v : simpl nomatch.
Arguments sem_notint t / v : simpl nomatch.
Arguments sem_add CS t1 t2 / v1 v2 : simpl nomatch.
Arguments sem_sub CS t1 t2 / v1 v2 : simpl nomatch.
Arguments sem_shift t1 t2 _ _  / v1 v2 : simpl nomatch.
Arguments sem_shl t1 t2  / v1 v2 : simpl nomatch.
Arguments sem_shr t1 t2  / v1 v2 : simpl nomatch.
Arguments sem_cmp c t1 t2 / v1 v2 : simpl nomatch.
Arguments sem_unary_operation op ty / v : simpl nomatch.
Arguments sem_binary_operation' CS op t1 t2 / v1 v2 : simpl nomatch.
(*Arguments sem_binary_operation CS op t1 t2 / m v1 v2 : simpl nomatch.*)
Arguments sem_cmp_default c t1 t2 / v1 v2 : simpl nomatch.
Arguments sem_binarith sem_int sem_long sem_float sem_single t1 t2 / v1 v2 : simpl nomatch.
Arguments Cop.sem_cast v !t1 !t2 m / .