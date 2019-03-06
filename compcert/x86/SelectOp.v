(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Instruction selection for operators *)

(** The instruction selection pass recognizes opportunities for using
  combined arithmetic and logical operations and addressing modes
  offered by the target processor.  For instance, the expression [x + 1]
  can take advantage of the "immediate add" instruction of the processor,
  and on the PowerPC, the expression [(x >> 6) & 0xFF] can be turned
  into a "rotate and mask" instruction.

  This file defines functions for building CminorSel expressions and
  statements, especially expressions consisting of operator
  applications.  These functions examine their arguments to choose
  cheaper forms of operators whenever possible.

  For instance, [add e1 e2] will return a CminorSel expression semantically
  equivalent to [Eop Oadd (e1 ::: e2 ::: Enil)], but will use a
  [Oaddimm] operator if one of the arguments is an integer constant,
  or suppress the addition altogether if one of the arguments is the
  null integer.  In passing, we perform operator reassociation
  ([(e + c1) * c2] becomes [(e * c2) + (c1 * c2)]) and a small amount
  of constant propagation.

  On top of the "smart constructor" functions defined below,
  module [Selection] implements the actual instruction selection pass.
*)

Require Import Coqlib.
Require Import Compopts.
Require Import AST Integers Floats.
Require Import Op CminorSel.

Local Open Scope cminorsel_scope.

(** ** Constants **)

(** External oracle to determine whether a symbol should be addressed
  through [Oindirectsymbol] or can be addressed via [Oleal Aglobal].
  This is to accommodate MacOS X's limitations on references to data
  symbols imported from shared libraries.  It can also help with PIC
  code under ELF. *)

Parameter symbol_is_external: ident -> bool.

Definition Olea_ptr (a: addressing) := if Archi.ptr64 then Oleal a else Olea a.

Definition addrsymbol (id: ident) (ofs: ptrofs) :=
  if symbol_is_external id then
    if Ptrofs.eq ofs Ptrofs.zero
    then Eop (Oindirectsymbol id) Enil
    else Eop (Olea_ptr (Aindexed (Ptrofs.unsigned ofs))) (Eop (Oindirectsymbol id) Enil ::: Enil)
  else
    Eop (Olea_ptr (Aglobal id ofs)) Enil.

Definition addrstack (ofs: ptrofs) :=
  Eop (Olea_ptr (Ainstack ofs)) Enil.

(** ** Integer logical negation *)

(** Original definition:
<<
Nondetfunction notint (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ointconst (Int.not n)) Enil
  | Eop (Oxorimm n) (e1 ::: Enil) => Eop (Oxorimm (Int.not n)) (e1 ::: Enil)
  | _ => Eop Onot (e ::: Enil)
  end.
>>
*)

Inductive notint_cases: forall (e: expr), Type :=
  | notint_case1: forall n, notint_cases (Eop (Ointconst n) Enil)
  | notint_case2: forall n e1, notint_cases (Eop (Oxorimm n) (e1 ::: Enil))
  | notint_default: forall (e: expr), notint_cases e.

Definition notint_match (e: expr) :=
  match e as zz1 return notint_cases zz1 with
  | Eop (Ointconst n) Enil => notint_case1 n
  | Eop (Oxorimm n) (e1 ::: Enil) => notint_case2 n e1
  | e => notint_default e
  end.

Definition notint (e: expr) :=
  match notint_match e with
  | notint_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.not n)) Enil
  | notint_case2 n e1 => (* Eop (Oxorimm n) (e1 ::: Enil) *) 
      Eop (Oxorimm (Int.not n)) (e1 ::: Enil)
  | notint_default e =>
      Eop Onot (e ::: Enil)
  end.


(** ** Integer addition and pointer addition *)

(** Original definition:
<<
Nondetfunction addimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e else
  match e with
  | Eop (Ointconst m) Enil => Eop (Ointconst(Int.add n m)) Enil
  | Eop (Olea addr) args   => Eop (Olea (offset_addressing_total addr (Int.signed n))) args
  | _                      => Eop (Olea (Aindexed (Int.signed n))) (e ::: Enil)
  end.
>>
*)

Inductive addimm_cases: forall (e: expr), Type :=
  | addimm_case1: forall m, addimm_cases (Eop (Ointconst m) Enil)
  | addimm_case2: forall addr args, addimm_cases (Eop (Olea addr) args)
  | addimm_default: forall (e: expr), addimm_cases e.

Definition addimm_match (e: expr) :=
  match e as zz1 return addimm_cases zz1 with
  | Eop (Ointconst m) Enil => addimm_case1 m
  | Eop (Olea addr) args => addimm_case2 addr args
  | e => addimm_default e
  end.

Definition addimm (n: int) (e: expr) :=
 if Int.eq n Int.zero then e else match addimm_match e with
  | addimm_case1 m => (* Eop (Ointconst m) Enil *) 
      Eop (Ointconst(Int.add n m)) Enil
  | addimm_case2 addr args => (* Eop (Olea addr) args *) 
      Eop (Olea (offset_addressing_total addr (Int.signed n))) args
  | addimm_default e =>
      Eop (Olea (Aindexed (Int.signed n))) (e ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction add (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => addimm n1 t2
  | t1, Eop (Ointconst n2) Enil => addimm n2 t1
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      Eop (Olea (Aindexed2 (n1 + n2))) (t1:::t2:::Enil)
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Ascaled sc n2)) (t2:::Enil) =>
      Eop (Olea (Aindexed2scaled sc (n1 + n2))) (t1:::t2:::Enil)
  | Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      Eop (Olea (Aindexed2scaled sc (n1 + n2))) (t2:::t1:::Enil)
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil =>
      Eop (Olea (Abased id (Ptrofs.add ofs (Ptrofs.repr n1)))) (t1:::Enil)
  | Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      Eop (Olea (Abased id (Ptrofs.add ofs (Ptrofs.repr n2)))) (t2:::Enil)
  | Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil =>
      Eop (Olea (Abasedscaled sc id (Ptrofs.add ofs (Ptrofs.repr n1)))) (t1:::Enil)
  | Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Ascaled sc n2)) (t2:::Enil) =>
      Eop (Olea (Abasedscaled sc id (Ptrofs.add ofs (Ptrofs.repr n2)))) (t2:::Enil)
  | Eop (Olea (Ascaled sc n)) (t1:::Enil), t2 =>
      Eop (Olea (Aindexed2scaled sc n)) (t2:::t1:::Enil)
  | t1, Eop (Olea (Ascaled sc n)) (t2:::Enil) =>
      Eop (Olea (Aindexed2scaled sc n)) (t1:::t2:::Enil)
  | Eop (Olea (Aindexed n)) (t1:::Enil), t2 =>
      Eop (Olea (Aindexed2 n)) (t1:::t2:::Enil)
  | t1, Eop (Olea (Aindexed n)) (t2:::Enil) =>
      Eop (Olea (Aindexed2 n)) (t1:::t2:::Enil)
  | _, _ =>
      Eop (Olea (Aindexed2 0)) (e1:::e2:::Enil)
  end.
>>
*)

Inductive add_cases: forall (e1: expr) (e2: expr), Type :=
  | add_case1: forall n1 t2, add_cases (Eop (Ointconst n1) Enil) (t2)
  | add_case2: forall t1 n2, add_cases (t1) (Eop (Ointconst n2) Enil)
  | add_case3: forall n1 t1 n2 t2, add_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | add_case4: forall n1 t1 sc n2 t2, add_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (Eop (Olea (Ascaled sc n2)) (t2:::Enil))
  | add_case5: forall sc n1 t1 n2 t2, add_cases (Eop (Olea (Ascaled sc n1)) (t1:::Enil)) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | add_case6: forall n1 t1 id ofs, add_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (Eop (Olea (Aglobal id ofs)) Enil)
  | add_case7: forall id ofs n2 t2, add_cases (Eop (Olea (Aglobal id ofs)) Enil) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | add_case8: forall sc n1 t1 id ofs, add_cases (Eop (Olea (Ascaled sc n1)) (t1:::Enil)) (Eop (Olea (Aglobal id ofs)) Enil)
  | add_case9: forall id ofs sc n2 t2, add_cases (Eop (Olea (Aglobal id ofs)) Enil) (Eop (Olea (Ascaled sc n2)) (t2:::Enil))
  | add_case10: forall sc n t1 t2, add_cases (Eop (Olea (Ascaled sc n)) (t1:::Enil)) (t2)
  | add_case11: forall t1 sc n t2, add_cases (t1) (Eop (Olea (Ascaled sc n)) (t2:::Enil))
  | add_case12: forall n t1 t2, add_cases (Eop (Olea (Aindexed n)) (t1:::Enil)) (t2)
  | add_case13: forall t1 n t2, add_cases (t1) (Eop (Olea (Aindexed n)) (t2:::Enil))
  | add_default: forall (e1: expr) (e2: expr), add_cases e1 e2.

Definition add_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return add_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => add_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => add_case2 t1 n2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) => add_case3 n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Ascaled sc n2)) (t2:::Enil) => add_case4 n1 t1 sc n2 t2
  | Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) => add_case5 sc n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil => add_case6 n1 t1 id ofs
  | Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Aindexed n2)) (t2:::Enil) => add_case7 id ofs n2 t2
  | Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil => add_case8 sc n1 t1 id ofs
  | Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Ascaled sc n2)) (t2:::Enil) => add_case9 id ofs sc n2 t2
  | Eop (Olea (Ascaled sc n)) (t1:::Enil), t2 => add_case10 sc n t1 t2
  | t1, Eop (Olea (Ascaled sc n)) (t2:::Enil) => add_case11 t1 sc n t2
  | Eop (Olea (Aindexed n)) (t1:::Enil), t2 => add_case12 n t1 t2
  | t1, Eop (Olea (Aindexed n)) (t2:::Enil) => add_case13 t1 n t2
  | e1, e2 => add_default e1 e2
  end.

Definition add (e1: expr) (e2: expr) :=
  match add_match e1 e2 with
  | add_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      addimm n1 t2
  | add_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      addimm n2 t1
  | add_case3 n1 t1 n2 t2 => (* Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) *) 
      Eop (Olea (Aindexed2 (n1 + n2))) (t1:::t2:::Enil)
  | add_case4 n1 t1 sc n2 t2 => (* Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Ascaled sc n2)) (t2:::Enil) *) 
      Eop (Olea (Aindexed2scaled sc (n1 + n2))) (t1:::t2:::Enil)
  | add_case5 sc n1 t1 n2 t2 => (* Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) *) 
      Eop (Olea (Aindexed2scaled sc (n1 + n2))) (t2:::t1:::Enil)
  | add_case6 n1 t1 id ofs => (* Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil *) 
      Eop (Olea (Abased id (Ptrofs.add ofs (Ptrofs.repr n1)))) (t1:::Enil)
  | add_case7 id ofs n2 t2 => (* Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Aindexed n2)) (t2:::Enil) *) 
      Eop (Olea (Abased id (Ptrofs.add ofs (Ptrofs.repr n2)))) (t2:::Enil)
  | add_case8 sc n1 t1 id ofs => (* Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil *) 
      Eop (Olea (Abasedscaled sc id (Ptrofs.add ofs (Ptrofs.repr n1)))) (t1:::Enil)
  | add_case9 id ofs sc n2 t2 => (* Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Ascaled sc n2)) (t2:::Enil) *) 
      Eop (Olea (Abasedscaled sc id (Ptrofs.add ofs (Ptrofs.repr n2)))) (t2:::Enil)
  | add_case10 sc n t1 t2 => (* Eop (Olea (Ascaled sc n)) (t1:::Enil), t2 *) 
      Eop (Olea (Aindexed2scaled sc n)) (t2:::t1:::Enil)
  | add_case11 t1 sc n t2 => (* t1, Eop (Olea (Ascaled sc n)) (t2:::Enil) *) 
      Eop (Olea (Aindexed2scaled sc n)) (t1:::t2:::Enil)
  | add_case12 n t1 t2 => (* Eop (Olea (Aindexed n)) (t1:::Enil), t2 *) 
      Eop (Olea (Aindexed2 n)) (t1:::t2:::Enil)
  | add_case13 t1 n t2 => (* t1, Eop (Olea (Aindexed n)) (t2:::Enil) *) 
      Eop (Olea (Aindexed2 n)) (t1:::t2:::Enil)
  | add_default e1 e2 =>
      Eop (Olea (Aindexed2 0)) (e1:::e2:::Enil)
  end.


(** ** Opposite *)

(** Original definition:
<<
Nondetfunction negint (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ointconst (Int.neg n)) Enil
  | _ =>  Eop Oneg (e ::: Enil)
  end.
>>
*)

Inductive negint_cases: forall (e: expr), Type :=
  | negint_case1: forall n, negint_cases (Eop (Ointconst n) Enil)
  | negint_default: forall (e: expr), negint_cases e.

Definition negint_match (e: expr) :=
  match e as zz1 return negint_cases zz1 with
  | Eop (Ointconst n) Enil => negint_case1 n
  | e => negint_default e
  end.

Definition negint (e: expr) :=
  match negint_match e with
  | negint_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.neg n)) Enil
  | negint_default e =>
      Eop Oneg (e ::: Enil)
  end.


(** ** Integer and pointer subtraction *)

(** Original definition:
<<
Nondetfunction sub (e1: expr) (e2: expr) :=
  match e1, e2 with
  | t1, Eop (Ointconst n2) Enil => addimm (Int.neg n2) t1
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      addimm (Int.repr (n1 - n2)) (Eop Osub (t1:::t2:::Enil))
  | Eop (Olea (Aindexed n1)) (t1:::Enil), t2 =>
      addimm (Int.repr n1) (Eop Osub (t1:::t2:::Enil))
  | t1, Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      addimm (Int.repr (-n2)) (Eop Osub (t1:::t2:::Enil))
  | _, _ =>
      Eop Osub (e1:::e2:::Enil)
  end.
>>
*)

Inductive sub_cases: forall (e1: expr) (e2: expr), Type :=
  | sub_case1: forall t1 n2, sub_cases (t1) (Eop (Ointconst n2) Enil)
  | sub_case2: forall n1 t1 n2 t2, sub_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | sub_case3: forall n1 t1 t2, sub_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (t2)
  | sub_case4: forall t1 n2 t2, sub_cases (t1) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | sub_default: forall (e1: expr) (e2: expr), sub_cases e1 e2.

Definition sub_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return sub_cases zz1 zz2 with
  | t1, Eop (Ointconst n2) Enil => sub_case1 t1 n2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) => sub_case2 n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), t2 => sub_case3 n1 t1 t2
  | t1, Eop (Olea (Aindexed n2)) (t2:::Enil) => sub_case4 t1 n2 t2
  | e1, e2 => sub_default e1 e2
  end.

Definition sub (e1: expr) (e2: expr) :=
  match sub_match e1 e2 with
  | sub_case1 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      addimm (Int.neg n2) t1
  | sub_case2 n1 t1 n2 t2 => (* Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) *) 
      addimm (Int.repr (n1 - n2)) (Eop Osub (t1:::t2:::Enil))
  | sub_case3 n1 t1 t2 => (* Eop (Olea (Aindexed n1)) (t1:::Enil), t2 *) 
      addimm (Int.repr n1) (Eop Osub (t1:::t2:::Enil))
  | sub_case4 t1 n2 t2 => (* t1, Eop (Olea (Aindexed n2)) (t2:::Enil) *) 
      addimm (Int.repr (-n2)) (Eop Osub (t1:::t2:::Enil))
  | sub_default e1 e2 =>
      Eop Osub (e1:::e2:::Enil)
  end.


(** ** Immediate shifts *)

Definition shift_is_scale (n: int) : bool :=
  Int.eq n (Int.repr 1) || Int.eq n (Int.repr 2) || Int.eq n (Int.repr 3).

(** Original definition:
<<
Nondetfunction shlimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  if negb (Int.ltu n Int.iwordsize) then
    Eop Oshl (e1:::Eop (Ointconst n) Enil:::Enil)
  else
    match e1 with
    | Eop (Ointconst n1) Enil =>
        Eop (Ointconst(Int.shl n1 n)) Enil
    | Eop (Oshlimm n1) (t1:::Enil) =>
        if Int.ltu (Int.add n n1) Int.iwordsize
        then Eop (Oshlimm (Int.add n n1)) (t1:::Enil)
        else Eop (Oshlimm n) (e1:::Enil)
    | Eop (Olea (Aindexed n1)) (t1:::Enil) =>
        if shift_is_scale n
        then Eop (Olea (Ascaled (Int.unsigned (Int.shl Int.one n))
                                (Int.unsigned (Int.shl (Int.repr n1) n)))) (t1:::Enil)
        else Eop (Oshlimm n) (e1:::Enil)
    | _ =>
        if shift_is_scale n
        then Eop (Olea (Ascaled (Int.unsigned (Int.shl Int.one n)) 0)) (e1:::Enil)
        else Eop (Oshlimm n) (e1:::Enil)
    end.
>>
*)

Inductive shlimm_cases: forall (e1: expr) , Type :=
  | shlimm_case1: forall n1, shlimm_cases (Eop (Ointconst n1) Enil)
  | shlimm_case2: forall n1 t1, shlimm_cases (Eop (Oshlimm n1) (t1:::Enil))
  | shlimm_case3: forall n1 t1, shlimm_cases (Eop (Olea (Aindexed n1)) (t1:::Enil))
  | shlimm_default: forall (e1: expr) , shlimm_cases e1.

Definition shlimm_match (e1: expr)  :=
  match e1 as zz1 return shlimm_cases zz1 with
  | Eop (Ointconst n1) Enil => shlimm_case1 n1
  | Eop (Oshlimm n1) (t1:::Enil) => shlimm_case2 n1 t1
  | Eop (Olea (Aindexed n1)) (t1:::Enil) => shlimm_case3 n1 t1
  | e1 => shlimm_default e1
  end.

Definition shlimm (e1: expr) (n: int) :=
 if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int.iwordsize) then Eop Oshl (e1:::Eop (Ointconst n) Enil:::Enil) else match shlimm_match e1 with
  | shlimm_case1 n1 => (* Eop (Ointconst n1) Enil *) 
      Eop (Ointconst(Int.shl n1 n)) Enil
  | shlimm_case2 n1 t1 => (* Eop (Oshlimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshlimm (Int.add n n1)) (t1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  | shlimm_case3 n1 t1 => (* Eop (Olea (Aindexed n1)) (t1:::Enil) *) 
      if shift_is_scale n then Eop (Olea (Ascaled (Int.unsigned (Int.shl Int.one n)) (Int.unsigned (Int.shl (Int.repr n1) n)))) (t1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  | shlimm_default e1 =>
      if shift_is_scale n then Eop (Olea (Ascaled (Int.unsigned (Int.shl Int.one n)) 0)) (e1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shruimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  if negb (Int.ltu n Int.iwordsize) then
    Eop Oshru (e1:::Eop (Ointconst n) Enil:::Enil)
  else
    match e1 with
    | Eop (Ointconst n1) Enil =>
        Eop (Ointconst(Int.shru n1 n)) Enil
    | Eop (Oshruimm n1) (t1:::Enil) =>
        if Int.ltu (Int.add n n1) Int.iwordsize
        then Eop (Oshruimm (Int.add n n1)) (t1:::Enil)
        else Eop (Oshruimm n) (e1:::Enil)
    | _ =>
        Eop (Oshruimm n) (e1:::Enil)
    end.
>>
*)

Inductive shruimm_cases: forall (e1: expr) , Type :=
  | shruimm_case1: forall n1, shruimm_cases (Eop (Ointconst n1) Enil)
  | shruimm_case2: forall n1 t1, shruimm_cases (Eop (Oshruimm n1) (t1:::Enil))
  | shruimm_default: forall (e1: expr) , shruimm_cases e1.

Definition shruimm_match (e1: expr)  :=
  match e1 as zz1 return shruimm_cases zz1 with
  | Eop (Ointconst n1) Enil => shruimm_case1 n1
  | Eop (Oshruimm n1) (t1:::Enil) => shruimm_case2 n1 t1
  | e1 => shruimm_default e1
  end.

Definition shruimm (e1: expr) (n: int) :=
 if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int.iwordsize) then Eop Oshru (e1:::Eop (Ointconst n) Enil:::Enil) else match shruimm_match e1 with
  | shruimm_case1 n1 => (* Eop (Ointconst n1) Enil *) 
      Eop (Ointconst(Int.shru n1 n)) Enil
  | shruimm_case2 n1 t1 => (* Eop (Oshruimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshruimm (Int.add n n1)) (t1:::Enil) else Eop (Oshruimm n) (e1:::Enil)
  | shruimm_default e1 =>
      Eop (Oshruimm n) (e1:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shrimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  if negb (Int.ltu n Int.iwordsize) then
    Eop Oshr (e1:::Eop (Ointconst n) Enil:::Enil)
  else
  match e1 with
  | Eop (Ointconst n1) Enil =>
      Eop (Ointconst(Int.shr n1 n)) Enil
  | Eop (Oshrimm n1) (t1:::Enil) =>
      if Int.ltu (Int.add n n1) Int.iwordsize
      then Eop (Oshrimm (Int.add n n1)) (t1:::Enil)
      else Eop (Oshrimm n) (e1:::Enil)
  | _ =>
      Eop (Oshrimm n) (e1:::Enil)
  end.
>>
*)

Inductive shrimm_cases: forall (e1: expr) , Type :=
  | shrimm_case1: forall n1, shrimm_cases (Eop (Ointconst n1) Enil)
  | shrimm_case2: forall n1 t1, shrimm_cases (Eop (Oshrimm n1) (t1:::Enil))
  | shrimm_default: forall (e1: expr) , shrimm_cases e1.

Definition shrimm_match (e1: expr)  :=
  match e1 as zz1 return shrimm_cases zz1 with
  | Eop (Ointconst n1) Enil => shrimm_case1 n1
  | Eop (Oshrimm n1) (t1:::Enil) => shrimm_case2 n1 t1
  | e1 => shrimm_default e1
  end.

Definition shrimm (e1: expr) (n: int) :=
 if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int.iwordsize) then Eop Oshr (e1:::Eop (Ointconst n) Enil:::Enil) else match shrimm_match e1 with
  | shrimm_case1 n1 => (* Eop (Ointconst n1) Enil *) 
      Eop (Ointconst(Int.shr n1 n)) Enil
  | shrimm_case2 n1 t1 => (* Eop (Oshrimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshrimm (Int.add n n1)) (t1:::Enil) else Eop (Oshrimm n) (e1:::Enil)
  | shrimm_default e1 =>
      Eop (Oshrimm n) (e1:::Enil)
  end.


(** ** Integer multiply *)

Definition mulimm_base (n1: int) (e2: expr) :=
  match Int.one_bits n1 with
  | i :: nil =>
      shlimm e2 i
  | i :: j :: nil =>
      Elet e2 (add (shlimm (Eletvar 0) i) (shlimm (Eletvar 0) j))
  | _ =>
      Eop (Omulimm n1) (e2:::Enil)
  end.

(** Original definition:
<<
Nondetfunction mulimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.one then e2
  else match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst(Int.mul n1 n2)) Enil
  | Eop (Olea (Aindexed n2)) (t2:::Enil) => addimm (Int.mul n1 (Int.repr n2)) (mulimm_base n1 t2)
  | _ => mulimm_base n1 e2
  end.
>>
*)

Inductive mulimm_cases: forall (e2: expr), Type :=
  | mulimm_case1: forall n2, mulimm_cases (Eop (Ointconst n2) Enil)
  | mulimm_case2: forall n2 t2, mulimm_cases (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | mulimm_default: forall (e2: expr), mulimm_cases e2.

Definition mulimm_match (e2: expr) :=
  match e2 as zz1 return mulimm_cases zz1 with
  | Eop (Ointconst n2) Enil => mulimm_case1 n2
  | Eop (Olea (Aindexed n2)) (t2:::Enil) => mulimm_case2 n2 t2
  | e2 => mulimm_default e2
  end.

Definition mulimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil else if Int.eq n1 Int.one then e2 else match mulimm_match e2 with
  | mulimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst(Int.mul n1 n2)) Enil
  | mulimm_case2 n2 t2 => (* Eop (Olea (Aindexed n2)) (t2:::Enil) *) 
      addimm (Int.mul n1 (Int.repr n2)) (mulimm_base n1 t2)
  | mulimm_default e2 =>
      mulimm_base n1 e2
  end.


(** Original definition:
<<
Nondetfunction mul (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => mulimm n1 t2
  | t1, Eop (Ointconst n2) Enil => mulimm n2 t1
  | _, _ => Eop Omul (e1:::e2:::Enil)
  end.
>>
*)

Inductive mul_cases: forall (e1: expr) (e2: expr), Type :=
  | mul_case1: forall n1 t2, mul_cases (Eop (Ointconst n1) Enil) (t2)
  | mul_case2: forall t1 n2, mul_cases (t1) (Eop (Ointconst n2) Enil)
  | mul_default: forall (e1: expr) (e2: expr), mul_cases e1 e2.

Definition mul_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return mul_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => mul_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => mul_case2 t1 n2
  | e1, e2 => mul_default e1 e2
  end.

Definition mul (e1: expr) (e2: expr) :=
  match mul_match e1 e2 with
  | mul_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      mulimm n1 t2
  | mul_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      mulimm n2 t1
  | mul_default e1 e2 =>
      Eop Omul (e1:::e2:::Enil)
  end.


Definition mulhs (e1: expr) (e2: expr) := Eop Omulhs (e1 ::: e2 ::: Enil).
Definition mulhu (e1: expr) (e2: expr) := Eop Omulhu (e1 ::: e2 ::: Enil).

(** ** Bitwise and, or, xor *)

(** Original definition:
<<
Nondetfunction andimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.mone then e2
  else match e2 with
  | Eop (Ointconst n2) Enil =>
      Eop (Ointconst (Int.and n1 n2)) Enil
  | Eop (Oandimm n2) (t2:::Enil) =>
     Eop (Oandimm (Int.and n1 n2)) (t2:::Enil)
  | Eop Ocast8unsigned (t2:::Enil) =>
     Eop (Oandimm (Int.and n1 (Int.repr 255))) (t2:::Enil)
  | Eop Ocast16unsigned (t2:::Enil) =>
     Eop (Oandimm (Int.and n1 (Int.repr 65535))) (t2:::Enil)
  | _ =>
     Eop (Oandimm n1) (e2:::Enil)
  end.
>>
*)

Inductive andimm_cases: forall (e2: expr), Type :=
  | andimm_case1: forall n2, andimm_cases (Eop (Ointconst n2) Enil)
  | andimm_case2: forall n2 t2, andimm_cases (Eop (Oandimm n2) (t2:::Enil))
  | andimm_case3: forall t2, andimm_cases (Eop Ocast8unsigned (t2:::Enil))
  | andimm_case4: forall t2, andimm_cases (Eop Ocast16unsigned (t2:::Enil))
  | andimm_default: forall (e2: expr), andimm_cases e2.

Definition andimm_match (e2: expr) :=
  match e2 as zz1 return andimm_cases zz1 with
  | Eop (Ointconst n2) Enil => andimm_case1 n2
  | Eop (Oandimm n2) (t2:::Enil) => andimm_case2 n2 t2
  | Eop Ocast8unsigned (t2:::Enil) => andimm_case3 t2
  | Eop Ocast16unsigned (t2:::Enil) => andimm_case4 t2
  | e2 => andimm_default e2
  end.

Definition andimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil else if Int.eq n1 Int.mone then e2 else match andimm_match e2 with
  | andimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.and n1 n2)) Enil
  | andimm_case2 n2 t2 => (* Eop (Oandimm n2) (t2:::Enil) *) 
      Eop (Oandimm (Int.and n1 n2)) (t2:::Enil)
  | andimm_case3 t2 => (* Eop Ocast8unsigned (t2:::Enil) *) 
      Eop (Oandimm (Int.and n1 (Int.repr 255))) (t2:::Enil)
  | andimm_case4 t2 => (* Eop Ocast16unsigned (t2:::Enil) *) 
      Eop (Oandimm (Int.and n1 (Int.repr 65535))) (t2:::Enil)
  | andimm_default e2 =>
      Eop (Oandimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction and (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => andimm n1 t2
  | t1, Eop (Ointconst n2) Enil => andimm n2 t1
  | _, _ => Eop Oand (e1:::e2:::Enil)
  end.
>>
*)

Inductive and_cases: forall (e1: expr) (e2: expr), Type :=
  | and_case1: forall n1 t2, and_cases (Eop (Ointconst n1) Enil) (t2)
  | and_case2: forall t1 n2, and_cases (t1) (Eop (Ointconst n2) Enil)
  | and_default: forall (e1: expr) (e2: expr), and_cases e1 e2.

Definition and_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return and_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => and_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => and_case2 t1 n2
  | e1, e2 => and_default e1 e2
  end.

Definition and (e1: expr) (e2: expr) :=
  match and_match e1 e2 with
  | and_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      andimm n1 t2
  | and_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      andimm n2 t1
  | and_default e1 e2 =>
      Eop Oand (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction orimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then e2
  else if Int.eq n1 Int.mone then Eop (Ointconst Int.mone) Enil
  else match e2 with
  | Eop (Ointconst n2) Enil =>
      Eop (Ointconst (Int.or n1 n2)) Enil
  | Eop (Oorimm n2) (t2:::Enil) =>
     Eop (Oorimm (Int.or n1 n2)) (t2:::Enil)
  | _ =>
     Eop (Oorimm n1) (e2:::Enil)
  end.
>>
*)

Inductive orimm_cases: forall (e2: expr), Type :=
  | orimm_case1: forall n2, orimm_cases (Eop (Ointconst n2) Enil)
  | orimm_case2: forall n2 t2, orimm_cases (Eop (Oorimm n2) (t2:::Enil))
  | orimm_default: forall (e2: expr), orimm_cases e2.

Definition orimm_match (e2: expr) :=
  match e2 as zz1 return orimm_cases zz1 with
  | Eop (Ointconst n2) Enil => orimm_case1 n2
  | Eop (Oorimm n2) (t2:::Enil) => orimm_case2 n2 t2
  | e2 => orimm_default e2
  end.

Definition orimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then e2 else if Int.eq n1 Int.mone then Eop (Ointconst Int.mone) Enil else match orimm_match e2 with
  | orimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.or n1 n2)) Enil
  | orimm_case2 n2 t2 => (* Eop (Oorimm n2) (t2:::Enil) *) 
      Eop (Oorimm (Int.or n1 n2)) (t2:::Enil)
  | orimm_default e2 =>
      Eop (Oorimm n1) (e2:::Enil)
  end.


Definition same_expr_pure (e1 e2: expr) :=
  match e1, e2 with
  | Evar v1, Evar v2 => if ident_eq v1 v2 then true else false
  | _, _ => false
  end.

(** Original definition:
<<
Nondetfunction or (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => orimm n1 t2
  | t1, Eop (Ointconst n2) Enil => orimm n2 t1
  | Eop (Oshlimm n1) (t1:::Enil), Eop (Oshruimm n2) (t2:::Enil) =>
      if Int.eq (Int.add n1 n2) Int.iwordsize then
        if same_expr_pure t1 t2
        then Eop (Ororimm n2) (t1:::Enil)
        else Eop (Oshldimm n1) (t1:::t2:::Enil)
      else Eop Oor (e1:::e2:::Enil)
  | Eop (Oshruimm n2) (t2:::Enil), Eop (Oshlimm n1) (t1:::Enil) =>
      if Int.eq (Int.add n1 n2) Int.iwordsize then
        if same_expr_pure t1 t2
        then Eop (Ororimm n2) (t1:::Enil)
        else Eop (Oshldimm n1) (t1:::t2:::Enil)
      else Eop Oor (e1:::e2:::Enil)
  | _, _ =>
      Eop Oor (e1:::e2:::Enil)
  end.
>>
*)

Inductive or_cases: forall (e1: expr) (e2: expr), Type :=
  | or_case1: forall n1 t2, or_cases (Eop (Ointconst n1) Enil) (t2)
  | or_case2: forall t1 n2, or_cases (t1) (Eop (Ointconst n2) Enil)
  | or_case3: forall n1 t1 n2 t2, or_cases (Eop (Oshlimm n1) (t1:::Enil)) (Eop (Oshruimm n2) (t2:::Enil))
  | or_case4: forall n2 t2 n1 t1, or_cases (Eop (Oshruimm n2) (t2:::Enil)) (Eop (Oshlimm n1) (t1:::Enil))
  | or_default: forall (e1: expr) (e2: expr), or_cases e1 e2.

Definition or_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return or_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => or_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => or_case2 t1 n2
  | Eop (Oshlimm n1) (t1:::Enil), Eop (Oshruimm n2) (t2:::Enil) => or_case3 n1 t1 n2 t2
  | Eop (Oshruimm n2) (t2:::Enil), Eop (Oshlimm n1) (t1:::Enil) => or_case4 n2 t2 n1 t1
  | e1, e2 => or_default e1 e2
  end.

Definition or (e1: expr) (e2: expr) :=
  match or_match e1 e2 with
  | or_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      orimm n1 t2
  | or_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      orimm n2 t1
  | or_case3 n1 t1 n2 t2 => (* Eop (Oshlimm n1) (t1:::Enil), Eop (Oshruimm n2) (t2:::Enil) *) 
      if Int.eq (Int.add n1 n2) Int.iwordsize then if same_expr_pure t1 t2 then Eop (Ororimm n2) (t1:::Enil) else Eop (Oshldimm n1) (t1:::t2:::Enil) else Eop Oor (e1:::e2:::Enil)
  | or_case4 n2 t2 n1 t1 => (* Eop (Oshruimm n2) (t2:::Enil), Eop (Oshlimm n1) (t1:::Enil) *) 
      if Int.eq (Int.add n1 n2) Int.iwordsize then if same_expr_pure t1 t2 then Eop (Ororimm n2) (t1:::Enil) else Eop (Oshldimm n1) (t1:::t2:::Enil) else Eop Oor (e1:::e2:::Enil)
  | or_default e1 e2 =>
      Eop Oor (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction xorimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then e2
  else match e2 with
  | Eop (Ointconst n2) Enil =>
      Eop (Ointconst (Int.xor n1 n2)) Enil
  | Eop (Oxorimm n2) (t2:::Enil) =>
     Eop (Oxorimm (Int.xor n1 n2)) (t2:::Enil)
  | Eop Onot (t2:::Enil) =>
     Eop (Oxorimm (Int.not n1)) (t2:::Enil)
  | _ =>
     Eop (Oxorimm n1) (e2:::Enil)
  end.
>>
*)

Inductive xorimm_cases: forall (e2: expr), Type :=
  | xorimm_case1: forall n2, xorimm_cases (Eop (Ointconst n2) Enil)
  | xorimm_case2: forall n2 t2, xorimm_cases (Eop (Oxorimm n2) (t2:::Enil))
  | xorimm_case3: forall t2, xorimm_cases (Eop Onot (t2:::Enil))
  | xorimm_default: forall (e2: expr), xorimm_cases e2.

Definition xorimm_match (e2: expr) :=
  match e2 as zz1 return xorimm_cases zz1 with
  | Eop (Ointconst n2) Enil => xorimm_case1 n2
  | Eop (Oxorimm n2) (t2:::Enil) => xorimm_case2 n2 t2
  | Eop Onot (t2:::Enil) => xorimm_case3 t2
  | e2 => xorimm_default e2
  end.

Definition xorimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then e2 else match xorimm_match e2 with
  | xorimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.xor n1 n2)) Enil
  | xorimm_case2 n2 t2 => (* Eop (Oxorimm n2) (t2:::Enil) *) 
      Eop (Oxorimm (Int.xor n1 n2)) (t2:::Enil)
  | xorimm_case3 t2 => (* Eop Onot (t2:::Enil) *) 
      Eop (Oxorimm (Int.not n1)) (t2:::Enil)
  | xorimm_default e2 =>
      Eop (Oxorimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction xor (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => xorimm n1 t2
  | t1, Eop (Ointconst n2) Enil => xorimm n2 t1
  | _, _ => Eop Oxor (e1:::e2:::Enil)
  end.
>>
*)

Inductive xor_cases: forall (e1: expr) (e2: expr), Type :=
  | xor_case1: forall n1 t2, xor_cases (Eop (Ointconst n1) Enil) (t2)
  | xor_case2: forall t1 n2, xor_cases (t1) (Eop (Ointconst n2) Enil)
  | xor_default: forall (e1: expr) (e2: expr), xor_cases e1 e2.

Definition xor_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return xor_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => xor_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => xor_case2 t1 n2
  | e1, e2 => xor_default e1 e2
  end.

Definition xor (e1: expr) (e2: expr) :=
  match xor_match e1 e2 with
  | xor_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      xorimm n1 t2
  | xor_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      xorimm n2 t1
  | xor_default e1 e2 =>
      Eop Oxor (e1:::e2:::Enil)
  end.


(** ** Integer division and modulus *)

Definition divu_base (e1: expr) (e2: expr) := Eop Odivu (e1:::e2:::Enil).
Definition modu_base (e1: expr) (e2: expr) := Eop Omodu (e1:::e2:::Enil).
Definition divs_base (e1: expr) (e2: expr) := Eop Odiv (e1:::e2:::Enil).
Definition mods_base (e1: expr) (e2: expr) := Eop Omod (e1:::e2:::Enil).

Definition shrximm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then e1 else Eop (Oshrximm n2) (e1:::Enil).

(** ** General shifts *)

(** Original definition:
<<
Nondetfunction shl (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shlimm e1 n2
  | _ => Eop Oshl (e1:::e2:::Enil)
  end.
>>
*)

Inductive shl_cases: forall (e2: expr), Type :=
  | shl_case1: forall n2, shl_cases (Eop (Ointconst n2) Enil)
  | shl_default: forall (e2: expr), shl_cases e2.

Definition shl_match (e2: expr) :=
  match e2 as zz1 return shl_cases zz1 with
  | Eop (Ointconst n2) Enil => shl_case1 n2
  | e2 => shl_default e2
  end.

Definition shl (e1: expr) (e2: expr) :=
  match shl_match e2 with
  | shl_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shlimm e1 n2
  | shl_default e2 =>
      Eop Oshl (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shr (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shrimm e1 n2
  | _ => Eop Oshr (e1:::e2:::Enil)
  end.
>>
*)

Inductive shr_cases: forall (e2: expr), Type :=
  | shr_case1: forall n2, shr_cases (Eop (Ointconst n2) Enil)
  | shr_default: forall (e2: expr), shr_cases e2.

Definition shr_match (e2: expr) :=
  match e2 as zz1 return shr_cases zz1 with
  | Eop (Ointconst n2) Enil => shr_case1 n2
  | e2 => shr_default e2
  end.

Definition shr (e1: expr) (e2: expr) :=
  match shr_match e2 with
  | shr_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shrimm e1 n2
  | shr_default e2 =>
      Eop Oshr (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shru (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shruimm e1 n2
  | _ => Eop Oshru (e1:::e2:::Enil)
  end.
>>
*)

Inductive shru_cases: forall (e2: expr), Type :=
  | shru_case1: forall n2, shru_cases (Eop (Ointconst n2) Enil)
  | shru_default: forall (e2: expr), shru_cases e2.

Definition shru_match (e2: expr) :=
  match e2 as zz1 return shru_cases zz1 with
  | Eop (Ointconst n2) Enil => shru_case1 n2
  | e2 => shru_default e2
  end.

Definition shru (e1: expr) (e2: expr) :=
  match shru_match e2 with
  | shru_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shruimm e1 n2
  | shru_default e2 =>
      Eop Oshru (e1:::e2:::Enil)
  end.


(** ** Floating-point arithmetic *)

Definition negf (e: expr) :=  Eop Onegf (e ::: Enil).
Definition absf (e: expr) :=  Eop Oabsf (e ::: Enil).
Definition addf (e1 e2: expr) :=  Eop Oaddf (e1 ::: e2 ::: Enil).
Definition subf (e1 e2: expr) :=  Eop Osubf (e1 ::: e2 ::: Enil).
Definition mulf (e1 e2: expr) :=  Eop Omulf (e1 ::: e2 ::: Enil).

Definition negfs (e: expr) :=  Eop Onegfs (e ::: Enil).
Definition absfs (e: expr) :=  Eop Oabsfs (e ::: Enil).
Definition addfs (e1 e2: expr) :=  Eop Oaddfs (e1 ::: e2 ::: Enil).
Definition subfs (e1 e2: expr) :=  Eop Osubfs (e1 ::: e2 ::: Enil).
Definition mulfs (e1 e2: expr) :=  Eop Omulfs (e1 ::: e2 ::: Enil).

(** ** Comparisons *)

(** Original definition:
<<
Nondetfunction compimm (default: comparison -> int -> condition)
                       (sem: comparison -> int -> int -> bool)
                       (c: comparison) (e1: expr) (n2: int) :=
  match c, e1 with
  | c, Eop (Ointconst n1) Enil =>
      Eop (Ointconst (if sem c n1 n2 then Int.one else Int.zero)) Enil
  | Ceq, Eop (Ocmp c) el =>
      if Int.eq_dec n2 Int.zero then
        Eop (Ocmp (negate_condition c)) el
      else if Int.eq_dec n2 Int.one then
        Eop (Ocmp c) el
      else
        Eop (Ointconst Int.zero) Enil
  | Cne, Eop (Ocmp c) el =>
      if Int.eq_dec n2 Int.zero then
        Eop (Ocmp c) el
      else if Int.eq_dec n2 Int.one then
        Eop (Ocmp (negate_condition c)) el
      else
        Eop (Ointconst Int.one) Enil
  | Ceq, Eop (Oandimm n1) (t1 ::: Enil) =>
      if Int.eq_dec n2 Int.zero then
        Eop (Ocmp (Cmaskzero n1)) (t1 ::: Enil)
      else
        Eop (Ocmp (default c n2)) (e1 ::: Enil)
  | Cne, Eop (Oandimm n1) (t1 ::: Enil) =>
      if Int.eq_dec n2 Int.zero then
        Eop (Ocmp (Cmasknotzero n1)) (t1 ::: Enil)
      else
        Eop (Ocmp (default c n2)) (e1 ::: Enil)
  | _, _ =>
       Eop (Ocmp (default c n2)) (e1 ::: Enil)
  end.
>>
*)

Inductive compimm_cases: forall (c: comparison) (e1: expr) , Type :=
  | compimm_case1: forall c n1, compimm_cases (c) (Eop (Ointconst n1) Enil)
  | compimm_case2: forall c el, compimm_cases (Ceq) (Eop (Ocmp c) el)
  | compimm_case3: forall c el, compimm_cases (Cne) (Eop (Ocmp c) el)
  | compimm_case4: forall n1 t1, compimm_cases (Ceq) (Eop (Oandimm n1) (t1 ::: Enil))
  | compimm_case5: forall n1 t1, compimm_cases (Cne) (Eop (Oandimm n1) (t1 ::: Enil))
  | compimm_default: forall (c: comparison) (e1: expr) , compimm_cases c e1.

Definition compimm_match (c: comparison) (e1: expr)  :=
  match c as zz1, e1 as zz2 return compimm_cases zz1 zz2 with
  | c, Eop (Ointconst n1) Enil => compimm_case1 c n1
  | Ceq, Eop (Ocmp c) el => compimm_case2 c el
  | Cne, Eop (Ocmp c) el => compimm_case3 c el
  | Ceq, Eop (Oandimm n1) (t1 ::: Enil) => compimm_case4 n1 t1
  | Cne, Eop (Oandimm n1) (t1 ::: Enil) => compimm_case5 n1 t1
  | c, e1 => compimm_default c e1
  end.

Definition compimm (default: comparison -> int -> condition) (sem: comparison -> int -> int -> bool) (c: comparison) (e1: expr) (n2: int) :=
  match compimm_match c e1 with
  | compimm_case1 c n1 => (* c, Eop (Ointconst n1) Enil *) 
      Eop (Ointconst (if sem c n1 n2 then Int.one else Int.zero)) Enil
  | compimm_case2 c el => (* Ceq, Eop (Ocmp c) el *) 
      if Int.eq_dec n2 Int.zero then Eop (Ocmp (negate_condition c)) el else if Int.eq_dec n2 Int.one then Eop (Ocmp c) el else Eop (Ointconst Int.zero) Enil
  | compimm_case3 c el => (* Cne, Eop (Ocmp c) el *) 
      if Int.eq_dec n2 Int.zero then Eop (Ocmp c) el else if Int.eq_dec n2 Int.one then Eop (Ocmp (negate_condition c)) el else Eop (Ointconst Int.one) Enil
  | compimm_case4 n1 t1 => (* Ceq, Eop (Oandimm n1) (t1 ::: Enil) *) 
      if Int.eq_dec n2 Int.zero then Eop (Ocmp (Cmaskzero n1)) (t1 ::: Enil) else Eop (Ocmp (default c n2)) (e1 ::: Enil)
  | compimm_case5 n1 t1 => (* Cne, Eop (Oandimm n1) (t1 ::: Enil) *) 
      if Int.eq_dec n2 Int.zero then Eop (Ocmp (Cmasknotzero n1)) (t1 ::: Enil) else Eop (Ocmp (default c n2)) (e1 ::: Enil)
  | compimm_default c e1 =>
      Eop (Ocmp (default c n2)) (e1 ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction comp (c: comparison) (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      compimm Ccompimm Int.cmp (swap_comparison c) t2 n1
  | t1, Eop (Ointconst n2) Enil =>
      compimm Ccompimm Int.cmp c t1 n2
  | _, _ =>
      Eop (Ocmp (Ccomp c)) (e1 ::: e2 ::: Enil)
  end.
>>
*)

Inductive comp_cases: forall (e1: expr) (e2: expr), Type :=
  | comp_case1: forall n1 t2, comp_cases (Eop (Ointconst n1) Enil) (t2)
  | comp_case2: forall t1 n2, comp_cases (t1) (Eop (Ointconst n2) Enil)
  | comp_default: forall (e1: expr) (e2: expr), comp_cases e1 e2.

Definition comp_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return comp_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => comp_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => comp_case2 t1 n2
  | e1, e2 => comp_default e1 e2
  end.

Definition comp (c: comparison) (e1: expr) (e2: expr) :=
  match comp_match e1 e2 with
  | comp_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      compimm Ccompimm Int.cmp (swap_comparison c) t2 n1
  | comp_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      compimm Ccompimm Int.cmp c t1 n2
  | comp_default e1 e2 =>
      Eop (Ocmp (Ccomp c)) (e1 ::: e2 ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction compu (c: comparison) (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      compimm Ccompuimm Int.cmpu (swap_comparison c) t2 n1
  | t1, Eop (Ointconst n2) Enil =>
      compimm Ccompuimm Int.cmpu c t1 n2
  | _, _ =>
      Eop (Ocmp (Ccompu c)) (e1 ::: e2 ::: Enil)
  end.
>>
*)

Inductive compu_cases: forall (e1: expr) (e2: expr), Type :=
  | compu_case1: forall n1 t2, compu_cases (Eop (Ointconst n1) Enil) (t2)
  | compu_case2: forall t1 n2, compu_cases (t1) (Eop (Ointconst n2) Enil)
  | compu_default: forall (e1: expr) (e2: expr), compu_cases e1 e2.

Definition compu_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return compu_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => compu_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => compu_case2 t1 n2
  | e1, e2 => compu_default e1 e2
  end.

Definition compu (c: comparison) (e1: expr) (e2: expr) :=
  match compu_match e1 e2 with
  | compu_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      compimm Ccompuimm Int.cmpu (swap_comparison c) t2 n1
  | compu_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      compimm Ccompuimm Int.cmpu c t1 n2
  | compu_default e1 e2 =>
      Eop (Ocmp (Ccompu c)) (e1 ::: e2 ::: Enil)
  end.


Definition compf (c: comparison) (e1: expr) (e2: expr) :=
  Eop (Ocmp (Ccompf c)) (e1 ::: e2 ::: Enil).

Definition compfs (c: comparison) (e1: expr) (e2: expr) :=
  Eop (Ocmp (Ccompfs c)) (e1 ::: e2 ::: Enil).

(** ** Integer conversions *)

(** Original definition:
<<
Nondetfunction cast8unsigned (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil =>
      Eop (Ointconst (Int.zero_ext 8 n)) Enil
  | Eop (Oandimm n) (t:::Enil) =>
      andimm (Int.and (Int.repr 255) n) t
  | _ =>
      Eop Ocast8unsigned (e:::Enil)
  end.
>>
*)

Inductive cast8unsigned_cases: forall (e: expr), Type :=
  | cast8unsigned_case1: forall n, cast8unsigned_cases (Eop (Ointconst n) Enil)
  | cast8unsigned_case2: forall n t, cast8unsigned_cases (Eop (Oandimm n) (t:::Enil))
  | cast8unsigned_default: forall (e: expr), cast8unsigned_cases e.

Definition cast8unsigned_match (e: expr) :=
  match e as zz1 return cast8unsigned_cases zz1 with
  | Eop (Ointconst n) Enil => cast8unsigned_case1 n
  | Eop (Oandimm n) (t:::Enil) => cast8unsigned_case2 n t
  | e => cast8unsigned_default e
  end.

Definition cast8unsigned (e: expr) :=
  match cast8unsigned_match e with
  | cast8unsigned_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.zero_ext 8 n)) Enil
  | cast8unsigned_case2 n t => (* Eop (Oandimm n) (t:::Enil) *) 
      andimm (Int.and (Int.repr 255) n) t
  | cast8unsigned_default e =>
      Eop Ocast8unsigned (e:::Enil)
  end.


(** Original definition:
<<
Nondetfunction cast8signed (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil =>
      Eop (Ointconst (Int.sign_ext 8 n)) Enil
  | _ =>
      Eop Ocast8signed (e ::: Enil)
  end.
>>
*)

Inductive cast8signed_cases: forall (e: expr), Type :=
  | cast8signed_case1: forall n, cast8signed_cases (Eop (Ointconst n) Enil)
  | cast8signed_default: forall (e: expr), cast8signed_cases e.

Definition cast8signed_match (e: expr) :=
  match e as zz1 return cast8signed_cases zz1 with
  | Eop (Ointconst n) Enil => cast8signed_case1 n
  | e => cast8signed_default e
  end.

Definition cast8signed (e: expr) :=
  match cast8signed_match e with
  | cast8signed_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.sign_ext 8 n)) Enil
  | cast8signed_default e =>
      Eop Ocast8signed (e ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction cast16unsigned (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil =>
      Eop (Ointconst (Int.zero_ext 16 n)) Enil
  | Eop (Oandimm n) (t:::Enil) =>
      andimm (Int.and (Int.repr 65535) n) t
  | _ =>
      Eop Ocast16unsigned (e:::Enil)
  end.
>>
*)

Inductive cast16unsigned_cases: forall (e: expr), Type :=
  | cast16unsigned_case1: forall n, cast16unsigned_cases (Eop (Ointconst n) Enil)
  | cast16unsigned_case2: forall n t, cast16unsigned_cases (Eop (Oandimm n) (t:::Enil))
  | cast16unsigned_default: forall (e: expr), cast16unsigned_cases e.

Definition cast16unsigned_match (e: expr) :=
  match e as zz1 return cast16unsigned_cases zz1 with
  | Eop (Ointconst n) Enil => cast16unsigned_case1 n
  | Eop (Oandimm n) (t:::Enil) => cast16unsigned_case2 n t
  | e => cast16unsigned_default e
  end.

Definition cast16unsigned (e: expr) :=
  match cast16unsigned_match e with
  | cast16unsigned_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.zero_ext 16 n)) Enil
  | cast16unsigned_case2 n t => (* Eop (Oandimm n) (t:::Enil) *) 
      andimm (Int.and (Int.repr 65535) n) t
  | cast16unsigned_default e =>
      Eop Ocast16unsigned (e:::Enil)
  end.


(** Original definition:
<<
Nondetfunction cast16signed (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil =>
      Eop (Ointconst (Int.sign_ext 16 n)) Enil
  | _ =>
      Eop Ocast16signed (e ::: Enil)
  end.
>>
*)

Inductive cast16signed_cases: forall (e: expr), Type :=
  | cast16signed_case1: forall n, cast16signed_cases (Eop (Ointconst n) Enil)
  | cast16signed_default: forall (e: expr), cast16signed_cases e.

Definition cast16signed_match (e: expr) :=
  match e as zz1 return cast16signed_cases zz1 with
  | Eop (Ointconst n) Enil => cast16signed_case1 n
  | e => cast16signed_default e
  end.

Definition cast16signed (e: expr) :=
  match cast16signed_match e with
  | cast16signed_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.sign_ext 16 n)) Enil
  | cast16signed_default e =>
      Eop Ocast16signed (e ::: Enil)
  end.


(** Floating-point conversions *)

Definition singleoffloat (e: expr) := Eop Osingleoffloat (e ::: Enil).
Definition floatofsingle (e: expr) := Eop Ofloatofsingle (e ::: Enil).

Definition intoffloat (e: expr) := Eop Ointoffloat (e ::: Enil).

(** Original definition:
<<
Nondetfunction floatofint (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ofloatconst (Float.of_int n)) Enil
  | _ => Eop Ofloatofint (e ::: Enil)
  end.
>>
*)

Inductive floatofint_cases: forall (e: expr), Type :=
  | floatofint_case1: forall n, floatofint_cases (Eop (Ointconst n) Enil)
  | floatofint_default: forall (e: expr), floatofint_cases e.

Definition floatofint_match (e: expr) :=
  match e as zz1 return floatofint_cases zz1 with
  | Eop (Ointconst n) Enil => floatofint_case1 n
  | e => floatofint_default e
  end.

Definition floatofint (e: expr) :=
  match floatofint_match e with
  | floatofint_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ofloatconst (Float.of_int n)) Enil
  | floatofint_default e =>
      Eop Ofloatofint (e ::: Enil)
  end.


Definition intuoffloat (e: expr) :=
  Elet e
    (Elet (Eop (Ofloatconst (Float.of_intu Float.ox8000_0000)) Enil)
      (Econdition (CEcond (Ccompf Clt) (Eletvar 1 ::: Eletvar 0 ::: Enil))
        (intoffloat (Eletvar 1))
        (addimm Float.ox8000_0000 (intoffloat (subf (Eletvar 1) (Eletvar 0))))))%nat.

(** Original definition:
<<
Nondetfunction floatofintu (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ofloatconst (Float.of_intu n)) Enil
  | _ =>
    let f := Eop (Ofloatconst (Float.of_intu Float.ox8000_0000)) Enil in
    Elet e
      (Econdition (CEcond (Ccompuimm Clt Float.ox8000_0000) (Eletvar O ::: Enil))
        (floatofint (Eletvar O))
        (addf (floatofint (addimm (Int.neg Float.ox8000_0000) (Eletvar O))) f))
  end.
>>
*)

Inductive floatofintu_cases: forall (e: expr), Type :=
  | floatofintu_case1: forall n, floatofintu_cases (Eop (Ointconst n) Enil)
  | floatofintu_default: forall (e: expr), floatofintu_cases e.

Definition floatofintu_match (e: expr) :=
  match e as zz1 return floatofintu_cases zz1 with
  | Eop (Ointconst n) Enil => floatofintu_case1 n
  | e => floatofintu_default e
  end.

Definition floatofintu (e: expr) :=
  match floatofintu_match e with
  | floatofintu_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ofloatconst (Float.of_intu n)) Enil
  | floatofintu_default e =>
      let f := Eop (Ofloatconst (Float.of_intu Float.ox8000_0000)) Enil in Elet e (Econdition (CEcond (Ccompuimm Clt Float.ox8000_0000) (Eletvar O ::: Enil)) (floatofint (Eletvar O)) (addf (floatofint (addimm (Int.neg Float.ox8000_0000) (Eletvar O))) f))
  end.


Definition intofsingle (e: expr) := Eop Ointofsingle (e ::: Enil).

(** Original definition:
<<
Nondetfunction singleofint (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Osingleconst (Float32.of_int n)) Enil
  | _ => Eop Osingleofint (e ::: Enil)
  end.
>>
*)

Inductive singleofint_cases: forall (e: expr), Type :=
  | singleofint_case1: forall n, singleofint_cases (Eop (Ointconst n) Enil)
  | singleofint_default: forall (e: expr), singleofint_cases e.

Definition singleofint_match (e: expr) :=
  match e as zz1 return singleofint_cases zz1 with
  | Eop (Ointconst n) Enil => singleofint_case1 n
  | e => singleofint_default e
  end.

Definition singleofint (e: expr) :=
  match singleofint_match e with
  | singleofint_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Osingleconst (Float32.of_int n)) Enil
  | singleofint_default e =>
      Eop Osingleofint (e ::: Enil)
  end.


Definition intuofsingle (e: expr) := intuoffloat (floatofsingle e).

(** Original definition:
<<
Nondetfunction singleofintu (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Osingleconst (Float32.of_intu n)) Enil
  | _ => singleoffloat (floatofintu e)
  end.
>>
*)

Inductive singleofintu_cases: forall (e: expr), Type :=
  | singleofintu_case1: forall n, singleofintu_cases (Eop (Ointconst n) Enil)
  | singleofintu_default: forall (e: expr), singleofintu_cases e.

Definition singleofintu_match (e: expr) :=
  match e as zz1 return singleofintu_cases zz1 with
  | Eop (Ointconst n) Enil => singleofintu_case1 n
  | e => singleofintu_default e
  end.

Definition singleofintu (e: expr) :=
  match singleofintu_match e with
  | singleofintu_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Osingleconst (Float32.of_intu n)) Enil
  | singleofintu_default e =>
      singleoffloat (floatofintu e)
  end.


(** ** Addressing modes *)

(** Original definition:
<<
Nondetfunction addressing (chunk: memory_chunk) (e: expr) :=
  match e with
  | Eop (Olea addr) args =>
      if (negb Archi.ptr64) && addressing_valid addr then (addr, args) else (Aindexed 0, e:::Enil)
  | Eop (Oleal addr) args =>
      if Archi.ptr64 && addressing_valid addr then (addr, args) else (Aindexed 0, e:::Enil)
  | _ => (Aindexed 0, e:::Enil)
  end.
>>
*)

Inductive addressing_cases: forall (e: expr), Type :=
  | addressing_case1: forall addr args, addressing_cases (Eop (Olea addr) args)
  | addressing_case2: forall addr args, addressing_cases (Eop (Oleal addr) args)
  | addressing_default: forall (e: expr), addressing_cases e.

Definition addressing_match (e: expr) :=
  match e as zz1 return addressing_cases zz1 with
  | Eop (Olea addr) args => addressing_case1 addr args
  | Eop (Oleal addr) args => addressing_case2 addr args
  | e => addressing_default e
  end.

Definition addressing (chunk: memory_chunk) (e: expr) :=
  match addressing_match e with
  | addressing_case1 addr args => (* Eop (Olea addr) args *) 
      if (negb Archi.ptr64) && addressing_valid addr then (addr, args) else (Aindexed 0, e:::Enil)
  | addressing_case2 addr args => (* Eop (Oleal addr) args *) 
      if Archi.ptr64 && addressing_valid addr then (addr, args) else (Aindexed 0, e:::Enil)
  | addressing_default e =>
      (Aindexed 0, e:::Enil)
  end.


(** ** Arguments of builtins *)

(** Original definition:
<<
Nondetfunction builtin_arg_addr (addr: Op.addressing) (el: exprlist) :=
  match addr, el with
  | Aindexed n, e1 ::: Enil =>
      BA_addptr (BA e1) (if Archi.ptr64 then BA_long (Int64.repr n) else BA_int (Int.repr n))
  | Aglobal id ofs, Enil => BA_addrglobal id ofs
  | Ainstack ofs, Enil => BA_addrstack ofs
  | _, _ => BA (Eop (Olea_ptr addr) el)
  end.
>>
*)

Inductive builtin_arg_addr_cases: forall (addr: Op.addressing) (el: exprlist), Type :=
  | builtin_arg_addr_case1: forall n e1, builtin_arg_addr_cases (Aindexed n) (e1 ::: Enil)
  | builtin_arg_addr_case2: forall id ofs, builtin_arg_addr_cases (Aglobal id ofs) (Enil)
  | builtin_arg_addr_case3: forall ofs, builtin_arg_addr_cases (Ainstack ofs) (Enil)
  | builtin_arg_addr_default: forall (addr: Op.addressing) (el: exprlist), builtin_arg_addr_cases addr el.

Definition builtin_arg_addr_match (addr: Op.addressing) (el: exprlist) :=
  match addr as zz1, el as zz2 return builtin_arg_addr_cases zz1 zz2 with
  | Aindexed n, e1 ::: Enil => builtin_arg_addr_case1 n e1
  | Aglobal id ofs, Enil => builtin_arg_addr_case2 id ofs
  | Ainstack ofs, Enil => builtin_arg_addr_case3 ofs
  | addr, el => builtin_arg_addr_default addr el
  end.

Definition builtin_arg_addr (addr: Op.addressing) (el: exprlist) :=
  match builtin_arg_addr_match addr el with
  | builtin_arg_addr_case1 n e1 => (* Aindexed n, e1 ::: Enil *) 
      BA_addptr (BA e1) (if Archi.ptr64 then BA_long (Int64.repr n) else BA_int (Int.repr n))
  | builtin_arg_addr_case2 id ofs => (* Aglobal id ofs, Enil *) 
      BA_addrglobal id ofs
  | builtin_arg_addr_case3 ofs => (* Ainstack ofs, Enil *) 
      BA_addrstack ofs
  | builtin_arg_addr_default addr el =>
      BA (Eop (Olea_ptr addr) el)
  end.


(** Original definition:
<<
Nondetfunction builtin_arg (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => BA_int n
  | Eop (Olongconst n) Enil => BA_long n
  | Eop (Olea addr) el =>
      if Archi.ptr64 then BA e else builtin_arg_addr addr el
  | Eop (Oleal addr) el =>
      if Archi.ptr64 then builtin_arg_addr addr el else BA e
  | Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) =>
        BA_long (Int64.ofwords h l)
  | Eop Omakelong (h ::: l ::: Enil) => BA_splitlong (BA h) (BA l)
  | Eload chunk (Aglobal id ofs) Enil => BA_loadglobal chunk id ofs
  | Eload chunk (Ainstack ofs) Enil => BA_loadstack chunk ofs
  | _ => BA e
  end.
>>
*)

Inductive builtin_arg_cases: forall (e: expr), Type :=
  | builtin_arg_case1: forall n, builtin_arg_cases (Eop (Ointconst n) Enil)
  | builtin_arg_case2: forall n, builtin_arg_cases (Eop (Olongconst n) Enil)
  | builtin_arg_case3: forall addr el, builtin_arg_cases (Eop (Olea addr) el)
  | builtin_arg_case4: forall addr el, builtin_arg_cases (Eop (Oleal addr) el)
  | builtin_arg_case5: forall h l, builtin_arg_cases (Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil))
  | builtin_arg_case6: forall h l, builtin_arg_cases (Eop Omakelong (h ::: l ::: Enil))
  | builtin_arg_case7: forall chunk id ofs, builtin_arg_cases (Eload chunk (Aglobal id ofs) Enil)
  | builtin_arg_case8: forall chunk ofs, builtin_arg_cases (Eload chunk (Ainstack ofs) Enil)
  | builtin_arg_default: forall (e: expr), builtin_arg_cases e.

Definition builtin_arg_match (e: expr) :=
  match e as zz1 return builtin_arg_cases zz1 with
  | Eop (Ointconst n) Enil => builtin_arg_case1 n
  | Eop (Olongconst n) Enil => builtin_arg_case2 n
  | Eop (Olea addr) el => builtin_arg_case3 addr el
  | Eop (Oleal addr) el => builtin_arg_case4 addr el
  | Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) => builtin_arg_case5 h l
  | Eop Omakelong (h ::: l ::: Enil) => builtin_arg_case6 h l
  | Eload chunk (Aglobal id ofs) Enil => builtin_arg_case7 chunk id ofs
  | Eload chunk (Ainstack ofs) Enil => builtin_arg_case8 chunk ofs
  | e => builtin_arg_default e
  end.

Definition builtin_arg (e: expr) :=
  match builtin_arg_match e with
  | builtin_arg_case1 n => (* Eop (Ointconst n) Enil *) 
      BA_int n
  | builtin_arg_case2 n => (* Eop (Olongconst n) Enil *) 
      BA_long n
  | builtin_arg_case3 addr el => (* Eop (Olea addr) el *) 
      if Archi.ptr64 then BA e else builtin_arg_addr addr el
  | builtin_arg_case4 addr el => (* Eop (Oleal addr) el *) 
      if Archi.ptr64 then builtin_arg_addr addr el else BA e
  | builtin_arg_case5 h l => (* Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) *) 
      BA_long (Int64.ofwords h l)
  | builtin_arg_case6 h l => (* Eop Omakelong (h ::: l ::: Enil) *) 
      BA_splitlong (BA h) (BA l)
  | builtin_arg_case7 chunk id ofs => (* Eload chunk (Aglobal id ofs) Enil *) 
      BA_loadglobal chunk id ofs
  | builtin_arg_case8 chunk ofs => (* Eload chunk (Ainstack ofs) Enil *) 
      BA_loadstack chunk ofs
  | builtin_arg_default e =>
      BA e
  end.

