(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pulling local scalar variables whose address is not taken
  into temporary variables. *)

Require Import FSets.
Require FSetAVL.
Require Import Coqlib.
Require Import Ordered.
Require Import AST.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.

Module VSet := FSetAVL.Make(OrderedPositive).

(** The set of local variables that can be lifted to temporaries,
  because they are scalar and their address is not taken. *)

Definition compilenv := VSet.t.

(** Renaming variables and temporaries *)

Definition for_var (id: ident) : ident := xO id.
Definition for_temp (id: ident) : ident := xI id.
Definition for_opttemp (optid: option ident) : option ident :=
  match optid with None => None | Some id => Some (for_temp id) end.

(** Rewriting of expressions and statements. *)

Fixpoint simpl_expr (cenv: compilenv) (a: expr) : expr :=
  match a with
  | Econst_int _ _ => a
  | Econst_float _ _ => a
  | Evar id ty => if VSet.mem id cenv then Etempvar (for_var id) ty else Evar id ty
  | Etempvar id ty => Etempvar (for_temp id) ty
  | Ederef a1 ty => Ederef (simpl_expr cenv a1) ty
  | Eaddrof a1 ty => Eaddrof (simpl_expr cenv a1) ty
  | Eunop op a1 ty => Eunop op (simpl_expr cenv a1) ty
  | Ebinop op a1 a2 ty => Ebinop op (simpl_expr cenv a1) (simpl_expr cenv a2) ty
  | Ecast a1 ty => Ecast (simpl_expr cenv a1) ty
  | Efield a1 fld ty => Efield (simpl_expr cenv a1) fld ty
  end.

Definition simpl_exprlist (cenv: compilenv) (al: list expr) : list expr :=
  List.map (simpl_expr cenv) al.

Definition is_liftable_var (cenv: compilenv) (a: expr) : option ident :=
  match a with
  | Evar id ty => if VSet.mem id cenv then Some id else None
  | _ => None
  end.

Fixpoint simpl_stmt (cenv: compilenv) (s: statement) : statement :=
  match s with
  | Sskip => Sskip
  | Sassign a b =>
      match is_liftable_var cenv a with
      | Some id => Sset (for_var id) (Ecast (simpl_expr cenv b) (typeof a))
      | None    => Sassign (simpl_expr cenv a) (simpl_expr cenv b)
      end
  | Sset id a =>
      Sset (for_temp id) (simpl_expr cenv a)
  | Scall optid a bl =>
      Scall (for_opttemp optid) (simpl_expr cenv a) (simpl_exprlist cenv bl)
  | Sbuiltin optid ef tyargs bl =>
      Sbuiltin (for_opttemp optid) ef tyargs (simpl_exprlist cenv bl)
  | Ssequence s1 s2 =>
      Ssequence (simpl_stmt cenv s1) (simpl_stmt cenv s2)
  | Sifthenelse a s1 s2 =>
      Sifthenelse (simpl_expr cenv a) (simpl_stmt cenv s1) (simpl_stmt cenv s2)
  | Sloop s1 s2 =>
      Sloop (simpl_stmt cenv s1) (simpl_stmt cenv s2)
  | Sbreak => Sbreak
  | Scontinue => Scontinue
  | Sreturn opta => Sreturn (option_map (simpl_expr cenv) opta)
  | Sswitch a ls =>
      Sswitch (simpl_expr cenv a) (simpl_lblstmt cenv ls)
  | Slabel lbl s =>
      Slabel lbl (simpl_stmt cenv s)
  | Sgoto lbl => Sgoto lbl
  end

with simpl_lblstmt (cenv: compilenv) (ls: labeled_statements) : labeled_statements :=
  match ls with
  | LSdefault s =>
      LSdefault (simpl_stmt cenv s)
  | LScase n s ls' =>
      LScase n (simpl_stmt cenv s) (simpl_lblstmt cenv ls')
  end.

(** Function parameters that are not lifted to temporaries must be
  stored in the corresponding local variable at function entry. *)

Fixpoint store_params (cenv: compilenv) (params: list (ident * type))
                      (s: statement): statement :=
  match params with
  | nil => s
  | (id, ty) :: params' =>
      if VSet.mem id cenv
      then store_params cenv params' s
      else Ssequence (Sassign (Evar id ty) (Etempvar (for_var id) ty))
                     (store_params cenv params' s)
  end.

(** Compute the set of variables whose address is taken *)

Fixpoint addr_taken_expr (a: expr): VSet.t :=
  match a with
  | Econst_int _ _ => VSet.empty
  | Econst_float _ _ => VSet.empty
  | Evar id ty => VSet.empty
  | Etempvar id ty => VSet.empty
  | Ederef a1 ty => addr_taken_expr a1
  | Eaddrof (Evar id ty1) ty => VSet.singleton id
  | Eaddrof a1 ty => addr_taken_expr a1
  | Eunop op a1 ty => addr_taken_expr a1
  | Ebinop op a1 a2 ty => VSet.union (addr_taken_expr a1) (addr_taken_expr a2)
  | Ecast a1 ty => addr_taken_expr a1
  | Efield a1 fld ty => addr_taken_expr a1
  end.

Fixpoint addr_taken_exprlist (l: list expr) : VSet.t :=
  match l with
  | nil => VSet.empty
  | a :: l' => VSet.union (addr_taken_expr a) (addr_taken_exprlist l')
  end.

Fixpoint addr_taken_stmt (s: statement) : VSet.t :=
  match s with
  | Sskip => VSet.empty
  | Sassign a b => VSet.union (addr_taken_expr a) (addr_taken_expr b)
  | Sset id a => addr_taken_expr a
  | Scall optid a bl => VSet.union (addr_taken_expr a) (addr_taken_exprlist bl)
  | Sbuiltin optid ef tyargs bl => addr_taken_exprlist bl
  | Ssequence s1 s2 => VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)
  | Sifthenelse a s1 s2 =>
      VSet.union (addr_taken_expr a) (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2))
  | Sloop s1 s2 => VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)
  | Sbreak => VSet.empty
  | Scontinue => VSet.empty
  | Sreturn None => VSet.empty
  | Sreturn (Some a) => addr_taken_expr a
  | Sswitch a ls => VSet.union (addr_taken_expr a) (addr_taken_lblstmt ls)
  | Slabel lbl s => addr_taken_stmt s
  | Sgoto lbl => VSet.empty
  end

with addr_taken_lblstmt (ls: labeled_statements) : VSet.t :=
  match ls with
  | LSdefault s => addr_taken_stmt s
  | LScase n s ls' => VSet.union (addr_taken_stmt s) (addr_taken_lblstmt ls')
  end.

(** The compilation environment for a function is the set of local variables
  that are scalars and whose addresses are not taken. *)

Definition add_local_variable (atk: VSet.t) (id_ty: ident * type)
                              (cenv: compilenv) : compilenv :=
  let (id, ty) := id_ty in
  match access_mode ty with
  | By_value chunk => if VSet.mem id atk then cenv else VSet.add id cenv
  | _ => cenv
  end.

Definition cenv_for (f: function) : compilenv :=
  let atk := addr_taken_stmt f.(fn_body) in
  List.fold_right (add_local_variable atk) VSet.empty (f.(fn_params) ++ f.(fn_vars)).

(** Transform a function *)

Definition rename_decl (rename: ident -> ident) (vars: list (ident * type)) :=
  List.map (fun id_ty => (rename (fst id_ty), snd id_ty)) vars.

Definition remove_lifted (cenv: compilenv) (vars: list (ident * type)) :=
  List.filter (fun id_ty => negb (VSet.mem (fst id_ty) cenv)) vars.

Definition add_lifted (cenv: compilenv) (vars1 vars2: list (ident * type)) :=
  rename_decl for_var (List.filter (fun id_ty => VSet.mem (fst id_ty) cenv) vars1)
  ++ rename_decl for_temp vars2.

Definition transf_function (f: function) : function :=
  let cenv := cenv_for f in
  {| fn_return := f.(fn_return);
     fn_params := rename_decl for_var f.(fn_params);
     fn_vars := remove_lifted cenv (f.(fn_params) ++ f.(fn_vars));
     fn_temps := add_lifted cenv f.(fn_vars) f.(fn_temps);
     fn_body := store_params cenv f.(fn_params) (simpl_stmt cenv f.(fn_body)) |}.

(** Whole-program transformation *)

Definition transf_fundef (fd: fundef) : fundef :=
  match fd with
  | Internal f => Internal (transf_function f)
  | External ef targs tres => External ef targs tres
  end.

Definition transf_program (p: program) : program :=
  AST.transform_program transf_fundef p.


