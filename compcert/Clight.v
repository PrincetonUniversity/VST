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

(** The Clight language: a simplified version of Compcert C where all
  expressions are pure and assignments and function calls are
  statements, not expressions. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Events.
Require Import Globalenvs.
Require Import Ctypes.

(** * Abstract syntax *)


(** ** Expressions *)

(** Clight expressions correspond to the "pure" subset of C expressions.
  The main omissions are string literals and assignment operators
  ([=], [+=], [++], etc).  In Clight, assignment is a statement,
  not an expression.  Additionally, an expression can also refer to
  temporary variables, which are a separate class of local variables
  that do not reside in memory and whose address cannot be taken.

  As in Compcert C, all expressions are annotated with their types,
  as needed to resolve operator overloading and type-dependent behaviors. *)

Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)
  | Econst_float: float -> type -> expr   (**r float literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Ecast: expr -> type -> expr   (**r type cast ([(ty) e]) *)
  | Econdition: expr -> expr -> expr -> type -> expr (**r conditional ([e1 ? e2 : e3]) *)
  | Efield: expr -> ident -> type -> expr. (**r access to a member of a struct or union *)

(** [sizeof] and [alignof] are derived forms. *)

Definition Esizeof (ty' ty: type) : expr := Econst_int (Int.repr(sizeof ty')) ty.
Definition Ealignof (ty' ty: type) : expr := Econst_int (Int.repr(alignof ty')) ty.

(** Extract the type part of a type-annotated Clight expression. *)

Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Evar _ ty => ty
  | Etempvar _ ty => ty
  | Ederef _ ty => ty
  | Eaddrof _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Ecast _ ty => ty
  | Econdition _ _ _ ty => ty
  | Efield _ _ ty => ty
  end.

(** ** Statements *)

(** Clight statements are similar to those of Compcert C, with the addition
  of assigment (of a rvalue to a lvalue), assignment to a temporary,
  and function call (with assignment of the result to a temporary).
  The [for] loop is slightly simplified: there is no initial statement. *)

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Svolread : ident -> expr -> statement (**r volatile read [tempvar = volatile lvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Swhile : expr -> statement -> statement   (**r [while] loop *)
  | Sdowhile : expr -> statement -> statement (**r [do] loop *)
  | Sfor': expr -> statement -> statement -> statement (**r [for] loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSdefault: statement -> labeled_statements
  | LScase: int -> statement -> labeled_statements -> labeled_statements.

(** The full [for] loop is a derived form. *)

Definition Sfor (s1: statement) (e2: expr) (s3 s4: statement) :=
  Ssequence s1 (Sfor' e2 s3 s4).

(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Inductive fundef : Type :=
  | Internal: function -> fundef
  | External: external_function -> typelist -> type -> fundef.

(** ** Programs *)

(** A program is a collection of named functions, plus a collection
  of named global variables, carrying their types and optional initialization 
  data.  See module [AST] for more details. *)

Definition program : Type := AST.program fundef type.

(** * Operations over types *)

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res => Tfunction args res
  end.

(** * Operational semantics *)

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].) *)

Definition genv := Genv.t fundef type.

(** The local environment maps local variables to block references
  and types.  The current value of the variable is stored in the associated memory
  block. *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** The temporary environment maps local temporaries to values. *)

Definition temp_env := PTree.t val.

(** Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. *)

Fixpoint select_switch (n: int) (sl: labeled_statements)
                       {struct sl}: labeled_statements :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.

(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSdefault s => s
  | LScase c s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

Section SEMANTICS.

Variable ge: genv.

(** [type_of_global b] returns the type of the global variable or function
  at address [b]. *)

Definition type_of_global (b: block) : option type :=
  match Genv.find_var_info ge b with
  | Some gv => Some gv.(gvar_info)
  | None =>
      match Genv.find_funct_ptr ge b with
      | Some fd => Some(type_of_fundef fd)
      | None => None
      end
  end.


Fixpoint create_undef_temps (temps: list (ident * type)) : temp_env :=
 match temps with
 | (id,t)::xl => PTree.set id Vundef (create_undef_temps xl)
 | nil => PTree.empty val
 end.

Fixpoint bind_parameter_temps
           (formals: list (ident * type)) (args: list val) (le: temp_env) : option temp_env :=
 match formals, args with
 | (id,t)::xl, v::vl => match bind_parameter_temps xl vl le with
                           | Some le' => Some (PTree.set id v le')
                           | None => None
                           end
 | nil, nil => Some le
 | _, _ => None
 end. 

End SEMANTICS.