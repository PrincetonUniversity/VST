Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

Definition type_id_env: Type := PTree.t type.
Definition empty_ti: type_id_env := @PTree.empty type.

Definition singleton_ti t: type_id_env :=
  match t with
  | Tstruct i _ _ => PTree.set i t empty_ti
  | Tunion i _ _ => PTree.set i t empty_ti
  | _ => empty_ti
  end.

Definition look_up_ident_default (i: ident) (e: type_id_env) : type :=
  match PTree.get i e with
  | Some res => res
  | None => Tvoid
  end.

Fixpoint add_type (t: type) (e: type_id_env): type_id_env :=
  match t with
  | Tvoid 
  | Tint _ _ _ 
  | Tlong _ _
  | Tfloat _ _ => e
  | Tpointer t1 a => add_type t1 e
  | Tarray t1 sz a => add_type t1 e
  | Tfunction t1 t2 _ => add_typelist t1 (add_type t2 e)
  | Tstruct id fld a => add_fieldlist fld (PTree.set id t e)
  | Tunion id fld a => add_fieldlist fld (PTree.set id t e)
  | Tcomp_ptr id a => e
  end
with add_typelist (ts: typelist) (e: type_id_env): type_id_env :=
  match ts with
  | Tnil => e
  | Tcons t ts' => add_typelist ts' (add_type t e)
  end
with add_fieldlist (flds: fieldlist) (e: type_id_env): type_id_env :=
  match flds with
  | Fnil => e
  | Fcons _ t flds' => add_fieldlist flds' (add_type t e)
  end.

Definition add_type_in_global_spec (sp: global_spec) (e: type_id_env) : type_id_env :=
  match sp with
  | Global_func (mk_funspec (its, t) _ _ _) =>
      fold_left (fun e X => add_type (snd X) e) its (add_type t e)
  | Global_var t => add_type t e
  end.

Definition compute_type_id_env (Delta: tycontext): type_id_env :=
  match Delta with
  | (A, B, C, D) =>
       let e0 := PTree.empty type in
       let e1 := PTree.fold1 (fun e X => add_type (fst X) e) A e0 in
       let e2 := PTree.fold1 (fun e X => add_type X e) B e1 in
       let e3 := add_type C e2 in
       let e4 := PTree.fold1 (fun e X => add_type_in_global_spec X e) D e3 in
       e4
  end.
