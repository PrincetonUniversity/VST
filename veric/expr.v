Require Import VST.veric.Clight_base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.mpred.
Require Import VST.veric.tycontext.
Require Import VST.veric.Clight_lemmas.
Require Export VST.veric.lift. Import LiftNotation.
Require Export VST.veric.Clight_Cop2.
Require Export VST.veric.val_lemmas.

Require Import VST.veric.seplog. (*For definition of tycontext*)

Import Ctypes.

Definition sizeof {cs: compspecs} t := @Ctypes.sizeof (@cenv_cs cs) t.
Definition alignof {cs: compspecs} t := @Ctypes.alignof (@cenv_cs cs) t.

(** Functions for evaluating expressions in environments,
these return vundef if something goes wrong, meaning they always return some value **)

Definition eval_unop (op: Cop.unary_operation) (t1 : type) :=
       force_val1 (Clight_Cop2.sem_unary_operation op t1).

Definition op_to_cmp cop :=
match cop with
| Cop.Oeq => Ceq | Cop.One =>  Cne
| Cop.Olt => Clt | Cop.Ogt =>  Cgt
| Cop.Ole => Cle | Cop.Oge =>  Cge
| _ => Ceq (*doesn't matter*)
end.

Definition is_comparison op :=
match op with
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => true
  | _ => false
end.

Definition eval_binop {CS:compspecs} (op: Cop.binary_operation) (t1 t2 : type) :=
       force_val2 (Clight_Cop2.sem_binary_operation'  op t1 t2).
Arguments eval_binop CS op t1 t2 / v1 v2.

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).
Arguments eval_cast t1 t2 / v.

Definition eval_field {CS: compspecs} (ty: type) (fld: ident) : val -> val :=
          match ty with
             | Tstruct id att =>
                 match cenv_cs !! id with
                 | Some co =>
                         match field_offset cenv_cs fld (co_members co) with
                         | Errors.OK (delta, Full) => offset_val delta
                         | _ => always Vundef
                         end
                 | _ => always Vundef
                 end
             | Tunion id att =>
                 match cenv_cs !! id with
                 | Some co => 
                         match union_field_offset cenv_cs fld (co_members co) with
                         | Errors.OK (delta, Full) => offset_val delta
                         | _ => always Vundef
                         end
                 | _ => always Vundef
                 end
             | _ => always Vundef
          end.

Definition eval_var (id:ident) (ty: type) (rho: environ) : val :=
                         match lookup id (ve_of rho) with
                         | Some (b,ty') => if eqb_type ty ty'
                                                    then Vptr b Ptrofs.zero
                                                    else Vundef
                         | None =>
                            match lookup id (ge_of rho) with
                            | Some b => Vptr b Ptrofs.zero
                            | None => Vundef
                            end
                        end.

Definition deref_noload (ty: type) : val -> val :=
 match access_mode ty with
 | By_reference => Datatypes.id
 | _ => always Vundef
 end.

Fixpoint eval_expr {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Econst_single f ty => `(Vsingle f)
 | Etempvar id ty => eval_id id
 | Eaddrof a ty => eval_lvalue a
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (eval_expr a)
 | Ebinop op a1 a2 ty =>
                  `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (eval_expr a)
 | Evar id ty => eval_var id ty (* typecheck ensure by-reference *)
 | Ederef a ty => eval_expr a (* typecheck ensure by-reference and isptr *)
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a) (* typecheck ensure by-reference *)
 | Esizeof t ty => `(if complete_type cenv_cs t 
                             then Vptrofs (Ptrofs.repr (sizeof t)) else Vundef)
 | Ealignof t ty => `(if complete_type cenv_cs t 
                             then Vptrofs (Ptrofs.repr (alignof t)) else Vundef)
 end

 with eval_lvalue {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a (* typecheck ensure isptr *)
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | _  => `Vundef
 end.

Fixpoint eval_exprlist {CS: compspecs} (et: list type) (el:list expr) : environ -> list val :=
 match et, el with
 | t::et', e::el' =>
    `(@cons val) (`force_val (`(sem_cast (typeof e) t) (eval_expr e))) (eval_exprlist et' el')
 | _, _ => `nil
 end.

Definition eval_expropt {CS: compspecs} (e: option expr) : environ -> option val :=
 match e with Some e' => `(@Some val) (eval_expr e')  | None => `None end.

(** Beginning of typechecking **)

Definition bool_type (t: type) : bool :=
  match t with
  | Tpointer _ _ => negb (eqb_type t int_or_ptr_type)
  | Tint _ _ _ | Tlong _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tfloat _ _ =>  true
  | _ => false
  end.

Definition is_scalar_type (ty:type) : bool :=
match ty with
| Tint _ _ _ => true
| Tfloat _ _ => true
| _ => false
end.

Definition is_int_type ty :=
match ty with
| Tint _ _ _ => true
| _ => false
end.

Definition is_int32_type ty :=
match ty with
| Tint I32 _ _ => true
| _ => false
end.

Definition is_long_type ty :=
match ty with
| Tlong _ _ => true
| _ => false
end.

Definition is_ptrofs_type :=
 if Archi.ptr64 then is_long_type else is_int32_type.

Definition is_float_type ty :=
match ty with
| Tfloat F64 _ => true
| _ => false
end.

Definition is_single_type ty :=
match ty with
| Tfloat F32 _ => true
| _ => false
end.

Definition is_anyfloat_type ty :=
match ty with
| Tfloat F64 _ => true
| Tfloat F32 _ => true
| _ => false
end.

Definition is_pointer_type ty :=
match ty with
| (Tpointer _ _ 
   | Tarray _ _ _ | Tfunction _ _ _
   | Tstruct _ _  | Tunion _ _) => 
    negb (eqb_type ty int_or_ptr_type)
| _ => false
end.

Section mpred.

Context `{!heapGS Σ}.

Inductive tc_error :=
| op_result_type : expr -> tc_error
| arg_type : expr -> tc_error
| pp_compare_size_0 : type -> tc_error
| pp_compare_size_exceed : type -> tc_error
| invalid_cast : type -> type -> tc_error
| invalid_cast_result : type -> type -> tc_error
| invalid_expression : expr -> tc_error
| var_not_in_tycontext : tycontext -> positive  -> tc_error
| mismatch_context_type : type -> type -> tc_error
| deref_byvalue : type -> tc_error
| volatile_load : type -> tc_error
| invalid_field_access : expr -> tc_error
| invalid_composite_name: ident -> tc_error
| invalid_struct_field : ident (* field name *) -> ident (* struct name *) -> tc_error
| invalid_lvalue : expr -> tc_error
| wrong_signature : tc_error
| int_or_ptr_type_error : tc_error
| miscellaneous_typecheck_error : tc_error.

Inductive tc_assert :=
| tc_FF: tc_error -> tc_assert
| tc_TT : tc_assert
| tc_andp': tc_assert -> tc_assert -> tc_assert
| tc_orp' : tc_assert -> tc_assert -> tc_assert
| tc_nonzero': expr -> tc_assert
| tc_iszero': expr -> tc_assert
| tc_isptr: expr -> tc_assert
| tc_isint: expr -> tc_assert
| tc_islong: expr -> tc_assert
| tc_test_eq': expr -> expr -> tc_assert
| tc_test_order': expr -> expr -> tc_assert
| tc_ilt': expr -> int -> tc_assert
| tc_llt': expr -> int64 -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover': expr -> expr -> tc_assert
| tc_initialized: Maps.PTree.elt -> type -> tc_assert
| tc_nosignedover: (Z->Z->Z) -> expr -> expr -> tc_assert.

Definition tc_noproof := tc_FF miscellaneous_typecheck_error.

Definition tc_iszero {CS: compspecs} (e: expr) : tc_assert :=
  match eval_expr e any_environ with
  | Vint i => if Int.eq i Int.zero then tc_TT else tc_FF (pp_compare_size_0 Tvoid)
  | Vlong i => if Int64.eq i Int64.zero then tc_TT else tc_FF (pp_compare_size_0 Tvoid)
  | _ => tc_iszero' e
  end.

Definition tc_nonzero {CS: compspecs} (e: expr) : tc_assert :=
  match eval_expr e any_environ with
   | Vint i => if negb (Int.eq i Int.zero) then tc_TT else tc_nonzero' e
   | Vlong i => if negb (Int64.eq i Int64.zero) then tc_TT else tc_nonzero' e
   | _ => tc_nonzero' e
   end.

Definition tc_test_eq {CS: compspecs} (e1 e2: expr) : tc_assert :=
 match eval_expr e1 any_environ, eval_expr e2 any_environ with
 | Vint i, Vint j => if andb (negb Archi.ptr64)
                             (andb (Int.eq i Int.zero) (Int.eq j Int.zero))
                             then tc_TT else tc_test_eq' e1 e2
 | Vlong i, Vlong j => if andb Archi.ptr64
                             (andb (Int64.eq i Int64.zero) (Int64.eq j Int64.zero))
                             then tc_TT else tc_test_eq' e1 e2
 | _, _ => tc_test_eq' e1 e2
 end.

Definition tc_test_order {CS: compspecs} (e1 e2: expr) : tc_assert :=
 match eval_expr e1 any_environ, eval_expr e2 any_environ with
 | Vint i, Vint j => if  andb (negb Archi.ptr64)
                                  (andb (Int.eq i Int.zero) (Int.eq j Int.zero))
                             then tc_TT else tc_test_order' e1 e2
 | Vlong i, Vlong j => if  andb Archi.ptr64
                                  (andb (Int64.eq i Int64.zero) (Int64.eq j Int64.zero))
                             then tc_TT else tc_test_order' e1 e2
 | _, _ => tc_test_order' e1 e2
 end.

Definition tc_nodivover {CS: compspecs} (e1 e2: expr) : tc_assert :=
 match eval_expr e1 any_environ, eval_expr e2 any_environ with
                           | Vint n1, Vint n2 => if (negb
                                   (Int.eq n1 (Int.repr Int.min_signed)
                                    && Int.eq n2 Int.mone))
                                     then tc_TT else tc_nodivover' e1 e2
                           | Vlong n1, Vlong n2 => if (negb
                                   (Int64.eq n1 (Int64.repr Int64.min_signed)
                                    && Int64.eq n2 Int64.mone))
                                     then tc_TT else tc_nodivover' e1 e2
                           | Vint n1, Vlong n2 => tc_TT
                           | Vlong n1, Vint n2 => if (negb
                                   (Int64.eq n1 (Int64.repr Int64.min_signed)
                                    && Int.eq n2 Int.mone))
                                     then tc_TT else tc_nodivover' e1 e2
                           | _ , _ => tc_nodivover' e1 e2
                          end.

Definition if_expr_signed (e1 e2 : expr) (tc: tc_assert) : tc_assert :=
 match typeof e1, typeof e2 with
 | Tint _ Signed _, Tint _ Signed _ => tc
 | Tlong Signed _, Tlong Signed _ => tc
 | Tint _ _ _, Tlong Signed _ => tc
 | Tlong Signed _, Tint _ _ _ => tc
 | _, _ => tc_TT
 end.

Definition tc_nobinover (op: Z->Z->Z) {CS: compspecs} (e1 e2: expr) : tc_assert :=
 if_expr_signed e1 e2
 match eval_expr e1 any_environ, eval_expr e2 any_environ with
 | Vint n1, Vint n2 => 
    if range_s32 (op (Int.signed n1) (Int.signed n2))
     then tc_TT else tc_nosignedover op e1 e2
 | Vlong n1, Vlong n2 => 
    if range_s64 (op (Int64.signed n1) (Int64.signed n2))
     then tc_TT else tc_nosignedover op e1 e2
 | Vint n1, Vlong n2 =>
    match typeof e1 with
    | Tint _ Signed _ => 
       if range_s64 (op (Int.signed n1) (Int64.signed n2))
        then tc_TT
        else tc_nosignedover op e1 e2
    | _ =>
        if range_s64 (op (Int.unsigned n1) (Int64.signed n2))
         then tc_TT else tc_nosignedover op e1 e2
    end
 | Vlong n1, Vint n2 =>
    match typeof e2 with
    | Tint _ Signed _ => 
       if range_s64 (op (Int64.signed n1) (Int.signed n2))
        then tc_TT
        else tc_nosignedover op e1 e2
    | _ =>
       if range_s64 (op (Int64.signed n1) (Int.unsigned n2))
        then tc_TT
        else tc_nosignedover op e1 e2
     end
 | _ , _ => tc_nosignedover op e1 e2
 end.

Definition tc_andp (a1: tc_assert) (a2 : tc_assert) : tc_assert :=
match a1 with
| tc_TT => a2
| tc_FF e => tc_FF e
| _ => match a2 with
      | tc_TT => a1
      | tc_FF e => tc_FF e
      | _ => tc_andp' a1 a2
      end
end.

Definition tc_orp (a1: tc_assert) (a2 : tc_assert) : tc_assert :=
match a1 with
| tc_TT => tc_TT
| tc_FF _ => a2
| _ => match a2 with
       | tc_TT => tc_TT
       | tc_FF _ => a1
       | _ => tc_orp' a1 a2
       end
end.

Definition tc_bool (b : bool) (e: tc_error) :=
if b then tc_TT else tc_FF e.

Definition check_pp_int {CS: compspecs} e1 e2 op t e :=
  match op with
  | Cop.Oeq | Cop.One =>
      tc_andp
        (tc_test_eq e1 e2)
        (tc_bool (is_int_type t) (op_result_type e))
  | Cop.Ole | Cop.Olt | Cop.Oge | Cop.Ogt =>
      tc_andp
        (tc_test_order e1 e2)
        (tc_bool (is_int_type t) (op_result_type e))
  | _ => tc_noproof
  end.

Definition binarithType t1 t2 ty deferr reterr : tc_assert :=
  match Cop.classify_binarith t1 t2 with
  | Cop.bin_case_i sg =>  tc_bool (is_int32_type ty) reterr
  | Cop.bin_case_l sg => tc_bool (is_long_type ty) reterr
  | Cop.bin_case_f   => tc_bool (is_float_type ty) reterr
  | Cop.bin_case_s   => tc_bool (is_single_type ty) reterr
  | Cop.bin_default => tc_FF deferr
  end.

Definition is_numeric_type t :=
match t with Tint _ _ _ | Tlong _ _ | Tfloat _ _ => true | _ => false end.

Definition tc_ilt {CS: compspecs} (e: expr) (j: int) :=
    match eval_expr e any_environ with
    | Vint i => if Int.ltu i j then tc_TT else tc_ilt' e j
    | _ => tc_ilt' e j
    end.

Definition tc_llt {CS: compspecs} (e: expr) (j: int64) :=
    match eval_expr e any_environ with
    | Vlong i => if Int64.ltu i j then tc_TT else tc_llt' e j
    | _ => tc_llt' e j
    end.

Definition tc_int_or_ptr_type (t: type) : tc_assert :=
 tc_bool (negb (eqb_type t int_or_ptr_type)) int_or_ptr_type_error.

Definition isUnOpResultType {CS: compspecs} op a ty : tc_assert :=
match op with
  | Cop.Onotbool => match typeof a with
                        | Tint _ _ _ | Tlong _ _ | Tfloat _ _ =>
                                        tc_bool (is_int_type ty) (op_result_type a)
                        | Tpointer _ _ => 
                             tc_andp (tc_int_or_ptr_type (typeof a))
                             (tc_andp (tc_bool (is_int_type ty) (op_result_type a))
                              (tc_test_eq a 
                                (if Archi.ptr64 
                                 then Econst_long Int64.zero (Tlong Signed noattr)
                                 else Econst_int Int.zero (Tint I32 Signed noattr))))
                        | _ => tc_FF (op_result_type a)
                        end
  | Cop.Onotint => match Cop.classify_notint (typeof a) with
                        | Cop.notint_default => tc_FF (op_result_type a)
                        | Cop.notint_case_i _ => tc_bool (is_int32_type ty) (op_result_type a)
                        | Cop.notint_case_l _ => tc_bool (is_long_type ty) (op_result_type a)
                        end
  | Cop.Oneg => match Cop.classify_neg (typeof a) with
                    | Cop.neg_case_i sg => 
                          tc_andp (tc_bool (is_int32_type ty) (op_result_type a))
                          match (typeof a) with
                          | Tint _ Signed _ => tc_nosignedover Z.sub (Econst_int Int.zero (typeof a)) a
                          | Tlong Signed _ => tc_nosignedover Z.sub (Econst_long Int64.zero (typeof a)) a
                          | _ => tc_TT
                          end
                    | Cop.neg_case_l sg => 
                          tc_andp (tc_bool (is_long_type ty) (op_result_type a))
                          match (typeof a) with
                          | Tlong Signed _ => tc_nosignedover Z.sub (Econst_long Int64.zero (typeof a)) a
                          | _ => tc_TT
                          end
                    | Cop.neg_case_f => tc_bool (is_float_type ty) (op_result_type a)
                    | Cop.neg_case_s => tc_bool (is_single_type ty) (op_result_type a)
                    | _ => tc_FF (op_result_type a)
                    end
  | Cop.Oabsfloat =>match Cop.classify_neg (typeof a) with
                    | Cop.neg_case_i sg => tc_bool (is_float_type ty) (op_result_type a)
                    | Cop.neg_case_l _ => tc_bool (is_float_type ty) (op_result_type a)
                    | Cop.neg_case_f => tc_bool (is_float_type ty) (op_result_type a)
                    | Cop.neg_case_s => tc_bool (is_float_type ty) (op_result_type a)
                    | _ => tc_FF (op_result_type a)
                    end
end.

(*Moved to Cop2.
  Definition size_t := if Archi.ptr64 then tulong else tuint.*)

Definition isBinOpResultType {CS: compspecs} op a1 a2 ty : tc_assert :=
let e := (Ebinop op a1 a2 ty) in
let reterr := op_result_type e in
let deferr := arg_type e in
match op with
  | Cop.Oadd => match Cop.classify_add (typeof a1) (typeof a2) with
                    | Cop.add_case_pi t si => tc_andp (tc_andp (tc_andp (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a1)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_ip si t => tc_andp (tc_andp (tc_andp (tc_isptr a2)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a2)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_pl t => tc_andp (tc_andp (tc_andp (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a1)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_lp t => tc_andp (tc_andp (tc_andp (tc_isptr a2)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a2)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_default => tc_andp 
                                           (binarithType (typeof a1) (typeof a2) ty deferr reterr)
                                           (tc_nobinover Z.add a1 a2)
            end
  | Cop.Osub => match Cop.classify_sub (typeof a1) (typeof a2) with
                    | Cop.sub_case_pi t si => tc_andp (tc_andp (tc_andp (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a1)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pl t => tc_andp (tc_andp (tc_andp (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_int_or_ptr_type (typeof a1)))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pp t =>
                             tc_andp (tc_andp (tc_andp (tc_andp (tc_andp (tc_andp (tc_andp 
                               (tc_andp (tc_samebase a1 a2)
                             (tc_isptr a1))
                              (tc_isptr a2))
                               (tc_int_or_ptr_type (typeof a1)))
                               (tc_int_or_ptr_type (typeof a2)))
                               (tc_bool (is_ptrofs_type ty) reterr))
			        (tc_bool (negb (Z.eqb (sizeof t) 0))
                                      (pp_compare_size_0 t)))
                                 (tc_bool (complete_type cenv_cs t) reterr))
                                   (tc_bool (Z.leb (sizeof t) Ptrofs.max_signed)
                                          (pp_compare_size_exceed t))
                    | Cop.sub_default => tc_andp 
                                    (binarithType (typeof a1) (typeof a2) ty deferr reterr)
                                    (tc_nobinover Z.sub a1 a2)
            end
  | Cop.Omul => tc_andp (binarithType (typeof a1) (typeof a2) ty deferr reterr)
                                    (tc_nobinover Z.mul a1 a2)
  | Cop.Omod => match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i Unsigned =>
                           tc_andp (tc_nonzero a2)
                           (tc_bool (is_int32_type ty) reterr)
                    | Cop.bin_case_l Unsigned =>
                           tc_andp (tc_nonzero a2)
                           (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_i Signed => tc_andp (tc_andp (tc_nonzero a2)
                                                      (tc_nodivover a1 a2))
                                                     (tc_bool (is_int32_type ty) reterr)
                    | Cop.bin_case_l Signed => tc_andp (tc_andp (tc_nonzero a2)
                                                      (tc_nodivover a1 a2))
                                                     (tc_bool (is_long_type ty) reterr)
                    | _ => tc_FF deferr
            end
  | Cop.Odiv => match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i Unsigned => tc_andp (tc_nonzero a2) (tc_bool (is_int32_type ty) reterr)
                    | Cop.bin_case_l Unsigned => tc_andp (tc_nonzero a2) (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_i Signed => tc_andp (tc_andp (tc_nonzero a2) (tc_nodivover a1 a2))
                                                        (tc_bool (is_int32_type ty) reterr)
                    | Cop.bin_case_l Signed => tc_andp (tc_andp (tc_nonzero a2) (tc_nodivover a1 a2))
                                                        (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_f  =>  tc_bool (is_float_type ty) reterr
                    | Cop.bin_case_s  =>  tc_bool (is_single_type ty) reterr
                    | Cop.bin_default => tc_FF deferr
            end
  | Cop.Oshl | Cop.Oshr => match Cop.classify_shift (typeof a1) (typeof a2) with
                    | Cop.shift_case_ii _ =>  tc_andp (tc_ilt a2 Int.iwordsize) (tc_bool (is_int32_type ty)
                                                                                         reterr)
                    | Cop.shift_case_il _ =>  tc_andp (tc_llt a2 (Int64.repr 32)) (tc_bool (is_int32_type ty)
                                                                                         reterr)
                    | Cop.shift_case_li _ =>  tc_andp (tc_ilt a2 Int64.iwordsize') (tc_bool (is_long_type ty)
                                                                                         reterr)
                    | Cop.shift_case_ll _ =>  tc_andp (tc_llt a2 Int64.iwordsize) (tc_bool (is_long_type ty)
                                                                                         reterr)
                    | Cop.shift_default => tc_FF deferr
                   end
  | Cop.Oand | Cop.Oor | Cop.Oxor =>
                   match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i _ =>tc_bool (is_int32_type ty) reterr
                    | Cop.bin_case_l _ =>tc_bool (is_long_type ty) reterr
                    | Cop.bin_case_f => tc_FF deferr
                    | Cop.bin_case_s => tc_FF deferr
                    | Cop.bin_default => tc_FF deferr
                   end
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge =>
         match Cop.classify_cmp (typeof a1) (typeof a2) with
              | Cop.cmp_default =>
                           tc_bool (is_numeric_type (typeof a1)
                                         && is_numeric_type (typeof a2)
                                          && is_int_type ty)
                                             deferr
	            | Cop.cmp_case_pp => 
                     tc_andp (tc_andp (tc_int_or_ptr_type (typeof a1)) 
                                      (tc_int_or_ptr_type (typeof a2)))
                       (check_pp_int a1 a2 op ty e)
              | Cop.cmp_case_pi si =>
                     tc_andp (tc_int_or_ptr_type (typeof a1))
                       (check_pp_int a1 (Ecast a2 size_t) op ty e)
              | Cop.cmp_case_ip si => 
                     tc_andp (tc_int_or_ptr_type (typeof a2))
                    (check_pp_int (Ecast a1 size_t) a2 op ty e)
              | Cop.cmp_case_pl => 
                     tc_andp (tc_int_or_ptr_type (typeof a1))
                       (check_pp_int a1 (Ecast a2 size_t) op ty e)
              | Cop.cmp_case_lp => 
                     tc_andp (tc_int_or_ptr_type (typeof a2))
                    (check_pp_int (Ecast a1 size_t) a2 op ty e)
              end
  end.

Definition isCastResultType {CS: compspecs} tfrom tto a : tc_assert :=
  (* missing casts from f2s and s2f *)
match classify_cast tfrom tto with
| Cop.cast_case_default => tc_FF (invalid_cast tfrom tto)
| Cop.cast_case_f2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed)
| Cop.cast_case_s2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed)
| Cop.cast_case_f2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_s2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_i2l _ => 
           tc_andp (tc_bool (is_int_type tfrom) (invalid_cast_result tfrom tto))
             (if is_pointer_type tto then tc_iszero a else tc_TT)
| Cop.cast_case_l2i _ _ => 
           tc_andp (tc_bool (is_long_type tfrom) (invalid_cast_result tfrom tto))
             (if is_pointer_type tto then tc_iszero a else tc_TT)
| Cop.cast_case_pointer  => 
           if eqb_type tfrom tto then tc_TT else
           if orb  (andb (is_pointer_type tto) (is_pointer_type tfrom))
                       (if Archi.ptr64
                        then (andb (is_long_type tto) (is_long_type tfrom)) 
                        else (andb (is_int_type tto) (is_int_type tfrom)))
           then tc_TT else 
           if (andb (eqb_type tto int_or_ptr_type) ((if Archi.ptr64 then is_long_type else is_int_type) tfrom))
           then tc_TT else
           if (andb (eqb_type tto int_or_ptr_type) (is_pointer_type tfrom))
           then tc_TT else
           if (andb (eqb_type tfrom int_or_ptr_type) (is_pointer_type tto))
           then tc_isptr a else
           if (andb (eqb_type tfrom int_or_ptr_type) ((if Archi.ptr64 then is_long_type else is_int_type) tto))
           then (if Archi.ptr64 then tc_islong else tc_isint) a
           else tc_iszero a
| Cop.cast_case_l2l => tc_bool (is_long_type tfrom && is_long_type tto) (invalid_cast_result tto tto)
| Cop.cast_case_void => tc_noproof
| Cop.cast_case_f2bool => tc_bool (is_float_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_s2bool => tc_bool (is_single_type tfrom) (invalid_cast_result tfrom tto)
(*| Cop.cast_case_p2bool => tc_andp (tc_test_eq a (Econst_int Int.zero (Tint I32 Signed noattr)))
                                                (tc_bool (orb (is_int_type tfrom) (is_pointer_type tfrom)) (invalid_cast_result tfrom tto))
*)
      (* before CompCert 2.5: tc_bool (orb (is_int_type tfrom) (is_pointer_type tfrom)) (invalid_cast_result tfrom tto) *)
| Cop.cast_case_l2bool => 
      if is_pointer_type tfrom
      then tc_test_eq a (Econst_long Int64.zero (Tlong Unsigned noattr))
      else tc_TT
| Cop.cast_case_i2bool =>
      if is_pointer_type tfrom
      then tc_test_eq a (Econst_int Int.zero (Tint I32 Unsigned noattr))
      else tc_TT
| Cop.cast_case_i2s _ => tc_TT
| Cop.cast_case_i2f _ => tc_TT
| _ => match tto with
      | Tint _ _ _  => tc_bool (is_int_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F64 _  => tc_bool (is_anyfloat_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F32 _  => tc_bool (is_anyfloat_type tfrom) (invalid_cast_result tto tto)
      | _ => tc_FF (invalid_cast tfrom tto)
      end
end.


(* A "neutral cast" from t1 to t2 is such that
  it satisfies the neutral_cast_lemma, i.e. if v already typechecks as t1
  then it will not be modified by casting to t2. *)
Definition is_neutral_cast t1 t2 :=
 match t1, t2 with
 | Tint IBool _ _, Tint _ _ _ => true
 | Tint I8 Signed _, Tint I8 Signed _ => true
 | Tint I8 Signed _, Tint I16 Signed _ => true
 | Tint I16 Signed _, Tint I16 Signed _ => true
 | Tint I8 Unsigned _, Tint I8 Unsigned _ => true
 | Tint I8 Unsigned _, Tint I16 Unsigned _ => true
 | Tint I16 Unsigned _, Tint I16 Unsigned _ => true
 | Tint _ _ _, Tint I32 _ _ => true
 | Tlong _ _, Tlong _ _ => true
 | Tfloat F64 _, Tfloat F64 _ => true
 | Tfloat F32 _, Tfloat F32 _ => true
 | Tpointer _ _, Tpointer _ _ => eqb_type t1 t2 
                    || negb (eqb_type t1 int_or_ptr_type) 
                     && negb (eqb_type t2 int_or_ptr_type)
 | _, _ => false
 end.

Definition get_var_type (Delta : tycontext) (id : ident) : option type :=
match (var_types Delta) !! id with
| Some ty => Some ty
| None => match (glob_types Delta) !! id with
         | Some g => Some g
         | None => None
           end
end.

Definition same_base_type t1 t2 : bool :=
match t1, t2 with
| (Tarray _ _ _ | Tfunction _ _ _),
   (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
     Bool.eqb (eqb_type t1 int_or_ptr_type)
              (eqb_type t2 int_or_ptr_type)
| (Tstruct _ _ | Tunion _ _), (Tstruct _ _ | Tunion _ _ ) => true
| _, _ => false
end.

(** Main typechecking function, with work will typecheck both pure
and non-pure expressions, for now mostly just works with pure expressions **)

Fixpoint typecheck_expr {CS: compspecs} (Delta : tycontext) (e: expr) : tc_assert :=
let tcr := typecheck_expr Delta in
match e with
 | Econst_int _ (Tint I32 _ _) => tc_TT
 | Econst_long _ (Tlong _ _) => tc_TT
 | Econst_float _ (Tfloat F64 _) => tc_TT
 | Econst_single _ (Tfloat F32 _) => tc_TT
 | Etempvar id ty =>
                       match (temp_types Delta)!!id with
                         | Some ty' => if is_neutral_cast ty' ty || same_base_type ty' ty then
                                         tc_initialized id ty'
                                       else tc_FF (mismatch_context_type ty ty')
		         | None => tc_FF (var_not_in_tycontext Delta id)
                       end
 | Eaddrof a ty => tc_andp (typecheck_lvalue Delta a) (tc_bool (is_pointer_type ty)
                                                      (op_result_type e))
 | Eunop op a ty => tc_andp (isUnOpResultType op a ty) (tcr a)
 | Ebinop op a1 a2 ty => tc_andp (tc_andp (isBinOpResultType op a1 a2 ty)  (tcr a1)) (tcr a2)
 | Ecast a ty => tc_andp (tcr a) (isCastResultType (typeof a) ty a)
 | Evar id ty => match access_mode ty with
                         | By_reference =>
                            match get_var_type Delta id with
                            | Some ty' => tc_bool (eqb_type ty ty')
                                                           (mismatch_context_type ty ty')
                            | None => tc_FF (var_not_in_tycontext Delta id)
                            end
                         | _ => tc_FF (deref_byvalue ty)
                        end
 | Efield a i ty => match access_mode ty with
                         | By_reference =>
                            tc_andp (typecheck_lvalue Delta a) (match typeof a with
                            | Tstruct id att =>
                               match cenv_cs !! id with
                               | Some co =>
                                  match field_offset cenv_cs i (co_members co) with
                                  | Errors.OK (delta,Full) => tc_TT
                                  | _ => tc_FF (invalid_struct_field i id)
                                  end
                               | _ => tc_FF (invalid_composite_name id)
                               end
                            | Tunion id att =>
                               match cenv_cs !! id with
                               | Some co => 
                                   match union_field_offset cenv_cs i (co_members co) with
                                     | Errors.OK (0, Full) => tc_TT
                                     | _ => tc_FF (invalid_struct_field i id)
                                   end
                               | _ => tc_FF (invalid_composite_name id)
                               end
                            | _ => tc_FF (invalid_field_access e)
                            end)
                         | _ => tc_FF (deref_byvalue ty)
                        end
 | Ederef a ty => match access_mode ty with
                  | By_reference => tc_andp
                       (tc_andp
                          (typecheck_expr Delta a)
                          (tc_bool (is_pointer_type (typeof a))(op_result_type e)))
                       (tc_isptr a)
                  | _ => tc_FF (deref_byvalue ty)
                  end
 | Esizeof ty t => tc_andp (tc_bool (complete_type cenv_cs ty) (invalid_expression e))
                     (tc_bool (eqb_type t size_t) (invalid_expression e))
 | Ealignof ty t => tc_andp (tc_bool (complete_type cenv_cs ty) (invalid_expression e))
                     (tc_bool (eqb_type t size_t) (invalid_expression e))
 | _ => tc_FF (invalid_expression e)
end

with typecheck_lvalue {CS: compspecs}(Delta: tycontext) (e: expr) : tc_assert :=
match e with
 | Evar id ty => match get_var_type Delta id with
                  | Some ty' => tc_bool (eqb_type ty ty')
                                           (mismatch_context_type ty ty')
                  | None => tc_FF (var_not_in_tycontext Delta id)
                 end
 | Ederef a ty => tc_andp
                       (tc_andp
                          (typecheck_expr Delta a)
                          (tc_bool (is_pointer_type (typeof a))(op_result_type e)))
                       (tc_isptr a)
 | Efield a i ty => tc_andp
                         (typecheck_lvalue Delta a)
                         (match typeof a with
                            | Tstruct id att =>
                              match cenv_cs !! id with
                              | Some co =>
                                   match field_offset cenv_cs i (co_members co) with
                                     | Errors.OK (delta, Full) => tc_TT
                                     | _ => tc_FF (invalid_struct_field i id)
                                   end
                              | _ => tc_FF (invalid_composite_name id)
                              end
                            | Tunion id att =>
                              match cenv_cs !! id with
                              | Some co => 
                                   match union_field_offset cenv_cs i (co_members co) with
                                     | Errors.OK (0, Full) => tc_TT
                                     | _ => tc_FF (invalid_struct_field i id)
                                   end
                              | _ => tc_FF (invalid_composite_name id)
                              end
                            | _ => tc_FF (invalid_field_access e)
                          end)
 | _  => tc_FF (invalid_lvalue e)
end.

Definition implicit_deref (t: type) : type :=
  match t with
  | Tarray t' _ _ => Tpointer t' noattr
  | _ => t
  end.

Definition typecheck_temp_id {CS: compspecs}id ty Delta a : tc_assert :=
  match (temp_types Delta)!!id with
  | Some t =>
      tc_andp (tc_bool (is_neutral_cast (implicit_deref ty) t) (invalid_cast ty t))
                  (isCastResultType (implicit_deref ty) t a)
  | None => tc_FF (var_not_in_tycontext Delta id)
 end.

Fixpoint tc_might_be_true (asn : tc_assert) :=
match asn with
 | tc_FF _ => false
 | tc_andp' a1 a2 => tc_might_be_true a1 && tc_might_be_true a2
 | _ => true
end.

Fixpoint tc_always_true (asn : tc_assert) :=
match asn with
 | tc_TT => true
 | tc_andp' a1 a2 => tc_always_true a1 && tc_always_true a2
 | _ => false
end.

(* A more standard typechecker, should approximate the c typechecker,
might need to add a tc_noproof for nested loads*)
Definition typecheck_b {CS: compspecs}Delta e :=  tc_might_be_true (typecheck_expr Delta e).

(*Definition of the original *pure* typechecker where true means the expression
will always evaluate, may not be useful since tc_denote will just compute to true
on these assertions*)
Definition typecheck_pure_b {CS: compspecs}Delta e := tc_always_true (typecheck_expr Delta e).

Fixpoint typecheck_exprlist {CS: compspecs}(Delta : tycontext) (tl : list type) (el : list expr) : tc_assert :=
match tl,el with
| t::tl', e:: el' => tc_andp (typecheck_expr Delta (Ecast e t))
                      (typecheck_exprlist Delta tl' el')
| nil, nil => tc_TT
| _, _ => tc_FF wrong_signature
end.

(** Type-checking of function parameters **)

Fixpoint match_fsig_aux (bl: list expr) (tl: list (ident*type)) : bool :=
 match bl, tl with
 | b::bl', (_,t'):: tl' => if eqb_type (typeof b) t' then match_fsig_aux bl' tl' else false
 | nil, nil => true
 | nil, _::_ => false
 | _::_, nil => false
 end.

Definition match_fsig (fs: funsig) (bl: list expr) (ret: option ident) : bool :=
  andb (match_fsig_aux bl (fst fs))
          (match snd fs, ret with
            | Tvoid , None => true
            | Tvoid, Some _ => false
            | _, None => false
            | _, Some _ => true
            end).

Lemma match_fsig_e: forall fs bl ret,
  match_fsig fs bl ret = true ->
  map typeof bl = map (@snd _ _) (fst fs) /\ (snd fs=Tvoid <-> ret=None).
Proof.
 intros.
 apply andb_true_iff in H.
 destruct H.
 split. clear H0.
 forget (fst fs) as tl.
 revert tl H; induction bl; destruct tl; intros; inv H.
  reflexivity.
 destruct p.
 revert H1; case_eq (eqb_type (typeof a) t); intros.
 apply eqb_type_true in H. subst; simpl in *. f_equal; auto.
 inv H1.
 clear H.
 destruct (snd fs); destruct ret; intuition congruence.
Qed.

Definition expr_closed_wrt_vars {CS: compspecs}(S: ident -> Prop) (e: expr) : Prop :=
  forall rho te',
     (forall i, S i \/ lookup i (te_of rho) = lookup i te') ->
     eval_expr e rho = eval_expr e (mkEnviron (ge_of rho) (ve_of rho) te').

Definition lvalue_closed_wrt_vars {CS: compspecs}(S: ident -> Prop) (e: expr) : Prop :=
  forall rho te',
     (forall i, S i \/ lookup i (te_of rho) = lookup i te') ->
     eval_lvalue e rho = eval_lvalue e (mkEnviron (ge_of rho) (ve_of rho) te').


Definition typecheck_store e1 :=
(is_int_type (typeof e1) = true -> typeof e1 = Tint I32 Signed noattr) /\
(is_float_type (typeof e1) = true -> typeof e1 = Tfloat F64 noattr).

(*Typechecking facts to help semax_store go through until it gets generalized*)

Ltac tc_assert_ext :=
repeat match goal with
| [H : _ /\ _ |- _] => destruct H
end.

Ltac of_bool_destruct :=
match goal with
  | [ |- context[Val.of_bool ?X] ] => destruct X
  | [ |- context[bool2val ?X] ] => destruct X
end.

Lemma orb_if : forall {D} b c (d:D) (e:D), (if (b || c) then d else e) = if b then d else if c then d else e.
intros.
remember (b || c). destruct b0; auto. symmetry in Heqb0. rewrite orb_true_iff in Heqb0.
intuition; subst; auto. destruct b; auto. symmetry in Heqb0; rewrite orb_false_iff in Heqb0.
intuition; subst; auto.
Qed.

Lemma andb_if : forall {D} b c (d:D) (e:D), (if (b && c) then d else e) = if b then (if c then d else e) else e.
Proof.
intros.
remember (b&&c). destruct b0; symmetry in Heqb0; 
try rewrite andb_true_iff in *; try rewrite andb_false_iff in *;
simple_if_tac; auto; intuition auto;
destruct c; auto; simpl in *; intuition congruence.
Qed.

Open Scope bi_scope.

Definition valid_pointer' (p: val) (d: Z) : mpred :=
 match p with
 | Vint i => if Archi.ptr64 then False else ⌜i = Int.zero⌝
 | Vlong i => if Archi.ptr64 then ⌜i = Int64.zero⌝ else False
 | Vptr b ofs => <absorb> ((∃dq r, (b, Ptrofs.unsigned ofs + d) ↦{dq} r) ∨ (∃ sh, ⌜sh ≠ Share.bot⌝ ∧ mapsto_no (b, Ptrofs.unsigned ofs + d) sh))
 | _ => False
 end.

Global Instance valid_pointer'_absorbing p d : Absorbing (valid_pointer' p d).
Proof. destruct p; apply _. Qed.

Definition valid_pointer (p: val) : mpred :=
 (valid_pointer' p 0).

Definition weak_valid_pointer (p: val) : mpred :=
 (valid_pointer' p 0) ∨ (valid_pointer' p (-1)).

Global Instance weak_valid_pointer_absorbing p : Absorbing (weak_valid_pointer p).
Proof.  apply _. Qed.

Lemma func_at_valid_pointer {phi b z} (Hz: 0 <= z <= Ptrofs.max_unsigned):
      func_at phi (b,z) ⊢ valid_pointer (Vptr b (Ptrofs.repr z)).
Proof. unfold func_at, valid_pointer, valid_pointer'.
  iIntros "(? & _)"; iLeft.
  rewrite Z.add_0_r Ptrofs.unsigned_repr //.
  iFrame.
Qed.

Lemma func_at'_valid_pointer {phi b z} (Hz: 0 <= z <= Ptrofs.max_unsigned):
      func_at' phi (b,z) ⊢ valid_pointer (Vptr b (Ptrofs.repr z)).
Proof. unfold func_at'; destruct phi.
  iIntros "(% & % & % & % & ?)"; iApply func_at_valid_pointer; done.
Qed.

Lemma func_ptr_si_valid_pointer {phi v}: func_ptr_si phi v ⊢ valid_pointer v.
Proof.
  unfold func_ptr_si.
  iIntros "(% & -> & % & _ & ?)"; iApply func_at_valid_pointer; done.
Qed.

Lemma func_ptr_valid_pointer {phi v}: func_ptr phi v ⊢ valid_pointer v.
Proof.
  unfold func_ptr_si.
  iIntros "(% & -> & % & _ & ?)"; iApply func_at_valid_pointer; done.
Qed.

(********************SUBSUME****************)

Definition funsig_of_function (f: function) : funsig :=
  (fn_params f, fn_return f).

Lemma binary_intersection_retty {phi1 phi2 phi} (BI : binary_intersection phi1 phi2 = Some phi):
      xtype_of_funspec phi1 = xtype_of_funspec phi.
Proof. unfold xtype_of_funspec. rewrite (binary_intersection_typesig BI); trivial. Qed.

(* If we were to require that a non-void-returning function must,
   at a function call, have its result assigned to a temp,
   then we could change "ret0_tycon" to "ret_tycon" in this
   definition (and in NDfunspec_sub). *)

Definition subsumespec x y :=
match x with
| Some hspec => exists gspec, y = Some gspec /\ (⊢ funspec_sub_si gspec hspec) (*contravariance!*)
| None => Logic.True
end. 

Lemma subsumespec_trans x y z (SUB1: subsumespec x y) (SUB2: subsumespec y z):
     subsumespec x z.
Proof. unfold subsumespec in *.
 destruct x; trivial. destruct SUB1 as [? [? ?]]; subst.
 destruct SUB2 as [? [? ?]]; subst. exists x0; split; trivial.
 iIntros; iApply funspec_sub_si_trans; auto.
Qed.

Lemma subsumespec_refl x: subsumespec x x.
Proof. unfold subsumespec.
 destruct x; trivial. exists f; split; [trivial| apply funspec_sub_si_refl ].
Qed.

Definition tycontext_sub (Delta Delta' : tycontext) : Prop :=
 (forall id : ident, match (temp_types Delta) !! id,  (temp_types Delta') !! id with
                 | None, _ => True
                 | Some t, None => False
                 | Some t, Some t' => t=t'
                end)
 /\ (forall id, (var_types Delta) !! id = (var_types Delta') !! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, sub_option ((glob_types Delta) !! id) ((glob_types Delta') !! id))

 /\ (forall id, subsumespec ((glob_specs Delta) !! id) ((glob_specs Delta') !! id))

 /\ (forall id, Annotation_sub ((annotations Delta) !! id) ((annotations Delta') !! id)).


Lemma tycontext_sub_trans:
 forall Delta1 Delta2 Delta3,
  tycontext_sub Delta1 Delta2 -> tycontext_sub Delta2 Delta3 ->
  tycontext_sub Delta1 Delta3.
Proof.
  intros ??? [G1 [G2 [G3 [G4 [G5 G6]]]]] [H1 [H2 [H3 [H4 [H5 H6]]]]].
  repeat split.
  * intros. specialize (G1 id); specialize (H1 id).
    destruct ((temp_types Delta1) !! id); auto.
    destruct ((temp_types Delta2) !! id);
      try contradiction.
    destruct ((temp_types Delta3) !! id); try contradiction.
    destruct G1, H1; split; subst; auto.
  * intros. specialize (G2 id); specialize (H2 id); congruence.
  * congruence.
  * intros. eapply sub_option_trans; eauto.
  * clear - H5 G5. intros. eapply subsumespec_trans; eauto.
  * intros. eapply Annotation_sub_trans; eauto.
Qed.

Lemma tycontext_sub_refl Delta: tycontext_sub Delta Delta.
Proof.
  repeat split; trivial.
  * intros. destruct ((temp_types Delta) !! id); trivial. 
  * intros. apply sub_option_refl. 
  * intros. apply subsumespec_refl.
  * intros. eapply Annotation_sub_refl.
Qed.

(*************************************)



(*Could weaken and say that only the data components of the composite need to identical, not the proofs*)
Definition cenv_sub (ce ce':composite_env) := forall i, sub_option (ce!!i) (ce'!!i).

Lemma cenv_sub_refl {ce}: cenv_sub ce ce.
Proof. intros i; apply sub_option_refl. Qed.

Lemma cenv_sub_trans {ce ce' ce''}: cenv_sub ce ce' -> cenv_sub ce' ce'' -> cenv_sub ce ce''.
Proof. intros X X' i; specialize (X i); specialize (X' i). eapply sub_option_trans; eassumption. Qed.

Definition ha_env_cs_sub (t t': Maps.PTree.t Z) := forall i, sub_option (t!!i) (t'!!i).

Lemma ha_env_cs_refl {ce}: ha_env_cs_sub ce ce.
Proof. intros i; apply sub_option_refl. Qed.

Lemma ha_env_cs_sub_trans {ce ce' ce''}: ha_env_cs_sub ce ce' -> ha_env_cs_sub ce' ce'' -> ha_env_cs_sub ce ce''.
Proof. intros X X' i; specialize (X i); specialize (X' i). eapply sub_option_trans; eassumption. Qed.

Definition la_env_cs_sub (t t': Maps.PTree.t align_mem.LegalAlignasFacts.LegalAlignas.legal_alignas_obs) :=
  forall i, sub_option (t!!i) (t'!!i).

Lemma la_env_cs_refl {ce}: la_env_cs_sub ce ce.
Proof. intros i; apply sub_option_refl. Qed.

Lemma la_env_cs_sub_trans {ce ce' ce''}: la_env_cs_sub ce ce' -> la_env_cs_sub ce' ce'' -> la_env_cs_sub ce ce''.
Proof. intros X X' i; specialize (X i); specialize (X' i). eapply sub_option_trans; eassumption. Qed.

Definition cspecs_sub (cs cs':compspecs) := cenv_sub (@cenv_cs cs) (@cenv_cs cs') /\
                                            ha_env_cs_sub (@ha_env_cs cs) (@ha_env_cs cs') /\
                                            la_env_cs_sub (@la_env_cs cs) (@la_env_cs cs').

Lemma cspecs_sub_refl {cs}: cspecs_sub cs cs.
Proof. split3; [ apply cenv_sub_refl | apply ha_env_cs_refl | apply la_env_cs_refl]. Qed.

Lemma cspecs_sub_trans {cs cs' cs''}: cspecs_sub cs cs' -> cspecs_sub cs' cs'' -> cspecs_sub cs cs''.
Proof.
  intros [A1 [A2 A3]] [B1 [B2 B3]]. split3.
  apply (cenv_sub_trans A1 B1). 
  apply (ha_env_cs_sub_trans A2 B2). 
  apply (la_env_cs_sub_trans A3 B3).
Qed.

Lemma valid_pointer_is_pointer_or_null p:
      valid_pointer p ⊢ ⌜is_pointer_or_null p⌝.
Proof. destruct p; simpl; auto. Qed.

End mpred.

Global Arguments typecheck_expr {_ _ _} _ !e / : simpl nomatch.
Global Arguments typecheck_lvalue {_ _ _} _ !e / : simpl nomatch.

(** Environment typechecking functions **)

Lemma typecheck_var_environ_None: forall ve vt,
  typecheck_var_environ ve vt ->
  forall (i : ident),
  vt !! i = None <-> lookup i ve = None.
Proof.
  intros.
  destruct (vt !! i) eqn:?H, (ve !! i)%stdpp eqn:?H; try (split; congruence).
  + apply H in H0 as (? & ?); congruence.
  + destruct p.
    assert (vt !! i = Some t) by (apply H; eauto).
    congruence.
Qed.

(* This naming is for the purpose when VST's developers do "Search typecheck_var_environ." *)
Lemma WARNING___________you_should_use_tactic___destruct_var_types___instead:
  forall (ve : venviron) (vt : Maps.PTree.t type), typecheck_var_environ ve vt -> forall i : ident,
     match vt !! i with
     | Some t => exists b, lookup i ve = Some (b, t)
     | None => lookup i ve = None
     end.
Proof.
  intros.
  pose proof (H i).
  destruct (vt !! i) eqn:?H.
  + specialize (H0 t).
    destruct H0 as [? _].
    specialize (H0 eq_refl).
    auto.
  + eapply typecheck_var_environ_None; eauto.
Qed.

(* This naming is for the purpose when VST's developers do "Search typecheck_glob_environ." *)
Lemma WARNING___________you_should_use_tactic___destruct_glob_types___instead:
  forall (ge : genviron) (gt : Maps.PTree.t type), typecheck_glob_environ ge gt -> forall i : ident,
     match gt !! i with
     | Some t => exists b, lookup i ge = Some b
     | None => True
     end.
Proof.
  intros.
  pose proof (H i).
  destruct (gt !! i).
  + specialize (H0 t).
    specialize (H0 eq_refl).
    auto.
  + auto.
Qed.

Ltac _destruct_var_types i Heq_vt Heq_ve t b :=
  let HH := fresh "H" in
  match goal with
  | H: typecheck_var_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_var_types___instead _ _ H i as HH
  | H: typecheck_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_var_types___instead _ _ (proj1 (proj2 H)) i as HH
  end;
  match type of HH with
  | match ?o with _ => _ end =>
      match goal with
      | H: o = Some _ |- _ =>
          rewrite H in HH
      | H: Some _ = o |- _ =>
          rewrite <- H in HH
      | H: o = None |- _ =>
          rewrite H in HH
      | H: None = o |- _ =>
          rewrite <- H in HH
      | _ =>
          let HH' := fresh "H" in
          pose proof eq_refl o as HH';
          destruct o as [t |] in HH, HH' at 2;
          pose proof HH' as Heq_vt; clear HH'
      end
  end;
  match type of HH with
  | ex _ =>
      pose proof HH as [b Heq_ve]
  | _ =>
      pose proof HH as Heq_ve
  end;
  clear HH.

Tactic Notation "destruct_var_types" constr(i) :=
  let Heq_vt := fresh "Heqo" in
  let Heq_ve := fresh "Heqo" in
  let t := fresh "t" in
  let b := fresh "b" in
  _destruct_var_types i Heq_vt Heq_ve t b.

Tactic Notation "destruct_var_types" constr(i) "as" "[" ident(t) ident(b) "]" :=
  let Heq_vt := fresh "Heqo" in
  let Heq_ve := fresh "Heqo" in
  _destruct_var_types i Heq_vt Heq_ve t b.

Tactic Notation "destruct_var_types" constr(i) "eqn" ":" simple_intropattern(Heq_vt) "&" simple_intropattern(Heq_ve) :=
  let t := fresh "t" in
  let b := fresh "b" in
  _destruct_var_types i Heq_vt Heq_ve t b.

Tactic Notation "destruct_var_types" constr(i) "as" "[" ident(t) ident(b) "]" "eqn" ":" simple_intropattern(Heq_vt) "&" simple_intropattern(Heq_ve) :=
  _destruct_var_types i Heq_vt Heq_ve t b.

Ltac _destruct_glob_types i Heq_gt Heq_ge t b :=
  let HH := fresh "H" in
  match goal with
  | H: typecheck_glob_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_glob_types___instead _ _ H i as HH
  | H: typecheck_environ _ _ |- _ =>
      pose proof WARNING___________you_should_use_tactic___destruct_glob_types___instead _ _ (proj2 (proj2 H)) i as HH
  end;
  match type of HH with
  | match ?o with _ => _ end =>
      match goal with
      | H: o = Some _ |- _ =>
          rewrite H in HH
      | H: Some _ = o |- _ =>
          rewrite <- H in HH
      | H: o = None |- _ =>
          rewrite H in HH
      | H: None = o |- _ =>
          rewrite <- H in HH
      | _ =>
          let HH' := fresh "H" in
          pose proof eq_refl o as HH';
          destruct o as [t |] in HH, HH' at 2;
          pose proof HH' as Heq_gt; clear HH'
      end
  end;
  match type of HH with
  | ex _ =>
      pose proof HH as [b Heq_ge]
  | _ =>
      idtac
  end;
  clear HH.

Tactic Notation "destruct_glob_types" constr(i) :=
  let Heq_gt := fresh "Heqo" in
  let Heq_ge := fresh "Heqo" in
  let t := fresh "t" in
  let b := fresh "b" in
  _destruct_glob_types i Heq_gt Heq_ge t b.

Tactic Notation "destruct_glob_types" constr(i) "as" "[" ident(t) ident(b) "]" :=
  let Heq_gt := fresh "Heqo" in
  let Heq_ge := fresh "Heqo" in
  _destruct_glob_types i Heq_gt Heq_ge t b.

Tactic Notation "destruct_glob_types" constr(i) "eqn" ":" simple_intropattern(Heq_gt) "&" simple_intropattern(Heq_ge) :=
  let t := fresh "t" in
  let b := fresh "b" in
  _destruct_glob_types i Heq_gt Heq_ge t b.

Tactic Notation "destruct_glob_types" constr(i) "as" "[" ident(t) ident(b) "]" "eqn" ":" simple_intropattern(Heq_gt) "&" simple_intropattern(Heq_ge) :=
  _destruct_glob_types i Heq_gt Heq_ge t b.
