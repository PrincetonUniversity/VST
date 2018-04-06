Require Import VST.msl.msl_standard.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.tycontext.
Require Import VST.veric.Clight_lemmas.
Require Export VST.veric.lift.
Require Export VST.veric.Cop2.

Definition is_true (b: bool) :=
  match b with true => True | false => False end.

Definition force_val (v: option val) : val :=
 match v with Some v' => v' | None => Vundef end.

Definition force_val1 (f: val -> option val) (v: val) := force_val (f v).
Definition force_val2 (f: val -> val -> option val) (v1 v2: val) := force_val (f v1 v2).

Arguments force_val1 f v /.
Arguments force_val2 f v1 v2 /.

Definition force_int (v: val) :=
 match v with
 | Vint i => i | _ => Int.zero
 end.
Arguments force_int !v / .

Definition force_signed_int v := Int.signed (force_int v).
Arguments force_signed_int !v / .

Lemma force_Vint:  forall i, force_int (Vint i) = i.
Proof.  reflexivity. Qed.
Hint Rewrite force_Vint : norm.

(* TWO ALTERNATE WAYS OF DOING LIFTING *)
(* LIFTING METHOD ONE: *)
Definition lift0 {B} (P: B) : environ -> B := fun _ => P.
Definition lift1 {A1 B} (P: A1 -> B) (f1: environ -> A1) : environ -> B := fun rho => P (f1 rho).
Definition lift2 {A1 A2 B} (P: A1 -> A2 -> B) (f1: environ -> A1) (f2: environ -> A2):
   environ -> B := fun rho => P (f1 rho) (f2 rho).
Definition lift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B)
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3) :  environ -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho).
Definition lift4 {A1 A2 A3 A4 B} (P: A1 -> A2 -> A3 -> A4 -> B)
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3)(f4: environ -> A4):  environ -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho) (f4 rho).

(* LIFTING METHOD TWO: *)
Canonical Structure LiftEnviron := Tend environ.

Ltac super_unfold_lift :=
  cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T lift_prod
  lift_last lifted lift_uncurry_open lift_curry lift lift0 lift1 lift2 lift3] beta iota in *.

(** Functions for evaluating expressions in environments,
these return vundef if something goes wrong, meaning they always return some value **)

Definition strict_bool_val (v: val) (t: type) : option bool :=
   match v, t with
   | Vint n, Tint _ _ _ => Some (negb (Int.eq n Int.zero))
   | Vlong n, Tlong _ _ => Some (negb (Int64.eq n Int64.zero))
   | (Vint n), (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
             if Int.eq n Int.zero then Some false else None
   | Vlong n, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
            if Archi.ptr64 then if Int64.eq n Int64.zero then Some false else None else None
   | Vptr b ofs, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) => Some true
   | Vfloat f, Tfloat F64 _ => Some (negb(Float.cmp Ceq f Float.zero))
   | Vsingle f, Tfloat F32 _ => Some (negb(Float32.cmp Ceq f Float32.zero))
   | _, _ => None
   end.

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).

Definition eval_unop (op: Cop.unary_operation) (t1 : type) :=
       force_val1 (Cop2.sem_unary_operation op t1).

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
       force_val2 (Cop2.sem_binary_operation'  op t1 t2).
Arguments eval_binop CS op t1 t2 / v1 v2.

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).
Arguments eval_cast t1 t2 / v.

Definition force_ptr (v: val) : val :=
              match v with Vptr l ofs => v | _ => Vundef  end.

Definition always {A B: Type} (b: B) (a: A) := b.

Definition offset_val (ofs: Z) (v: val) : val :=
  match v with
  | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr ofs))
  | _ => Vundef
 end.

Definition eval_field {CS: compspecs} (ty: type) (fld: ident) : val -> val :=
          match ty with
             | Tstruct id att =>
                 match cenv_cs ! id with
                 | Some co =>
                         match field_offset cenv_cs fld (co_members co) with
                         | Errors.OK delta => offset_val delta
                         | _ => always Vundef
                         end
                 | _ => always Vundef
                 end
             | Tunion id att =>
                 match cenv_cs ! id with
                 | Some co => force_ptr
                 | _ => always Vundef
                 end
             | _ => always Vundef
          end.

Definition eval_var (id:ident) (ty: type) (rho: environ) : val :=
                         match Map.get (ve_of rho) id with
                         | Some (b,ty') => if eqb_type ty ty'
                                                    then Vptr b Ptrofs.zero
                                                    else Vundef
                         | None =>
                            match (ge_of rho) id with
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
 | Esizeof t ty => `(Vptrofs (Ptrofs.repr (sizeof t)))
 | Ealignof t ty => `(Vptrofs (Ptrofs.repr (alignof t)))
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
| tc_test_eq': expr -> expr -> tc_assert
| tc_test_order': expr -> expr -> tc_assert
| tc_ilt': expr -> int -> tc_assert
| tc_llt': expr -> int64 -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover': expr -> expr -> tc_assert
| tc_initialized: PTree.elt -> type -> tc_assert
| tc_nosignedover: (Z->Z->Z) -> expr -> expr -> tc_assert.

Definition tc_noproof := tc_FF miscellaneous_typecheck_error.

Definition tc_iszero {CS: compspecs} (e: expr) : tc_assert :=
  match eval_expr e any_environ with
  | Vint i => if Int.eq i Int.zero then tc_TT else tc_FF (pp_compare_size_0 Tvoid)
  | Vlong i => if Int64.eq (Int64.repr (Int64.unsigned i)) Int64.zero then tc_TT else tc_FF (pp_compare_size_0 Tvoid)
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

Definition range_s32 (i: Z) : bool := 
   andb (Z.leb Int.min_signed i) (Z.leb i Int.max_signed).

Definition range_s64 (i: Z) : bool := 
   andb (Z.leb Int64.min_signed i) (Z.leb i Int64.max_signed).

Definition if_expr_signed (e: expr) (tc: tc_assert) : tc_assert :=
 match typeof e with
 | Tint _ Signed _ => tc
 | Tlong Signed _ => tc
 | _ => tc_TT
 end.

Definition tc_nobinover (op: Z->Z->Z) {CS: compspecs} (e1 e2: expr) : tc_assert :=
 if_expr_signed e1
 match eval_expr e1 any_environ, eval_expr e2 any_environ with
 | Vint n1, Vint n2 => 
    if range_s32 (op (Int.signed n1) (Int.signed n2))
     then tc_TT else tc_nosignedover Z.add e1 e2
 | Vlong n1, Vlong n2 => 
    if range_s64 (op (Int64.signed n1) (Int64.signed n2))
     then tc_TT else tc_nosignedover op e1 e2
 | Vint n1, Vlong n2 =>
    if range_s64 (op (Int.signed n1) (Int64.signed n2))
     then tc_TT else tc_nosignedover op e1 e2
 | Vlong n1, Vint n2 =>
    if range_s64 (op (Int64.signed n1) (Int.signed n2))
     then tc_TT else tc_nosignedover op e1 e2
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

Definition intptr_t := if Archi.ptr64 then Tlong Unsigned noattr else Tint I32 Unsigned noattr.

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
                               (tc_bool (is_int32_type ty) reterr))
			        (tc_bool (negb (Z.eqb (sizeof t) 0))
                                      (pp_compare_size_0 t)))
                                 (tc_bool (complete_type cenv_cs t) reterr))
                                   (tc_bool (Z.leb (sizeof t) Int.max_signed)
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
                       (check_pp_int a1 (Ecast a2 intptr_t) op ty e)
              | Cop.cmp_case_ip si => 
                     tc_andp (tc_int_or_ptr_type (typeof a2))
                    (check_pp_int (Ecast a1 intptr_t) a2 op ty e)
              | Cop.cmp_case_pl => 
                     tc_andp (tc_int_or_ptr_type (typeof a1))
                       (check_pp_int a1 (Ecast a2 intptr_t) op ty e)
              | Cop.cmp_case_lp => 
                     tc_andp (tc_int_or_ptr_type (typeof a2))
                    (check_pp_int (Ecast a1 intptr_t) a2 op ty e)
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
           (if orb  (andb (is_pointer_type tto) (is_pointer_type tfrom))
                       (if Archi.ptr64
                        then (andb (is_long_type tto) (is_long_type tfrom)) 
                        else (andb (is_int_type tto) (is_int_type tfrom)))
              then tc_TT
              else tc_iszero a)
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
| _ => match tto with
      | Tint _ _ _  => tc_bool (is_int_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F64 _  => tc_bool (is_anyfloat_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F32 _  => tc_bool (is_anyfloat_type tfrom) (invalid_cast_result tto tto)
      | _ => tc_FF (invalid_cast tfrom tto)
      end
end.

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

Definition is_long (v: val) :=
 match v with Vlong i => True | _ => False end.
Definition is_float (v: val) :=
 match v with Vfloat i => True | _ => False end.
Definition is_single (v: val) :=
 match v with Vsingle i => True | _ => False end.

Definition is_pointer_or_null (v: val) :=
 match v with
 | Vint i => if Archi.ptr64 then False else  i = Int.zero
 | Vlong i => if Archi.ptr64 then i=Int64.zero else False
 | Vptr _ _ => True
 | _ => False
 end.

Definition is_pointer_or_integer (v: val) :=
 match v with
 | Vint i => if Archi.ptr64 then False else True
 | Vlong i => if Archi.ptr64 then True else False
 | Vptr _ _ => True
 | _ => False
 end.

Definition isptr v :=
   match v with | Vptr _ _ => True | _ => False end.

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

Definition get_var_type (Delta : tycontext) id : option type :=
match (var_types Delta) ! id with
| Some ty => Some ty
| None => match (glob_types Delta) ! id with
         | Some g => Some g
         | None => None
           end
end.

Definition same_base_type t1 t2 : bool :=
match t1, t2 with
| (Tarray _ _ _ | Tfunction _ _ _),
   (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => 
     eqb (eqb_type t1 int_or_ptr_type)
         (eqb_type t2 int_or_ptr_type)
| (Tstruct _ _ | Tunion _ _), (Tstruct _ _ | Tunion _ _ ) => true
| _, _ => false
end.

(** Main typechecking function, with work will typecheck both pure
and non-pure expressions, for now mostly just works with pure expressions **)

Fixpoint typecheck_expr {CS: compspecs}(Delta : tycontext) (e: expr) : tc_assert :=
let tcr := typecheck_expr Delta in
match e with
 | Econst_int _ (Tint I32 _ _) => tc_TT
 | Econst_float _ (Tfloat F64 _) => tc_TT
 | Econst_single _ (Tfloat F32 _) => tc_TT
 | Etempvar id ty =>
                       match (temp_types Delta)!id with
                         | Some ty' => if is_neutral_cast (fst ty') ty || same_base_type (fst ty') ty then
                                         if (snd ty') then tc_TT else (tc_initialized id ty)
                                       else tc_FF (mismatch_context_type ty (fst ty'))
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
                               match cenv_cs ! id with
                               | Some co =>
                                  match field_offset cenv_cs i (co_members co) with
                                  | Errors.OK delta => tc_TT
                                  | _ => tc_FF (invalid_struct_field i id)
                                  end
                               | _ => tc_FF (invalid_composite_name id)
                               end
                            | Tunion id att =>
                               match cenv_cs ! id with
                               | Some co => tc_TT
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
                     (tc_bool (eqb_type t (Tint I32 Unsigned noattr)) (invalid_expression e))
 | Ealignof ty t => tc_andp (tc_bool (complete_type cenv_cs ty) (invalid_expression e))
                     (tc_bool (eqb_type t (Tint I32 Unsigned noattr)) (invalid_expression e))
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
                              match cenv_cs ! id with
                              | Some co =>
                                   match field_offset cenv_cs i (co_members co) with
                                     | Errors.OK delta => tc_TT
                                     | _ => tc_FF (invalid_struct_field i id)
                                   end
                              | _ => tc_FF (invalid_composite_name id)
                              end
                            | Tunion id att =>
                              match cenv_cs ! id with
                              | Some co => tc_TT
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
  match (temp_types Delta)!id with
  | Some (t,_) =>
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

(** Environment typechecking functions **)

Definition typecheck_temp_environ
(te: tenviron) (tc: PTree.t (type * bool)) :=
forall id b ty , tc ! id = Some (ty,b) -> exists v, (Map.get te id = Some v /\ ((is_true (negb b)) \/ tc_val ty v)).

Definition typecheck_var_environ
(ve: venviron) (tc: PTree.t type) :=
forall id ty, tc ! id = Some (ty) <-> exists v, Map.get ve id = Some(v,ty).

Definition typecheck_glob_environ
(ge: genviron) (tc: PTree.t type) :=
forall id  t,  tc ! id = Some t ->
(exists b, ge id = Some b).

Definition same_env (rho:environ) (Delta:tycontext)  :=
forall id t, (glob_types Delta) ! id = Some t ->
  (ve_of rho) id = None
  \/ exists t,  (var_types Delta) ! id = Some t.

(*
Definition specs_types (Delta: tycontext) :=
  forall id s, (glob_specs Delta) ! id = Some s ->
                (glob_types Delta) ! id = Some (type_of_funspec s).
*)
(*
Definition same_mode (ge: genviron) (ve:venviron)
                     (gt : PTree.t global_spec) (vt : PTree.t type) id  :=
match (vt ! id), (gt ! id), ve id  with
| None, Some _, Some _ => false
| _, _, _  => true
end.

Fixpoint same_env  (rho : environ) (Delta : tycontext) (ids : list positive) : bool :=
match ids with
| h::t => same_mode (ge_of rho) (ve_of rho) (glob_types Delta) (var_types Delta) h && same_env rho Delta t
| nil => true
end.

Definition all_var_ids (Delta : tycontext) : list positive :=
(fst (split (PTree.elements (glob_types Delta)))).
*)

Definition typecheck_environ (Delta: tycontext)  (rho : environ) :=
typecheck_temp_environ (te_of rho) (temp_types Delta) /\
typecheck_var_environ  (ve_of rho) (var_types Delta) /\
typecheck_glob_environ (ge_of rho) (glob_types Delta) /\
same_env rho Delta.

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
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     eval_expr e rho = eval_expr e (mkEnviron (ge_of rho) (ve_of rho) te').

Definition lvalue_closed_wrt_vars {CS: compspecs}(S: ident -> Prop) (e: expr) : Prop :=
  forall rho te',
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     eval_lvalue e rho = eval_lvalue e (mkEnviron (ge_of rho) (ve_of rho) te').

Definition env_set (rho: environ) (x: ident) (v: val) : environ :=
  mkEnviron (ge_of rho) (ve_of rho) (Map.set x v (te_of rho)).

Lemma eval_id_same: forall rho id v, eval_id id (env_set rho id v) = v.
Proof. unfold eval_id; intros; simpl. unfold force_val. rewrite Map.gss. auto.
Qed.
Hint Rewrite eval_id_same : normalize.

Lemma eval_id_other: forall rho id id' v,
   id<>id' -> eval_id id' (env_set rho id v) = eval_id id' rho.
Proof.
 unfold eval_id, force_val; intros. simpl. rewrite Map.gso; auto.
Qed.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : normalize.

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
simple_if_tac; auto; intuition;
destruct c; auto; intuition.
Qed.

Lemma int_eq_e: forall i j, Int.eq i j = true -> i=j.
Proof. intros. pose proof (Int.eq_spec i j); rewrite H in H0; auto. Qed.

Lemma two_p_neg:
 forall n, n<0 -> two_p n = 0.
Proof.
destruct n; intros; simpl; auto; try omega.
pose proof (Zgt_pos_0 p); omega.
Qed.

Lemma testbit_signed_neg:
 forall i j n,
   - two_p n <= Int.signed i < 0 ->
    0 <= n <= j ->
    j < Int.zwordsize ->
   Int.testbit i j = true.
Proof.
intros. rename H1 into Wj.
pose proof (Int.unsigned_range i).
unfold Int.signed in H.
if_tac in H. omega.
unfold Int.testbit.
forget (Int.unsigned i) as i'; clear i; rename i' into i.
rewrite <- (Z2Nat.id j) in * by omega.
unfold Int.half_modulus in *.
unfold Int.modulus in *.
unfold Int.zwordsize in Wj.
forget Int.wordsize as W.
assert (Z.to_nat j < W)%nat by (apply Nat2Z.inj_lt; auto).
clear Wj.
assert (W = Z.to_nat j + 1 + (W-Z.to_nat j-1))%nat by omega.
forget (W - Z.to_nat j - 1)%nat as K.
subst W.

clear H3.
rewrite <- (Z2Nat.id n) in H by omega.
rewrite <- (Z2Nat.id n) in H0 by omega.
rewrite <- two_power_nat_two_p in H.
assert (Z.to_nat n <= Z.to_nat j)%nat.
  apply Nat2Z.inj_le; omega.
clear H0.
forget (Z.to_nat n) as n'; clear n; rename n' into n.
forget (Z.to_nat j) as j'; clear j; rename j' into j.
destruct H as [H _].
revert n i H3 H2 H  H1; induction j; intros.
*
simpl (Z.of_nat) in *.
assert (n=0)%nat by omega. subst n.
simpl plus in *. clear H3.
change (- two_power_nat 0) with (-1) in H.
assert (i = (two_power_nat (S K) - 1)) by omega. subst i.
rewrite two_power_nat_S.
clear.
forget (two_power_nat K) as A.
replace A with ((A-1)+1) by omega.
rewrite Z.mul_add_distr_l.
replace (2 * (A - 1) + 2 * 1 - 1) with (2 * (A - 1) + 1) by omega.
apply Z.testbit_odd_0.
*
destruct n.
change (- two_power_nat 0)%Z with (-1) in H.
assert (i = two_power_nat (S j + 1 + K) - 1) by omega.
clear H H1 H2.
subst i.
replace (two_power_nat (S j + 1 + K) - 1) with (Z.ones (Z.of_nat (S j + 1 + K))).
apply Z.ones_spec_low. split; [omega | ].
apply Nat2Z.inj_lt. omega.
rewrite Z.ones_equiv.
rewrite two_power_nat_equiv.
omega.
rewrite inj_S.
rewrite Int.Ztestbit_succ by omega.
apply (IHj n); clear IHj.
+
omega.
+
rewrite Zdiv2_div.
apply Z_div_ge; try omega.
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H2 by omega.
rewrite two_power_nat_S in H2.
rewrite Z.mul_comm in H2.
rewrite Z_div_mult_full in H2 by omega. auto.
+
rewrite two_power_nat_S in H.
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H by omega.
rewrite two_power_nat_S in H.
rewrite (Zdiv2_odd_eqn i) in H.
destruct (Z.odd i) eqn:?H; omega.
+
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H1 by omega.
rewrite two_power_nat_S in H1.
rewrite (Zdiv2_odd_eqn i) in H1.
destruct (Z.odd i) eqn:?H; omega.
Qed.

Lemma sign_ext_inrange:
  forall n i, - two_p (n-1) <= Int.signed i <= two_p (n-1) - 1 ->
       Int.sign_ext n i = i.
Proof.
intros.
destruct (zlt n Int.zwordsize);
  [ | apply Int.sign_ext_above; auto].
destruct (zlt n 0).
assert (n-1 < 0) by omega.
repeat rewrite two_p_neg in H by omega.
omega.
destruct (zeq n 0).
subst n. simpl in H.
assert (Int.signed i = 0) by omega.
clear - H0.
rewrite <- (Int.repr_signed i).
rewrite H0. reflexivity.
assert (0 < n < Int.zwordsize) by omega.
clear - H H0.

apply Int.same_bits_eq; intros j ?.
destruct H0.
rewrite (Int.bits_sign_ext n i j H1 H0).
if_tac; auto.
destruct H1.
destruct (zlt (Int.signed i) 0).
* (* negative *)
assert (- two_p (n - 1) <= Int.signed i  < 0) by omega.
clear H.
rewrite (testbit_signed_neg i (n-1) (n-1)); auto; try omega.
rewrite (testbit_signed_neg i j (n-1)); auto; omega.
* (* nonnegative *)
rewrite Int.signed_eq_unsigned in H by (apply Int.signed_positive; auto).
unfold Int.testbit in *.
transitivity false.
apply (Int.Ztestbit_above (Z.to_nat (n-1))).
rewrite two_power_nat_two_p.
rewrite Z2Nat.id by omega.
pose proof (Int.unsigned_range i).
omega.
rewrite Z2Nat.id by omega.
omega.
symmetry.
apply (Int.Ztestbit_above (Z.to_nat (n-1))).
rewrite two_power_nat_two_p.
rewrite Z2Nat.id by omega.
pose proof (Int.unsigned_range i).
omega.
rewrite Z2Nat.id by omega.
omega.
Qed.

Lemma zero_ext_inrange:
  forall n i, Int.unsigned i <= two_p n - 1 ->
       Int.zero_ext n i = i.
Proof.
intros.
destruct (zlt n Int.zwordsize);
  [ | apply Int.zero_ext_above; auto].
destruct (zlt n 0).
assert (n-1 < 0) by omega.
repeat rewrite two_p_neg in H by omega.
pose proof (Int.unsigned_range i).
omega.
destruct (zeq n 0).
subst n. simpl in H.
assert (Int.unsigned i = 0) by (pose proof (Int.unsigned_range i); omega).
clear - H0.
rewrite <- (Int.repr_unsigned i).
rewrite H0. reflexivity.
assert (0 < n < Int.zwordsize) by omega.
clear - H H0.
apply Int.same_bits_eq; intros j ?.
rewrite (Int.bits_zero_ext n i j) by omega.
if_tac; auto.
symmetry.
unfold Int.testbit.
apply (Int.Ztestbit_above (Z.to_nat n));
 [ | rewrite Z2Nat.id by omega; omega].
rewrite two_power_nat_two_p.
rewrite Z2Nat.id by omega.
pose proof (Int.unsigned_range i); omega.
Qed.

Program Definition valid_pointer' (p: val) (d: Z) : mpred :=
 match p with
 | Vint i => if Archi.ptr64 then FF else prop (i = Int.zero)
 | Vlong i => if Archi.ptr64 then prop (i=Int64.zero) else FF
 | Vptr b ofs =>
  fun m =>
    match m @ (b, Ptrofs.unsigned ofs + d) with
    | YES _ _ _ pp => True
    | NO sh _ => nonidentity sh
    | _ => False
    end
 | _ => FF
 end.
Next Obligation.
split; intros; congruence.
Qed.
Next Obligation.
hnf; simpl; intros.
destruct (a@(b,Ptrofs.unsigned ofs + d)) eqn:?; try contradiction.
rewrite (necR_NO a a') in Heqr.
rewrite Heqr; auto.
constructor; auto.
subst.
apply (necR_YES a a') in Heqr; [ | constructor; auto].
rewrite Heqr.
auto.
Qed.
Next Obligation.
split3; intros; congruence.
Qed.
Next Obligation.
split3; intros; congruence.
Qed.
Next Obligation.
split3; intros; congruence.
Qed.

Definition valid_pointer (p: val) : mpred :=
 (valid_pointer' p 0).

Definition weak_valid_pointer (p: val) : mpred :=
 orp (valid_pointer' p 0) (valid_pointer' p (-1)).
