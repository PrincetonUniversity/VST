Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.tycontext.
Require Import veric.Clight_lemmas.
Require Export veric.lift.
Require Export veric.Cop2.

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

Definition eqb_ident : ident -> ident -> bool := Peqb.

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

(** Functions for evaluating expressions in environments, 
these return vundef if something goes wrong, meaning they always return some value **)

Definition strict_bool_val (v: val) (t: type) : option bool :=
   match v, t with
   | Vint n, Tint _ _ _ => Some (negb (Int.eq n Int.zero))
   | Vlong n, Tlong _ _ => Some (negb (Int64.eq n Int64.zero))
   | (Vint n), (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
             if Int.eq n Int.zero then Some false else None
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

Definition true2 (b : block) (i : Z) := true.

Definition eval_binop {CS:compspecs} (op: Cop.binary_operation) (t1 t2 : type) :=
       force_val2 (Cop2.sem_binary_operation'  op t1 t2 true2).
Arguments eval_binop CS op t1 t2 / v1 v2.

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).
Arguments eval_cast t1 t2 / v.

Definition force_ptr (v: val) : val :=
              match v with Vptr l ofs => v | _ => Vundef  end.

Definition always {A B: Type} (b: B) (a: A) := b.

Definition offset_val (ofs: int) (v: val) : val :=
  match v with
  | Vptr b z => Vptr b (Int.add z ofs)
  | _ => Vundef
 end.

Definition eval_field {CS: compspecs} (ty: type) (fld: ident) : val -> val :=
          match ty with
             | Tstruct id att =>
                 match cenv_cs ! id with
                 | Some co =>
                         match field_offset cenv_cs fld (co_members co) with 
                         | Errors.OK delta => offset_val (Int.repr delta)
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
                                                    then Vptr b Int.zero
                                                    else Vundef
                         | None => 
                            match (ge_of rho) id with
                            | Some b => Vptr b Int.zero
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
 | Evar id ty => `(deref_noload ty) (eval_var id ty)
 | Ederef a ty => `(deref_noload ty) (`force_ptr (eval_expr a))
 | Efield a i ty => `(deref_noload ty) (`(eval_field (typeof a) i) (eval_lvalue a))
 | Esizeof t ty => `(Vint (Int.repr (sizeof cenv_cs t)))
 | Ealignof t ty => `(Vint (Int.repr (alignof cenv_cs t)))
 end

 with eval_lvalue {CS: compspecs} (e: expr) : environ -> val := 
 match e with 
 | Evar id ty => eval_var id ty
 | Ederef a ty => `force_ptr (eval_expr a)
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
  | Tint _ _ _ | Tlong _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tfloat _ _ => true
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

Definition is_pointer_type ty :=
match ty with
| (Tpointer _ _ | Tarray _ _ _ 
                   | Tfunction _ _ _ | Tstruct _ _ 
                   | Tunion _ _) => true
| _ => false
end.

Inductive tc_error :=
| op_result_type : expr -> tc_error
| arg_type : expr -> tc_error
| pp_compare_size_0 : type -> tc_error
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
| wrong_signature : tc_error.

Inductive tc_assert :=
| tc_FF: tc_error -> tc_assert
| tc_noproof : tc_assert
| tc_TT : tc_assert
| tc_andp': tc_assert -> tc_assert -> tc_assert
| tc_orp' : tc_assert -> tc_assert -> tc_assert
| tc_nonzero': expr -> tc_assert
| tc_iszero': expr -> tc_assert
| tc_isptr: expr -> tc_assert
| tc_comparable': expr -> expr -> tc_assert
| tc_ilt': expr -> int -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover': expr -> expr -> tc_assert
| tc_initialized: PTree.elt -> type -> tc_assert.

Definition tc_iszero {CS: compspecs} (e: expr) : tc_assert :=
  match eval_expr e any_environ with
  | Vint i => if Int.eq i Int.zero then tc_TT else tc_FF (pp_compare_size_0 Tvoid)
  | Vlong i => if Int.eq (Int.repr (Int64.unsigned i)) Int.zero then tc_TT else tc_FF (pp_compare_size_0 Tvoid)
  | _ => tc_iszero' e
  end.

Definition tc_nonzero {CS: compspecs} (e: expr) : tc_assert :=
  match eval_expr e any_environ with
   | Vint i => if negb (Int.eq i Int.zero) then tc_TT else tc_nonzero' e
   | _ => tc_nonzero' e
   end.

Definition tc_comparable {CS: compspecs} (e1 e2: expr) : tc_assert :=
 match eval_expr e1 any_environ, eval_expr e2 any_environ with
 | Vint i, Vint j => if andb (Int.eq i Int.zero) (Int.eq j Int.zero) 
                             then tc_TT else tc_comparable' e1 e2
 | _, _ => tc_comparable' e1 e2
 end.

Definition tc_nodivover {CS: compspecs} (e1 e2: expr) : tc_assert :=
 match eval_expr e1 any_environ, eval_expr e2 any_environ with
                           | Vint n1, Vint n2 => if (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone))
                                     then tc_TT else tc_nodivover' e1 e2
                           | _ , _ => tc_nodivover' e1 e2
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
| Cop.Oeq | Cop.One => tc_andp 
                         (tc_comparable e1 e2)
                         (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.

(*
Definition check_pl_long (Delta: tycontext) e2 op t e :=
match op with 
| Cop.Oeq | Cop.One => tc_andp 
                         (tc_comparable Delta e2)
                         (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.
*)

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

Definition isUnOpResultType {CS: compspecs} op a ty : tc_assert := 
match op with 
  | Cop.Onotbool => match Cop.classify_bool (typeof a) with
                        | Cop.bool_default => tc_FF (op_result_type a)
                        | Cop.bool_case_p => 
                           tc_andp (tc_bool (is_int_type ty) (op_result_type a))
                                         (tc_comparable a (Econst_int Int.zero (Tint I32 Signed noattr)))
                        | _ => tc_bool (is_int_type ty) (op_result_type a)
                        end
  | Cop.Onotint => match Cop.classify_notint (typeof a) with
                        | Cop.notint_default => tc_FF (op_result_type a)
                        | Cop.notint_case_i _ => tc_bool (is_int32_type ty) (op_result_type a)
                        | Cop.notint_case_l _ => tc_bool (is_long_type ty) (op_result_type a)
                        end
  | Cop.Oneg => match Cop.classify_neg (typeof a) with
                    | Cop.neg_case_i sg => tc_bool (is_int32_type ty) (op_result_type a)
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

Definition isBinOpResultType {CS: compspecs} op a1 a2 ty : tc_assert :=
let e := (Ebinop op a1 a2 ty) in
let reterr := op_result_type e in
let deferr := arg_type e in 
match op with
  | Cop.Oadd => match Cop.classify_add (typeof a1) (typeof a2) with 
                    | Cop.add_case_pi t => tc_andp (tc_andp (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_ip t => tc_andp (tc_andp (tc_isptr a2)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_pl t => tc_andp (tc_andp (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_lp t => tc_andp (tc_andp (tc_isptr a2)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_default => binarithType (typeof a1) (typeof a2) ty deferr reterr
            end
  | Cop.Osub => match Cop.classify_sub (typeof a1) (typeof a2) with 
                    | Cop.sub_case_pi t => tc_andp (tc_andp (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pl t => tc_andp (tc_andp (tc_isptr a1)
                                           (tc_bool (complete_type cenv_cs t) reterr))
                                            (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pp t =>  (*tc_isptr may be redundant here*)
                             tc_andp (tc_andp (tc_andp (tc_andp (tc_andp (tc_andp (tc_samebase a1 a2)
                             (tc_isptr a1))
                              (tc_isptr a2))
                               (tc_bool (is_int32_type ty) reterr))
			        (tc_bool (negb (Int.eq (Int.repr (sizeof cenv_cs t)) Int.zero)) 
                                      (pp_compare_size_0 t)))
                                 (tc_bool (complete_type cenv_cs t) reterr))
                                  (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_default => binarithType (typeof a1) (typeof a2) ty deferr reterr
            end 
  | Cop.Omul => binarithType (typeof a1) (typeof a2) ty deferr reterr
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
                    (* NEED TO HANDLE OTHER SHIFT CASES *)
                    | _ => tc_FF deferr
                   end
  | Cop.Oand | Cop.Oor | Cop.Oxor => 
                   match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i _ =>tc_bool (is_int32_type ty) reterr
                    (* NEED TO HANDLE OTHER BIN CASES *)
                    | _ => tc_FF deferr
                   end   
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => 
                   match Cop.classify_cmp (typeof a1) (typeof a2) with
                    | Cop.cmp_default => 
                           tc_bool (is_numeric_type (typeof a1) 
                                         && is_numeric_type (typeof a2)
                                          && is_int_type ty)
                                             deferr
		    | Cop.cmp_case_pp => check_pp_int a1 a2 op ty e
                    | Cop.cmp_case_pl => check_pp_int (Ecast a1 (Tint I32 Unsigned noattr)) a2 op ty e
                    | Cop.cmp_case_lp => check_pp_int (Ecast a2 (Tint I32 Unsigned noattr)) a1 op ty e
                   end
  end.

Definition isCastResultType {CS: compspecs} tfrom tto a : tc_assert :=
  (* missing casts from f2s and s2f *)
match Cop.classify_cast tfrom tto with
| Cop.cast_case_default => tc_FF (invalid_cast tfrom tto)
| Cop.cast_case_f2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed)
| Cop.cast_case_s2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed)  
| Cop.cast_case_f2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned) 
| Cop.cast_case_s2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_i2l _ => tc_bool (is_int_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_neutral  => if eqb_type tfrom tto then tc_TT else 
                            (if orb  (andb (is_pointer_type tto) (is_pointer_type tfrom)) (andb (is_int_type tto) (is_int_type tfrom)) then tc_TT
                                else tc_iszero a)
| Cop.cast_case_l2l => tc_bool (is_long_type tfrom && is_long_type tto) (invalid_cast_result tto tto)
| Cop.cast_case_void => tc_noproof
| Cop.cast_case_f2bool => tc_bool (is_float_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_s2bool => tc_bool (is_single_type tfrom) (invalid_cast_result tfrom tto)
| Cop.cast_case_p2bool => tc_bool (is_int_type tfrom) (invalid_cast_result tfrom tto)
      (* before CompCert 2.5: tc_bool (orb (is_int_type tfrom) (is_pointer_type tfrom)) (invalid_cast_result tfrom tto) *)
| Cop.cast_case_l2bool => tc_bool (is_long_type tfrom) (invalid_cast_result tfrom tto)
| _ => match tto with 
      | Tint _ _ _  => tc_bool (is_int_type tfrom) (invalid_cast_result tto tto) 
      | Tfloat F64 _  => tc_bool (is_float_type tfrom) (invalid_cast_result tto tto)
      | Tfloat F32 _  => tc_bool (is_single_type tfrom) (invalid_cast_result tto tto)
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
 | Vint i => i = Int.zero
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
 | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ => is_pointer_or_null
 | Tstruct _ _ => isptr
 | Tunion _ _ => isptr
 | _ => fun _ => False
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
 | Tpointer _ _, Tpointer _ _ => true
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
| (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _), 
   (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => true
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

Definition typecheck_val (v: val) (ty: type) : bool :=
 match v, ty with
 | Vint i, Tint sz sg _ => 
  match v with
  | Vint i => 
    match sz, sg with
    | I8, Signed => andb (Z.leb Byte.min_signed (Int.signed i))
                                      (Z.leb (Int.signed i) Byte.max_signed)
    | I8, Unsigned => Z.leb (Int.unsigned i) Byte.max_unsigned
    | I16, Signed => andb (Z.leb (-two_p (16-1)) (Int.signed i))
                                        (Z.leb (Int.signed i) (two_p (16-1) -1))
    | I16, Unsigned => Z.leb (Int.unsigned i) (two_p 16 - 1)
    | I32, _ => true
    | IBool, _ => orb (Int.eq i Int.zero) (Int.eq i Int.one)
    end
  | _ => false
  end
 | Vlong i, Tlong _ _ => true
 | Vfloat v, Tfloat F64 _ => true  
 | Vsingle v, Tfloat F32 _ => true  
 | Vint i, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) => 
                    (Int.eq i Int.zero) 
(* | Vlong i, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tcomp_ptr _ _) => 
                    (Int64.eq i Int64.zero)  *)
 | Vptr b z,  (Tpointer _ _ | Tarray _ _ _ 
                   | Tfunction _ _ _ | Tstruct _ _ | Tunion _ _) => true
 | Vundef, _ => false
 | _, _ => false
 end.

Fixpoint typecheck_vals (v: list val) (ty: list type) : bool :=
 match v, ty with
 | v1::vs , t1::ts => typecheck_val v1 t1 && typecheck_vals vs ts
 | nil, nil => true
 | _, _ => false
end.

(** Environment typechecking functions **)

Definition typecheck_temp_environ
(te: tenviron) (tc: PTree.t (type * bool)) :=
forall id b ty , tc ! id = Some (ty,b) -> exists v, (Map.get te id = Some v /\ ((is_true (negb b)) \/ (typecheck_val v ty) = true)). 

Definition typecheck_var_environ
(ve: venviron) (tc: PTree.t type) :=
forall id ty, tc ! id = Some (ty) <-> exists v, Map.get ve id = Some(v,ty).

Definition typecheck_glob_environ 
(ge: genviron) (tc: PTree.t type) :=
forall id  t,  tc ! id = Some t -> 
((exists b, 
(ge id = Some b /\ typecheck_val (Vptr b Int.zero) t = true))).

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

Definition match_fsig (fsig: funsig) (bl: list expr) (ret: option ident) : bool :=
  andb (match_fsig_aux bl (fst fsig))
          (match snd fsig, ret with 
            | Tvoid , None => true 
            | Tvoid, Some _ => false
            | _, None => false
            | _, Some _ => true
            end).

Lemma match_fsig_e: forall fsig bl ret,
  match_fsig fsig bl ret = true ->
  map typeof bl = map (@snd _ _) (fst fsig) /\ (snd fsig=Tvoid <-> ret=None).
Proof.
 intros.
 apply andb_true_iff in H.
 destruct H.
 split. clear H0.
 forget (fst fsig) as tl.
 revert tl H; induction bl; destruct tl; intros; inv H.
  reflexivity.
 destruct p.
 revert H1; case_eq (eqb_type (typeof a) t); intros.
 apply eqb_type_true in H. subst; simpl in *. f_equal; auto.
 inv H1.
 clear H.
 destruct (snd fsig); destruct ret; intuition congruence.
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
remember (b&&c). destruct b0; symmetry in Heqb0; try rewrite andb_true_iff in *; try rewrite andb_false_iff in *; if_tac; auto; intuition;
destruct c; auto; intuition.
Qed.

Lemma int_eq_e: forall i j, Int.eq i j = true -> i=j.
Proof. intros. pose proof (Int.eq_spec i j); rewrite H in H0; auto. Qed.

Lemma tc_val_eq: tc_val = fun t v => typecheck_val v t = true.
Proof.
extensionality t v.
unfold tc_val.
destruct t  as [ | [ | | | ] [ | ] | | [ | ] | | | | | ] , v; try reflexivity;
apply prop_ext; intuition; try apply I;
simpl in *; subst;
try apply Int.eq_true;
try solve [apply int_eq_e; auto];
try solve [try (rewrite andb_true_iff; split); rewrite <- Zle_is_le_bool; omega];
try solve [try (rewrite andb_true_iff in H; destruct H; split);
               rewrite -> Zle_is_le_bool; auto];
try solve [rewrite orb_true_iff; destruct H; [left | right]; subst; apply Int.eq_true];
try solve [rewrite orb_true_iff in H; destruct H; [left | right];  apply int_eq_e; auto].
Qed.

Lemma tc_val_eq':
  forall t v, (typecheck_val v t = true) =  tc_val t v.
Proof. intros. rewrite tc_val_eq. auto. Qed.

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
rewrite <- (Z2Nat.id n) in * by omega.
rewrite <- two_power_nat_two_p in H.
assert (Z.to_nat n <= Z.to_nat j)%nat.
apply Nat2Z.inj_le; omega. clear H0.
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
 | Vint i => prop (i = Int.zero)
 | Vptr b ofs =>
  fun m =>
    match m @ (b, Int.unsigned ofs + d) with
    | YES _ _ _ pp => True
    | NO sh => nonidentity sh
    | _ => False
    end
 | _ => FF
 end.
Next Obligation.
split; intros; congruence.
Qed.
Next Obligation.
hnf; simpl; intros.
destruct (a@(b,Int.unsigned ofs + d)) eqn:?; try contradiction.
rewrite (necR_NO a a') in Heqr.
rewrite Heqr; auto.
constructor; auto.
subst.
apply (necR_YES a a') in Heqr; [ | constructor; auto].
rewrite Heqr.
auto.
Qed.
Next Obligation.
split; intros; congruence.
Qed.
Next Obligation.
split; intros; congruence.
Qed.
Next Obligation.
split; intros; congruence.
Qed.
Next Obligation.
split; intros; congruence.
Qed.

Definition valid_pointer (p: val) : mpred :=
 (valid_pointer' p 0).

Definition weak_valid_pointer (p: val) : mpred :=
 orp (valid_pointer' p 0) (valid_pointer' p (-1)).
