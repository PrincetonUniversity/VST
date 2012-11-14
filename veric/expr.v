Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.

Definition test := true.
Definition any_environ : environ :=
 (* Mainly for use in demonstrating that the environ type is inhabited *)
  mkEnviron (fun _ => None)  (Map.empty _) (Map.empty _).

Definition lift0 {B} (P: B) : environ -> B := fun _ => P.
Definition lift1 {A1 B} (P: A1 -> B) (f1: environ -> A1) : environ -> B := fun rho => P (f1 rho).
Definition lift2 {A1 A2 B} (P: A1 -> A2 -> B) (f1: environ -> A1) (f2: environ -> A2): 
   environ -> B := fun rho => P (f1 rho) (f2 rho).

(* Make a completely computational version of type_eq *)

Definition eqb_attr (a b: attr) : bool :=
 match a, b with
 | mk_attr av, mk_attr bv => eqb av bv
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

Fixpoint eqb_type (a b: type) {struct a} : bool :=
 match a, b with
 | Tvoid, Tvoid => true
 | Tint ia sa aa, Tint ib sb ab => andb (eqb_intsize ia ib) 
                                                    (andb (eqb_signedness sa sb) (eqb_attr aa ab))
 | Tfloat sa aa, Tfloat sb ab => andb (eqb_floatsize sa sb) (eqb_attr aa ab)
 | Tpointer ta aa, Tpointer tb ab => andb (eqb_type ta tb) (eqb_attr aa ab)
 | Tarray ta sa aa, Tarray tb sb ab => andb (eqb_type ta tb) 
                                                                   (andb (Zeq_bool sa sb) (eqb_attr aa ab))
 | Tfunction sa ta, Tfunction sb tb => andb (eqb_typelist sa sb) (eqb_type ta tb)
 | Tstruct ia fa aa, Tstruct ib fb ab => andb (eqb_ident ia ib) 
                                                                  (andb (eqb_fieldlist fa fb) (eqb_attr aa ab))
 | Tunion ia fa aa, Tunion ib fb ab => andb (eqb_ident ia ib) 
                                                                  (andb (eqb_fieldlist fa fb) (eqb_attr aa ab))
 | Tcomp_ptr ia aa, Tcomp_ptr ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | _, _ => false
 end
with eqb_typelist (a b: typelist)  {struct a}: bool :=
  match a, b with
  | Tcons ta ra, Tcons tb rb => andb (eqb_type ta tb) (eqb_typelist ra rb)
  | Tnil, Tnil => true
  | _ , _ => false
  end
with eqb_fieldlist (a b: fieldlist)  {struct a}: bool :=
  match a, b with
  | Fcons ia ta ra, Fcons ib tb rb =>  andb (eqb_ident ia ib) 
                                                             (andb (eqb_type ta tb) (eqb_fieldlist ra rb))
  | Fnil, Fnil => true
  | _ , _ => false
  end.

Lemma eqb_type_true: forall a b, eqb_type a b = true -> a=b.
Admitted.

Lemma eqb_type_refl: forall a, eqb_type a a = true. 
Proof.
Admitted.

(*Functions for evaluating expressions in environments, 
these return vundef if something goes wrong, meaning they always return some value*)

Definition strict_bool_val (v: val) (t: type) : option bool :=
   match v, t with
   | Vint n, Tint _ _ _ => Some (negb (Int.eq n Int.zero))
   | Vint n, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) =>
             if Int.eq n Int.zero then Some false else None
   | Vptr b ofs, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => Some true
   | Vfloat f, Tfloat sz _ => Some (negb(Float.cmp Ceq f Float.zero))
   | _, _ => None
   end.

Lemma strict_bool_val_sub : forall v t b, 
strict_bool_val v t = Some b ->
bool_val v t = Some b.
Proof.
intros. destruct v; destruct t; simpl in *; auto; try if_tac in H; auto; try congruence.
Qed.

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).

Definition eval_cast (t t': type) (v: val) : val := force_val (sem_cast v t t').

Definition eval_unop (op: unary_operation) (t1 : type) (v1 : val) :=
       force_val (sem_unary_operation op v1 t1).

Definition eval_binop (op: binary_operation) (t1 t2 : type) (v1 v2: val) :=
       force_val (sem_binary_operation op v1 t1 v2 t2 (fun _ _ => false)).

Definition force_ptr (v: val) : val :=
              match v with Vptr l ofs => v | _ => Vundef  end.

Definition eval_struct_field (delta: Z) (v: val) : val :=
          match v with
             | Vptr l ofs => Vptr l (Int.add ofs (Int.repr delta))
             | _ => Vundef
          end.

Definition eval_field (ty: type) (fld: ident) (v: val) : val :=
          match ty with
             | Tstruct id fList att =>
                         match field_offset fld fList with 
                         | Errors.OK delta => eval_struct_field delta v
                         | _ => Vundef
                        end
             | Tunion id fList att => force_ptr v
             | _ => Vundef
          end.

Definition eval_var (id:ident) (ty: type) (rho: environ) : val := 
                         match Map.get (ve_of rho) id with
                         | Some (b,ty') => if eqb_type ty ty'
                                                    then if negb (type_is_volatile ty')
                                                       then Vptr b Int.zero else Vundef
                                                    else Vundef
                         | None => 
                            match (ge_of rho) id with
                            | Some (v,ty') => if eqb_type ty ty' then v else Vundef
                            | None => Vundef
                            end
                        end.

Fixpoint eval_expr (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => lift0 (Vint i)
 | Econst_float f ty => lift0 (Vfloat f)
 | Etempvar id ty => eval_id id 
 | Eaddrof a ty => eval_lvalue a 
 | Eunop op a ty =>  lift1 (eval_unop op (typeof a)) (eval_expr a) 
 | Ebinop op a1 a2 ty =>  
                  lift2 (eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2)
 | Econdition a1 a2 a3 ty =>  fun rho =>
    match strict_bool_val (eval_expr a1 rho) (typeof a1) with
    | Some true => force_val (sem_cast (eval_expr a2 rho) (typeof a2) ty)
    | Some false => force_val (sem_cast (eval_expr a3 rho) (typeof a3) ty)
    | None => Vundef
    end
 | Ecast a ty => lift1 (eval_cast (typeof a) ty) (eval_expr a) 
 | _ => lift0 Vundef
 end

 with eval_lvalue (e: expr) : environ -> val := 
 match e with 
 | Evar id ty => eval_var id ty
 | Ederef a ty => lift1 force_ptr (eval_expr a)
 | Efield a i ty => lift1 (eval_field (typeof a) i) (eval_lvalue a)
 | _  => lift0 Vundef
 end.


Definition cast_exp e toty rho :=
force_val (sem_cast (eval_expr e rho) (typeof e) toty). 

Fixpoint eval_exprlist (et: list type) (el:list expr) : environ -> list val :=
 match et, el with
 | t::et', e::el' => lift2 cons (cast_exp e t) (eval_exprlist et' el')
 | _, _ => lift0 nil
 end.

Definition eval_expropt (e: option expr) : environ -> option val :=
 match e with Some e' => lift1 Some (eval_expr e')  | None => lift0 None end.

(* things related to function specifications and return assertions *)
Inductive exitkind : Type := EK_normal | EK_break | EK_continue | EK_return.

Instance EqDec_exitkind: EqDec exitkind.
Proof.
hnf. intros.
decide equality.
Qed.

Definition mpred := pred rmap.
Definition assert := environ -> mpred.

Inductive funspec :=
   mk_funspec: funsig -> forall A: Type, (A -> assert) -> (A -> assert) -> funspec.

Definition funspecs := list (ident * funspec).

Definition type_of_funspec (fs: funspec) : type :=  
  match fs with mk_funspec fsig _ _ _ => Tfunction (type_of_params (fst fsig)) (snd fsig)  end.

Inductive global_spec :=
| Global_func : forall fs: funspec, global_spec
| Global_var:  forall gv: type, global_spec.

(*Declaration of type context for typechecking *)

(*Temps, vars, function return, list of variables that are not vars
 (meaning they can be looked up as globals)*)
Definition tycontext: Type := (PTree.t (type * bool) * (PTree.t type) * type 
                                  * (PTree.t global_spec))%type.

Definition empty_tycontext : tycontext := (PTree.empty (type * bool), PTree.empty type, Tvoid, PTree.empty _).

Definition temp_types (Delta: tycontext): PTree.t (type*bool) := fst (fst (fst Delta)).
Definition var_types (Delta: tycontext) : PTree.t type := snd (fst (fst Delta)).
Definition ret_type (Delta: tycontext) : type := snd (fst Delta).
Definition glob_types (Delta: tycontext) : PTree.t global_spec := snd Delta.

(*Beginning of typechecking *)

Definition bool_type (t: type) : bool :=
  match t with
  | Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ | Tfloat _ _ => true
  | _ => false
  end.

Definition is_scalar_type (ty:type) : bool :=
match ty with
| Tint _ _ _ => true
| Tfloat _ _ => true
| _ => false
end.
(*Make sure I am using the above correctly!!!*)

Definition unOp_result_type op a := 
match op with 
  | Onotbool => (Tint IBool Signed noattr) (*Bool, classify doesn't change *)
  | Onotint => (Tint I32 Signed noattr) (*Int, classify doesn't change *)
  | Oneg => (typeof a)
end.

Definition is_int_type ty := 
match ty with
| Tint _ _ _ => true
| _ => false
end.

Definition is_float_type ty := 
match ty with
| Tfloat _ _ => true
| _ => false
end.

Definition is_pointer_type ty :=
match ty with
| (Tpointer _ _ | Tarray _ _ _ 
                   | Tfunction _ _ | Tstruct _ _ _ 
                   | Tunion _ _ _) => true
| _ => false
end.

Definition isUnOpResultType op a ty := 
match op with 
  | Onotbool => match classify_bool (typeof a) with
                        | bool_default => false
                        | _ => is_int_type ty 
                        end
  | Onotint => match classify_notint (typeof a) with
                        | notint_default => false
                        | _ => is_int_type ty 
                        end
  | Oneg => match classify_neg (typeof a) with
                    | neg_case_i sg => is_int_type ty
                    | neg_case_f => is_float_type ty
                    | neg_case_default => false
                    end
end.

Inductive tc_assert :=
| tc_FF: tc_assert
| tc_noproof : tc_assert (*I want to use this for things that should still typecheck in
                           C, but that we can't really prove correct. Right now this is
                           only for valid pointers in pp compare*)
| tc_TT : tc_assert
| tc_andp: tc_assert -> tc_assert -> tc_assert
| tc_nonzero: expr -> tc_assert
| tc_iszero: expr -> tc_assert
| tc_isptr: expr -> tc_assert
| tc_ilt: expr -> int -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover: expr -> expr -> tc_assert
| tc_initialized: PTree.elt -> tc_assert.

Definition tc_bool (b : bool) :=
if b then tc_TT else tc_FF.

Fixpoint tc_assert_simpl asn :=
match asn with
| tc_andp a1 a2 =>
      match (tc_assert_simpl a1), (tc_assert_simpl a2) with
            | tc_FF, _ => tc_FF
            | _ , tc_FF => tc_TT
            | tc_TT, s => s
            | s, tc_TT => s
            | tc_noproof, _ => tc_noproof
            | _, tc_noproof => tc_noproof
            | _, _ => asn
            end
| tc_nonzero (Econst_int i _)=>if (Int.eq i Int.zero) then tc_FF else tc_TT
| tc_ilt (Econst_int i1 _) i => if (Int.ltu i1 i) then tc_TT else tc_FF
| tc_Zle (Econst_float f _) z => match (Float.Zoffloat f) with
                                   | Some n => if (Zle_bool n z) then tc_TT else tc_FF
                                   | None => tc_FF
                                 end
| tc_Zge (Econst_float f _) z => match (Float.Zoffloat f) with
                                   | Some n => if (Zle_bool z n) then tc_TT else tc_FF
                                   | None => tc_FF
                                 end
| _ => asn
end.


Definition isBinOpResultType op a1 a2 ty : tc_assert :=
match op with
  | Oadd => match classify_add (typeof a1) (typeof a2) with 
                    | add_default => tc_FF
                    | add_case_ii _ => tc_bool (is_int_type ty) 
                    | add_case_pi _ _ => tc_andp (tc_isptr a1) (tc_bool (is_pointer_type ty)) 
                    | add_case_ip _ _ => tc_andp (tc_isptr a2) (tc_bool (is_pointer_type ty))
                    | _ => tc_bool (is_float_type ty)
            end
  | Osub => match classify_sub (typeof a1) (typeof a2) with 
                    | sub_default => tc_FF
                    | sub_case_ii _ => tc_bool (is_int_type ty) 
                    | sub_case_pi _ => tc_andp (tc_isptr a1) (tc_bool (is_pointer_type ty))
                    | sub_case_pp ty2 =>  (*tc_isptr may be redundant here*)
                             tc_andp (tc_andp (tc_andp (tc_andp (tc_samebase a1 a2)
                             (tc_isptr a1)) (tc_isptr a2)) (tc_bool (is_int_type ty)))
			     (tc_bool (negb (Int.eq (Int.repr (sizeof ty2)) Int.zero)))
                    | _ => tc_bool (is_float_type ty)
            end 
  | Omul => match classify_mul (typeof a1) (typeof a2) with 
                    | mul_default => tc_FF
                    | mul_case_ii _ => tc_bool (is_int_type ty)
                    | _ => tc_bool (is_float_type ty)
            end 
  | Omod => match classify_binint (typeof a1) (typeof a2) with
                    | binint_case_ii Unsigned => tc_andp (tc_nonzero a2) 
                                                     (tc_bool (is_int_type ty))
                    | binint_case_ii Signed => tc_andp (tc_andp (tc_nonzero a2) 
                                                      (tc_nodivover a1 a2))
                                                     (tc_bool (is_int_type ty))
                    | binint_default => tc_FF
            end
  | Odiv => match classify_div (typeof a1) (typeof a2) with
                    | div_case_ii Unsigned => tc_andp (tc_nonzero a2) (tc_bool (is_int_type ty))
                    | div_case_ii Signed => tc_andp (tc_andp (tc_nonzero a2) (tc_nodivover a1 a2)) (tc_bool (is_int_type ty))
                    | div_case_ff | div_case_if _ | div_case_fi _ =>
                          tc_bool (is_float_type ty) 
                    | div_default => tc_FF
            end
  | Oshl | Oshr => match classify_shift (typeof a1) (typeof a2) with
                    | shift_case_ii _ =>  tc_andp (tc_ilt a2 Int.iwordsize) (tc_bool (is_int_type ty))
                    | shift_case_default => tc_FF
                   end
  | Oand | Oor | Oxor => 
                   match classify_binint (typeof a1) (typeof a2) with
                    | binint_case_ii _ =>tc_bool (is_int_type ty)
                    | _ => tc_FF
                   end   
  | Oeq | One | Olt | Ogt | Ole | Oge => 
                   match classify_cmp (typeof a1) (typeof a2) with
                    | cmp_default 
		    | cmp_case_pp => tc_noproof
                    | _ => tc_bool (is_int_type ty)
                   end
  end.


Definition isCastResultType tfrom tto ty a : tc_assert :=
match classify_cast tfrom tto with
| cast_case_default => tc_FF
| cast_case_f2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed) 
| cast_case_f2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| cast_case_neutral  => if eqb_type tfrom ty then tc_TT else 
                            (if andb (is_pointer_type ty) (is_pointer_type tfrom) then tc_TT
                                else tc_iszero a)
| cast_case_void => tc_noproof
(*Disabling this for the program logic, the only time it is used is not for
  functionality, more as a noop that "uses" some expression*)
| _ => match tto with 
      | Tint _ _ _  => tc_bool (is_int_type ty)
      | Tfloat _ _  => tc_bool (is_float_type ty)
      | _ => tc_FF
      end
end.

Definition globtype (g: global_spec) : type :=
match g with 
 | Global_func fs => type_of_funspec fs
 | Global_var gv => gv end.

Definition get_var_type (Delta : tycontext) id : option type :=
match (var_types Delta) ! id with
| Some ty => Some ty
| None => match (glob_types Delta) ! id with
         | Some g => Some (globtype g)
         | None => None
           end
end.

(*Main typechecking function, with work will typecheck both pure
and non-pure expressions, for now mostly just works with pure expressions*)
Fixpoint typecheck_expr (Delta : tycontext) (e: expr) : tc_assert :=
let tcr := typecheck_expr Delta in
match e with
 | Econst_int _ (Tint _ _ _) => tc_TT 
 | Econst_float _ (Tfloat _ _) => tc_TT
 | Etempvar id ty => if negb (type_is_volatile ty) then
                       match (temp_types Delta)!id with 
                         | Some ty' => if eqb_type ty (fst ty') then 
                                         if (snd ty') then tc_TT else (tc_initialized id)
                                       else tc_FF
		         | None => tc_FF
                       end
                     else tc_FF
 | Eaddrof a ty => tc_andp (typecheck_lvalue Delta a) (tc_bool (is_pointer_type ty))
 | Eunop op a ty => tc_andp (tc_bool (isUnOpResultType op a ty)) (tcr a)
 | Ebinop op a1 a2 ty => tc_andp (tc_andp (isBinOpResultType op a1 a2 ty)  (tcr a1)) (tcr a2)
 | Econdition a1 a2 a3 ty => tc_andp (tc_andp (tc_andp (tc_andp (tc_andp (tcr a1) (tcr a2)) (tcr a3)) 
                              (tc_bool (is_scalar_type (typeof a1)))) (*int or float...*)
                              (isCastResultType (typeof a2) ty ty a2)) (isCastResultType (typeof a3) ty ty a3)
 | Ecast a ty => tc_andp (tcr a) (isCastResultType (typeof a) ty ty a)
 | _ => tc_FF
end

with typecheck_lvalue (Delta: tycontext) (e: expr) : tc_assert :=
match e with
 | Evar id ty => match get_var_type Delta id with 
                  | Some ty' => tc_andp (if eqb_type ty ty' then tc_TT else tc_FF) 
                                (tc_bool (negb (type_is_volatile ty)))
                  | None => tc_FF
                 end
 | Ederef a ty => tc_andp (tc_andp (tc_andp (typecheck_expr Delta a) 
                          (tc_bool (is_pointer_type (typeof a))))
                          (tc_isptr a)) (tc_bool (negb (type_is_volatile ty)))
 | Efield a i ty => tc_andp (tc_andp (typecheck_lvalue Delta a) (match typeof a with
                            | Tstruct id fList att =>
                                  match field_offset i fList with 
                                  | Errors.OK delta => tc_TT
                                  | _ => tc_FF
                                  end
                            | Tunion id fList att => tc_TT
                            | _ => tc_FF
                            end)) (tc_bool (negb (type_is_volatile ty)))
 | _  => tc_FF
end.

Definition typecheck_temp_id id ty Delta : bool :=
  match (temp_types Delta)!id with
  | Some (t,_) => eqb_type t ty 
  | None => false
 end.

Fixpoint tc_might_be_true (asn : tc_assert) :=
match asn with
 | tc_FF => false
 | tc_andp a1 a2 => tc_might_be_true a1 && tc_might_be_true a2
 | _ => true
end.

Fixpoint tc_always_true (asn : tc_assert) := 
match asn with
 | tc_TT => true
 | tc_andp a1 a2 => tc_always_true a1 && tc_always_true a2
 | _ => false
end.



(*A more standard typechecker, should approximate the c typechecker,
might need to add a tc_noproof for nested loads*)
Definition typecheck_b Delta e :=  tc_might_be_true (typecheck_expr Delta e).

(*Definition of the original *pure* typechecker where true means the expression
will always evaluate, may not be useful since tc_denote will just compute to true
on these assertions*)
Definition typecheck_pure_b Delta e := tc_always_true (typecheck_expr Delta e). 

Fixpoint typecheck_exprlist (Delta : tycontext) (tl : list type) (el : list expr) : tc_assert :=
match tl,el with
| t::tl', e:: el' => tc_andp (typecheck_expr Delta (Ecast e t)) 
                      (typecheck_exprlist Delta tl' el')
| nil, nil => tc_TT
| _, _ => tc_FF
end.


Definition typecheck_val (v: val) (ty: type) : bool :=
 match v, ty with
 | Vint i, Tint _ _ _ => true  (* Maybe this needs to be adjusted to account for
                                               the size of the int?  Maybe not? *)
 | Vfloat v, Tfloat _ _ => true (*  Maybe this needs to be adjusted, ditto *) 
 | Vint i, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => 
                    (Int.eq i Int.zero) 
 | Vptr b z,  (Tpointer _ _ | Tarray _ _ _ 
                   | Tfunction _ _ | Tstruct _ _ _ 
                   | Tunion _ _ _) => true
 | Vundef, _ => false
(* | _, Tvoid => true (* the only way this should occur is void cast which we have
                          disabled *)*)
 | _, _ => false
 end.

Fixpoint typecheck_vals (v: list val) (ty: list type) : bool :=
 match v, ty with
 | v1::vs , t1::ts => typecheck_val v1 t1 && typecheck_vals vs ts
 | nil, nil => true
 | _, _ => false
end.

(*Environment typechecking functions *)

Fixpoint typecheck_temp_environ (tty : list(positive * (type * bool))) (te : Map.t val) : bool :=
match tty with 
 | (id,(ty, asn))::tl => match Map.get te id with
                  | Some v => if typecheck_val v ty (*&& asn*) then typecheck_temp_environ tl te else false
                  | None => false
                  end
 | nil => true
end.


Fixpoint typecheck_var_environ (vty : list(positive * type)) (ve: venviron)
 : bool :=
match vty with
 | (id,ty)::tl => match Map.get ve id with
                  | Some (_,ty') => eqb_type ty ty' && 
                           typecheck_var_environ tl ve 
                  | None => false
                  end
 | nil => true
end.

Fixpoint typecheck_glob_environ (gty:  list(positive * global_spec)) (ge: genviron) : bool :=
match gty with
 | (id,gspec)::tl => match ge id with
                                | Some (Vptr b i , ty') => if eqb_type (globtype gspec) ty' &&  
                                                      typecheck_val (Vptr b i) ty' &&
                                                      is_pointer_type ty' then 
                                                   typecheck_glob_environ tl ge  else
                                                   false
                                | None => false
                                | _ => false
                                end
 | nil => true
end.

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

Definition typecheck_environ (env : environ) (Delta: tycontext) : bool :=
typecheck_temp_environ (PTree.elements (temp_types Delta)) (te_of env) &&
typecheck_var_environ (PTree.elements (var_types Delta)) (ve_of env) &&
typecheck_glob_environ (PTree.elements (glob_types Delta)) (ge_of env)&&
same_env env Delta (all_var_ids Delta).
 

(*Denotation functions for each of the assertions that can be produced by the typechecker*)

Definition denote_tc_iszero v :=
         match v with Vint i => is_true (Int.eq i Int.zero) | _ => False end.

Definition denote_tc_nonzero v := 
         match v with Vint i => if negb (Int.eq i Int.zero) then True else False
                                               | _ => False end.

(*mostly used to make sure that a pointer isn't null *)
Definition denote_tc_isptr v := 
   match v with | Vptr _ _ => True | _ => False end.

Definition denote_tc_igt i v :=
     match v with | Vint i1 => is_true (Int.ltu i1 i)
                     | _ => False
                  end.

Definition denote_tc_Zge z v := 
          match v with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => is_true (Zge_bool z n)
                                    | None => False
                                   end
                     | _ => False 
                  end.

Definition denote_tc_Zle z v := 
          match v with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => is_true (Zle_bool z n)
                                    | None => False
                                   end
                     | _ => False 
                  end.

Definition denote_tc_samebase v1 v2 :=
                         match v1, v2 with
                           | Vptr b1 _, Vptr b2 _ => is_true (zeq b1 b2)
                           | _, _ => False 
                         end.

(*Case for division of int min by -1, which would cause overflow*)
Definition denote_tc_nodivover v1 v2 :=
match v1, v2 with
                           | Vint n1, Vint n2 => is_true (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone))
                           | _ , _ => False
                          end.

Definition denote_tc_initialized id rho := exists v, Map.get (te_of rho) id = Some v.

Fixpoint denote_tc_assert (a: tc_assert) : environ -> Prop :=
  match a with
  | tc_FF => lift0 False
  | tc_noproof => lift0 False
  | tc_TT => lift0 True
  | tc_andp b c => lift2 and (denote_tc_assert b) (denote_tc_assert c)
  | tc_nonzero e => lift1 denote_tc_nonzero (eval_expr e)
  | tc_isptr e => lift1 denote_tc_isptr (eval_expr e)
  | tc_ilt e i => lift1 (denote_tc_igt i) (eval_expr e)
  | tc_Zle e z => lift1 (denote_tc_Zge z) (eval_expr e)
  | tc_Zge e z => lift1 (denote_tc_Zle z) (eval_expr e)
  | tc_samebase e1 e2 => lift2 denote_tc_samebase (eval_expr e1) (eval_expr e2)
  | tc_nodivover e1 e2 => lift2 denote_tc_nodivover (eval_expr e1) (eval_expr e2)
  | tc_initialized id => denote_tc_initialized id
  | tc_iszero e => lift1 denote_tc_iszero (eval_expr e)
  end.

(*Functions that modify type environments*)
Definition initialized id (Delta: tycontext) :=
match (temp_types Delta) ! id with
| Some (ty, _) => ( PTree.set id (ty,true) (temp_types Delta)  
                    , var_types Delta, ret_type Delta, glob_types Delta)
| None => Delta (*Shouldn't happen *)
end.

Definition join_te' te2 (te : PTree.t (type * bool)) (id: positive) (val: type * bool) := 
   let (ty, assn) := val in
        match (te2 ! id) with
        | Some (ty2, assn2) => if eq_dec ty ty2 then
                                    PTree.set id (ty, assn && assn2) te
                               else
                                    te
        | None => te
        end.

Definition join_te te1 te2 : PTree.t (type * bool):=
PTree.fold (join_te' te2) te1 (PTree.empty (type * bool)).

Definition join_tycon (tycon1: tycontext) (tycon2 : tycontext) : tycontext :=
match tycon1 with  (te1, ve1, r, vl1)  =>
match tycon2 with  (te2, _, _, _)  =>
  ((join_te te1 te2), ve1, r, vl1)
end end.               

(*Strictly for updating the type context... no typechecking here*)
Fixpoint update_tycon (Delta: tycontext) (c: Clight.statement) {struct c} : tycontext :=
 match c with
 | Sskip | Scontinue | Sbreak => Delta
 | Sassign e1 e2 => Delta (*already there?*)
 | Sset id e2 => (initialized id Delta)
 | Ssequence s1 s2 => let Delta' := update_tycon Delta s1 in
                      update_tycon Delta' s2
 | Sifthenelse b s1 s2 => join_tycon (update_tycon Delta s1) (update_tycon Delta s2)
 | Swhile b s1  => Delta
 | Sdowhile b s1 => (update_tycon Delta s1) 
 | Sfor' b inc body => Delta
 | Sswitch e ls => join_tycon_labeled ls Delta
 | Scall (Some id) _ _ => (initialized id Delta)
 | _ => Delta  (* et cetera *)
end
(*Definition bool_expr Delta e := typecheck_expr Delta e && is_scalar_type (typeof e).*)

with join_tycon_labeled ls Delta :=
match ls with
| LSdefault s => update_tycon Delta s 
| LScase int s ls' => join_tycon (update_tycon Delta s) 
                      (join_tycon_labeled ls' Delta)
end.

(*change this to typechecking using typecheck_b, which should estimate the
c typechecker*)
(*Fixpoint update_tycon (Delta: tycontext) (c: Clight.statement) {struct c} : option tycontext :=
 match c with
 | Sskip | Scontinue | Sbreak => Some Delta
 | Sassign e1 e2 => if
                          typecheck_expr Delta e1 &&
                          typecheck_expr Delta e2 &&
                          isCastResultType (typeof e2) (typeof e1) (typeof e1)
                    then Some Delta else None
 | Sset id e2 => if
                          (typecheck_expr Delta e2  (* this case for pure expressions  *)
                          || typecheck_lvalue Delta e2)  (* this case for top-level loads *)
                          &&   true (* also check t1 matches t2, will need two cases like above*)
                 then Some (set_temp_assigned Delta id) else None
 | Ssequence s1 s2 =>match update_tycon Delta s1 with
                    | Some Delta' => match update_tycon Delta' s2 with
                                     | Some Delta'' => Some Delta''
                                     | None => None
                                     end
                    | None => None
                    end
 | Sifthenelse b s1 s2 =>if bool_expr Delta b then
                            match update_tycon Delta s1 with
                            | Some Delta1 => match update_tycon Delta s2 with
                                             | Some Delta2 => Some (join_tycon Delta1 Delta2)
                                             | None => None
                                             end
                            | None => None      
                            end
                            else None
 | Swhile b s1  => if bool_expr Delta b then option_map (fun _ => Delta) (update_tycon Delta s1) else None
 | Sdowhile b s1 => if bool_expr Delta b then (update_tycon Delta s1) else None 
 | Sfor' b inc body => if bool_expr Delta b then 
                         match update_tycon Delta inc with
                         | Some Delta' => match update_tycon Delta' body with
                                          | Some Delta'' => Some Delta 
                                          | None => None
                                          end
                         | None => None
                         end 
                       else None
 | Sswitch e ls => if typecheck_labeled_statements Delta ls && typecheck_expr Delta e 
                   then Some Delta else None
 | _ => Some Delta  (* et cetera *)
end*)

(*with typecheck_labeled_statements Delta ls :=
match ls with
| LSdefault s => match update_tycon Delta s with Some _ => true | _ => false end
| LScase int s ls => match update_tycon Delta s with 
                     | Some _ => typecheck_labeled_statements Delta ls
                     | None => false
                     end
end.*)                               

(*Creates a typecontext from a function definition *)
(* NOTE:  params start out initialized, temps do not! *)

Definition varspecs : Type := list (ident * type).

Definition make_tycontext (params: list (ident*type)) (temps: list (ident*type)) (vars: list (ident*type))
                       (return_ty: type)
                       (V: varspecs) (G: funspecs) :  tycontext :=
(fold_right (fun (param: ident*type) => PTree.set (fst param) (snd param, true))
 (fold_right (fun (temp : ident *type) tenv => let (id,ty):= temp in PTree.set id (ty,false) tenv) 
  (PTree.empty (type * bool)) temps) params,
fold_right (fun (var : ident * type) venv => let (id, ty) := var in PTree.set id ty venv) 
   (PTree.empty type) vars ,
   return_ty,
  (fold_right (fun (var : ident * funspec) => PTree.set (fst var) (Global_func (snd var))) 
      (fold_right (fun (v: ident * type) => PTree.set (fst v) (Global_var (snd v)))
         (PTree.empty _) V)
            G)).

Definition func_tycontext (func: function) (V: varspecs) (G: funspecs) : tycontext :=
  make_tycontext (func.(fn_params)) (func.(fn_temps)) (func.(fn_vars)) (func.(fn_return)) V G.

Definition nofunc_tycontext (V: varspecs) (G: funspecs) : tycontext :=
   make_tycontext nil nil nil Tvoid V G.

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

Fixpoint id_in_list (id: ident) (ids: list ident) : bool :=
 match ids with i::ids' => orb (Peqb id i) (id_in_list id ids') | _ => false end. 

Fixpoint compute_list_norepet (ids: list ident) : bool :=
 match ids with
 | id :: ids' => if id_in_list id ids' then false else compute_list_norepet ids'
 | nil => true
 end.

Lemma id_in_list_true: forall i ids, id_in_list i ids = true -> In i ids.
Proof.
 induction ids; simpl; intros. inv H. apply orb_true_iff in H; destruct H; auto.
 apply Peqb_true_eq in H. subst; auto.
Qed.

Lemma id_in_list_false: forall i ids, id_in_list i ids = false -> ~In i ids.
Proof.
 induction ids; simpl; intros; auto.
 apply orb_false_iff in H. destruct H.
 intros [?|?]. subst.
 rewrite Peqb_refl in H; inv H.
 apply IHids; auto.
Qed.

Lemma compute_list_norepet_e: forall ids, 
     compute_list_norepet ids = true -> list_norepet ids.
Proof.
 induction ids; simpl; intros.
 constructor.
 revert H; case_eq (id_in_list a ids); intros.
 inv H0.
 constructor; auto.
 apply id_in_list_false in H.
 auto.
Qed.


Definition expr_closed_wrt_vars (S: ident -> Prop) (e: expr) : Prop := 
  forall rho te',  
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     eval_expr e rho = eval_expr e (mkEnviron (ge_of rho) (ve_of rho) te').

Definition lvalue_closed_wrt_vars (S: ident -> Prop) (e: expr) : Prop := 
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

(*Test function to typecheck expressions in a statement, is a start on a typechecker
that is useful for all of compcert, not just one useful for the program logic*)



Fixpoint typecheck_all_exprs' (body: statement) (Delta :tycontext) : tc_assert:=
match body with
    Sskip | Sbreak | Scontinue => tc_TT
  | Sassign e1 e2 => tc_andp (typecheck_lvalue Delta e1) (typecheck_expr Delta e2)
  | Sset _ e => typecheck_expr Delta e 
  | Svolread _ e => typecheck_expr Delta e
  | Scall _ e el => (typecheck_expr Delta e)
  | Ssequence s1 s2 => tc_andp (typecheck_all_exprs' s1 Delta) 
       (typecheck_all_exprs' s2 (update_tycon Delta s1)) 
  | Sifthenelse b s1 s2 => tc_andp (tc_andp (typecheck_expr Delta b) (typecheck_all_exprs' s1 Delta))
                            (typecheck_all_exprs' s2 Delta)
  | Swhile b s => (tc_andp (typecheck_expr Delta b) (typecheck_all_exprs' s Delta))
  | Sdowhile b s => (tc_andp (typecheck_expr Delta b) (typecheck_all_exprs' s Delta))
  | Sfor' b s1 s2 => tc_andp (tc_andp (typecheck_expr Delta b) (typecheck_all_exprs' s1 Delta))
                            (typecheck_all_exprs' s2 (update_tycon Delta s1))
  | Sreturn (Some e) => typecheck_expr Delta e
  | Sreturn (None) => tc_TT
  | Sswitch e ls => tc_andp (typecheck_expr Delta e) (typecheck_labeled_st_exprs Delta ls)
  | Slabel _ st => typecheck_all_exprs' st Delta
  | Sgoto _ => tc_TT
end

with typecheck_labeled_st_exprs Delta ls:= 
match ls with 
| LSdefault s => typecheck_all_exprs' s Delta
| LScase int s ls2 => tc_andp (typecheck_all_exprs' s Delta) (typecheck_labeled_st_exprs Delta ls2) 
end.

Definition typecheck_all_exprs (func: function) (V: varspecs) (G: funspecs): tc_assert :=
typecheck_all_exprs' func.(fn_body) (func_tycontext func V G).

Definition tc_val (t: type) (v: val) : Prop := typecheck_val v t = true.


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