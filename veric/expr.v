Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.


Definition eval_id (rho: environ) (id: ident) := force_val (PTree.get id (te_of rho)).

Fixpoint eval_expr (rho:environ) (e: expr) : val :=
 match e with
 | Econst_int i ty => Vint i
 | Econst_float f ty => Vfloat f
 | Etempvar id ty => eval_id rho id (* Don't write force_val here directly; with
                                                           the intermediate definition eval_id, then
                                                           eval_expr (Etempvar _ _) simplifies nicer. *)
 | Eaddrof a ty => eval_lvalue rho a
 | Eunop op a ty =>  force_val (sem_unary_operation op (eval_expr rho a) (typeof a))
 | Ebinop op a1 a2 ty =>  
         force_val (sem_binary_operation op
                    (eval_expr rho a1) (typeof a1)
                    (eval_expr rho a2) (typeof a2)
                    (fun _ _ => false))
 | Econdition a1 a2 a3 ty => 
    match bool_val (eval_expr rho a1) (typeof a1) with
    | Some true => force_val (sem_cast (eval_expr rho a2) (typeof a2) ty)
    | Some false => force_val (sem_cast (eval_expr rho a3) (typeof a3) ty)
    | None => Vundef
    end
 | Ecast a ty => force_val (sem_cast (eval_expr rho a) (typeof a) ty)
 | _ => Vundef
 end 

 with eval_lvalue (rho: environ) (e: expr) : val := 
 match e with 
 | Evar id ty => match PTree.get id (ve_of rho) with
                         | Some (b,ty') => if type_eq ty ty'
                                                    then if negb (type_is_volatile ty')
                                                       then Vptr b Int.zero else Vundef
                                                    else Vundef
                         | None => 
                            match (ge_of rho) id with
                            | Some (v,ty') => if type_eq ty ty' then v else Vundef
                            | None => Vundef
                            end
                        end
 | Ederef a ty => match eval_expr rho a with
                        | Vptr l ofs => Vptr l ofs
                        | _ => Vundef
	          end
 | Efield a i ty => match eval_expr rho a, typeof a with
                            | Vptr l ofs, Tstruct id fList att =>
                                  match field_offset i fList with 
                                  | Errors.OK delta => Vptr l (Int.add ofs (Int.repr delta))
                                  | _ => Vundef
                                  end
                            | Vptr l ofs, Tunion id fList att => Vptr l ofs
                            | _, _ => Vundef
                            end
 | _  => Vundef
 end.

Definition eval_exprlist rho el := map (eval_expr rho) el.

(*Temps, vars, function return*)
Definition tycontext: Type := (PTree.t (type * bool) * (PTree.t type) * type)%type.

Definition empty_tycontext : tycontext := (PTree.empty (type * bool), PTree.empty type, Tvoid).

Definition temp_types (Delta: tycontext) := fst (fst Delta).
Definition var_types (Delta: tycontext) := snd (fst Delta).
Definition ret_type (Delta: tycontext) := snd Delta.

Parameter binary_conversion : binary_operation -> type -> type -> type.

Definition is_scalar_type (ty:type) : bool :=
match ty with
| Tint _ _ _ => true
| Tfloat _ _ => true
| _ => false
end.
(*Make sure I am using the above correctly!!!*)

(*
Parameter combine_types : type -> type -> option type .

Definition compatable_types (t1: type) (t2 : type) : bool :=
match combine_types t1 t2 with
| Some _ => true
| None => false
end.
*)
Parameter b: bool.
(*
Parameter cast_compatible : type -> type -> bool.
*)
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
| tc_isptr: expr -> tc_assert
| tc_ilt: expr -> int -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover: expr -> expr -> tc_assert.

Definition tc_bool (b : bool) :=
if b then tc_TT else tc_FF.


(*TODO make sure return types are correct, figure out valid types for bool
 also, decide if we can reliably always consider boolean returns (from compares)
 as an int, rather than other valid boolean types*)
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
                    | binint_case_ii Unsigned => tc_andp (tc_nonzero a2) (tc_bool (is_int_type ty))
                    | binint_case_ii Signed => tc_andp (tc_andp (tc_nonzero a2) (tc_nodivover a1 a2))
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
| cast_case_neutral  => if type_eq tfrom ty then tc_TT else tc_FF
| _ => match tto with 
      | Tint _ _ _  => tc_bool (is_int_type ty)
      | Tfloat _ _  => tc_bool (is_float_type ty)
      | _ => tc_FF
      end
end.

(* NOTE: typecheck_expr allows only _pure_ expressions that don't access the heap if pure=true *)
Fixpoint typecheck_expr (Delta : tycontext) (e: expr) : tc_assert :=
let tcr := typecheck_expr Delta in
match e with
 | Econst_int _ (Tint _ _ _) => tc_TT 
 | Econst_float _ (Tfloat _ _) => tc_TT
 | Etempvar id ty => match (temp_types Delta)!id with 
                       | Some ty' => if type_eq ty (fst ty') then tc_TT else tc_FF 
		       | None => tc_FF
                     end
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
 | Evar id ty => match (var_types Delta) ! id with 
                  | Some ty' => tc_andp (if type_eq ty ty' then tc_TT else tc_FF) 
                                (tc_bool (negb (type_is_volatile ty)))
                  | None => tc_FF
                 end
 | Ederef a ty => tc_andp (tc_andp (typecheck_expr Delta a) 
                          (tc_bool (is_pointer_type (typeof a))))
                          (tc_isptr a) 
 | Efield a i ty => tc_andp (typecheck_expr Delta a) (match typeof a with
                            | Tstruct id fList att =>
                                  match field_offset i fList with 
                                  | Errors.OK delta => tc_TT
                                  | _ => tc_FF
                                  end
                            | Tunion id fList att => tc_TT
                            | _ => tc_FF
                            end)
 | _  => tc_FF
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

Definition typecheck_exprlist (Delta: tycontext) (el: list expr) : tc_assert := 
 fold_right (fun e a => tc_andp (typecheck_expr Delta e) a) tc_TT el.

Definition typecheck_val (v: val) (ty: type) : bool :=
 match v, ty with
 | Vint i, Tint _ _ _ => true  (* Maybe this needs to be adjusted to account for
                                               the size of the int?  Maybe not? *)
 | Vfloat v, Tfloat _ _ => true (*  Maybe this needs to be adjusted, ditto *) 
 | Vint i, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => 
                    negb (Int.eq i Int.zero) 
 | Vptr b z,  (Tpointer _ _ | Tarray _ _ _ 
                   | Tfunction _ _ | Tstruct _ _ _ 
                   | Tunion _ _ _) => true
 | Vundef, _ => false
 | _, Tvoid => true
 | _, _ => false
 end.

Fixpoint typecheck_vals (v: list val) (ty: list type) : bool :=
 match v, ty with
 | v1::vs , t1::ts => typecheck_val v1 t1 && typecheck_vals vs ts
 | nil, nil => true
 | _, _ => false
end.

Fixpoint typecheck_temp_environ (tty : list(positive * type)) (te : PTree.t val) : bool :=
match tty with 
 | (id,ty)::tl => match te ! id with
                  | Some v => if typecheck_val v ty then typecheck_temp_environ tl te else false
                  | None => false
                  end
 | nil => true
end.

Fixpoint typecheck_var_environ (vty : list(positive * type)) (ve: env) (ge : genviron) : bool :=
match vty with
 | (id,ty)::tl => match ve!id with
                  | Some (_,ty') => if type_eq ty ty' then 
                           typecheck_var_environ tl ve ge
                           else false
                  | None => match ge id with
                                | Some (Vptr b i , ty') => if type_eq ty ty' &&  
                                                      typecheck_val (Vptr b i) ty' &&
                                                      is_pointer_type ty' then 
                                                   typecheck_var_environ tl ve ge else
                                                   false
                                | None => false
                                | _ => false
                                end
                  end
 | nil => true
end.

Definition remove_assignedness {A B C} (x: (A * (B*C))) := let (a,d) := x in
let (b,c) := d in 
(a,b).

Definition typecheck_environ (env : environ) (Delta: tycontext) : bool :=
typecheck_temp_environ (map remove_assignedness (PTree.elements (temp_types Delta))) (te_of env) &&
typecheck_var_environ (PTree.elements (var_types Delta)) (ve_of env) (ge_of env).
 

Fixpoint denote_tc_assert (a: tc_assert) (rho: environ): Prop :=
  match a with
  | tc_FF => False
  | tc_noproof => False
  | tc_TT => True
  | tc_andp b c => denote_tc_assert b rho /\ denote_tc_assert c rho
  | tc_nonzero e => match eval_expr rho e with Vint i => if negb (Int.eq i Int.zero) then True else False
                                               | _ => False end
  | tc_isptr e => match (eval_expr rho e) with | Vptr _ _ => True | _ => False end
  | tc_ilt e i => match (eval_expr rho e) with 
                     | Vint i1 => is_true (Int.ltu i1 i)
                     | _ => False
                  end 
  | tc_Zle e z => match (eval_expr rho e) with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => is_true (Zle_bool n z)
                                    | None => False
                                   end
                     | _ => False (*Might need int here*)
                  end
  | tc_Zge e z => match (eval_expr rho e) with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => is_true (Zle_bool z n)
                                    | None => False
                                   end
                     | _ => False
                  end
  | tc_samebase e1 e2 => match (eval_expr rho e1), (eval_expr rho e2) with
                           | Vptr b1 _, Vptr b2 _ => is_true (zeq b1 b2)
                           | _, _ => False 
                         end  
  | tc_nodivover e1 e2 => match (eval_expr rho e1), (eval_expr rho e2) with
                           | Vint n1, Vint n2 => is_true (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone))
                           | _ , _ => False
                          end
  end.

Definition set_temp_assigned (Delta:tycontext) id :=
match (temp_types Delta) ! id with
| Some (ty, _) => ( PTree.set id (ty,true) (temp_types Delta)  
                    , var_types Delta, ret_type Delta)
| None => Delta (*Shouldn't happen *)
end.

Parameter join_tycon: tycontext -> tycontext -> tycontext.

(*Definition bool_expr Delta e := typecheck_expr Delta e && is_scalar_type (typeof e).*)



(*update_tycon can be separate from typechecking, do this reasonably soon*)
Parameter update_tycon : tycontext -> Clight.statement -> option tycontext.
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



Definition typecheck_stmt (Delta: tycontext) (c: statement) : bool :=
match update_tycon Delta c with
| Some _ => true
| None => false
end.

(* NOTE:  params start out initialized, temps do not! *)
Definition func_tycontext (func: function) : tycontext :=
(fold_right (fun (param: ident*type) => PTree.set (fst param) (snd param, true))
 (fold_right (fun (temp : ident *type) tenv => let (id,ty):= temp in PTree.set id (ty,false) tenv) 
  (PTree.empty (type * bool)) func.(fn_temps)) func.(fn_params),
fold_right (fun (var : ident * type) venv => let (id, ty) := var in PTree.set id ty venv) 
   (PTree.empty type) func.(fn_vars) ,
fn_return func).


(** Type-checking of function parameters **)

Fixpoint match_fsig_aux (bl: list expr) (tl: typelist) : bool :=
 match bl, tl with
 | b::bl', Tcons t' tl' => if eq_dec (typeof b) t' then match_fsig_aux bl' tl' else false
 | nil, Tnil => true
 | nil, Tcons _ _ => false
 | _::_, Tnil => false
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
  map typeof bl = typelist2list (fst fsig) /\ (snd fsig=Tvoid <-> ret=None).
Proof.
 intros.
 apply andb_true_iff in H.
 destruct H.
 split. clear H0.
 forget (fst fsig) as tl.
 revert tl H; induction bl; destruct tl; intros; inv H.
  reflexivity.
 if_tac in H1. simpl. f_equal; auto. inv H1.
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
     (forall i, S i \/ PTree.get i (te_of rho) = PTree.get i te') ->
     eval_expr rho e = eval_expr (mkEnviron (ge_of rho) (ve_of rho) te') e.

Definition lvalue_closed_wrt_vars (S: ident -> Prop) (e: expr) : Prop := 
  forall rho te',  
     (forall i, S i \/ PTree.get i (te_of rho) = PTree.get i te') ->
     eval_lvalue rho e = eval_lvalue (mkEnviron (ge_of rho) (ve_of rho) te') e.

Definition env_set (rho: environ) (x: ident) (v: val) : environ :=
  mkEnviron (ge_of rho) (ve_of rho) (Maps.PTree.set x v (te_of rho)).


Lemma eval_id_same: forall rho id v, eval_id (env_set rho id v) id = v.
Proof. unfold eval_id; intros; simpl. unfold force_val. rewrite PTree.gss. auto.
Qed.
Hint Rewrite eval_id_same : normalize.

Lemma eval_id_other: forall rho id id' v,
   id<>id' -> eval_id (env_set rho id v) id' = eval_id rho id'.
Proof.
 unfold eval_id, force_val; intros. simpl. rewrite PTree.gso; auto.
Qed.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : normalize.


(* expr.v is not quite the right place for these next few definitions, but
   we'll work that out later *)
Inductive exitkind : Type := EK_normal | EK_break | EK_continue | EK_return.

Instance EqDec_exitkind: EqDec exitkind.
Proof.
hnf. intros.
decide equality.
Qed.

Inductive funspec :=
   mk_funspec: funsig -> 
           forall A: Type, (A -> list val -> pred rmap) -> (A -> list val -> pred rmap) 
                 -> funspec.

Definition funspecs := list (ident * funspec).

Definition type_of_funspec (fs: funspec) : type :=  
  match fs with mk_funspec fsig _ _ _ => Tfunction (fst fsig) (snd fsig)  end.

(* END expr.v is not quite the right place for these next few definitions *)
