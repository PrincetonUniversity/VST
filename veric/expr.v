Require Export msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.

Fixpoint eval_expr (rho:environ) (e: expr) : val :=
 match e with
 | Econst_int i ty => Vint i
 | Econst_float f ty => Vfloat f
 | Etempvar id ty => force_val (PTree.get id (te_of rho))
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


(*Temps, vars, function return*)
Definition tycontext: Type := (PTree.t (type * bool) * (PTree.t type) * type)%type.

Definition empty_tycontext : tycontext := (PTree.empty (type * bool), PTree.empty type, Tvoid).

Definition Delta1 : tycontext := (PTree.set 1%positive (type_int32s, false) (PTree.empty (type * bool)),
                                 PTree.empty type, Tvoid).

Definition temp_types (Delta: tycontext) := fst (fst Delta).
Definition var_types (Delta: tycontext) := snd (fst Delta).
Definition ret_type (Delta: tycontext) := snd Delta.

Parameter binary_conversion : binary_operation -> type -> type -> type.

Definition is_skalar_type (ty:type) : bool :=
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

(*Might need to include quite a few more!*)
Definition is_pointer_type ty :=
match ty with
| (Tpointer _ _ | Tarray _ _ _ 
                   | Tfunction _ _ | Tstruct _ _ _ 
                   | Tunion _ _ _) => true
| _ => false
end.

Definition isUnOpResultType op a ty := 
match op with 
(*Using classify makes sure that arguments are appropriate*)
  | Onotbool => match classify_bool (typeof a) with
                        | bool_default => false
                        | _ => is_int_type ty 
                        end
  | Onotint => match classify_notint (typeof a) with
                        | notint_default => false
                        | _ => is_int_type ty (*Int, classify doesn't change *)
                        end
  | Oneg => match classify_neg (typeof a) with
                    | neg_case_i sg => is_int_type ty
                    | neg_case_f => is_float_type ty
                    | _ => false
                    end
end.

Inductive tc_assert :=
| tc_FF: tc_assert
| tc_TT : tc_assert
| tc_andp: tc_assert -> tc_assert -> tc_assert
| tc_nonzero: expr -> tc_assert
| tc_isptr: expr -> tc_assert
| tc_range32: expr -> tc_assert.

Definition tc_bool (b : bool) :=
if b then tc_TT else tc_FF.


(*TODO most tc_FF should be an assert of some sort (not default)*)
Definition isBinOpResultType op a1 a2 ty : tc_assert :=
match op with
  | Oadd => match classify_add (typeof a1) (typeof a2) with 
                    | add_default => tc_FF
                    | add_case_ii _ => tc_bool (is_int_type ty) 
                    | add_case_pi _ _ | add_case_ip _ _ => tc_FF 
                        (*is_pointer_type ty*)
                    | _ => tc_bool (is_float_type ty)
                    end
  | Osub => match classify_sub (typeof a1) (typeof a2) with 
                    | sub_default => tc_FF
                    | sub_case_ii _ => tc_bool (is_int_type ty) 
                    | sub_case_pi _ => tc_FF (*is_pointer_type ty ... comment for now, until I figure out null issue*)
                    | sub_case_pp _ => tc_FF
                    | _ => tc_bool (is_float_type ty)
                    end 
  | Omul => match classify_mul (typeof a1) (typeof a2) with 
                    | mul_default => tc_FF
                    | mul_case_ii _ => tc_bool (is_int_type ty)
                    | _ => tc_bool (is_float_type ty)
                    end 
  | Omod | Odiv | Oshl | Oshr => tc_FF (*these need asserts, not done yet*)
  | Oand | Oor  | Oxor => match classify_binint (typeof a1) (typeof a2) with
                          | binint_case_ii _ =>tc_bool (is_int_type ty)
                          | _ => tc_FF
                          end   
  | Oeq | One | Olt 
    | Ogt | Ole | Oge => 
       match classify_cmp (typeof a1) (typeof a2) with
       | cmp_case_pp | cmp_default => tc_FF
       | _ => tc_bool (is_int_type ty)
       end
end.


Definition isCastResultType tfrom tto ty : tc_assert :=
match classify_cast tfrom tto with
| cast_case_default | 
   cast_case_f2i _ _ => tc_FF (*figure out what this case is and assert it*)
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
                              (tc_bool (is_skalar_type (typeof a1)))) (*int or float...*)
                              (isCastResultType (typeof a2) ty ty)) (isCastResultType (typeof a3) ty ty)
 | Ecast a ty => tc_andp (tcr a) (isCastResultType (typeof a) ty ty)
 | _ => tc_FF
end

with typecheck_lvalue (Delta: tycontext) (e: expr) : tc_assert :=
match e with
 | Evar id ty => match (var_types Delta) ! id with 
                  | Some ty' => tc_andp (if type_eq ty ty' then tc_TT else tc_FF) 
                                (tc_bool (negb (type_is_volatile ty)))
                  | None => tc_FF
                 end
 (*| Ederef a ty => typecheck_expr_pure Delta a && is_pointer_type (typeof a) --need proof it isn't null*) 
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
                                | Some (v, ty') => if type_eq ty ty' &&  
                                                      typecheck_val v ty' &&
                                                      is_pointer_type ty' then 
                                                   typecheck_var_environ tl ve ge else
                                                   false
                                | None => false
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

Definition temp_element_correct (te : temp_env) :=
(fun (tyconEl : (PTree.elt * type)) => let (id,elt) := tyconEl in
  match te ! id with
  | Some v => typecheck_val v elt = true
  | _ => False
end). 

Definition te_correct (te : temp_env) (Delta: tycontext) := Forall
  (temp_element_correct te)
  (map remove_assignedness (PTree.elements (temp_types Delta))).

Definition var_element_correct (ve: env) (ge:genviron) : 
(PTree.elt * type) -> Prop :=
(fun (varel : (PTree.elt * type)) => let (id,ty) := varel in
  match ve ! id with
  | Some (_,ty') => if type_eq ty ty' then True else False
  | None => match (ge id) with
        | Some (v,ty2') => if type_eq ty ty2' && 
                              typecheck_val v ty2' &&
                              is_pointer_type ty2'(*Double check===================================*)
                              (*^will be correct with change to base.v*)
        then True else False 
        | None => False
        end
  end).

Definition ve_correct (ve:env) (ge:genviron) (Delta: tycontext) :=
Forall (var_element_correct ve ge) (PTree.elements (var_types Delta)).


Lemma typecheck_environ_sound : forall ge te ve Delta,
typecheck_environ (mkEnviron ge ve te) Delta = true ->
te_correct te Delta /\ ve_correct ve ge Delta.
Proof.
intros.
unfold typecheck_environ in *. destruct Delta. destruct p.
unfold te_correct. unfold ve_correct.
unfold temp_types in *. simpl in *. split.

induction (PTree.elements t0).
constructor. 
unfold temp_element_correct.
simpl in *. destruct a. destruct p0. rewrite Forall_forall; intros.
destruct x. simpl in *. destruct H0. inv H0. destruct (te!e). 
destruct (typecheck_val v t3). auto. inv H. inv H.
destruct (te!p). remember (typecheck_val v t2). destruct b1. 
intuition. rewrite Forall_forall in *. unfold temp_element_correct in *.
specialize (H1 (e,t3)). intuition. inv H. inv H.

unfold var_types in *; simpl in *. rewrite andb_true_iff in H. destruct H.
clear H. rewrite Forall_forall. intros. 
destruct x. induction (PTree.elements t1). inv H.
simpl in *. destruct a. destruct H. inv H. destruct (ve !e). destruct p.
destruct (type_eq t2 t3). auto. inv H0. destruct (ge e). destruct p.
destruct (type_eq t2 t3 && typecheck_val v t3 && is_pointer_type t3). auto.
intuition. inv H0. 
apply IHl.
clear IHl.  destruct (ve ! p). destruct p0. 
destruct (type_eq t3 t4). subst.
auto. inv H0. destruct (ge p). destruct p0. 
destruct (type_eq t3 t4 && typecheck_val v t4 && is_pointer_type t4).
auto. inv H0. inv H0. auto. 
Qed.

Lemma typecheck_te_sound : forall dv te,
typecheck_temp_environ dv te = true ->
Forall (temp_element_correct te) dv.
Proof.
intros. induction dv. auto.
simpl in *. destruct a. remember (te! p). destruct o; auto.
remember (typecheck_val v t). destruct b0. 
rewrite Forall_forall. intros. simpl in H0. destruct H0. inv H0.
unfold temp_element_correct. rewrite <- Heqo. auto. intuition.
rewrite Forall_forall in H1. apply H1. auto. inv H. inv H.
Qed.

Lemma in_fst_in : forall A B (L : list (A*B)) (a:A) (b:B), In (a, b) L  -> In a (map (@fst A B) L) .
Proof.
intros A B L. induction L; intros. auto. simpl in *. inv H. auto. right. eapply IHL. apply H0.
Qed.

Lemma in_rem_in : forall A B C (L : list (A*(B*C))) a b c,
In (a, (b, c)) L -> In (a,b) (map remove_assignedness (L)).
intros A B C L. induction L; intros. inv H. simpl in *.
inv H. left. auto. right. eapply  IHL. eauto.
Qed.

(*I think I need this eventually
but can't figure it out right now...
Lemma typecheck_environ_put_te : forall ge te ve Delta id v ,
typecheck_environ (mkEnviron ge ve te) Delta = true ->
(*((temp_types Delta) ! id = Some t ->
  (typecheck_val v (fst t)) = true) ->*)
(*typecheck_expr Delta (Etempvar id (typeof e)) = true ->
typecheck_expr Delta e = true ->*) 
typecheck_environ (mkEnviron ge ve (PTree.set id v te)) Delta = true.
Proof.
intros. unfold typecheck_environ in *. simpl in *. repeat rewrite andb_true_iff in *.
intuition. clear H1. destruct Delta. destruct p. unfold temp_types in *; simpl in *.

remember (map remove_assignedness (PTree.elements t0)).
generalize dependent t0.
induction l; intros; auto.

simpl in *. destruct  a.  
remember (te ! p). destruct o; intuition.
remember (typecheck_val v0 t2). destruct b0; intuition.
remember ((PTree.set id v te) ! p).
destruct o. remember (typecheck_val v1 t2). destruct b0.
eapply H.
Focus 2. clear H.
assert (typecheck_val v1 t2 = true). 
apply typecheck_te_sound in H0. rewrite Forall_forall in *.
unfold temp_element_correct in H0.
clear Heqb1. 

Focus 3. clear H.   
assert (In (p,t3) (p,t3::l)).
assert (x:=eq_dec p id). destruct x. subst. rewrite PTree.gss in Heqo0.
inv Heqo0. apply typecheck_te_sound in H1. rewrite Forall_forall in H1.
unfold temp_element_correct in H1.

unfold typecheck_temp_environ in H. 
 rewrite typecheck_environ_sound in H1. 
*)



Lemma no_rep_in_pair : forall A B L a b b2, list_norepet (map (@fst A B) (L)) ->
  In (a, b) L -> In (a,b2) L -> b = b2.
Proof.
intros A B L. induction L; intros. inv H0. simpl in *.
inv H. intuition.
  destruct a. inv H0. inv H. auto.
 
  destruct H4. destruct a; simpl. inv H. eapply in_fst_in. eauto. 
  
  destruct H4. destruct a; simpl. inv H0. eapply in_fst_in. eauto.

  eapply IHL; eauto.
Qed. 


Lemma type_eq_true : forall a b, proj_sumbool  (type_eq a b) =true  -> a = b.
Proof. intros. destruct (type_eq a b0). auto. simpl in H. inv H.
Qed.

Ltac of_bool_destruct :=
match goal with
  | [ |- context[Val.of_bool ?X] ] => destruct X
end.


Lemma classify_add_int_cases_both : forall i1 s1 a1 i2 s2 a2,
exists s3,
classify_add (Tint i1 s1 a1) (Tint i2 s2 a2) 
= add_case_ii s3.
Proof.
intros; destruct i1; destruct s1; destruct i2; destruct s2; eexists;  
unfold classify_add; simpl; eauto.
Qed.

Lemma undef_not_typecheck : forall t, typecheck_val Vundef t = false.
intros.
destruct t; auto.
Qed.

Fixpoint denote_tc_assert (a: tc_assert) (rho: environ): Prop :=
  match a with
  | tc_FF => False
  | tc_TT => True
  | tc_andp b c => denote_tc_assert b rho /\ denote_tc_assert c rho
  | tc_nonzero e => match eval_expr rho e with Vint i => if negb (Int.eq i Int.zero) then True else False
                                               | _ => False end
  | _ => False
  end.

Definition tc_expr (Delta: tycontext) (e: expr) (rho: environ) : Prop := 
          denote_tc_assert (typecheck_expr Delta e) rho.

Definition tc_exprlist (Delta: tycontext) (e: list expr) (rho: environ) : Prop := 
          denote_tc_assert (typecheck_exprlist Delta e) rho.

Definition tc_lvalue (Delta: tycontext) (e: expr) (rho: environ) : Prop := 
          denote_tc_assert (typecheck_lvalue Delta e) rho.



(*come back here
Lemma typecheck_binop_sound:
forall (Delta : tycontext) (rho : environ) (b0 : binary_operation)
  (e1 e2 : expr) (t : type),
typecheck_expr Delta e2 = true ->
isBinOpResultType b0 e1 e2 t = true ->
typecheck_expr Delta e1 = true ->
typecheck_val (eval_expr rho e2) (typeof e2) = true ->
typecheck_val (eval_expr rho e1) (typeof e1) = true ->
typecheck_val (eval_expr rho (Ebinop b0 e1 e2 t)) t = true.
Proof.
Admitted. (*for memory, proof below should work*)
(*intros.
unfold eval_expr in *. simpl in *.
destruct b0; simpl in *;
match goal with 
| [ |- typecheck_val ( force_val (?X _ _ _ _)) _ = true ] => unfold X in *
| [ |- typecheck_val ( force_val (?X _ _ _ _ _)) _ = true ] => unfold X in *
| [ |- typecheck_val ( force_val (?X _ _ _ _ _ _)) _ = true ] => unfold X in *
end;(
do 2
(match goal with
| [ |- context[(typeof ?X)]] => let x := fresh "tofx" in remember (typeof X) as x; destruct x
end); intuition; simpl;
try solve [try destruct i; try destruct s; try destruct i0; try destruct s0; intuition;(
simpl in *;
try solve [do 2 try
match goal with
| [ |- context[compute_expr ?ge ?ve ?te ?e]] => remember (compute_expr ge ve te e) as compR; destruct compR
end; try destruct t; auto; intuition; try (of_bool_destruct; auto)])]). 
Qed.*) *)

Lemma typecheck_both_sound: 
  forall Delta rho e P, 
             typecheck_environ rho Delta = true -> 
             (typecheck_expr Delta e = P ->
              denote_tc_assert P rho ->
             typecheck_val (eval_expr rho e) (typeof e) = true) /\
             (forall pt, typecheck_lvalue Delta e = P -> 
             denote_tc_assert P rho ->
             is_pointer_type pt = true -> 
             typecheck_val (eval_lvalue rho e) pt=true).
Proof.
intros. induction e; intuition.
Admitted. (*So I can get it committed
(*Const int*)
simpl. destruct t; auto; simpl in H0; inv H0; intuition.

(*Const float*)
simpl in *. destruct t; intuition. 

(*Var*)
simpl in *. unfold eval_lvalue. simpl.

apply typecheck_environ_sound in H. destruct H.
clear H. unfold ve_correct in H2. rewrite Forall_forall in *.
unfold var_element_correct in *.
remember ((var_types Delta) ! i). destruct o; intuition. rewrite andb_true_iff in *.
intuition. apply type_eq_true in H. subst. symmetry in Heqo.
apply PTree.elements_correct in Heqo.
specialize (H2 (i,t0)). intuition.
remember ((ve_of rho) ! i). destruct o.
destruct p. remember (type_eq t0 t). destruct s; intuition.
subst. rewrite H3. destruct pt; auto.
destruct (ge_of rho i); auto. destruct p. 
remember (@proj_sumbool (t0 = t) (t0 = t -> False) (type_eq t0 t) &&
       typecheck_val v t && is_pointer_type t).
destruct b0; try contradiction. symmetry in Heqb0. repeat rewrite andb_true_iff in *. intuition.
destruct (type_eq t0 t); auto. subst. admit.
(*Stuck. If an int can typecheck as a pointer, should it be able to
check as struct and union in the same cases??*)
 (* Focus 2. destruct v; 
destruct t; auto; intuition. destruct pt; intuition. 


simpl in *. simpl in H5. simpl in *. simpl in *.
 destruct t; auto.
destruct t; auto.
auto.*)

(*Temp*)
simpl in *. destruct rho. apply typecheck_environ_sound in H. intuition. 
unfold te_correct in *. unfold temp_element_correct in *.
rewrite Forall_forall in *. clear H2. 

unfold eval_expr. unfold compute_expr. simpl. unfold force_val.
destruct Delta. destruct p. 
unfold temp_types in *. simpl in *.
remember (t1 ! i). destruct o.
  symmetry in Heqo. apply PTree.elements_correct in Heqo. 
  destruct p. specialize (H1 (i,t3)). simpl in H1.
apply type_eq_true in H0. inv H0. simpl in *.
apply in_rem_in in Heqo. intuition. destruct (te ! i); auto.
inv H0.  

(*deref  -- no proof now, doesn't typecheck
simpl in *. rewrite andb_true_iff in *; intuition. 
unfold eval_lvalue. simpl. unfold eval_expr in *.
remember (compute_expr (ge_of rho) (ve_of rho) (te_of rho) e).
destruct v; intuition; destruct (typeof e); intuition. simpl in *. 
*)

(*addrof*)
unfold eval_expr in *. simpl in *. rewrite andb_true_iff in *; intuition. 
destruct t. Focus 4. simpl in *. apply H2. unfold typecheck_lvalue_pure in *.a

(*Unop*)
simpl in *. rewrite andb_true_iff in *. intuition.
unfold eval_expr in *; destruct u; simpl in *. 

unfold sem_notbool in *.
remember (typeof e). destruct t0; simpl in *; intuition; try destruct i; try destruct s; simpl in *;
destruct ((compute_expr (ge_of rho) (ve_of rho) (te_of rho) e)); intuition;
simpl; try of_bool_destruct; try destruct t; intuition.

unfold sem_notint. remember (typeof e). destruct t0; simpl in *; 
try destruct i; try destruct s; intuition;
destruct (compute_expr (ge_of rho) (ve_of rho) (te_of rho) e);
simpl in *; try of_bool_destruct; destruct t; intuition.

unfold sem_neg. remember (typeof e). destruct t0; simpl in *; 
try destruct i; try destruct s; intuition;
destruct (compute_expr (ge_of rho) (ve_of rho) (te_of rho) e);
simpl in *; try of_bool_destruct; destruct t; intuition.

(*binop*)
simpl in *. repeat rewrite andb_true_iff in *; intuition.
clear H1. clear H3. clear H.

eapply typecheck_binop_sound; eauto.

(* cast *)
simpl. unfold eval_expr. simpl. simpl in *. rewrite andb_true_iff in *; intuition.
unfold eval_expr in *. remember (compute_expr (ge_of rho) (ve_of rho) (te_of rho) e).
destruct v; intuition; remember (typeof e); destruct t0; intuition; destruct t; intuition;
try destruct i; try destruct i0; try destruct i1; intuition.

(*condition*)
simpl in *. repeat rewrite andb_true_iff in *; intuition.
unfold eval_expr in *.
simpl in *. 
remember (compute_expr (ge_of rho) (ve_of rho) (te_of rho) e2).
remember (compute_expr (ge_of rho) (ve_of rho) (te_of rho) e3).

destruct ((compute_expr (ge_of rho) (ve_of rho) (te_of rho) e1)); intuition.
remember (typeof e1); destruct t0; intuition. simpl.
destruct (negb (Int.eq i Int.zero)). destruct v; intuition; remember (typeof e2);
destruct t0; intuition; destruct t; intuition; try destruct i2; try destruct s0; intuition;
try destruct i3; try destruct s0; try destruct s1; try destruct i1; intuition.
destruct v0; intuition; remember (typeof e3); destruct t0; intuition; destruct t; intuition; 
try destruct i2; try destruct s0; intuition;
try destruct i3; try destruct s0; try destruct s1; try destruct i1; intuition.
remember (typeof e1); destruct t0; intuition. simpl.
destruct (negb (Float.cmp Ceq f Float.zero)).
remember (typeof e2). destruct v; destruct t0; destruct t; intuition;
try destruct i0; try destruct s; intuition; try destruct i1; try destruct s0; try destruct i; intuition.
remember (typeof e3). destruct v0; destruct t0; destruct t; intuition; 
try destruct i0; try destruct s; intuition; try destruct i1; try destruct s0; try destruct i; intuition.
remember (typeof e1). unfold bool_val. destruct t0; intuition.

(*EField*)
simpl in H2. rewrite andb_true_iff in *; intuition. unfold eval_lvalue in *.
unfold eval_expr in *.
simpl.
remember (compute_expr (ge_of rho) (ve_of rho) (te_of rho) e).
destruct v; intuition; 
remember (typeof e); destruct t0; intuition. 

remember (field_offset i f). destruct r; intuition.

Qed. *)

Lemma typecheck_expr_sound : forall Delta rho e P,
 typecheck_environ rho Delta = true -> 
             (typecheck_expr Delta e = P ->
              denote_tc_assert P rho ->
             typecheck_val (eval_expr rho e) (typeof e) = true).
Proof. intros. 
assert (TC := typecheck_both_sound Delta rho e P). intuition. Qed.


(*Figure out where this is used, would not hold when pointers typecheck as
ints*)
Lemma get_typed_int:
    forall v att, typecheck_val v (Tint I32 Signed att) = true -> 
                      exists i:int, v = Vint i.
intros; destruct v; inv H; eauto.
Qed.

Definition is_ptr_type (ty: type) : bool :=
  match ty with
  | Tpointer _ _ => true
  | Tarray _ _ _ => true
  | Tfunction _ _ => true
  | Tstruct _ _ _ => true
  | Tunion _ _ _ => true
  | _ => false
end.

(*Not going to work because of null pointer
Lemma get_typed_ptr:
   forall v ty, 
                   typecheck_val v ty = true -> 
                   is_ptr_type ty = true ->
                      exists b, exists ofs, v = Vptr b ofs.
Proof.
intros; destruct v; destruct ty; inv H; eauto; inv H0.
Qed.*)


Lemma eval_expr_relate:
  forall Delta ge rho e m,
              filter_genv ge = ge_of rho ->
              typecheck_environ rho Delta = true ->
              tc_expr Delta e rho ->
              Clight_sem.eval_expr ge (ve_of rho) (te_of rho) m e  (eval_expr rho e).
Admitted.

Lemma eval_lvalue_relate:
  forall Delta ge rho e m,
              filter_genv ge = ge_of rho ->
              typecheck_environ rho Delta = true ->
              tc_lvalue Delta e rho ->
              exists b, exists ofs, 
              Clight_sem.eval_lvalue ge (ve_of rho) (te_of rho) m e b ofs /\
              eval_lvalue rho e = Vptr b ofs.
Admitted. 

Definition set_temp_assigned (Delta:tycontext) id :=
match (temp_types Delta) ! id with
| Some (ty, _) => ( PTree.set id (ty,true) (temp_types Delta)  
                    , var_types Delta, ret_type Delta)
| None => Delta (*Shouldn't happen *)
end.

Parameter join_tycon: tycontext -> tycontext -> tycontext.

(*Definition bool_expr Delta e := typecheck_expr Delta e && is_skalar_type (typeof e).*)

(*Rework when I figure out how non-pure typecheck will work now... probably just make sure there is
no tc_FF in the assertion*)
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
 (fold_right (fun (temp : ident *type) tenv, let (id,ty):= temp in PTree.set id (ty,false) tenv) 
  (PTree.empty (type * bool)) func.(fn_temps)) func.(fn_params),
fold_right (fun (var : ident * type) venv, let (id, ty) := var in PTree.set id ty venv) 
   (PTree.empty type) func.(fn_vars) ,
fn_return func).