Require Export msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.

Definition eval_expr (rho: environ) (e: expr) : val :=
   compute_expr (ge_of rho) (ve_of rho) (te_of rho) e.

Definition eval_lvalue (rho: environ) (e: expr) : val :=
   compute_lvalue (ge_of rho) (ve_of rho) (te_of rho) e.

(*Temps, vars, function return*)
Definition tycontext: Type := prod (prod (PTree.t type) (PTree.t type)) type.

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
(*
Parameter combine_types : type -> type -> option type .

Definition compatable_types (t1: type) (t2 : type) : bool :=
match combine_types t1 t2 with
| Some _ => true
| None => false
end.
*)
Parameter b: bool.
Check (andb b b).
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
| Tpointer _ _ => true
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

Definition isBinOpResultType op a1 a2 ty : bool :=
match op with
  | Oadd => match classify_add (typeof a1) (typeof a2) with 
                    | add_default => false
                    | add_case_ii _ => is_int_type ty 
                    | add_case_pi _ _ | add_case_ip _ _ => 
                        is_pointer_type ty
                    | _ => is_float_type ty
                    end
  | Osub => match classify_sub (typeof a1) (typeof a2) with 
                    | sub_default => false
                    | sub_case_ii _ => is_int_type ty 
                    | sub_case_pi _ => is_pointer_type ty
                    | sub_case_pp _ => false
                    | _ => is_float_type ty
                    end 
  | Omul => match classify_mul (typeof a1) (typeof a2) with 
                    | mul_default => false
                    | mul_case_ii _ => is_int_type ty
                    | _ => is_float_type ty
                    end 
  | Omod | Odiv | Oshl | Oshr => false (*pushing this to command because of possible non-evaluation*)
  | Oand | Oor  | Oxor => match classify_binint (typeof a1) (typeof a2) with
                          | binint_case_ii _ => is_int_type ty
                          | _ => false
                          end   
  | Oeq | One | Olt 
    | Ogt | Ole | Oge => 
       match classify_cmp (typeof a1) (typeof a2) with
       | cmp_case_pp | cmp_default => false
       | _ => is_int_type ty
       end
end.


Definition isCastResultType tfrom tto ty : bool :=
match classify_cast tfrom tto with
| cast_case_default | 
   cast_case_f2i _ _ => false
| cast_case_neutral  => type_eq tfrom ty
| _ => match tto with 
      | Tint _ _ _  => is_int_type ty
      | Tfloat _ _  => is_float_type ty
      | _ => false
      end
end.


(* NOTE: typecheck_expr allows only _pure_ expressions that don't access the heap if pure=true *)
Fixpoint typecheck_expr_pure (Delta : tycontext) (e: expr) : bool :=
let tcr := typecheck_expr_pure Delta in
match e with
 | Econst_int _ (Tint _ _ _) => true 
 | Econst_float _ (Tfloat _ _) => true
 | Etempvar id ty => match (temp_types Delta)!id with 
                       | Some ty' => type_eq ty ty' 
		       | None => false 
                     end
 | Eaddrof a ty => typecheck_lvalue_pure Delta a && is_pointer_type (ty)
 | Eunop op a ty => (isUnOpResultType op a ty) && (tcr a)
 | Ebinop op a1 a2 ty => (isBinOpResultType op a1 a2 ty) && (tcr a1) && (tcr a2)
 | Econdition a1 a2 a3 ty => (tcr a1) && (tcr a2) && (tcr a3) && (is_skalar_type (typeof a1)) && (*int or pointer*)
                              (isCastResultType (typeof a2) ty ty) && (isCastResultType (typeof a3) ty ty)
 | Ecast a ty => (tcr a) && isCastResultType (typeof a) (ty) ty
 | _ => false
end

with typecheck_lvalue_pure (Delta: tycontext) (e: expr) : bool :=
match e with
 | Evar id ty => match (var_types Delta) ! id with 
                  | Some ty' => type_eq ty ty' && 
                                negb (type_is_volatile ty')
                  | None => false
                 end
 | Ederef a ty => typecheck_expr_pure Delta a && is_pointer_type (typeof a)
 | Efield a i ty => typecheck_expr_pure Delta a && match typeof a with
                            | Tstruct id fList att =>
                                  match field_offset i fList with 
                                  | Errors.OK delta => true
                                  | _ => false
                                  end
                            | Tunion id fList att => true
                            | _ => false
                            end
 | _  => false
end.

(*Declaring these for now so uses everywhere else match up...
typecheck_expr with no boolean is the "pure" typecheck*)
Definition typecheck_expr Delta e : bool :=
typecheck_expr_pure Delta e.

Definition typecheck_lvalue Delta e : bool :=
typecheck_lvalue_pure Delta e.

Definition typecheck_exprlist Delta := forallb (typecheck_expr Delta).

(*BE SURE TO CHECK IF INT SHOULD TYPE CHECK AS POINTER*)
Definition typecheck_val (v: val) (ty: type) : bool :=
 match v, ty with
 | Vint i, Tint _ _ _ => true  (* Maybe this needs to be adjusted to account for
                                               the size of the int?  Maybe not? *)
 | Vfloat v, Tfloat _ _ => true (*  Maybe this needs to be adjusted, ditto *)
(*I don't think this matters now, I believe an int should always be an int*)
 (*| Vint i, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => 
                    negb (Int.eq i Int.zero) (*commented for now, double check *)*)
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
                           else match ge id with
                                | Some (_, ty') => if type_eq ty ty' then 
                                                   typecheck_var_environ tl ve ge else
                                                   false
                                | None => false
                                end
                  | None => false
                  end
 | nil => true
end.

Definition typecheck_environ (env : environ) (Delta: tycontext) : bool :=
typecheck_temp_environ (PTree.elements (temp_types Delta)) (te_of env) &&
typecheck_var_environ (PTree.elements (var_types Delta)) (ve_of env) (ge_of env).

Definition temp_element_correct (te : temp_env) :=
(fun (tyconEl : (PTree.elt * type)) => let (id,elt) := tyconEl in
  match te ! id with
  | Some v => True
  | _ => False
end). 

Definition te_correct (te : temp_env) (Delta: tycontext) := Forall
  (temp_element_correct te)
  (PTree.elements (temp_types Delta)).

Definition var_element_correct (ve: env) (ge:genviron) : 
(PTree.elt * type) -> Prop :=
(fun (varel : (PTree.elt * type)) => let (id,ty) := varel in
  match ve ! id with
  | Some (_,ty') => if type_eq ty ty' then True else
        match (ge id) with
        | Some (_,ty2') => if type_eq ty ty2' then True else False 
        | None => False
        end
  | None => False
  end).

Definition ve_correct (ve:env) (ge:genviron) (Delta: tycontext) :=
Forall (var_element_correct ve ge) (PTree.elements (var_types Delta)).


Lemma typecheck_environ_sound : forall ge te ve Delta,
(*Incomplete, final lemma will have ge_correct and ve correct
maybe not... at least in pure mode*)
typecheck_environ (mkEnviron ge ve te) Delta = true ->
te_correct te Delta.
Proof.
intros.
unfold typecheck_environ in *. destruct Delta. destruct p.
unfold te_correct.
unfold temp_types in *. simpl in *. induction (PTree.elements t0).
auto.
unfold temp_element_correct.
simpl in *. destruct a. rewrite Forall_forall; intros.
destruct x. simpl in H0. destruct H0. inv H0. destruct (te!e). auto. inv H.
destruct (te!p). remember (typecheck_val v t2). destruct b0. 
intuition. rewrite Forall_forall in *. unfold temp_element_correct in *.
specialize (H1 (e,t3)). intuition. inv H. inv H.
Qed.

Lemma in_fst_in : forall A B (L : list (A*B)) (a:A) (b:B), In (a, b) L  -> In a (map (@fst A B) L) .
Proof.
intros A B L. induction L; intros. auto. simpl in *. inv H. auto. right. eapply IHL. apply H0.
Qed.


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
try destruct i; try destruct s; try destruct i0; try destruct s0; intuition;(
simpl in *;
try solve [do 2 try
match goal with
| [ |- context[compute_expr ?ge ?ve ?te ?e]] => remember (compute_expr ge ve te e) as compR; destruct compR
end; try destruct t; auto; intuition; try (of_bool_destruct; auto)])). 
Qed.*)

Lemma typecheck_both_sound: 
  forall Delta rho e, 
             typecheck_environ rho Delta = true -> 
             (typecheck_expr Delta e = true ->
             typecheck_val (eval_expr rho e) (typeof e) = true) /\
             (typecheck_lvalue Delta e = true -> 
             typecheck_val (eval_lvalue rho e) (Tpointer Tvoid noattr)=true).
Proof.
intros. induction e; intuition.
simpl. destruct t; auto; simpl in H0; inv H0; intuition.

simpl in *. destruct t; intuition. 

simpl in *. unfold eval_lvalue. simpl.

 admit. (*________________Finish when typecheck-environ is done*)

(*tempvar*)
admit. (*________________________________________________________Also need to figure out typecheck-environ*)
(* simpl in *. destruct rho. apply typecheck_environ_sound in H. 
unfold te_correct in *. unfold te_complete in *. unfold type_element_correct in *.
unfold type_element_complete in *. intuition. rewrite Forall_forall in *. 

unfold eval_expr. unfold compute_expr. simpl. unfold force_val.
remember (te ! i). destruct o. remember (Delta ! i). destruct o.
  symmetry in Heqo0. apply PTree.elements_correct in Heqo0. specialize (H1 (i,v)).
  symmetry in Heqo. apply PTree.elements_correct in Heqo. intuition.
  specialize (H2 (i,t0)). intuition. remember (te ! i).  destruct o; auto.
  remember (Delta ! i); destruct o; auto. remember (type_eq t t0).
  destruct s; intuition. subst. clear H0. clear Heqs. symmetry in Heqo2. 
  apply PTree.elements_correct in Heqo2. 
  assert (norep := PTree.elements_keys_norepet Delta). 
    assert (t0 = t1). eapply no_rep_in_pair; eauto. subst; auto.
  intuition. remember (Delta ! i). destruct o. symmetry in Heqo0. 
  apply PTree.elements_correct in Heqo0. specialize (H2 (i,t0)). intuition.
  rewrite <- Heqo in H. intuition. intuition.
*)

(*deref*)
simpl in *. rewrite andb_true_iff in *; intuition. 
unfold eval_lvalue. simpl. unfold eval_expr in *.
remember (compute_expr (ge_of rho) (ve_of rho) (te_of rho) e).
destruct v; intuition; destruct (typeof e); intuition. 

(*addrof*)
unfold eval_expr in *. simpl in *. rewrite andb_true_iff in *; intuition. 
destruct t; intuition.

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

Qed. (*Threeish admits for figuring out type context!!-------------------------------*)



Lemma typecheck_expr_sound : forall Delta rho e,
 typecheck_environ rho Delta = true -> 
             (typecheck_expr Delta e = true ->
             typecheck_val (eval_expr rho e) (typeof e) = true).
Proof.
apply typecheck_both_sound. Qed.


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

Lemma get_typed_ptr:
   forall v ty, 
                   typecheck_val v ty = true -> 
                   is_ptr_type ty = true ->
                      exists b, exists ofs, v = Vptr b ofs.
Proof.
intros; destruct v; destruct ty; inv H; eauto; inv H0.
Qed.

(*do we get (most of) this with a proof relating compute_expr to eval_expr?
and existing soundness proofs?*)
Lemma eval_expr_relate:
  forall Delta ge rho e m,
              filter_genv ge = ge_of rho ->
              typecheck_environ rho Delta = true ->
              typecheck_expr Delta e = true ->
              Clight_sem.eval_expr ge (ve_of rho) (te_of rho) m e  (eval_expr rho e).
Admitted.

Lemma eval_lvalue_relate:
  forall Delta ge rho e m,
              filter_genv ge = ge_of rho ->
              typecheck_environ rho Delta = true ->
              typecheck_lvalue Delta e = true ->
              exists b, exists ofs, 
              Clight_sem.eval_lvalue ge (ve_of rho) (te_of rho) m e b ofs /\
              eval_lvalue rho e = Vptr b ofs.
Admitted. 

Fixpoint typecheck_stmt (Delta: tycontext) (c: Clight.statement) {struct c} : bool :=
 match c with
 | Clight.Sskip => true
 | Clight.Sassign e1 e2 => 
                          typecheck_expr Delta e1 &&
                          typecheck_expr Delta e2 &&
                          true (* also check t1 matches t2 *)
 | Clight.Sset id e2 => 
                          true &&
                          (typecheck_expr Delta e2  (* this case for pure expressions  *)
                          || typecheck_lvalue Delta e2)  (* this case for top-level loads *)
                       &&   true (* also check t1 matches t2 *)
 | _ => true  (* et cetera *)
 end.
 
(* Admitted: move to expr.v *)
Parameter func_tycontext: Clight.function -> tycontext.


