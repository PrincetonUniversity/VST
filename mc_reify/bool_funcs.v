Require Import veric.expr.
Require Import veric.SeparationLogic.
Require Import floyd.local2ptree.
Require Import floyd.client_lemmas.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Fixpoint denote_tc_assert_b_norho a:=
match a with 
| tc_TT => true
| tc_andp' a b => andb (denote_tc_assert_b_norho a) (denote_tc_assert_b_norho b)
| tc_orp' a b => orb (denote_tc_assert_b_norho a) (denote_tc_assert_b_norho b)
| _ => false
end.

Definition tc_expr_b_norho Delta e :=
denote_tc_assert_b_norho (typecheck_expr Delta e).

Definition tc_temp_id_b_norho id t Delta e:=
denote_tc_assert_b_norho (typecheck_temp_id id t Delta e).

Lemma tc_expr_b_sound : 
forall e Delta rho,
tc_expr_b_norho Delta e = true ->
tc_expr Delta e rho .
Proof.
intros.
unfold tc_expr, tc_expr_b_norho in *. 
induction (typecheck_expr Delta e); simpl in *; unfold_lift; simpl; auto; try congruence. 
rewrite andb_true_iff in *. intuition.
rewrite orb_true_iff in *. intuition.
Qed.

Lemma tc_temp_id_b_sound : 
forall id t Delta e rho,
tc_temp_id_b_norho id t Delta e= true ->
tc_temp_id id t Delta e rho .
Proof.
intros. 
unfold tc_temp_id, tc_temp_id_b_norho in *.
induction (typecheck_temp_id id t Delta e); simpl in *; unfold_lift; simpl; auto; try congruence.
rewrite andb_true_iff in *. intuition.
rewrite orb_true_iff in *. intuition.
Qed.

Fixpoint msubst_eval_expr_norho (T1: PTree.t val) (T2: PTree.t (type * val)) (e: Clight.expr) : option val :=
  match e with
  | Econst_int i ty => Some (Vint i)
  | Econst_long i ty => Some (Vlong i)
  | Econst_float f ty => Some (Vfloat f)
  | Econst_single f ty => Some (Vsingle f)
  | Etempvar id ty => PTree.get id T1
  | Eaddrof a ty => msubst_eval_lvalue_norho T1 T2 a 
  | Eunop op a ty =>  option_map (eval_unop op (typeof a)) (msubst_eval_expr_norho T1 T2 a) 
  | Ebinop op a1 a2 ty => match (msubst_eval_expr_norho T1 T2 a1), (msubst_eval_expr_norho T1 T2 a2) with
                            | Some v1, Some v2 => Some (eval_binop op (typeof a1) (typeof a2) v1 v2) 
                            | _, _ => None
                          end
  | Ecast a ty => option_map (eval_cast (typeof a) ty) (msubst_eval_expr_norho T1 T2 a)
  | Evar id ty => option_map (deref_noload ty)
                    match PTree.get id T2 with
                    | Some (ty', v) =>
                      if eqb_type ty ty'
                      then Some v
                      else None
                    | None => None
                    end
  | Ederef a ty => option_map (deref_noload ty) (option_map force_ptr (msubst_eval_expr_norho T1 T2 a))
  | Efield a i ty => option_map (deref_noload ty) (option_map (eval_field (typeof a) i) (msubst_eval_lvalue_norho T1 T2 a))
  end
  with msubst_eval_lvalue_norho (T1: PTree.t val) (T2: PTree.t (type * val)) (e: Clight.expr) : option val := 
  match e with 
  | Evar id ty => match PTree.get id T2 with
                  | Some (ty', v) =>
                    if eqb_type ty ty'
                    then Some v
                    else None
                  | None => None
                  end
  | Ederef a ty => option_map force_ptr (msubst_eval_expr_norho T1 T2 a)
  | Efield a i ty => option_map (eval_field (typeof a) i) (msubst_eval_lvalue_norho T1 T2 a)
  | _  => Some Vundef
  end.

Definition localD (temps : PTree.t val) (locals : PTree.t (type * val)) :=
LocalD temps locals nil.

Definition assertD (P : list Prop) (Q : list (environ -> Prop)) (sep : list mpred) := 
PROPx P (LOCALx Q (SEPx (map (liftx) sep))).
