Require Import floyd.proofauto.
Require Import reverse_defs.
Require Import MirrorShard.Expr.
Require Import sep.
Require Import wrapExpr.
Require Import types.
Require Import reify_derives.
Require Import functions.
Require Import MirrorShard.ReifyExpr MirrorShard.ReifySepExpr.
Require Import msl.Axioms.
Require Import MirrorShard.Env.
Require Import c_to_expr.

Local Open Scope logic.

Existing Instance NullExtension.Espec.

Inductive sepE :=
| all_lift : Sep.sexpr -> sepE
| one_arg : expr -> sepE.

Record Triple := mkTriple
{ Tdelta : tycontext;
  Tprop : list expr;
  Tlocal : list expr;
  Tsep : list sepE;
  Tcommand : statement;
  Tpost : ret_assert(*;
  Tret : option exitkind*)
}.

Section denotation.

Variable functions : functions (all_types_r (@nil type)).
Variable preds : Sep.predicates (all_types_r (@nil type)).
Variable uvars : Expr.env (all_types_r (@nil type)).


Definition reflect_prop e := force_Opt (exprD functions uvars nil e tvProp) False.
Definition False' (_ : environ) := False.
Definition True' (_ : environ) := True.
Definition reflect_local (e: expr) :=  (force_Opt (exprD functions uvars nil e (Expr.tvType 17)) False').

Definition s_reflect (e : sepE) := 
match e with
| all_lift sexpr => `(Sep.sexprD functions preds uvars nil sexpr)
| one_arg expr => force_Opt (exprD functions uvars nil expr (Expr.tvType 18)) TT
end.

(*Redefining map so we won't unfold user maps when we reflect *)
Fixpoint map' {A B} (f : A -> B) (l : list A) : list B :=
 match l with
  | nil => nil
  | a :: t => f a :: map' f t
  end.


Definition reflect_Tprop l :=
map' reflect_prop l.

Definition reflect_Tlocal l :=
map' reflect_local l.

Definition reflect_Tsep l := 
map' s_reflect l.

Definition PreD t :=
PROPx (reflect_Tprop (Tprop t)) 
      ( LOCALx (reflect_Tlocal (Tlocal t)) 
               (SEPx (reflect_Tsep (Tsep t)))).

Definition TripleD t :=
  semax (Tdelta t) (PreD t) (Tcommand t) ((Tpost t)).

End denotation.
                
(*shouldn't need these, can probably do this as part of reification*)
(*Ltac change_eqs' l :=
try
match l with
| ?H :: ?T => match H with
                | `(eq ?l) (eval_id ?r) => change H with (functions.lift_eq l r)
              end; change_eqs' T
end.*)

Ltac change_eqs :=
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] => change_eqs Q
end.

Ltac is_const f := false.


Ltac reify_exprs isConst es types funcs uvars vars k :=
  match es with
    | tt => k uvars funcs (@nil expr)
    | nil => idtac "nill"; idtac k; k uvars funcs (@nil expr)
    | (?e, ?es) =>
      reify_expr ltac:(isConst) e types funcs uvars vars ltac:(fun uvars funcs e =>
        reify_exprs ltac:(isConst) es types funcs uvars vars ltac:(fun uvars funcs es =>
          let res := constr:(e :: es) in
          k uvars funcs res))
    | ?e :: ?es => idtac "consc";
      reify_expr ltac:(isConst) e types funcs uvars vars ltac:(fun uvars funcs e =>
        idtac "cons"; reify_exprs ltac:(isConst) es types funcs uvars vars ltac:(fun uvars funcs es =>
  let res := constr:(e :: es) in
          k uvars funcs res))
  end.


Ltac reify_props types funcs uvars vars k := 
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_exprs is_const P types funcs uvars (@nil bool) k
end. 

Ltac reify_props_change types funcs uvars vars  :=
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_props types funcs uvars vars 
ltac:(fun uvars funcs res =>idtac "replace"; 
 change P with 
(reflect_Tprop funcs uvars res))
end.
(*Compute lift_eq_f.*)
(*114%nat is supposed to be Compute lift_eq_f. lift_eq_f breaks things for some reason*)
Ltac reify_locals' types funcs uvars vars k l :=
match l with
| nil => k uvars funcs (@nil expr)
| (`(eq ?e) (eval_id ?v))::?T => 
  reify_expr ltac:(is_const) e types funcs uvars vars ltac:(
    fun uvars' funcs' e_r => reify_expr ltac:(is_const) v types funcs' uvars' vars 
  ltac:(
        fun uvars'' funcs'' v_r => 
          reify_locals' types funcs'' uvars'' vars ltac:(
            fun uvars''' funcs''' rest_r => 
              let res := constr:((Func 114%nat (e_r :: v_r :: nil)) :: rest_r) in
              k uvars''' funcs''' res) T))
end. 
      
Ltac reify_locals types funcs uvars vars k :=
match goal with
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_locals' types funcs uvars vars k Q
end.

Ltac reify_locals_change types funcs uvars vars  :=
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_locals types funcs uvars vars 
ltac:(fun uvars funcs res =>idtac "replace"; 
 replace Q with 
(reflect_Tlocal funcs uvars res))
end.


Ltac reify_sep' types funcs preds uvars vars k l :=
match l with
| nil => k uvars funcs preds (@nil sepE)
| (`(?S) (?E) :: ?T) => fail 1000 "unimplemented"
| (`(?S)::?T) =>  
  ReifySepM.reify_sexpr ltac:(is_const) S types funcs tt tt preds uvars vars ltac:(
    fun uvars' funcs' preds' S_r => 
      reify_sep' types funcs' preds' uvars' vars ltac:(
        fun uvars'' funcs'' preds'' rest_r => 
          let res := constr:((all_lift S_r) :: rest_r) in
          k uvars'' funcs'' preds''  res) T)
end. 

Ltac reify_sep types funcs preds uvars vars k :=
match goal with
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_sep' types funcs preds uvars vars k R end.

Ltac reify_sep_change types funcs preds uvars vars :=
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_sep types funcs preds uvars vars 
ltac:(fun uvars funcs preds res =>idtac "replace"; 
 replace R with 
(reflect_Tsep funcs preds uvars res))
end.

Ltac change_goal w := 
match goal with 
    [ |- ?P] => replace P with w; [  | try (exact (eq_refl _)) ]
end.

Ltac abbreviate_triple :=
match goal with
[ |- TripleD ?f ?p ?u _ ] => 
clear_all;
abbreviate f as funcs;
abbreviate p as preds;
abbreviate u as uenv
end.

Ltac reify_triple :=
let types := get_types in
let funcs := get_funcs types in
let preds := get_predicates types in 
let uvars := get_uenv types in 
let vars := nil in 
match goal with
[ |- semax ?Delta _ ?C ?P] =>
reify_props types funcs uvars vars ltac:(
  fun uvars' funcs' props_r =>
    reify_locals types funcs' uvars' vars ltac:(
      fun uvars'' funcs'' locals_r => 
        reify_sep types funcs'' preds uvars'' vars ltac:(
          fun uvars''' funcs''' preds' sep_r => 
            change_goal (TripleD funcs''' preds' uvars''' (mkTriple Delta props_r locals_r sep_r C P)))))
end;
try abbreviate_triple. 

Import ListNotations.


Fixpoint msubst_eval_expr (P: PTree.t expr) (e: Clight.expr) 
 : option expr :=
 match e with
 | Econst_int i ty => Some (Func functions.vint_f [int32_to_expr i])
 | Econst_long i ty => Some (Func functions.vlong_f [int64_to_expr i])
 | Econst_float f ty => None (*Some (Func functions.vfloat_f [float_to_expr f])*)
 | Etempvar id ty => P ! id
 | Eaddrof a ty => msubst_eval_lvalue_expr P a 
 | Eunop op a _ => option_map (fun v => Func eval_unop_f [unop_to_expr op; type_to_expr (Clight.typeof a); v]) (msubst_eval_expr P a)  
 | Ebinop op a1 a2 ty => 
   match (msubst_eval_expr P a1), (msubst_eval_expr P a2) with
     | Some v1, Some v2 => 
       Some (Func eval_binop_f [binop_to_expr op; type_to_expr (Clight.typeof a1);
                          type_to_expr (Clight.typeof a2);
                          v1 ; v2 ])
     | _, _ => None
   end
 | Ecast a ty => option_map (fun v => 
                               Func eval_cast_f [type_to_expr (Clight.typeof a); type_to_expr ty;
                                                 v ])
                            (msubst_eval_expr P a )
 | Evar id ty => None
 | Ederef a ty => 
   option_map (fun v => (Func deref_noload_f [type_to_expr ty; Func force_ptr_f [v ]]))
              (msubst_eval_expr P a)
 | Efield a i ty => 
   option_map (fun v =>
   Func deref_noload_f [type_to_expr ty;
                         Func eval_field_f
                              [type_to_expr (Clight.typeof a);
                                ident_to_expr i; v]])
              (msubst_eval_lvalue_expr P a)
                                
end
with msubst_eval_lvalue_expr (P: PTree.t expr) (e: Clight.expr) := 
       match e with 
         | Evar id ty => None
         | Ederef a ty => 
           option_map (fun v => Func force_ptr_f 
                               [v]) (msubst_eval_expr P a)
         | Efield a i ty =>  
           option_map (fun v =>  Func eval_field_f
                                  [type_to_expr (Clight.typeof a);
                                    ident_to_expr i; v ])
                                  (msubst_eval_lvalue_expr P a)
         | _  =>  None
 end.



(*Compute lift_eq_f.*)
(*114%nat is supposed to be Compute lift_eq_f. lift_eq_f breaks things for some reason*)
Definition reflect_id (funcs' : functions (all_types_r (@nil type))) uvars e := force_Opt (exprD funcs' uvars nil e ident_tv) 1%positive.
(*
Definition reflect_id (id_e: expr) (funcs:  list (signature (all_types_r []))) : positive := 
match id_e with
  | Func id [] => 
    match nth_error funcs id with
      | Some {| Domain := nil;
                Range := tvType 12;
                Denotation := de |} => de
      | _ => 1%positive
    end
  | _ => 1%positive
end. *)

Fixpoint make_P' P l funcs' uenv:=
match l with
Func 114%nat [val_e; id_e] :: t => make_P' (PTree.set (reflect_id funcs' uenv id_e) val_e P) t funcs' uenv
| _ => P
end.

Definition make_P funcs uenv l :=
make_P' (PTree.empty expr) l funcs uenv.

Definition symexe (t : Triple) funcs uenv : Triple :=
match (Tcommand t) with
| (Ssequence (Sset id e) c) => 
  match (msubst_eval_expr (make_P funcs uenv (Tlocal t)) e) with
    | Some v => 
      {|Tdelta := update_tycon (Tdelta t) (Sset id e); 
        Tprop := Tprop t;
        Tlocal := (Func 114%nat [v ; ident_to_expr id] :: Tlocal t);
        Tsep := Tsep t;
        Tcommand := c;
        Tpost := Tpost t
      |}
    | _ => t
  end
| _ => t
end.

Axiom symexe_sound : forall funcs preds uenv trip, TripleD funcs preds uenv (symexe trip funcs uenv) ->
TripleD funcs preds uenv trip.

Ltac reflect_triple :=
let types' := get_types in
let types := get_types_name in
let funcs := get_funcs_name types' in
let preds := get_predicates_name types' in 
let uenv := get_uenv_name types' in
cbv [
TripleD Tdelta Tcommand Tpost Tprop Tlocal Tsep PreD reflect_Tprop reflect_prop map' 
force_Opt reflect_Tlocal reflect_Tsep s_reflect all_preds tvar_rec tvar_rect
exprD functionTypeD applyD reflect_local
forallEach AllProvable_impl AllProvable_gen AllProvable_and projT1 projT2 Provable lookupAs
nth_error equiv_dec length fold_right tvarD Impl_ EqDec_tvar eq_nat_dec
Basics.impl Impl Exc
Sep.sexprD Sep.SDenotation Sep.SDomain Denotation Domain Range 
VericSepLogic.himp  VericSepLogic.inj VericSepLogic.star VericSepLogic_Kernel.emp VericSepLogic.hprop
sumbool_rec sumbool_rect nat_rec nat_rect eq_rec_r eq_rec eq_rect eq_sym f_equal
funcs preds types uenv abbreviate value

functions.two_power_nat_signature functions.O_signature functions.force_ptr_signature
functions.app_val_signature functions.int_max_unsigned_signature functions.and_signature
functions.align_signature functions.cons_val_signature functions.int_sub_signature 
functions.Vint_signature functions.map_Vint_signature functions.typed_true_signature 
functions.int_add_signature functions.S_signature functions.Z_lt_signature
functions.Z_le_signature functions.Z_gt_signature functions.Z_ge_signature
functions.Zpos_signature functions.Zneg_signature functions.Z0_signature
functions.xI_signature functions.xO_signature functions.xH_signature functions.int_lt_signature
functions.int_ltu_signature functions.int_mul_signature functions.int_neg_signature 
functions.Z_add_signature functions.Z_sub_signature functions.Z_mul_signature
functions.Z_div_signature functions.Z_mod_signature functions.Z_max_signature
functions.Z_opp_signature functions.Ceq_signature functions.Cne_signature
functions.Clt_signature functions.Cle_signature functions.Cgt_signature
functions.Cge_signature functions.int_cmp_signature functions.int_cmpu_signature
functions.int_repr_signature functions.int_signed_signature functions.int_unsigned_signature
functions.nullval_signature functions.tptr_signature functions.nil_val_signature
functions.reverse_t_struct_list_signature functions.reverse__tail_signature
functions.True_signature functions.eval_id_signature
functions.lift_eq_signature functions.lift_eq functions.sep_predicates
functions.lseg_sample_ls_psig
eval_binop_signature  eval_unop_signature  Some_N_signature  None_N_signature  N0_signature
 Npos_signature true_signature false_signature mk_attr_signature I8_signature I16_signature
 I32_signature IBool_signature signed_signature unsigned_signature Tnil_signature Tcons_signature
 Fnil_signature Fcons_signature F32_signature F64_signature Onotbool_signature Onotint_signature
 Oneg_signature Oadd_signature Osub_signature Omul_signature Odiv_signature Omod_signature 
Oand_signature Oor_signature Oxor_signature Oshl_signature Oshr_signature Oeq_signature
 One_signature Olt_signature Ogt_signature Ole_signature Oge_signature eval_cast_signature
 deref_noload_signature eval_field_signature
Tvoid_signature Tint_signature Tlong_signature Tfloat_signature
 Tpointer_signature Tarray_signature Tfunction_signature
 Tstruct_signature  Tunion_signature Tcomp_ptr_signature 
xIp_signature xOp_signature xHp_signature Vint_signature Vfloat_signature Vlong_signature
int64_repr_signature tc_environ_signature False_signature 

 two_power_nat_f O_f  force_ptr_f app_val_f  int_max_unsigned_f and_f  align_f  cons_val_f
 int_sub_f vint_f  map_Vint_f  typed_true_f  int_add_f S_f Z_lt_f Z_le_f Z_gt_f Z_ge_f 
 Zpos_f  Zneg_f  Z0_f xI_f 
 xO_f xH_f int_lt_f int_ltu_f int_mul_f int_neg_f Z_add_f Z_sub_f Z_mul_f Z_div_f 
 Z_mod_f Z_max_f Z_opp_f Ceq_f Cne_f Clt_f Cle_f Cgt_f Cge_f int_cmp_f int_cmpu_f 
 int_repr_f int_signed_f int_unsigned_f nullval_f tptr_f nil_val_f 
 reverse_t_struct_list_f reverse__tail_f vfloat_f vlong_f Tvoid_f Tint_f Tlong_f 
 Tfloat_f Tpointer_f Tarray_f Tfunction_f Tstruct_f Tunion_f Tcomp_ptr_f eval_binop_f
 eval_unop_f Some_N_f None_N_f N0_f Npos_f true_f false_f mk_attr_f I8_f 
 I16_f I32_f IBool_f signed_f unsigned_f Tnil_f Tcons_f Fnil_f Fcons_f F32_f 
 F64_f Onotbool_f Onotint_f Oneg_f Oadd_f Osub_f Omul_f Odiv_f Omod_f Oand_f Oor_f Oxor_f
 Oshl_f Oshr_f Oeq_f One_f Olt_f Ogt_f Ole_f Oge_f eval_cast_f deref_noload_f
 eval_field_f int_64_repr_f xIp_f xOp_f xHp_f 

types.tycontext_tv lift_prop_tv
types.c_expr_tv types.c_type_tv types.environ_tv types.val_tv types.share_tv 
types.ident_tv types.list_val_tv types.list_int_tv types.int_tv types.Z_tv
types.nat_tv types.positive_tv types.bool_tv types.comparison_tv types.tc_assert_tv 
types.our_types typelist_tv
binary_operation_tv float_tv int64_tv floatsize_tv unary_operation_tv 
N_tv option_N_tv attr_tv intsize_tv signedness_tv fieldlist_tv 

val_map_type 
types.tycontext_type
types.c_expr_type types.c_type_type types.environ_type types.val_type types.share_type 
types.ident_type types.list_val_type types.list_int_type  types.int_type types.Z_type
types.nat_type types.positive_type types.bool_type types.comparison_type
types.tc_assert_type
types.no_eqb_type lift_prop_type
lift_mpred_type int64_type float_type
                                  attr_type signedness_type intsize_type
                                  floatsize_type typelist_type
                                  fieldlist_type binary_operation_type
                                  unary_operation_type N_type
                                  option_N_type
 val_eq.list_eqb_type  

Env.repr Env.listToRepr

symexe int32_to_expr Z_to_expr eqb_comparison make_P make_P' reflect_id msubst_eval_expr
msubst_eval_lvalue_expr  binop_to_expr unop_to_expr pos_to_expr type_to_expr
pos_to_expr Z_to_expr int32_to_expr int64_to_expr  optN_to_expr bool_to_expr attr_to_expr
intsize_to_expr  floatsize_to_expr signedness_to_expr ident_to_expr type_from_eq
value fieldlist_to_expr

Int.intval Int.repr Int.Z_mod_modulus 

PTree.get PTree.set map Clight.typeof tint tptr tlong tvoid noattr

_w].


Ltac simpl_reflect := cbv [Tdelta Tprop Tlocal Tsep PreD Tcommand Tpost] in *.

Ltac simpl_nth H :=
try match goal with
[ H : context[nth_error ?f ?n] |- _] => simpl (nth_error f n) in H
end.

Ltac simpl_reflect_local_H H:=
repeat (cbv [reflect_local TripleD reflect_Tlocal map'] in H; simpl_reflect; simpl_nth H).

Tactic Notation "simpl_reflect_local" "in" constr(H) := simpl_reflect_local_H H.
Check exprD.

Definition funcs funcs' := (our_functions nil) ++ funcs'.


Definition denote_local_ptree (P: PTree.t expr) funcs' uenv rho:=
  forall i v val , 
    Some val = exprD (funcs funcs') uenv nil v val_tv ->
    PTree.get i P = Some v -> eval_id i rho = val.

Ltac do_n n t :=
let nn := eval vm_compute in n in
match nn with
S ?n' => t; do_n n' t
| _ => idtac
end.

Hint Rewrite PTree.gempty : pt.
Ltac pts := autorewrite with pt in *; try congruence.

Fixpoint id_in_local i l funcs uenv:=
match l with
h :: t => match h with
            | Func 114%nat args => match args with
                                     | _ :: i2 :: _ => 
                                       orb (Pos.eqb (reflect_id funcs uenv i2) i) 
                                           (id_in_local i t funcs uenv)
                                     | _ => false
                                    end
            | _ => false
          end
| _ => true
end.
Check exprD.
Inductive locals_wf (funcs' : list (signature (all_types_r []))) uenv : list expr -> Prop :=
  | locals_wf_nil : locals_wf  funcs' uenv []
  | locals_wf_cons : forall tl id val v,
       id_in_local (reflect_id (funcs') uenv id) tl (funcs') uenv = false ->
       exprD funcs' uenv nil val val_tv = Some v -> 
       locals_wf funcs' uenv tl ->
       locals_wf funcs' uenv ((Func (lift_eq_f nil)  [val; id]) :: tl).

Lemma make_P_help : forall locals id id2 funcs' uenv val P 
(LWF : locals_wf (funcs funcs') uenv locals),
id_in_local id locals (funcs funcs') uenv = false ->
(make_P' (PTree.set id val P) locals (funcs funcs') uenv) ! id2 =
(PTree.set id val (make_P' P locals (funcs funcs') uenv)) ! id2 .
Proof.
induction locals; intros. simpl in *. auto.
inv LWF.
simpl in *. rewrite orb_false_iff in H. destruct H.
erewrite IHlocals; eauto.
repeat rewrite (PTree.gsspec).
destruct (peq id2 id), (peq id2 (reflect_id (funcs funcs') uenv id0)); subst;
try congruence.
subst. rewrite Pos.eqb_refl in *; congruence.
erewrite IHlocals; eauto. rewrite PTree.gss; auto.
erewrite IHlocals; eauto. rewrite PTree.gss; auto.
repeat (erewrite IHlocals; eauto).
repeat rewrite PTree.gso; auto.
Qed.

Definition make_P_sound : forall funcs' uenv locals rho 
(LWF :locals_wf (funcs funcs') uenv locals),
(fold_right (`and) (`True) (reflect_Tlocal (funcs funcs') uenv locals)) rho->
denote_local_ptree (make_P (funcs funcs') uenv locals) funcs' uenv rho.
Proof.
intros.
unfold denote_local_ptree; intros.
simpl in *.
induction locals; simpl in *. 
  + unfold make_P in H1. simpl in H1.
    pts.
  + inv LWF. unfold make_P in H1. simpl in H1.
    rewrite make_P_help in *; auto. super_unfold_lift.
    destruct H. rewrite PTree.gsspec in *.
    destruct (peq i (reflect_id (funcs funcs') uenv id)); subst.
      - inv H1. 
        unfold reflect_local in H.
        simpl in H.
        rewrite <- H0 in H. 
        unfold reflect_id.
        case_eq (exprD (funcs funcs') uenv [] id ident_tv); intros; try rewrite H1 in *.
        simpl in H. unfold lift_eq in H. super_unfold_lift. subst.
        simpl. auto. simpl.
        inv H.
      - eapply IHlocals; eauto.
Qed.

Ltac transl_H H :=
autorewrite with translate in H. 

Ltac ind1 hyp hyp2 :=
repeat
(simpl in *; try congruence; 
match goal with
| [ H0 : Some _ = Some _ |- _] => inv H0; try reflexivity; try congruence
| [ H0 : context[option_map _ (?f ?P ?e)] |- _ ]  =>
    let c := fresh "Case" in
    let v := fresh "val" in
    case_eq (f P e); [intros v c | intros c]; try rewrite c in *
| [ H0 : context[match (?f ?P ?e) with _ => _ end] |- _] =>
    let c := fresh "Case" in
    let v := fresh "val" in
    case_eq (f P e); [intros v c | intros c]; try rewrite c in *
| [ H : context[match exprD ?F ?U [] ?v val_tv with _ => _ end ] |- _] => 
  let c := fresh "Case" in
  let v := fresh "val" in
  case_eq (exprD F U [] v val_tv);  [intros v c | intros c]; rewrite c in *
| [ H : ?F ?P ?e = Some _, 
    H1 : exprD ?f ?uenv [] ?v val_tv = Some _ |- _] =>
      solve [super_unfold_lift; simpl; first [erewrite <- hyp2 | repeat erewrite <- hyp]; eauto; reflexivity]
| [ H0 : context[match exprD (?Funcs) ?uenv [] _ _ with _ => _ end] |- _] => transl_H H0

end).

Lemma msubst_eval_expr_eq:
  forall P e rho val funcs' uenv val_e, 
    denote_local_ptree P funcs' uenv rho ->
    Some val_e = msubst_eval_expr P e ->
    Some val = exprD (funcs funcs') uenv nil val_e val_tv ->
    val = eval_expr e rho
with msubst_eval_lvalue_eq: 
  forall P e rho val funcs' uenv val_e,
    denote_local_ptree P funcs' uenv rho ->
    Some val_e = msubst_eval_lvalue_expr P e ->
    Some val = exprD (funcs funcs') uenv nil val_e val_tv ->
    val = eval_lvalue e rho.
Proof with ind1 msubst_eval_expr_eq msubst_eval_lvalue_eq.
- intros.
  destruct e...
    + simpl in *. case_eq (P ! i); [intros e ce | intros ce]; rewrite ce in *.
      unfold denote_local_ptree in H.
      eapply H in H1. simpl. symmetry. apply H1. 
      congruence.
      congruence.
    + simpl. erewrite <- msubst_eval_lvalue_eq; eauto.
- intros.
  destruct e...
Qed.

Lemma wf_locals_P : forall local funcs' uenv id v,
locals_wf (funcs funcs') uenv local ->
(make_P (funcs funcs') uenv local) ! id = Some v ->
exists r, exprD (funcs funcs') uenv [] v val_tv = Some r.
Proof.
induction local; intros.
  unfold make_P in H0. simpl in H0. rewrite PTree.gempty in H0. congruence.
  simpl in *. inv H. unfold make_P in H0. simpl in H0. rewrite make_P_help in H0; auto.
  rewrite PTree.gsspec in H0. if_tac in H0. subst. inv H0. rewrite H4; eauto.
  simpl in *. eapply IHlocal; eauto. 
Qed.


Lemma wf_locals_reflect : forall e funcs' uenv local v,
locals_wf (funcs funcs') uenv local -> 
Some v = msubst_eval_expr (make_P (funcs funcs') uenv local) e ->
exists r, 
exprD (funcs funcs') uenv [] v val_tv = Some r
with wf_locals_lvalue_reflect :
forall e funcs' uenv local v,
locals_wf (funcs funcs') uenv local -> 
Some v = msubst_eval_lvalue_expr (make_P (funcs funcs') uenv local) e ->
exists r, 
exprD (funcs funcs') uenv [] v val_tv = Some r.
Proof.
- destruct e; intros; try solve [inv H0; repeat simpl in *; transl; eauto].
  + simpl in *. 
    symmetry in H0. apply wf_locals_P in H0; auto.
  + simpl in *. 
    case_eq ((msubst_eval_expr (make_P (funcs funcs') uenv local) e)); intros; rewrite H1 in *;
    simpl in *; try congruence.
    inv H0. simpl. transl. 
    case_eq (exprD (funcs funcs') uenv [] e0 val_tv); intros. eauto.
    symmetry in H1. eapply wf_locals_reflect in H1. destruct H1. congruence. auto.
  + simpl in *. case_eq ((msubst_eval_expr (make_P (funcs funcs') uenv local) e)); intros;
                try rewrite H1 in *; simpl in *; try congruence. inv H0. 
    simpl. transl. edestruct wf_locals_reflect; eauto. rewrite H0; eauto.
  + simpl in *. ind1 idtac idtac. simpl; transl.
    edestruct wf_locals_reflect. eauto. symmetry in Case. apply Case.
    edestruct wf_locals_reflect. eauto. symmetry in Case0. apply Case0.
    rewrite H1. rewrite H0. eauto.
  + ind1 idtac idtac. simpl in *. transl. edestruct wf_locals_reflect; eauto.
    rewrite H0. eauto.
  + ind1 idtac idtac. simpl; transl. edestruct wf_locals_lvalue_reflect; eauto.
    rewrite H0; eauto.
- destruct e; intros; try solve [inv H0; repeat simpl in *; transl; eauto].
  + ind1 idtac idtac. simpl in *. edestruct wf_locals_reflect; eauto.
    rewrite H0; eauto.
  + ind1 idtac idtac. simpl in *. transl.
    edestruct (wf_locals_lvalue_reflect); eauto. rewrite H0; eauto.
Qed.
 
Theorem symexe_sound_s : forall funcs' preds uenv trip
(LWF : locals_wf (funcs funcs') uenv (Tlocal trip)),
TripleD (funcs funcs') preds uenv (symexe trip (funcs funcs') uenv) ->
TripleD (funcs funcs') preds uenv trip.
intros.
unfold TripleD.
destruct trip.
destruct Tcommand0;
try solve [unfold symexe in *; simpl in *; auto].
destruct Tcommand0_1;
try solve [unfold symexe in *; simpl in *; auto].
simpl_reflect. unfold symexe in H. simpl_reflect.
unfold TripleD, PreD, Tlocal, reflect_Tlocal, reflect_Tprop in H.
revert H. case_eq (msubst_eval_expr (make_P (funcs funcs') uenv Tlocal0) e); intros. simpl in *.
unfold reflect_local in H0. simpl in H0. edestruct wf_locals_reflect; eauto.
rewrite H1 in H0. transl_H H0. simpl in H0.
eapply semax_seq.
apply sequential'. 
eapply semax_post; [ | apply forward_setx; auto]. 
intros.
Focus 3.
simpl. 
 apply H0. intro rho. normalize.
apply normal_ret_assert_derives.
entailer!.
SearchAbout subst.
Check semax_seq. intros. destruct ek; simpl. 

intros. 
Check forward_setx.
Print normal_ret_assert.
rewrite overridePost_normal'.
SearchAbout overridePost.
Check normal_ret_assert.
intros.  entailer!.
intro rho. normalize.
SearchAbout normal_ret_assert.
apply derives_extract_prop.

 simpl in H.
symmetry in H0.
extensionality.
eapply msubst_eval_expr_eq in H0; eauto.
Focus 2.
forward. Focus 2. simpl.
simpl_reflect_local in H.
simpl ((force_Opt
                 (exprD funcs uenv []
                    (Func 114%nat
                       [msubst_eval_expr (make_P funcs Tlocal0) e;
                       ident_to_expr i]) (tvType 17)) False')) in H.
unfold TripleD in H; unfold PreD in H; simpl in H.
simpl_reflect_local in H.  simpl in H.

simpl (nth_error funcs 114) in H.

compute (nth_error_funcs 114).

unfold TripleD in H0. simpl_reflect.
unfold reflect_Tlocal in H0. unfold map' in H0. simpl in H0.

let f := eval vm_compute in funcs in id_this f.

Ltac nth_unfold H :=
match goal with
[ H : context[nth_error ?funcs ?id]] 




unfold reflect_local in H0.

Ltac compute_exprD_h H :=
match goal with


 simpl in H0. rewrite H in H0.
simpl in H0.
Print closed_wrt_vars. 

*)

Lemma triple : forall p contents sh,
exists POSTCONDITION,
semax Delta2
     (PROP  ()
      LOCAL  (`(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip) POSTCONDITION.
intros. 
eexists.
pose_env.
reify_triple.
apply symexe_sound.
reflect_triple. simpl. 

assert (
(PROP  ()
      LOCAL  (`(eq (Vint (Int.repr 0))) (eval_id _w); 
      `(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval))) (*the one from forward*)
|--
(PROP  ()
      LOCAL 
      (`(eq
           (Vint
              {|
              Int.intval := 0;
              Int.intrange := Int.Z_mod_modulus_range' 0 |}))
         (eval_id 19%positive); `(eq p) (eval_id _p))
      SEP  (`(lseg LS sh contents p nullval)))). (*the one from symexe*)
entailer!.
Abort.
