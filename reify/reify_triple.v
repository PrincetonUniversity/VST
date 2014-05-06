Require Import floyd.proofauto.
Require Import reverse_defs.
Require Import MirrorShard.Expr.
Require Import sep.
Require Import wrapExpr.
Require Import types.
Require Import reify_derives.
Require Import MirrorShard.ReifyExpr MirrorShard.ReifySepExpr.

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
  Tpost : ret_assert
}.

Section denotation.

Variable functions : functions our_types.
Variable preds : Sep.predicates our_types.
Variable uvars : Expr.env our_types.


Definition reflect_prop e := force_Opt (exprD functions uvars nil e tvProp) False.
Definition False' (_ : environ) := False.
Definition reflect_local (e: expr) :=  (force_Opt (exprD functions uvars nil e (Expr.tvType 17)) False').

Definition s_reflect (e : sepE) := 
match e with
| all_lift sexpr => `(Sep.sexprD functions preds uvars nil sexpr)
| one_arg expr => force_Opt (exprD functions uvars nil expr (Expr.tvType 18)) FF
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
Ltac change_eqs' l :=
try
match l with
| ?H :: ?T => match H with
                | `(eq ?l) (eval_id ?r) => change H with (functions.lift_eq l r)
              end; change_eqs' T
end.

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
              let res := constr:((Func 55%nat (e_r :: v_r :: nil)) :: rest_r) in
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
    [ |- ?P] => replace P with w by (exact (eq_refl _))
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
abbreviate_triple. 

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

types.tycontext_tv lift_prop_tv
types.c_expr_tv types.c_type_tv types.environ_tv types.val_tv types.share_tv 
types.ident_tv types.list_val_tv types.list_int_tv types.int_tv types.Z_tv
types.nat_tv types.positive_tv types.bool_tv types.comparison_tv types.tc_assert_tv 
types.our_types 

types.tycontext_type
types.c_expr_type types.c_type_type types.environ_type types.val_type types.share_type 
types.ident_type types.list_val_type types.list_int_type  types.int_type types.Z_type
types.nat_type types.positive_type types.bool_type types.comparison_type
types.tc_assert_type
types.no_eqb_type 

Env.repr Env.listToRepr].


Lemma triple : forall p contents sh q r,
exists POSTCONDITION,
semax Delta
     (PROP  (p = q)
      LOCAL  (`(eq p) (eval_id _p); `(eq q) (eval_id r))  SEP  (`(lseg LS sh contents p nullval)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip) POSTCONDITION.
intros. eexists. pose_env.
reify_triple.
reflect_triple.
Abort.
