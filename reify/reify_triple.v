Require Import floyd.proofauto.
Require Import reverse_defs.
Require Import MirrorShard.Expr.
Require Import sep.
Require Import wrapExpr.
Require Import types.
Require Import reify_derives.
Require Import functions.
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

Import ListNotations.

Fixpoint pos_to_expr (p: positive) :=
match p with
  | xI p' => Func functions.xI_f [pos_to_expr p']
  | xO p' => Func functions.xO_f [pos_to_expr p']
  | xH => Func functions.xH_f []
end.

Definition Z_to_expr (z : Z) :=
match z with
| Zpos p => Func functions.Zpos_f [pos_to_expr p]
| Zneg p => Func functions.Zneg_f [pos_to_expr p]
| Z0 => Func functions.Z0_f []
end.

Definition optN_to_expr (on : option N) :=
match on with
    Some N0 => Func Some_N_f [Func N0_f []]
  | Some (Npos p) => Func Some_N_f [Func Npos_f [pos_to_expr p]]
  | None => Func None_N_f []
end.

Definition bool_to_expr (b: bool) :=
match b with
| true => Func true_f []
| false => Func false_f []
end.

Definition attr_to_expr (a : attr) :=
match a with
{| attr_volatile := b; attr_alignas := a |} =>
Func mk_attr_f [bool_to_expr b; optN_to_expr a]
end.

Definition intsize_to_expr (sz : intsize) :=
match sz with
I8 => Func I8_f []
| I16 => Func I16_f []
| I32 => Func I32_f [] 
| IBool => Func IBool_f []
end.
Print floatsize.


Definition floatsize_to_expr (sz: floatsize) :=
match sz with
F32 => Func F32_f []
| F64 => Func F64_f []
end.


Definition signedness_to_expr (s: signedness) :=
match s with
  Signed => Func signed_f [] 
| Unsigned => Func unsigned_f []
end.

Print Ctypes.type.
Locate Tlist.
Fixpoint type_to_expr (ty : Ctypes.type) :=
match ty with
  | Tvoid => Func functions.Tvoid_f []
  | Tint sz sn attr => Func functions.Tint_f [intsize_to_expr sz; signedness_to_expr sn; attr_to_expr attr]
  | Tlong sg attr => Func functions.Tlong_f [signedness_to_expr sg; attr_to_expr attr]
  | Tfloat fs attr => Func functions.Tfloat_f [floatsize_to_expr fs; attr_to_expr attr] 
  | Tpointer t attr => Func functions.Tpointer_f [type_to_expr t; attr_to_expr attr] 
  | Tarray t z attr => Func functions.Tpointer_f [type_to_expr t; Z_to_expr z; attr_to_expr attr] 
  | Tfunction tl t => Func functions.Tfunction_f [typelist_to_expr tl; type_to_expr t]
  | Tstruct id fl attr => Func Tstruct_f [pos_to_expr id; fieldlist_to_expr fl; attr_to_expr attr]
  | Tunion id fl attr => Func Tunion_f [pos_to_expr id; fieldlist_to_expr fl; attr_to_expr attr]
  | Tcomp_ptr id attr => Func Tcomp_ptr_f [pos_to_expr id; attr_to_expr attr]
end

with typelist_to_expr tl :=
match tl with
  Ctypes.Tnil => Func Tnil_f []
| Ctypes.Tcons h t => Func Tcons_f [type_to_expr h; typelist_to_expr t]
end

with fieldlist_to_expr fl :=
match fl with 
 Fnil => Func Fnil_f []
| Fcons id ty t => Func Fcons_f [pos_to_expr id; type_to_expr ty; fieldlist_to_expr t]
end.

(*
Fixpoint msubst_eval_expr (P: PTree.t val) (e: Clight.expr) 
(i32m : Z -> nat) (i64m : Z -> nat) (fm : float -> nat) (env : ident -> option expr)
 : expr :=
 match e with
 | Econst_int i ty => Func functions.vint_f [Func (i32m (Int.intval i)) []]
 | Econst_long i ty => Func functions.vlong_f [Func (i64m (Int64.intval i)) []]
 | Econst_float f ty => Func functions.vfloat_f [Func (fm f) []]
 | Etempvar id ty => match env id with
                                 | Some v => v
                                 | None => Func (functions.eval_id_f nil) [pos_to_expr id] (*eval_id_lift?? maybe fail... this isn't right though, fail might be right, this may not be possible*) 
                                 end
(* | Eaddrof a ty => msubst_eval_lvalue_expr P a *)
 | Eunop op a ty =>  Func functions.eval_unop [op_to_expr op; type_to_expr ty; msubst_eval_expr a]
 | _ => Func functions.O_f []
end.


 | Ebinop op a1 a2 ty =>  
                  `(eval_binop op (typeof a1) (typeof a2)) (msubst_eval_expr P a1) (msubst_eval_expr P a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (msubst_eval_expr P a)
 | Evar id ty => `(deref_noload ty) (eval_var id ty)
 | Ederef a ty => `(deref_noload ty) (`force_ptr (msubst_eval_expr P a))
 | Efield a i ty => `(deref_noload ty) (`(eval_field (typeof a) i) (msubst_eval_lvalue P a))
 end

 with msubst_eval_lvalue (P: PTree.t val) (e: Clight.expr) : environ -> val := 
 match e with 
 | Evar id ty => eval_var id ty
 | Ederef a ty => `force_ptr (msubst_eval_expr P a)
 | Efield a i ty => `(eval_field (typeof a) i) (msubst_eval_lvalue P a)
 | _  => `Vundef
 end.*)

(*
Definition symexe (t : Triple) : Triple :=
match (Tcommand t) with
| (Ssequence (Sset v e) c) => 
 {| Tprop := tprop t;
    Tlocal := (
| _ => t
end.*)




Lemma triple : forall p contents sh q r,
exists POSTCONDITION,
semax Delta2
     (PROP  (p = q)
      LOCAL  (`(eq p) (eval_id _p); `(eq q) (eval_id r))  SEP  (`(lseg LS sh contents p nullval)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip) POSTCONDITION.
intros. eexists.
forward. 
simpl ((temp_types Delta) ! _w).
 pose_env.
reify_triple.
reflect_triple.
Abort.
