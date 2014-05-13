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

Fixpoint ident_to_expr (i: ident) :=
match i with 
  | xI p' => Func functions.xIp_f [ident_to_expr p']
  | xO p' => Func functions.xOp_f [ident_to_expr p']
  | xH => Func functions.xHp_f []
end. 

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

Definition int32_to_expr (i : int) :=
Func int_repr_f [Z_to_expr (Int.intval i)].

Definition int64_to_expr (i : int64) :=
Func int_repr_f [Z_to_expr (Int64.intval i)].

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


Fixpoint type_to_expr (ty : Ctypes.type) :=
match ty with
  | Tvoid => Func functions.Tvoid_f []
  | Tint sz sn attr => Func functions.Tint_f [intsize_to_expr sz; signedness_to_expr sn; attr_to_expr attr]
  | Tlong sg attr => Func functions.Tlong_f [signedness_to_expr sg; attr_to_expr attr]
  | Tfloat fs attr => Func functions.Tfloat_f [floatsize_to_expr fs; attr_to_expr attr] 
  | Tpointer t attr => Func functions.Tpointer_f [type_to_expr t; attr_to_expr attr] 
  | Tarray t z attr => Func functions.Tpointer_f [type_to_expr t; Z_to_expr z; attr_to_expr attr] 
  | Tfunction tl t => Func functions.Tfunction_f [typelist_to_expr tl; type_to_expr t]
  | Tstruct id fl attr => Func Tstruct_f [ident_to_expr id; fieldlist_to_expr fl; attr_to_expr attr]
  | Tunion id fl attr => Func Tunion_f [ident_to_expr id; fieldlist_to_expr fl; attr_to_expr attr]
  | Tcomp_ptr id attr => Func Tcomp_ptr_f [ident_to_expr id; attr_to_expr attr]
end

with typelist_to_expr tl :=
match tl with
  Ctypes.Tnil => Func Tnil_f []
| Ctypes.Tcons h t => Func Tcons_f [type_to_expr h; typelist_to_expr t]
end

with fieldlist_to_expr fl :=
match fl with 
 Fnil => Func Fnil_f []
| Fcons id ty t => Func Fcons_f [ident_to_expr id; type_to_expr ty; fieldlist_to_expr t]
end.

Definition unop_to_expr o :=
match o with
    Onotbool => Func Onotbool_f []
  | Onotint => Func Onotint_f []
  | Oneg => Func Oneg_f []
end.

Print Cop.binary_operation.
Definition binop_to_expr o :=
match o with
    Oadd => Func Oadd_f []
  | Osub => Func Osub_f []
  | Omul => Func Omul_f []
  | Odiv => Func Odiv_f []
  | Omod => Func Omod_f []
  | Oand => Func Oand_f []
  | Oor => Func Oor_f [] 
  | Oxor => Func Oxor_f []
  | Oshl => Func Oshl_f []
  | Oshr => Func Oshr_f []
  | Oeq => Func Oeq_f [] 
  | One => Func One_f [] 
  | Olt => Func Olt_f [] 
  | Ogt => Func Ogt_f []
  | Ole => Func Ole_f [] 
  | Oge => Func Oge_f []
end.

Definition float_to_expr (f:float) := Func functions.O_f []. (*Placeholder, deal with floats later*)

Fixpoint msubst_eval_expr (P: PTree.t expr) (e: Clight.expr) 
 : expr :=
 match e with
 | Econst_int i ty => Func functions.vint_f [int32_to_expr i]
 | Econst_long i ty => Func functions.vlong_f [int64_to_expr i]
 | Econst_float f ty => Func functions.vfloat_f [float_to_expr f]
 | Etempvar id ty => match P ! id with
                                 | Some v => v
                                 | None => Func (functions.eval_id_f nil) [ident_to_expr id] (*eval_id_lift?? maybe fail... this isn't right though, fail might be right, this may not be possible*) 
                                 end
 | Eaddrof a ty => msubst_eval_lvalue_expr P a 
 | Eunop op a ty =>  Func eval_unop_f [unop_to_expr op; type_to_expr ty; 
                                       msubst_eval_expr P a  ]
 | Ebinop op a1 a2 ty => Func eval_binop_f [binop_to_expr op; type_to_expr ty;
                                            msubst_eval_expr P a1  ;
                                            msubst_eval_expr P a2  ]
 | Ecast a ty => Func eval_cast_f [type_to_expr (Clight.typeof a); type_to_expr ty;
                                   msubst_eval_expr P a  ]
 | Evar id ty => (*Func deref_noload [type_to_expr ty; ]*) Func functions.O_f [] (*shouldn't happen?*)
 | Ederef a ty => Func deref_noload_f [type_to_expr ty; 
                                       Func force_ptr_f 
                                            [msubst_eval_expr P a ]]
 | Efield a i ty => Func deref_noload_f [type_to_expr ty;
                                          Func eval_field_f
                                               [type_to_expr (Clight.typeof a);
                                                 ident_to_expr i;
                                                 msubst_eval_expr P a ]]
end
with msubst_eval_lvalue_expr (P: PTree.t expr) (e: Clight.expr) := 
       match e with 
         | Evar id ty => Func functions.O_f []
         | Ederef a ty => Func force_ptr_f 
                               [msubst_eval_expr P a ]
         | Efield a i ty =>  Func eval_field_f
                                  [type_to_expr (Clight.typeof a);
                                    ident_to_expr i;
                                    msubst_eval_lvalue_expr P a ]
         | _  =>  Func functions.O_f []
 end.



(*Compute lift_eq_f.*)
(*111%nat is supposed to be Compute lift_eq_f. lift_eq_f breaks things for some reason*)
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
end. 
Check PTree.set.

Fixpoint make_P' P l funcs :=
match l with
Func 111%nat [val_e; id_e] :: t => make_P' (PTree.set (reflect_id id_e funcs) val_e P) t funcs
| _ => P
end.

Definition make_P funcs l :=
make_P' (PTree.empty expr) l funcs.
Check lift_eq.

Definition symexe (t : Triple) funcs : Triple :=
match (Tcommand t) with
| (Ssequence (Sset id e) c) => 
 {|Tdelta := Tdelta t; 
   Tprop := Tprop t;
   Tlocal := (Func 114%nat [msubst_eval_expr (make_P funcs (Tlocal t)) e; ident_to_expr id] :: Tlocal t);
   Tsep := Tsep t;
   Tcommand := c;
   Tpost := Tpost t
 |}
| _ => t
end.

Axiom symexe_sound : forall funcs preds uenv trip, TripleD funcs preds uenv (symexe trip funcs) ->
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
forward.
reify_triple.
apply symexe_sound.
reflect_triple. simpl. 

assert (
(PROP  ()
      LOCAL  (`(eq (Vint (Int.repr 0))) (eval_id _w); 
      `(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))
|--
(PROP  ()
      LOCAL 
      (`(eq
           (Vint
              {|
              Int.intval := 0;
              Int.intrange := Int.Z_mod_modulus_range' 0 |}))
         (eval_id 19%positive); `(eq p) (eval_id _p))
      SEP  (`(lseg LS sh contents p nullval)))).
entailer!.

assert (
derives (PROP  (p = q)
      LOCAL 
      (`eq (eval_id _w)
         (eval_expr (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)));
      `(eq p) (eval_id _p); `(eq q) (subst _w `x (eval_id r))))
(PROP  (p = q)
      LOCAL 
      (`(eq
           (Vint
              {|
              Int.intval := 0;
              Int.intrange := Int.Z_mod_modulus_range' 0 |}))
         (eval_id 19%positive); `(eq p) (eval_id _p); 
      `(eq q) (eval_id r))  SEP  (`(lseg LS sh contents p nullval)))).

Abort.
