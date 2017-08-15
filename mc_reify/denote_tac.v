Require Import MirrorCore.Lambda.ExprDsimul.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Export MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Import MirrorCharge.RTac.Tactics.
Import ExprDenote.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import func_defs.
Require Import funcs.
Require Import types.

Ltac cbv_denote g' e :=
eval cbv [
              g'
          reflect_prop reflect Expr_expr_fs RType_typ Typ2_tyArr RSym_sym
                      RSym_Func'

		  (* ExprD' *)
          ExprI.exprD' funcAs  typeof_sym typeof_func
          typeof_func_opt
          type_cast (*type_cast_typ*)
          exprD'_simul func_simul
          ExprD.Expr_expr
          ExprDsimul.ExprDenote.exprD'
          (* RSym *)

          SymSum.RSym_sum Rcast Relim Rsym eq_sym symD (*RSym_env*)
          Rcast_val eq_rect_r eq_rect Datatypes.id

          (* Monad *)

          Monad.bind Monad.ret

          OptionMonad.Monad_option

          (* HList *)

          HList.hlist_hd HList.hlist_tl

          (* TypesI *)

          TypesI.typD
          typ2_match typ2 typ2_cast
          typ0_match typ0 typ0_cast (*SubstTypeD_typ*)
          (* ExprI *)

          MirrorCore.VariablesI.Var ExprVariables.ExprVar_expr
          MirrorCore.VariablesI.UVar
          MirrorCore.Lambda.ExprVariables.ExprUVar_expr
          ExprI.exprT_Inj ExprI.exprT_UseV ExprI.exprT_UseU
          exprT_App ExprI.exprT OpenT
          nth_error_get_hlist_nth

          exprT_GetVAs exprT_GetUAs

          (* ILogicFunc*)

          ILogicFunc.mkEntails ILogicFunc.mkTrue ILogicFunc.mkFalse
          ILogicFunc.mkAnd ILogicFunc.mkOr ILogicFunc.mkImpl
          ILogicFunc.mkExists ILogicFunc.mkForall

          ILogicFunc.fEntails ILogicFunc.fTrue ILogicFunc.fFalse ILogicFunc.fAnd
          ILogicFunc.fOr ILogicFunc.fImpl ILogicFunc.fExists ILogicFunc.fForall
          ILogicFuncSumL ILogicFuncSumR ILogicFuncExpr
          ILogicFunc.RSym_ilfunc
          MirrorCharge.ModularFunc.ILogicFunc.ILogicFuncInst

          ILogicFunc.funcD ILogicFunc.typ2_cast_quant ILogicFunc.typ2_cast_bin

          (* BILogicFunc *)

          BILogicFunc.mkEmp BILogicFunc.mkStar BILogicFunc.mkWand

          BILogicFunc.fEmp BILogicFunc.fStar BILogicFunc.fWand

          BILogicFuncSumL BILogicFuncSumR BILogicFuncExpr
          BILogicFunc.RSym_bilfunc BILogicFunc.BILogicFuncInst

          BILogicFunc.funcD BILogicFunc.typ2_cast_bin

          BILogicFunc.typeof_bilfunc

          (* LaterFunc *)

          LaterFunc.mkLater

          LaterFunc.fLater

          LaterFunc.LaterFuncSumL LaterFunc.LaterFuncSumR LaterFunc.LaterFuncExpr
          LaterFunc.RSym_later_func LaterFunc.LaterFuncInst

          LaterFunc.funcD LaterFunc.typ2_cast'

          LaterFunc.typeof_later_func

          (* EmbedFunc *)

          EmbedFunc.mkEmbed

          EmbedFunc.fEmbed

          EmbedFunc.EmbedFuncSumL EmbedFunc.EmbedFuncSumR EmbedFunc.EmbedFuncExpr
          EmbedFunc.RSym_embed_func EmbedFunc.EmbedFuncInst

          EmbedFunc.funcD EmbedFunc.typ2_cast_bin


          EmbedFunc.typeof_embed_func

          (* BaseFunc *)

          BaseFunc.BaseFuncSumL BaseFunc.BaseFuncSumR BaseFunc.BaseFuncExpr

          BaseFunc.BaseFuncInst
          BaseFunc.mkNat BaseFunc.mkString BaseFunc.mkBool
          BaseFunc.mkEq BaseFunc.mkPair

          BaseFunc.fNat BaseFunc.fString BaseFunc.fBool
          BaseFunc.fEq BaseFunc.fPair

          BaseFunc.RSym_BaseFunc

          BaseFunc.typeof_base_func BaseFunc.base_func_eq BaseFunc.base_func_symD
          BaseFunc.RelDec_base_func

          (* ListFunc *)

          ListFunc.ListFuncSumL ListFunc.ListFuncSumR ListFunc.ListFuncExpr

          ListFunc.ListFuncInst
          ListFunc.mkNil ListFunc.mkCons ListFunc.mkLength
          ListFunc.mkZip ListFunc.mkMap ListFunc.mkFold

          ListFunc.fNil ListFunc.fCons ListFunc.fLength
          ListFunc.fZip ListFunc.fMap ListFunc.fFold

          ListFunc.typeof_list_func ListFunc.list_func_eq ListFunc.list_func_symD
          ListFunc.RelDec_list_func

		  (* OpenFunc *)
		
		  OpenFunc.mkConst OpenFunc.mkAp OpenFunc.mkVar OpenFunc.mkNull OpenFunc.mkStackGet
		  OpenFunc.mkStackSet OpenFunc.mkApplySubst OpenFunc.mkSingleSubst OpenFunc.mkSubst
		  OpenFunc.mkTruncSubst
		
		  OpenFunc.fConst OpenFunc.fAp OpenFunc.fVar OpenFunc.fNull OpenFunc.fStackGet
		  OpenFunc.fApplySubst OpenFunc.fSingleSubst OpenFunc.fSubst OpenFunc.fTruncSubst
		
		  OpenFunc.OpenFuncSumL OpenFunc.OpenFuncSumR OpenFunc.OpenFuncExpr
		  OpenFunc.OpenFuncInst
		
		  OpenFunc.typeof_open_func OpenFunc.RSym_OpenFunc
		  OpenFunc.typ2_cast_bin OpenFunc.typ3_cast_bin
		  OpenFunc.RelDec_open_func
		
		  OpenFunc.RSym_OpenFunc_obligation_1

          (* BaseType *)

          BaseType.tyPair BaseType.tyNat BaseType.tyString BaseType.tyBool
          BaseType.btPair BaseType.btNat BaseType.btBool BaseType.btString

          (* ListType *)

          ListType.tyList ListType.btList

          (* SubstType *)

          SubstType.tyVar SubstType.tyVal SubstType.tySubst
          SubstType.stSubst

          (*Denotation*)
constD
z_opD
int_opD
valueD
evalD
otherD
sepD
dataD
typD
funcs.funcD
smxD

typeof_func
typeof_const
typeof_z_op
typeof_int_op
typeof_value
typeof_eval
typeof_other
typeof_sep
typeof_data
typeof_smx

(* OTHER *)

          (*SubstType_typ*)

          goalD propD exprD'_typ0 exprD split_env

          amap_substD
          substD
          FMapSubst.SUBST.raw_substD
          UVarMap.MAP.fold
          FMapPositive.PositiveMap.fold
          FMapPositive.PositiveMap.xfoldi
          FMapPositive.append
          UVarMap.MAP.from_key
          pred
          plus
          Pos.to_nat
          Pos.iter_op
          app
          HList.hlist_app
          Quant._foralls
          Quant._exists
          goalD_Prop

(* type equality*)
typ_eq_dec typ_rec typ_rect sumbool_rec sumbool_rect eq_rec eq_rect eq_rec_r eq_rect_r False_ind eq_ind expr.eqb_type expr.eqb_intsize expr.eqb_signedness expr.eqb_attr
expr.eqb_option expr.eqb_floatsize Bool.eqb BinNat.N.eqb expr.eqb_calling_convention expr.eqb_ident
f_equal False_rect False_rec

(*SymEnv*)
SymEnv.funcD
SymEnv.fdenote
SymEnv.RSym_func
SymEnv.func_typeof_sym
SymEnv.ftype
FMapPositive.PositiveMap.find
elem_ctor
Tactics.elem_ctor

Ext
func_defs.reflect

exprD_Prop
Tactics.exprD_Prop

goalD_Prop
Tactics.exprD_Prop

goalD_aux
Tactics.goalD_aux
Typ0_tyProp

func_defs.RSym_ilfunc
func_defs.ilops
ILogic.lforall
ILogic.ILogicOps_Prop
ILogic.lentails
ILogicOps_mpred

ILogic.land

reptyp_reptype
reptype_reptyp
typD_reptyp_reptype
data_at_lemmas.type_mut
proj1T
proj2T
data_at_lemmas.is_Fnil
ModularFunc.ILogicFunc.typeof_func
reptyp
reptyp_structlist
reptyp_unionlist

 exportclight.Clightdefs.tvoid
 exportclight.Clightdefs.tschar
 exportclight.Clightdefs.tuchar
 exportclight.Clightdefs.tshort
 exportclight.Clightdefs.tushort
 exportclight.Clightdefs.tint
 exportclight.Clightdefs.tuint
 exportclight.Clightdefs.tbool
 exportclight.Clightdefs.tlong
 exportclight.Clightdefs.tulong
 exportclight.Clightdefs.tfloat
 exportclight.Clightdefs.tdouble
 exportclight.Clightdefs.tptr
 exportclight.Clightdefs.tarray

eq_ind_r
eq_ind
          ] in e.

Ltac cbv_denote_goal :=
match goal with
[ |- ?G] => let x := cbv_denote hd G in change x
end.

Require Import VST.floyd.proofauto.

(*
Definition t_struct_a :=
   (Tstruct 5%positive (Fcons 3%positive tint (Fcons 1%positive tint Fnil)) noattr).

Goal forall n, n = reptyp_reptype t_struct_a (Vint Int.zero, Vint Int.zero).
intros.
unfold t_struct_a.
cbv_denote_goal.
unfold type_mut, proj1T, proj2T.
unfold eq_ind_r, eq_ind.
cbv_denote_goal.
*)

(*Tactic Notation "cbv_denote" "in" ident(H) := cbv_denote_in H.*)
(*Locate goalD_Prop.

Require Import reify.
Require Import VST.floyd.proofauto.

Goal forall p e,
(@semax e empty_tycontext
     p
      Sskip
     (normal_ret_assert p)).
intros.
reify_vst (semax empty_tycontext p Sskip (normal_ret_assert p)).
assert (forall n, n = func_defs.reflect tbl nil nil e0 (typrop)).
intros.
 unfold tbl, e0.
cbv_denote.
Locate elem_ctor.
 cbv [elem_ctor].
Abort.
*)
