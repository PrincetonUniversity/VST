Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.ExprCore.
Require Import types.
Require Import funcs.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.


Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Declare Patterns patterns_vst_typ := typ.
Reify Declare Patterns patterns_vst := (ExprCore.expr typ func).

Reify Declare Syntax reify_vst_typ :=
  { (@Patterns.CPatterns _ patterns_vst_typ (@Patterns.CFail typ)) }.

Reify Declare Typed Table term_table : BinNums.positive => reify_vst_typ.

Let Ext x := @ExprCore.Inj typ func (inl (inl (inl x))).

Reify Declare Syntax reify_vst :=
  { (@Patterns.CVar (expr typ func) (@ExprCore.Var typ func)
    (@Patterns.CPatterns _ patterns_vst
    (@Patterns.CApp _ (@ExprCore.App typ func)
    (@Patterns.CAbs (expr typ func) reify_vst_typ (@ExprCore.Abs typ func)
    (@Patterns.CTypedTable _ _ _ term_table Ext
    (@Patterns.CFail (expr typ func)))))))
}.

Reify Pattern patterns_vst_typ += (!!Values.val) => tyval.
Reify Pattern patterns_vst_typ += (@RImpl (?0) (?1)) => 
       (fun (a b : Patterns.function reify_vst_typ) => tyArr a b). 
Reify Pattern patterns_vst_typ += (!!list_dt.listspec @ ?!0 @ ?!1 ) =>
       (fun (a : id Ctypes.type) (b : id AST.ident) => tylistspec a b).
Reify Pattern patterns_vst_typ += (!!AST.ident) => tyident.
Reify Pattern patterns_vst_typ += (!!expr.environ) => tyenviron.
Reify Pattern patterns_vst_typ += (!!shares.share) => tyshare.
Reify Pattern patterns_vst_typ += (!!shares.Share.t) => tyshare.
Reify Pattern patterns_vst_typ += (!!list @ ?0) =>
       (fun (a : Patterns.function reify_vst_typ) => tylist a).
Reify Pattern patterns_vst_typ += (!!expr.mpred) => tympred.
Reify Pattern patterns_vst_typ += (!!Prop) => typrop. 
Reify Pattern patterns_vst_typ += (!!juicy_extspec.OracleKind) => tyOracleKind.

Reify Pattern patterns_vst_typ += (!!Integers.Int.int) => tyint.
Reify Pattern patterns_vst_typ += (!!Clight.expr) => tyc_expr.
Reify Pattern patterns_vst_typ += (!!Ctypes.type) => tyc_type.
Reify Pattern patterns_vst_typ += (!!expr.tycontext) => tytycontext.
Reify Pattern patterns_vst_typ += (!!BinNums.Z) => tyZ.
Reify Pattern patterns_vst_typ += (!!Datatypes.nat) => tynat.
Reify Pattern patterns_vst_typ += (!!BinNums.positive) => typositive.
Reify Pattern patterns_vst_typ += (!!expr.tc_assert) => tytc_assert.
Reify Pattern patterns_vst_typ += (!!Integers.comparison) => tycomparison.
Reify Pattern patterns_vst_typ += (!!Integers.int64) => tyint64.
Reify Pattern patterns_vst_typ += (!!Floats.float) => tyfloat.
Reify Pattern patterns_vst_typ += (!!Ctypes.typelist) => tytypelist.
Reify Pattern patterns_vst_typ += (!!Ctypes.fieldlist) => tyfieldlist.
Reify Pattern patterns_vst_typ += (!!Cop.binary_operation) => tybinary_operation.
Reify Pattern patterns_vst_typ += (!!Cop.unary_operation) => tyunary_operation.
Reify Pattern patterns_vst_typ += (!!BinNums.N ) => tyN.
Reify Pattern patterns_vst_typ += (!!option @ ?0) => 
    (fun (a : function reify_vst_typ) => tyoption a).
Reify Pattern patterns_vst_typ += (!!sum @ ?0 @ ?1) => 
    (fun (a b : function reify_vst_typ) => tysum a b).
Reify Pattern patterns_vst_typ += (!!prod @ ?0 @ ?1) => 
    (fun (a b : function reify_vst_typ) => typrod a b).
Reify Pattern patterns_vst_typ += (!!unit) => tyunit.
Reify Pattern patterns_vst_typ += (!!Clight.statement) => tystatement.
Reify Pattern patterns_vst_typ += (!!seplog.ret_assert) => tyret_assert.
Reify Pattern patterns_vst_typ += (!!SeparationLogic.ret_assert) => tyret_assert.

Reify Pattern patterns_vst_typ += (!!(lift.lifted (expr.LiftEnviron Prop))) => 
(tyArr tyenviron typrop).
Reify Pattern patterns_vst_typ += (!!(lift.lifted (expr.LiftEnviron expr.mpred))) => 
(tyArr tyenviron tympred).

Reify Pattern patterns_vst_typ += (!!@list_dt.elemtype @ ?0 @ ?1 @ ?2) =>
(fun (a : id Ctypes.type) (b : id AST.ident) (c : id (list_dt.listspec a b)) => 
  reptyp_structlist (@list_dt.all_but_link b (@list_dt.list_fields a b c))).

(*Zop*)

Reify Pattern patterns_vst += (!!BinInt.Z.lt) => (@Inj typ func (inr (Zop fZ_lt))).
Reify Pattern patterns_vst += (!!BinInt.Z.le) => (@Inj typ func (inr (Zop fZ_le))).
Reify Pattern patterns_vst += (!!BinInt.Z.gt) => (@Inj typ func (inr (Zop fZ_gt))).
Reify Pattern patterns_vst += (!!BinInt.Z.ge) => (@Inj typ func (inr (Zop fZ_ge))).
Reify Pattern patterns_vst += (!!BinInt.Z.add) => (@Inj typ func (inr (Zop fZ_add))).
Reify Pattern patterns_vst += (!!BinInt.Z.sub) => (@Inj typ func (inr (Zop fZ_sub))).
Reify Pattern patterns_vst += (!!BinInt.Z.mul) => (@Inj typ func (inr (Zop fZ_mul))).
Reify Pattern patterns_vst += (!!BinInt.Z.div) => (@Inj typ func (inr (Zop fZ_div))).
Reify Pattern patterns_vst += (!!Zdiv.Zmod) => (@Inj typ func (inr (Zop fZ_mod))).
Reify Pattern patterns_vst += (!!BinInt.Z.max) => (@Inj typ func (inr (Zop fZ_max))).
Reify Pattern patterns_vst += (!!BinInt.Z.opp) => (@Inj typ func (inr (Zop fZ_opp))).

Reify Pattern patterns_vst += (!!Integers.Int.add) => (@Inj typ func (inr (Intop fint_add))).
Reify Pattern patterns_vst += (!!Integers.Int.lt) => (@Inj typ func (inr (Intop fint_lt))).
Reify Pattern patterns_vst += (!!Integers.Int.ltu) => (@Inj typ func (inr (Intop fint_ltu))).
Reify Pattern patterns_vst += (!!Integers.Int.mul) => (@Inj typ func (inr (Intop fint_mul))).
Reify Pattern patterns_vst += (!!Integers.Int.neg) => (@Inj typ func (inr (Intop fint_neg))).
Reify Pattern patterns_vst += (!!Integers.Int.sub) => (@Inj typ func (inr (Intop fint_sub))).
Reify Pattern patterns_vst += (!!Integers.Int.cmp) => (@Inj typ func (inr (Intop fint_cmp))).
Reify Pattern patterns_vst += (!!Integers.Int.cmpu) => (@Inj typ func (inr (Intop fint_cmpu))).
Reify Pattern patterns_vst += (!!Integers.Int.repr) => (@Inj typ func (inr (Intop fint_repr))).
Reify Pattern patterns_vst += (!!Integers.Int.signed) => (@Inj typ func (inr (Intop fint_signed))).
Reify Pattern patterns_vst += (!!Integers.Int.unsigned) => (@Inj typ func (inr (Intop fint_unsigned))).
Reify Pattern patterns_vst += (!!Integers.Int.max_unsigned) => (@Inj typ func (inr (Intop fint_max_unsigned))).
Reify Pattern patterns_vst += (!!Integers.Int.repr) => (@Inj typ func (inr (Intop fint64_repr))).

Reify Pattern patterns_vst += (!!Values.Vint) => (@Inj typ func (inr (Value fVint))).
Reify Pattern patterns_vst += (!!Values.Vfloat) => (@Inj typ func (inr (Value fVfloat))).
Reify Pattern patterns_vst += (!!Values.Vlong) => (@Inj typ func (inr (Value fVlong))).
Reify Pattern patterns_vst += (!!Values.Vptr) => (@Inj typ func (inr (Value fVptr))).
Reify Pattern patterns_vst += (!!Values.Vundef) => (@Inj typ func (inr (Value fVundef))).

Reify Pattern patterns_vst += (!!expr.eval_cast) => (@Inj typ func (inr (Eval_f feval_cast))).
Reify Pattern patterns_vst += (!!expr.deref_noload) => (@Inj typ func (inr (Eval_f fderef_noload))).
Reify Pattern patterns_vst += (!!expr.eval_field) => (@Inj typ func (inr (Eval_f feval_field))).
Reify Pattern patterns_vst += (!!expr.eval_binop) => (@Inj typ func (inr (Eval_f feval_binop))).
Reify Pattern patterns_vst += (!!expr.eval_unop) => (@Inj typ func (inr (Eval_f feval_unop))).
Reify Pattern patterns_vst += (!!expr.eval_id) => (@Inj typ func (inr (Eval_f feval_id))).

Reify Pattern patterns_vst += (!!Zpower.two_power_nat) =>  (@Inj typ func (inr (Other ftwo_power_nat))).
Reify Pattern patterns_vst += (!!expr.force_ptr) =>  (@Inj typ func (inr (Other fforce_ptr))). 
Reify Pattern patterns_vst += (!!and) =>  (@Inj typ func (inr (Other fand))).
Reify Pattern patterns_vst += (!!Coqlib.align) =>  (@Inj typ func (inr (Other falign))).
Reify Pattern patterns_vst += (!!seplog.typed_true) => (@Inj typ func (inr (Other ftyped_true))).
Reify Pattern patterns_vst += 
      (!!@eq @ ?0) => (fun (a : function reify_vst_typ) 
                       => @Inj typ func (inr (Other (feq a)))).

Reify Pattern patterns_vst += 
      (!!seplog.derives) => (fEntails (func := expr typ func) tympred).
Reify Pattern patterns_vst += 
      (!!seplog.sepcon) => (fStar (func := expr typ func) tympred).
Reify Pattern patterns_vst += 
      (!!seplog.emp) => (mkEmp (func := func) tympred).
Reify Pattern patterns_vst +=
      (!!@list_dt.lseg @ ?0 @ ?1 @ ?2) => 
         (fun  (a : id Ctypes.type) (b : id AST.ident) 
               (c : id (list_dt.listspec a b)) =>
              (@Inj typ func (inr (Sep (flseg a b c))))).
Reify Pattern patterns_vst += (!!seplog.TT) => (mkTrue (func := func) tympred).
Reify Pattern patterns_vst += (!!seplog.FF) => (mkFalse (func := func) tympred).
Reify Pattern patterns_vst += (!!seplog.andp) => (fAnd (func := expr typ func) tympred).
Reify Pattern patterns_vst += (!!seplog.orp) => (fOr (func := expr typ func) tympred).
Reify Pattern patterns_vst += (!!SeparationLogic.local) => (@Inj typ func (inr (Sep flocal))).
Reify Pattern patterns_vst += (!!seplog.prop) => (@Inj typ func (inr (Sep fprop))).

Reify Pattern patterns_vst += (!!client_lemmas.PROPx) => (@Inj typ func (inr (Triple fPROPx))).
Reify Pattern patterns_vst += (!!client_lemmas.LOCALx) => (@Inj typ func (inr (Triple fLOCALx))).
Reify Pattern patterns_vst += (!!client_lemmas.SEPx) => (@Inj typ func (inr (Triple fSEPx))).

Reify Pattern patterns_vst += (!!SeparationLogic.normal_ret_assert) => (@Inj typ func (inr (Triple fnormal_ret_assert))).
Reify Pattern patterns_vst += (!!seplog.normal_ret_assert) => (@Inj typ func (inr (Triple fnormal_ret_assert))).


Reify Pattern patterns_vst += (!!@SeparationLogicSoundness.SoundSeparationLogic.CSL.semax) => (@Inj typ func (inr (Triple fsemax))).

Reify Pattern patterns_vst += (!!semax.semax) => (@Inj typ func (inr (Triple fsemax))).


Reify Pattern patterns_vst += (!!(@seplog.exp expr.mpred SeparationLogic.Nveric) @ ?0) => 
     (fun (a : function reify_vst_typ) => (fExists (func := expr typ func) a tympred)).

Reify Pattern patterns_vst += (!!(@seplog.allp expr.mpred SeparationLogic.Nveric) @ ?0) => 
     (fun (a : function reify_vst_typ) => (fForall (func := expr typ func) a tympred)).



Reify Pattern patterns_vst +=
      (!!@data_at_lemmas.data_at @ ?0) => 
         (fun  (a : id Ctypes.type)  =>
              (@Inj typ func (inr (Sep (fdata_at a ))))).
Reify Pattern patterns_vst +=
      (!!@data_at_lemmas.field_at @ ?0 @ ?1) => 
         (fun  (a : id Ctypes.type) (b : id (list AST.ident)) =>
              (@Inj typ func (inr (Sep (ffield_at a b))))).

Reify Pattern patterns_vst += 
      (!!@map @ ?0 @ ?1) => (fun (a b: function reify_vst_typ) => 
                          (@Inj typ func (inr (Lst (fmap a b))))).

Reify Pattern patterns_vst +=
      (!!@nil @ ?0) => (fun (a : function reify_vst_typ) => 
        (@Inj typ func (inr (Lst (fnil a))))).

Reify Pattern patterns_vst +=
      (!!@fold_right @ ?0 @ ?1) => (fun (a b: function reify_vst_typ) =>
        (@Inj typ func (inr (Lst (ffold_right a b))))).

Reify Pattern patterns_vst +=
      (!!@fold_left @ ?0 @ ?1) => (fun (a b: function reify_vst_typ) =>
        (@Inj typ func (inr (Lst (ffold_left a b))))).

Reify Pattern patterns_vst +=
      (!!@cons @ ?0) => (fun (a : function reify_vst_typ) => 
        (@Inj typ func (inr (Lst (fcons a))))).

Reify Pattern patterns_vst +=
      (!!@app @ ?0) => (fun (a : function reify_vst_typ) => 
        (@Inj typ func (inr (Lst (fappend a))))).


Reify Pattern patterns_vst += 
      (RHasType AST.ident (?0)) => (fun (a : id AST.ident) 
                                       => (@Inj typ func (inr (Const (Pos a))))).

Reify Pattern patterns_vst += 
      (RHasType Clight.statement (?0)) => (fun (a : id Clight.statement) 
                                       => (@Inj typ func (inr (Triple (fstatement a))))).

Reify Pattern patterns_vst += 
      (RHasType expr.tycontext (?0)) => (fun (a : id expr.tycontext) 
                                       => (@Inj typ func (inr (Triple (ftycontext a))))).

Reify Pattern patterns_vst += 
      (RHasType (Maps.PTree.tree (Ctypes.type * bool) * Maps.PTree.t Ctypes.type * Ctypes.type *
       Maps.PTree.tree expr.global_spec) (?0)) => (fun (a : id expr.tycontext) 
                                       => (@Inj typ func (inr (Triple (ftycontext a))))).


Reify Pattern patterns_vst += (RPi (?0) (?1)) => (fun (x : function reify_vst_typ) (y : function reify_vst) => 
  ExprCore.App (fForall (func := expr typ func) x typrop)
               (Abs x y)).



Ltac reify_typ trm :=
  let k e :=
      pose e
  in
  reify_expr reify_vst_typ k [ True ] [ trm ].


(*Ltac reify_vst trm:=
(*match goal with
[ |- ?trm ] => *)
  let k e :=
      pose e
  in
  reify_expr reify_vst k [ True ] [ trm ]
(*end*).*)

Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_vst e :=
  let k fs e :=
      pose e in
  reify_expr reify_vst k
             [ (fun (y : @mk_dvar_map_abs _ _ _ (list Type) _ term_table elem_ctor) => True) ]
             [ e ].

