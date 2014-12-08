Require Import mc_reify.func_defs.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.RTac.Core.
(*Require Import MirrorCharge.RTac.ReifyLemma.*)
Require Import mc_reify.update_tycon.

Section tbled.

Existing Instance SubstUpdate_ctx_subst.

Parameter tbl : SymEnv.functions RType_typ.

Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.



Definition REFLEXIVITYTAC : rtac typ (expr typ func) :=
fun tus tvs n m c s e => 
  match e with 
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l r ty s with
    | Some s => RTac.Core.Solved s 
    | None =>  RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Lemma REFLEXIVITYTAC_sound  :
rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) REFLEXIVITYTAC.
unfold rtac_sound.
intros.
 unfold rtac_spec.
simpl in *.
Admitted.

Definition REFLEXIVITY := REFLEXIVITYTAC.

<<<<<<< HEAD
Definition REFLEXIVITY_DENOTE (rtype : typ) (H: @RelDec.RelDec (typD rtype) eq) tbl : rtac typ (expr typ func) := 
   fun tus tvs lus lvs c s e => (
=======
Definition REFLEXIVITY_BOOL : rtac typ (expr typ func) := 
   fun tus tvs lus lvs c s e =>(
>>>>>>> 68e6d6750bf218c26d1d686ec1c9eb2d19942bfc
match e with
| (App (App (Inj (inr (Other (feq _)))) l) r) =>
  match reflect tbl nil nil l rtype, reflect tbl nil nil r rtype with
  | Some v1, Some v2 => if @RelDec.rel_dec _ eq H v1 v2 then Solved s else Fail
  | _, _ => Fail
  end
| _ => Fail
end).

<<<<<<< HEAD
Definition REFLEXIVITY_BOOL := REFLEXIVITY_DENOTE tybool _.

Instance eq_dec : @RelDec.RelDec (option Ctypes.type) eq.
  constructor.
  intros x y.
  destruct x eqn:?, y eqn:?.
  + exact (expr.eqb_type t t0).
  + exact false.
  + exact false.
  + exact true.
Defined.

Definition REFLEXIVITY_OP_CTYPE := REFLEXIVITY_DENOTE (tyoption tyc_type) _.


=======
End tbled.
>>>>>>> 68e6d6750bf218c26d1d686ec1c9eb2d19942bfc
